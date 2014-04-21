-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_reduce.idr
-- Normalize an expression reflecting an element in a group
-------------------------------------------------------------------

module group_reduce

import Decidable.Equality
import dataTypes
import tools


--%default total

total
exprG_eq : (p:dataTypes.Group c) -> {g:Vect n c} -> {c1 : c} -> {c2 : c} -> (e1:ExprG p g c1) -> (e2:ExprG p g c2) -> (Maybe (e1=e2))
exprG_eq p (PlusG x y) (PlusG x' y') with (exprG_eq p x x', exprG_eq p y y')
  exprG_eq p (PlusG x y) (PlusG x y) | (Just refl, Just refl) = Just refl
  exprG_eq p (PlusG x y) (PlusG x' y') | _ = Nothing
exprG_eq p (VarG p i b1) (VarG p j b2) with (decEq i j, decEq b1 b2)
  exprG_eq p (VarG p i b1) (VarG p i b1) | (Yes refl, Yes refl) = Just refl
  exprG_eq p (VarG p i b1) (VarG p j b2) | _ = Nothing
exprG_eq p (ConstG p const1) (ConstG p const2) with ((group_eq_as_elem_of_set p) const1 const2)
    exprG_eq p (ConstG p const1) (ConstG p const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprG_eq p (ConstG p const1) (ConstG p const2) | _ = Nothing
exprG_eq p _ _  = Nothing


total
elimMinus : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
elimMinus p (ConstG p const) = (_ ** (ConstG p const, refl))
elimMinus p (PlusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MelimMinus1))
elimMinus p (VarG p v b) = (_ ** (VarG p v b, refl))    
elimMinus p (MinusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus p e2) in
    ((Plus r_ih1 (Neg r_ih2)) ** (PlusG e_ih1 (NegG e_ih2), ?MelimMinus2)) 
elimMinus p (NegG e1) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p e1) in
    (_ ** (NegG e_ih1, ?MelimMinus3))
  
  
-- Ex : -(a+b) becomes (-b) + (-a)
-- Not total for Idris, because recursive call with argument (NegG ei) instead of ei. Something can be done for this case with a natural number representing the size
propagateNeg : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
propagateNeg p (NegG (PlusG e1 e2)) =
  let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg p (NegG e1)) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg p (NegG e2)) in
    ((Plus r_ih2 r_ih1) ** (PlusG e_ih2 e_ih1, ?MpropagateNeg_1)) -- Carefull : - (a + b) = (-b) + (-a) in a group and *not* (-a) + (-b) in general. See mathsResults.bad_push_negation_IMPLIES_commutativeGroup for more explanations about this
propagateNeg p (NegG e) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg p e in
      (Neg r_ih1 ** (NegG e_ih1, ?MpropagateNeg_2))
propagateNeg p (PlusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MpropagateNeg_3))
propagateNeg p e =
  (_ ** (e, refl)) 
  

-- Needed because calling propagateNeg on -(-(a+b)) gives - [-b + -a] : we may need other passes
propagateNeg_fix : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
propagateNeg_fix p e = 
	let (r_1 ** (e_1, p_1)) = propagateNeg p e in
		case exprG_eq p e e_1 of -- Look for syntactical equality (ie, if we have fone some simplification in the last passe)!
			Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg_fix p e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?MpropagateNeg_fix_1))
  
      
elimDoubleNeg : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
elimDoubleNeg p (NegG (NegG e1)) =
  let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg p e1 in
    (_ ** (e_ih1, ?MelimDoubleNeg_1))
elimDoubleNeg p (NegG e) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg p e in
    ((Neg r_ih1) ** (NegG e_ih1, ?MelimDoubleNeg_2))
elimDoubleNeg p (PlusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimDoubleNeg p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimDoubleNeg p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MelimDoubleNeg_3))        
elimDoubleNeg p e1 = 
    (_ ** (e1, refl))
    

countNeg : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> Nat
countNeg p (ConstG p c1) = 0
countNeg p (PlusG e1 e2) = (countNeg p e1) + (countNeg p e2)
countNeg p (MinusG e1 e2) = (countNeg p e1) + (countNeg p e2)
countNeg p (NegG e) = 1 + (countNeg p e) 
countNeg p (VarG p i b) = 0


-- Constructs the extension of the context, using the expression "e". This extension is formed with all the Neg of something that appear in the expression "e"
construct_contextExtension : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p g c1) -> (Vect (countNeg p e) c)
construct_contextExtension c p g (ConstG p c1) = Nil
construct_contextExtension c p g (PlusG e1 e2) = (construct_contextExtension c p g e1) ++ (construct_contextExtension c p g e2)
construct_contextExtension c p g (MinusG e1 e2) = (construct_contextExtension c p g e1) ++ (construct_contextExtension c p g e2)
construct_contextExtension c p g (NegG e) = let x : c = ?M_HOW_TO_ADD_A_VARIABLE_CORRESPONDING_TO_NEG_OF_E in
                                                x :: (construct_contextExtension c p g e)
construct_contextExtension c p g (VarG p i b) = Nil


-- convert i from an element toFin n to an element of Fin m, provided that m is greater or equal than n
convertFin : {n:Nat} -> (i:Fin n) -> (m:Nat) -> Fin m
convertFin i m = ?M_CONVERT_FIN

-- Construct the extension and adds it to the current context
transfoContext : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p g c1) -> (Vect (n+countNeg p e) c)
transfoContext c p g e = g ++ (construct_contextExtension c p g e)

-- g2 is the context on which you want to have the result indexed
-- j is the next fresh variable (of type Fin m, where m is the size of the new context)
pre_encode : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (e:ExprG p g c1) -> (pm:Nat) -> (g2:Vect (S pm) c) -> (j:Fin (S pm)) -> (c2 ** ((ExprMo (group_to_monoid_class p) g2 c2, c1=c2), Fin (S pm)))
pre_encode p (ConstG p c1) pm g2 j = (c1 ** ((ConstMo (group_to_monoid_class p) c1, refl), j)) --j hasn't changed
pre_encode p (PlusG e1 e2) pm g2 j = 
    let (r_ih1 ** ((e_ih1, p_ih1), j_ih1)) = pre_encode p e1 pm g2 j in
    let (r_ih2 ** ((e_ih2, p_ih2), j_ih2)) = pre_encode p e2 pm g2 j_ih1 in -- note the use of j_ih1 in the second call
        (_ ** ((PlusMo e_ih1 e_ih2, ?M_pre_encode_1), j_ih2)) --j has potentially changed
-- Not total : Nothing for (MinusG e1 e2) since they should have been removed at this time
pre_encode p (NegG e) pm g2 (fS pj) = (_ ** ((VarMo (group_to_monoid_class p) (pj) False, ?M_pre_encode_2), pj)) -- j has changed
pre_encode p (VarG p i b) pm g2 j = (_ ** ((VarMo (group_to_monoid_class p) (convertFin i (S pm)) b, ?M_pre_encode_3), j)) -- j hasn't changed


--encode : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p g c1) -> (c2 ** (ExprMo (group_to_monoid_class p) (transfoContext c p g e) c2, c1=c2))
--encode c p g e = (_ ** (pre_encode p e (transfoContext c p g e), ?M_encode_1))


code_reduceM_andDecode : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
code_reduceM_andDecode p e = (_ ** (e, refl)) 
                                              
                                              
                                              		
mutual
--------------------------------------------
-- Simplify (+e) + (-e) at *one* level of +
--------------------------------------------
	elim_plusInverse : {c:Type} -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
	elim_plusInverse p g (ConstG p const) = (_ ** (ConstG p const, refl))
	elim_plusInverse p g (VarG p v b) = (_ ** (VarG p v b, refl))
	-- Reminder : e1 and e2 can't be a Neg themselves, because you are suppose to call elimDoubleNeg before calling this function...
	elim_plusInverse p g (PlusG (NegG e1) (NegG e2)) = 
		let (r_e1' ** (e1', p_e1')) = elim_plusInverse p g e1 in
		let (r_e2' ** (e2', p_e2')) = elim_plusInverse p g e2 in
		(_ ** ((PlusG (NegG e1') (NegG e2')), ?Melim_plusInverse_1))
	-- If e2 is not a Neg !
	elim_plusInverse p g (PlusG (NegG e1) e2) with (groupDecideEq p g e1 e2) -- compare les versions simplifiees de e1 et de e2
		elim_plusInverse p g (PlusG (NegG e1) e1) | (Just refl) = (_ ** ((ConstG _ Zero), ?Melim_plusInverse_2))
		elim_plusInverse p g (PlusG (NegG e1) e2) | _ = 
			let (r_e1' ** (e1', p_e1')) = elim_plusInverse p g e1 in
			let (r_e2' ** (e2', p_e2')) = elim_plusInverse p g e2 in
			(_ ** ((PlusG (NegG e1') e2'), ?Melim_plusInverse_2))
	-- If e1 is not a Neg !
	elim_plusInverse p g (PlusG e1 (NegG e2)) with (groupDecideEq p g e1 e2) -- compare les versions simplifiees de e1 et de e2
		elim_plusInverse p g (PlusG e1 (NegG e1)) | (Just refl) = (_ ** ((ConstG _ Zero), ?Melim_plusInverse_3))
		elim_plusInverse p g (PlusG e1 (NegG e2)) | _ = 
			let (r_e1' ** (e1', p_e1')) = elim_plusInverse p g e1 in
			let (r_e2' ** (e2', p_e2')) = elim_plusInverse p g e2 in
			(_ ** ((PlusG e1' (NegG e2')), ?Melim_plusInverse_4))
	-- If e1 and e2 are not Neg 
	elim_plusInverse p g (PlusG e1 e2) = 
		let (r_e1' ** (e1', p_e1')) = elim_plusInverse p g e1 in
		let (r_e2' ** (e2', p_e2')) = elim_plusInverse p g e2 in
		(_ ** ((PlusG e1' e2'), ?Melim_plusInverse_5))
	elim_plusInverse p g e = (_ ** (e, refl))
		
		
--------------------------------------------------------------------------
-- Simplifying (+e) + (-e) with associativity (at two levels of +) !
--------------------------------------------------------------------------
	plusInverse_assoc : {c:Type} -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
	-- (e1 + (-e2 + e3))
	plusInverse_assoc p g (PlusG e1 (PlusG (NegG e2) e3)) with (groupDecideEq p g e1 e2)
		plusInverse_assoc p g (PlusG e1 (PlusG (NegG e1) e3)) | (Just refl) = 
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in
				(_ ** (e3', ?MplusInverse_assoc_1))
		plusInverse_assoc p g (PlusG e1 (PlusG (NegG e2) e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in
				(_ ** ((PlusG e1' (PlusG (NegG e2') e3')), ?MplusInverse_assoc_2))
	
	-- (-e1 + (e2+e3))
	plusInverse_assoc p g (PlusG (NegG e1) (PlusG e2 e3)) with (groupDecideEq p g e1 e2)
		plusInverse_assoc p g (PlusG (NegG e1) (PlusG e1 e3)) | (Just refl) = 
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in 
				(_ ** (e3', ?MplusInverse_assoc_3))
		plusInverse_assoc p g (PlusG (NegG e1) (PlusG e2 e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in
				(_ ** ((PlusG (NegG e1') (PlusG e2' e3')), ?MplusInverse_assoc_4))
	
	-- ((e1+e2) + -e3))
	plusInverse_assoc p g (PlusG (PlusG e1 e2) (NegG e3)) with (groupDecideEq p g e2 e3)
		plusInverse_assoc p g (PlusG (PlusG e1 e2) (NegG e2)) | (Just refl) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
				(_ ** (e1', ?MplusInverse_assoc_5))
		plusInverse_assoc p g (PlusG (PlusG e1 e2) (NegG e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in
				(_ ** ((PlusG (PlusG e1' e2') (NegG e3')), ?MplusInverse_assoc_6))
				
	-- ((e1+(-e2)) + e3)		
	plusInverse_assoc p g (PlusG (PlusG e1 (NegG e2)) e3) with (groupDecideEq p g e2 e3)
		plusInverse_assoc p g (PlusG (PlusG e1 (NegG e2)) e2) | (Just refl) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
				(_ ** (e1', ?MplusInverse_assoc_7))
		plusInverse_assoc p g (PlusG (PlusG e1 (NegG e2)) e3) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p g e3 in
				(_ ** ((PlusG (PlusG e1' (NegG e2')) e3'), ?MplusInverse_assoc_8))
				
	plusInverse_assoc p g (PlusG e1 e2) =
		let (r_ih1 ** (e_ih1, p_ih1)) = (plusInverse_assoc p g e1) in
		let (r_ih2 ** (e_ih2, p_ih2)) = (plusInverse_assoc p g e2) in
			((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MplusInverse_assoc_9))
			
	-- Anything else
	plusInverse_assoc p g e =
		(_ ** (e, refl))


	groupReduce : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
	groupReduce c p g e = 
		let (r_1 ** (e_1, p_1)) = elimMinus p e in
		let (r_2 ** (e_2, p_2)) = propagateNeg_fix p e_1 in
		let (r_3 ** (e_3, p_3)) = elimDoubleNeg p e_2 in
		let (r_4 ** (e_4, p_4)) = elim_plusInverse p g e_3 in
		let (r_5 ** (e_5, p_5)) = plusInverse_assoc p g e_4 in
		-- IMPORTANT : At this stage, we only have negation on variables and constants.
		-- Thus, we can continue the reduction by calling the reduction for a monoid on another set, which encodes the minus :
		-- the expression (-c) is encoded as a constant c', and the variable (-x) as a varible x'
		let (r_6 ** (e_6, p_6)) = code_reduceM_andDecode p e_5 in
			(r_6 ** (e_6, ?MgroupReduce_1))
     

	buildProofGroup : (p:dataTypes.Group c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprG p g c1) -> (ExprG p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
	buildProofGroup p e1 e2 lp rp with (exprG_eq p e1 e2)
		buildProofGroup p e1 e1 lp rp | Just refl = ?MbuildProofGroup
		buildProofGroup p e1 e2 lp rp | Nothing = Nothing

    
	groupDecideEq : (p:dataTypes.Group c) -> (g:Vect n c) -> (ExprG p g x) -> (ExprG p g y) -> Maybe (x = y)
	-- e1 is the left side, e2 is the right side
	groupDecideEq p g e1 e2 = 
		let (r_e1 ** (e_e1, p_e1)) = groupReduce _ p g e1 in
		let (r_e2 ** (e_e2, p_e2)) = groupReduce _ p g e2 in
			buildProofGroup p e_e1 e_e2 p_e1 p_e2
  
---------- Proofs ----------
group_reduce.MelimMinus1 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  trivial

group_reduce.MelimMinus2 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine Minus_simpl
  
group_reduce.MelimMinus3 = proof
  intros
  rewrite p_ih1 
  trivial
  
group_reduce.MpropagateNeg_1 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine push_negation
  
group_reduce.MpropagateNeg_2 = proof
  intros
  rewrite p_ih1 
  mrefine refl
  
group_reduce.MpropagateNeg_3 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine refl
  
group_reduce.MpropagateNeg_fix_1 = proof
  intros
  rewrite p_ih1 
  exact p_1
   
group_reduce.MelimDoubleNeg_1 = proof
  intros
  rewrite p_ih1
  mrefine group_doubleNeg
  
group_reduce.MelimDoubleNeg_2 = proof
  intros
  rewrite p_ih1
  mrefine refl
  
group_reduce.MelimDoubleNeg_3 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine refl  
  
group_reduce.Melim_plusInverse_1 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  mrefine refl
  
group_reduce.Melim_plusInverse_2 = proof
  intros
  rewrite (sym(right(Plus_inverse c2)))
  trivial

group_reduce.Melim_plusInverse_3 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  mrefine refl   
  
group_reduce.Melim_plusInverse_4 = proof
  intros
  rewrite (sym(left(Plus_inverse c2)))
  mrefine refl  

group_reduce.Melim_plusInverse_5 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  mrefine refl  
  
group_reduce.Melim_plusInverse_6 = proof
  intros
  rewrite p_e1' 
  rewrite p_e2'
  mrefine refl

{-  
group_reduce.Melim_plusInverse_2 = proof
  intros
  rewrite (sym(left(Plus_inverse c2)))
  trivial  
  -}  
  
group_reduce.MplusInverse_assoc_1 = proof
  intros
  rewrite p_e3'
  rewrite (Plus_assoc c3 (Neg c3) c2)
  rewrite (sym(left(Plus_inverse c3)))
  mrefine Plus_neutral_1

group_reduce.MplusInverse_assoc_2 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  rewrite p_e3'
  mrefine refl
  
group_reduce.MplusInverse_assoc_3 = proof
  intros
  rewrite p_e3'
  rewrite (Plus_assoc (Neg c2) c2 c3)
  rewrite (sym(right(Plus_inverse c2)))
  mrefine Plus_neutral_1  

group_reduce.MplusInverse_assoc_4 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  rewrite p_e3'
  mrefine refl

group_reduce.MplusInverse_assoc_5 = proof
  intros
  rewrite p_e1'
  rewrite (sym(Plus_assoc c1 c3 (Neg c3)))
  rewrite (sym(left(Plus_inverse c3)))
  mrefine Plus_neutral_2
  
group_reduce.MplusInverse_assoc_6 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  rewrite p_e3'
  mrefine refl
	
group_reduce.MplusInverse_assoc_7 = proof
  intros
  rewrite p_e1'
  rewrite (sym(Plus_assoc c1 (Neg c2) c2))
  rewrite (sym(right(Plus_inverse c2)))
  mrefine Plus_neutral_2

group_reduce.MplusInverse_assoc_8 = proof
  intros
  rewrite p_e1'
  rewrite p_e2'
  rewrite p_e3'
  mrefine refl
   
group_reduce.MplusInverse_assoc_9 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine refl  
    
group_reduce.MgroupReduce_1 = proof
  intros
  rewrite p_6
  rewrite p_5
  rewrite p_4
  rewrite p_3
  rewrite p_2
  rewrite p_1
  exact refl  
  
group_reduce.MbuildProofGroup = proof
  intros
  rewrite (sym lp)
  rewrite (sym rp)
  exact (Just refl)  
  







