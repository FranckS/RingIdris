-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_reduce.idr
-- Normalize an expression reflecting an element in a group
-------------------------------------------------------------------

module group_reduce

import Decidable.Equality
import dataTypes
import tools
import Prelude.Vect

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
    
------------------------------------------------------------------------ 
-- --------- Part concerning the encoding from Group to Monoid ---------
------------------------------------------------------------------------   
    
{-
countNeg : {c:Type} -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> Nat
countNeg p (ConstG p c1) = 0
countNeg p (PlusG e1 e2) = (countNeg p e1) + (countNeg p e2)
countNeg p (MinusG e1 e2) = (countNeg p e1) + (countNeg p e2)
countNeg p (NegG e) = 1 + (countNeg p e) 
countNeg p (VarG p i b) = 0
-}


using (c:Type, n:Nat, m:Nat)
    data SubSet : Vect n c -> Vect m c -> Type where
        SubSet_same : (g:Vect n c) -> SubSet g g
        SubSet_add : (c1:c) -> (g1:Vect n c) -> (g2:Vect k c) -> (SubSet g1 g2) -> SubSet g1 (c1 :: g2)


total
SubSet_wkn : (g1:Vect n c) -> (g2:Vect m c) -> (c1:c) -> (SubSet (c1::g1) g2) -> (SubSet g1 g2)
SubSet_wkn g1 _ c1 (SubSet_same _) = SubSet_add c1 g1 g1 (SubSet_same g1)
SubSet_wkn g1 (h2::t2) c1 (SubSet_add h2 g1 t2 c1_cons_g1_in_t2) = SubSet_add h2 g1 t2 (SubSet_wkn g1 t2 c1 c1_cons_g1_in_t2)


total
SubSet_trans : (g1:Vect n c) -> (g2:Vect m c) -> (g3 : Vect k c) -> (SubSet g1 g2) -> (SubSet g2 g3) -> (SubSet g1 g3)
SubSet_trans g1 _ _ (SubSet_same g1) (SubSet_same _) = SubSet_same g1
SubSet_trans g1 _ (h3::t3) (SubSet_same g1) (SubSet_add h3 g1 t3 g1_in_t3) = SubSet_add h3 g1 t3 g1_in_t3
SubSet_trans g1 (h2::t2) _ (SubSet_add h2 g1 t2 g1_in_t2) (SubSet_same _) = SubSet_add h2 g1 t2 g1_in_t2
SubSet_trans g1 (h2::t2) (h3::t3) (SubSet_add h2 g1 t2 g1_in_t2) (SubSet_add h3 _ t3 h2_cons_t2_in_t3) = 
    let t2_in_t3 : SubSet t2 t3 = SubSet_wkn t2 t3 h2 h2_cons_t2_in_t3 in 
        SubSet_add h3 g1 t3 (SubSet_trans g1 t2 t3 g1_in_t2 t2_in_t3)


weakenMo : {c:Type} -> {p:dataTypes.Monoid c} -> {n:Nat} -> {g1:Vect n c} -> {c1:c} -> (e:ExprMo p g1 c1) -> {m:Nat} -> (g2 : Vect m c) -> (SubSet g1 g2) -> ExprMo p g2 c1

weakenG : {c:Type} -> {p:dataTypes.Group c} -> {n:Nat} -> {g1:Vect n c} -> {c1:c} -> (e:ExprG p g1 c1) -> {m:Nat} -> (g2 : Vect m c) -> (SubSet g1 g2) -> ExprG p g2 c1

--weaken_correct : {c:Type} -> (p:dataTypes.Group c) -> {n:Nat} -> (g1:Vect n c) -> {c1:c} -> (e:ExprG p g1 c1) -> {m:Nat} -> (g2 : Vect m c) -> (weaken p g1 e g2 = e)


changeIeme : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (Vect n A)

changeIeme_correct : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (a = index_reverse i (changeIeme g i a))


encode : {c:Type} -> {p:dataTypes.Group c} -> (n:Nat) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p g c1) -> (n2 ** (g2 ** (c2 ** ((ExprMo {n=n2} (group_to_monoid_class p) g2 c2, c1=c2), SubSet g g2))))
encode n g (ConstG p c1) = (_ ** (g ** (c1 ** ((ConstMo (group_to_monoid_class p) c1, refl), SubSet_same _))))
encode n g (PlusG e1 e2) = 
    let (n_ih1 ** (g_ih1 ** (c2_ih1 ** ((e_ih1, p_ih1), prSubSet_ih1)))) = encode n g e1 in 
      	let (n_ih2 ** (g_ih2 ** (c2_ih2 ** ((e_ih2, p_ih2), prSubSet_ih2)))) = encode n_ih1 g_ih1 (weakenG e2 g_ih1 prSubSet_ih1) in 
	  (n_ih2 ** (g_ih2 ** (_** (((PlusMo (weakenMo e_ih1 g_ih2 prSubSet_ih2) e_ih2, ?Mencode_1), ?Mencode_2)))))
encode n g (VarG p i True) = (n ** (g ** (_ ** (((VarMo (group_to_monoid_class p) i True), refl), (SubSet_same g)))))
-- We've got to deal with the case of a VarG (p i False), even if this case will never happen (Var representing negative values are produced by this function and can't occur in input)
encode n g (VarG p i False) = (n ** (g ** (_ ** (((VarMo (group_to_monoid_class p) i False), refl), (SubSet_same g))))) -- Little pb here
encode n g (NegG {p=p} {c1=c1} (ConstG _ c1)) = ((S n) ** (((Neg c1)::g) ** (_ ** (((VarMo (group_to_monoid_class p) (lastElement n) False), ?Mencode_3), SubSet_add (Neg c1) g g (SubSet_same g)))))
encode n g (NegG {p=p} (VarG _ i b)) = (n ** ((changeIeme g i (Neg (index_reverse i g))) ** (_ ** (((VarMo _ i False), ?Mencode_4), ?MAAA))))


decode : {c:Type} -> (p:dataTypes.Group c) -> (n:Nat) -> (g:Vect n c) -> {c1:c} -> (e:ExprMo (group_to_monoid_class p) g c1) -> (n2 ** (g2 ** (c2 ** ((ExprG {n=n2} p g2 c2, c1=c2), SubSet g2 g))))  
decode p n g (ConstMo _ c1) = (_ ** (g ** (c1 ** ((ConstG p c1, refl), SubSet_same _))))
decode p n g (VarMo _ i True) = (n ** (g ** (_ ** (((VarG p i True), refl), (SubSet_same g)))))
--decode p n g (VarMo _ i False) = (_ ** (g ** (_ ** (((NegG (VarG _ i True)), refl), (SubSet_same g)))))


--decode p n g (PlusMo e1 e2) = 
--	let (n_ih1 ** (g_ih1 ** (c2_ih1 ** ((e_ih1, p_ih1), prSubSet_ih1)))) = decode p n g e1 in 
--	 let (n_ih2 ** (g_ih2 ** (c2_ih2 ** ((e_ih2, p_ih2), prSubSet_ih2)))) = decode p n_ih1 g_ih1 (weakenMo e2 g_ih1 prSubSet_ih1) in 
--	  (n_ih2 ** (g_ih2 ** (_** (((PlusG (weakenG e_ih1 g_ih2 prSubSet_ih2) e_ih2, ?Mencode_1), ?Mencode_2)))))
	  


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

group_reduce.Mencode_1 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl

group_reduce.Mencode_2 = proof
  intros
  exact (SubSet_trans _ _ _ prSubSet_ih1 prSubSet_ih2)  

group_reduce.Mencode_3 = proof
  intros
  mrefine lastElement_of_reverse_is_first 
  exact n
  exact c
  exact ((Neg c1) :: g)

group_reduce.Mencode_4 = proof
  intros
  mrefine changeIeme_correct 



