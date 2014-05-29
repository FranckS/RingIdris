-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_reduce.idr
-- Normalize an expression reflecting an element in a group
-------------------------------------------------------------------

module group_reduce

import Decidable.Equality
import dataTypes
import monoid_reduce
import tools
import Prelude.Vect
import Decidable.Equality

--%default total

{-
-- Two remarks : 
-- 	1) The two vectors may have different size
-- 	2) The result is a Maybe, instead of Dec (a proof is only provided if they are equal)
total
vect_eq : {a:Type} -> (a_eq : (a1:a)->(a2:a)->Maybe(a1=a2)) -> (n:Nat) -> (m:Nat) -> (g1:Vect n a) -> (g2:Vect m a) -> Maybe (g1=g2)
vect_eq a_eq _ _ Nil Nil = Just refl
vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) with (decEq pn pm)
	vect_eq a_eq (S pn) (S pn) (h1::t1) (h2::t2) | (Yes refl) with (a_eq h1 h2, vect_eq a_eq pn pn t1 t2)
		vect_eq a_eq _ _ (h1::t1) (h1::t1) | (Yes refl) | (Just refl, Just refl) = Just refl
		vect_eq a_eq _ _ (h1::t1) _ | (Yes refl) | _ = Nothing
	vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) | (No _) = Nothing
vect_eq a_eq _ _ _ _ = Nothing
-}


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
exprG_eq p (NegG e1) (NegG e2) with (exprG_eq p e1 e2)
	exprG_eq p (NegG e1) (NegG e1) | (Just refl) = Just refl
	exprG_eq p (NegG e1) (NegG e2) | _ = Nothing
exprG_eq p (MinusG x y) (MinusG x' y') with (exprG_eq p x x', exprG_eq p y y')
	exprG_eq p (MinusG x y) (MinusG x y) | (Just refl, Just refl) = Just refl
	exprG_eq p (MinusG x y) (MinusG x' y') | _ = Nothing	
exprG_eq p _ _  = Nothing	
	

{-
total
exprG_eq : (p:dataTypes.Group c) -> (n:Nat) -> (m:Nat) -> (g1:Vect n c) -> (g2:Vect m c) -> {c1 : c} -> {c2 : c} -> (e1:ExprG p g1 c1) -> (e2:ExprG p g2 c2) -> (Maybe (e1=e2))
exprG_eq p n m g1 g2 e1 e2 with (vect_eq set_eq _ _ g1 g2)
	exprG_eq p n n g1 g1 e1 e2 | (Just refl) = pre_exprG_eq p e1 e2 -- I am very surprised that Idris is able to see than m is n. And if not, it complains, and that's weird because the default equality is supposed to be JMeq
	exprG_eq p n m g1 g2 e1 e2 | _ = Nothing
	-}
	

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
		case exprG_eq p e e_1 of -- Look for syntactical equality (ie, if we have done some simplification in the last passe)!
			Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg_fix p e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?MpropagateNeg_fix_1))
  

total
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


total
weakenMo : {c:Type} -> {p:dataTypes.Monoid c} -> (n:Nat) -> (g1:Vect n c) -> {c1:c} -> (e:ExprMo p g1 c1) -> (m:Nat) -> (g2 : Vect m c) -> (SubSet g1 g2) -> (c2 ** (ExprMo p g2 c2, c1=c2))
weakenMo _ g1 e m _ (SubSet_same _) = (_ ** (e, refl))
-- Case Subset_add
weakenMo n g1 (ConstMo _ c1) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = (_ ** (ConstMo _ c1, refl))
weakenMo n g1 (VarMo _ i b) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) =
	let paux : (GTE pm n) = (SubSet_size n pm g1 t p_g1_subset_t) in
	let paux2 : (GTE (S pm) n) = (bigger_value pm n paux) in
	let i':(Fin (S pm)) = (pre_convertFin i pm paux2) in
		((index_reverse i' (h::t)) ** ((VarMo _ i' b), ?MweakenMo_1))
weakenMo n g1 (PlusMo e1 e2) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = 
	let (c2_ih1 ** (e2_ih1, p_ih1)) = weakenMo n g1 e1 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in
	let (c2_ih2 ** (e2_ih2, p_ih2)) = weakenMo n g1 e2 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in	
		(_ ** ((PlusMo e2_ih1 e2_ih2), ?MweakenMo_2))



total
weakenG : {c:Type} -> {p:dataTypes.Group c} -> (n:Nat) -> (g1:Vect n c) -> {c1:c} -> (e:ExprG p g1 c1) -> (m:Nat) -> (g2 : Vect m c) -> (SubSet g1 g2) -> (c2 ** (ExprG p g2 c2, c1=c2))
weakenG _ g1 e m _ (SubSet_same _) = (_ ** (e, refl))
-- Case Subset_add
weakenG n g1 (ConstG _ c1) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = (_ ** (ConstG _ c1, refl))
weakenG n g1 (VarG _ i b) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) =
	let paux : (GTE pm n) = (SubSet_size n pm g1 t p_g1_subset_t) in
	let paux2 : (GTE (S pm) n) = (bigger_value pm n paux) in
	let i':(Fin (S pm)) = (pre_convertFin i pm paux2) in
		((index_reverse i' (h::t)) ** ((VarG _ i' b), ?MweakenG_1))
weakenG n g1 (PlusG e1 e2) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = 
	let (c2_ih1 ** (e2_ih1, p_ih1)) = weakenG n g1 e1 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in
	let (c2_ih2 ** (e2_ih2, p_ih2)) = weakenG n g1 e2 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in	
		(_ ** ((PlusG e2_ih1 e2_ih2), ?MweakenG_2))
weakenG n g1 (MinusG e1 e2) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = 
	let (c2_ih1 ** (e2_ih1, p_ih1)) = weakenG n g1 e1 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in
	let (c2_ih2 ** (e2_ih2, p_ih2)) = weakenG n g1 e2 (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in	
		(_ ** ((MinusG e2_ih1 e2_ih2), ?MweakenG_3))
weakenG n g1 (NegG e) (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) = 
	let (c2_ih1 ** (e2_ih1, p_ih1)) = weakenG n g1 e (S pm) (h::t) (SubSet_add h g1 t p_g1_subset_t) in
		(_ ** ((NegG e2_ih1), ?MweakenG_4))

--weaken_correct : {c:Type} -> (p:dataTypes.Group c) -> {n:Nat} -> (g1:Vect n c) -> {c1:c} -> (e:ExprG p g1 c1) -> {m:Nat} -> (g2 : Vect m c) -> (weaken p g1 e g2 = e)



total
transformExp : {c:Type} -> {p:dataTypes.Monoid c} -> {c1:c} -> (g1:Vect n c) -> (g2:Vect m c) -> (n=m) -> (g1=g2) -> ExprMo {n=n} p g1 c1 -> ExprMo {n=m} p g2 c1
transformExp g1 g1 refl refl e = e 


-- Can't be tagged as total because of the missing case for Minus (they have been deleted when we reach this point)
encode : (c:Type) -> (p:dataTypes.Group c) -> (n:Nat) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p g c1) -> (x ** (g2 ** (c2 ** (ExprMo {n=x+n} (group_to_monoid_class p) (g2++g) c2, c1=c2))))
encode c p n g (ConstG p c1) = (Z ** (Nil ** (c1 ** (ConstMo (group_to_monoid_class p) c1, refl))))
encode c p n g (PlusG e1 e2) = 
	let (x_ih1 ** (g_ih1 ** (c2_ih1 ** (e_ih1, p_ih1)))) = encode c p n g e1 in 
	let (cWeak ** (eWeak, pWeak)) = (weakenG n g e2 (x_ih1+n) (g_ih1++g) (concat_SubSet g g_ih1)) in
	let (x_ih2 ** (g_ih2 ** (c2_ih2 ** (e_ih2, p_ih2)))) = encode c p (x_ih1+n) (g_ih1++g) eWeak in 
	let (cWeak2 ** (eWeak2, pWeak2)) = (weakenMo (x_ih1+n) (g_ih1++g) e_ih1 _ (g_ih2++(g_ih1++g)) (concat_SubSet (g_ih1++g) g_ih2)) in 
	
	let paux:(x_ih2 + (x_ih1 + n) = (x_ih2 + x_ih1 + n)) = plusAssociative _ _ _ in
	let paux2:(g_ih2 ++ (g_ih1 ++ g) = (g_ih2 ++ g_ih1) ++ g) = (vectorAppend_assoc g_ih2 g_ih1 g) in
	let vectTotal : Vect ((x_ih2 + x_ih1) + n) c = ((g_ih2 ++ g_ih1) ++ g) in 
	let exprTransformed : ExprMo {n=(x_ih2 + x_ih1) + n} (group_to_monoid_class p) vectTotal (Plus cWeak2 c2_ih2) = (transformExp _ ((g_ih2 ++ g_ih1) ++ g) paux paux2 (PlusMo eWeak2 e_ih2)) in
	--let prSubSet_ih2_transformed : SubSet (g_ih1 ++ g) ((g_ih2 ++ g_ih1) ++ g) = SubSet_rewriteRight _ _ _ prSubSet_ih2 paux2 in
		((x_ih2+x_ih1) ** ((g_ih2 ++ g_ih1) ** (_** (exprTransformed, ?Mencode_1))))
encode c p n g (VarG p i b) = (Z ** (Nil ** (_ ** ((VarMo (group_to_monoid_class p) i b), refl))))
-- For the (NegG e) (where e can only be a variable or a constant), we encode the variable or the constant
-- I AM NOT ENTIRELY SURE YET FOR THESE TWO LINES JUST UNDER :
encode c p n g (NegG {p=p} {c1=c1} (ConstG _ c1)) = (Z ** (Nil ** ((Neg c1) ** ((ConstMo (group_to_monoid_class p) (Neg c1)), refl))))
encode c p n g (NegG {p=p} {c1=c1} e) = ((S Z) ** (([Neg c1]) ** (_ ** ((VarMo (group_to_monoid_class p) (lastElement n) False), ?Mencode_3))))


--encode n g (NegG {p=p} {c1=c1} (ConstG _ c1)) = ((S n) ** (((Neg c1)::g) ** (_ ** (((VarMo (group_to_monoid_class p) (lastElement n) False), ?Mencode_3), SubSet_add (Neg c1) g g (SubSet_same g)))))
--encode n g (NegG {p=p} (VarG _ i b)) = (n ** ((changeIeme g i (Neg (index_reverse i g))) ** (_ ** (((VarMo _ i False), ?Mencode_4), ?MAAA))))



total
decode : {c:Type} -> (p:dataTypes.Group c) -> (n:Nat) -> (g1:Vect n c) -> (x:Nat) -> (g2:Vect x c) -> {c1:c} -> (e:ExprMo (group_to_monoid_class p) (g2++g1) c1) -> (c2 ** (ExprG {n=n} p g1 c2, c1=c2))  
decode p n g1 x g2 (ConstMo _ c1) = (c1 ** (((ConstG {g=g1} p c1, refl))))
-- For the variable, if it's a first n variable, we can't convert it back. Otherwise, we have to interpret it like a constant
-- Note: I don't need the boolean in VarMo, because I can guess with the position in the context : from 1 to n : that's a real variable, from n+1 to n+x : that's a fake variable
-- THE LINE JUST UNDER (FOR VarMo) IS JUST FOR MATTER OF TESTING : WE CAN'T LEAVE IT LIKE THAT FOR ALL THE STRUCTURES ABOVE (WE DESTROY THE ABSTRACT SYNTAX BY DOING SO)
decode p n g1 x g2 (VarMo _ i b) = (_ ** ((ConstG {g=g1} p (index_reverse i (g2++g1))), refl))
decode p n g1 x g2 (PlusMo e1 e2) = 
	let (c2_ih1 ** ((e_ih1, p_ih1))) = decode p n g1 x g2 e1 in 
	let (c2_ih2 ** ((e_ih2, p_ih2))) = decode p n g1 x g2 e2 in 
		(_** (PlusG e_ih1 e_ih2, ?Mdecode_1))

{-
decode p (S pn) g1 x g2 (VarMo _ i True) with (isBeforeDec i (lastElement pn))
	decode p (S pn) g1 x g2 (VarMo _ i True) | Yes p = 
		let i' = transformeFin i (S pn) p in
		(_ ** (((VarG {g=g1} p i' True, ?MA))))
	decode p (S pn) g1 x g2 (VarMo _ i True) | No p =
	-}
--decode p n g1 x g2 (VarMo _ i False) = (_ ** (((ConstG _ (index_reverse i g), refl))))



code_reduceM_andDecode : {c:Type} -> (p:dataTypes.Group c) -> {n:Nat} -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG {n=n} p g c2, c1=c2))
code_reduceM_andDecode p g e = 
	let (n2 ** (g2 ** (c2 ** (e2, pEncode)))) = encode _ _ _ _ e in
	let (c3 ** (e3, pReduce)) = monoidReduce (group_to_monoid_class p) (g2++g) e2 in
	let (c4 ** (e4, pDecode)) = decode p _ g _ g2 e3 in
		(c4 ** (e4, ?Mcode_reduceM_andDecode_1))
                                              
                                              
                                              		
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

	
	-- NEW : 3 levels of +
	plusInverse_assoc' : {c:Type} -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
	-- (a+b) + ((-c)+d)
	plusInverse_assoc' p g (PlusG (PlusG e1 e2) (PlusG (NegG e3) e4)) with (groupDecideEq p g e2 e3)
		plusInverse_assoc' p g (PlusG (PlusG e1 e2) (PlusG (NegG e2) e4)) | (Just refl) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p g e1 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p g e4 in
				(_ ** (PlusG e1' e4', ?MplusInverse_assoc'_1))
		plusInverse_assoc' p g (PlusG (PlusG e1 e2) (PlusG (NegG e3) e4)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc' p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc' p g e3 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p g e4 in
				(_ ** ((PlusG (PlusG e1' e2') (PlusG (NegG e3') e4')), ?MplusInverse_assoc'_2))
				
	-- (a+(-b)) + (c+d)
	plusInverse_assoc' p g (PlusG (PlusG e1 (NegG e2)) (PlusG e3 e4)) with (groupDecideEq p g e2 e3)
		plusInverse_assoc' p g (PlusG (PlusG e1 (NegG e2)) (PlusG e2 e4)) | (Just refl) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p g e1 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p g e4 in
				(_ ** (PlusG e1' e4', ?MplusInverse_assoc'_3))
		plusInverse_assoc' p g (PlusG (PlusG e1 (NegG e2)) (PlusG e3 e4)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc' p g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc' p g e3 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p g e4 in
				(_ ** ((PlusG (PlusG e1' (NegG e2')) (PlusG e3' e4')), ?MplusInverse_assoc'_4))
				
	-- Anything else
	plusInverse_assoc' p g e =
		(_ ** (e, refl))
				
			
	pre_groupReduce : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG {n=n} p g c2, c1=c2))
	pre_groupReduce c p g e =
		let (r_1 ** (e_1, p_1)) = elimMinus p e in
		let (r_2 ** (e_2, p_2)) = propagateNeg_fix p e_1 in
		let (r_3 ** (e_3, p_3)) = elimDoubleNeg p e_2 in
		let (r_4 ** (e_4, p_4)) = elim_plusInverse p g e_3 in
		let (r_5 ** (e_5, p_5)) = plusInverse_assoc p g e_4 in
		let (r_6 ** (e_6, p_6)) = plusInverse_assoc' p g e_5 in -- NEW (assoc at 3 levels of +, for dealing with things like (x+y) + (-y + z)
		-- IMPORTANT : At this stage, we only have negation on variables and constants.
		-- Thus, we can continue the reduction by calling the reduction for a monoid, with encoding for the minus :
		-- the expression (-c) is encoded as a constant c', and the variable (-x) as a varible x'
		let (r_7 ** (e_7, p_7)) = code_reduceM_andDecode p g e_6 in
			(r_7 ** (e_7, ?Mpre_groupReduce_1))
			
			
	-- Computes the fixpoint of pre_groupReduce : do the entire serie of simplification as long as we've not finished (ie, as long as we don't loop on the same term)
	-- That's needed because some simplification done at the monoid level could lead to new simplification.
	-- Exemple : (0+(Y)) become (Y) at the Monoid level. And if this Y was encoding (-x), then at the toplevel we can have x + (-x) now,
	-- which need a new simplification at the group level
	groupReduce : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG {n=n} p g c2, c1=c2))
	groupReduce c p g e = 
		let (c' ** (e', p')) = pre_groupReduce c p g e in
			case exprG_eq p e e' of 
				Just pr => (c' ** (e', p'))-- We stop here
				Nothing => let (c'' ** (e'', p'')) = groupReduce c p g e' in
								(c'' ** (e'', ?Mgroup_Reduce_1))
			
			
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
  
group_reduce.MplusInverse_assoc'_1 = proof
  intros
  rewrite p_e1' 
  rewrite p_e4' 
  rewrite (groupAssoc_4terms c p c1 c4 (Neg c4) c3)
  rewrite (sym (left (Plus_inverse c4)))
  rewrite (sym(Plus_neutral_2  c1))
  exact refl
  
group_reduce.MplusInverse_assoc'_2 = proof
  intros
  rewrite p_e1' 
  rewrite p_e2' 
  rewrite p_e3' 
  rewrite p_e4' 
  exact refl

group_reduce.MplusInverse_assoc'_3 = proof
  intros
  rewrite p_e1' 
  rewrite p_e4' 
  rewrite (groupAssoc_4terms c p c1 (Neg c3) c3 c4)
  rewrite (sym (right(Plus_inverse c3)))
  rewrite (sym(Plus_neutral_2 c1))
  exact refl  
    
group_reduce.MplusInverse_assoc'_4 = proof
  intros
  rewrite p_e1' 
  rewrite p_e2' 
  rewrite p_e3' 
  rewrite p_e4' 
  exact refl
        
group_reduce.Mpre_groupReduce_1 = proof
  intros
  rewrite p_7
  rewrite p_6
  rewrite p_5
  rewrite p_4
  rewrite p_3
  rewrite p_2
  rewrite p_1
  exact refl 
  
group_reduce.Mgroup_Reduce_1 = proof
  intros
  rewrite p''
  rewrite p'
  exact refl
    
group_reduce.MbuildProofGroup = proof
  intros
  rewrite (sym lp)
  rewrite (sym rp)
  exact (Just refl)   

group_reduce.MweakenG_1 = proof
  intros
  mrefine indexReverse_of_convert 
  exact c
  exact n
  exact g1
  exact i
  exact pm
  exact (h::t)
  exact (lower_value n pm (SubSet_size n pm g1 t p_g1_subset_t))
  exact (SubSet_add h g1 t p_g1_subset_t)
  
group_reduce.MweakenG_2 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl
  
group_reduce.MweakenG_3 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl
  
group_reduce.MweakenG_4 = proof
  intros
  rewrite p_ih1
  exact refl
  
group_reduce.MweakenMo_1 = proof
  intros
  mrefine indexReverse_of_convert 
  exact c
  exact n
  exact g1
  exact i
  exact pm
  exact (h::t)
  exact (lower_value n pm (SubSet_size n pm g1 t p_g1_subset_t))
  exact (SubSet_add h g1 t p_g1_subset_t)
  
group_reduce.MweakenMo_2 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl    
  
group_reduce.Mencode_1 = proof
  intros
  rewrite pWeak2
  rewrite p_ih1
  rewrite p_ih2
  rewrite pWeak
  exact refl

{-  
group_reduce.Mencode_2 = proof
  intros
  exact (SubSet_trans _ _ _ prSubSet_ih1 prSubSet_ih2_transformed)  
-}  
  
group_reduce.Mencode_3 = proof
  intros
  mrefine lastElement_of_reverse_is_first 
  exact n
  exact c
  exact ((Neg c1) :: g)
  
{-  
group_reduce.Mencode_4 = proof
  intros
  mrefine changeIeme_correct 
-}
    
group_reduce.Mdecode_1 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl
  
group_reduce.Mcode_reduceM_andDecode_1 = proof
  intros
  rewrite (sym pEncode )
  rewrite (sym pReduce  )
  rewrite (sym pDecode )
  exact refl
  
