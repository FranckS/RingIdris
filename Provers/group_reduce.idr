-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_reduce.idr
-- Normalize an expression reflecting an element in a group
-------------------------------------------------------------------

module Provers.group_reduce

import Data.Vect
import Data.Fin
import Decidable.Equality

import Provers.dataTypes
import Provers.monoid_reduce
import Provers.tools

%access public export

--%default total


total
elimMinus : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
elimMinus {c} p setAndMult (ConstG _ _ _ const) = (_ ** (ConstG _ _ _ const, set_eq_undec_refl {c} _))
elimMinus p setAndMult (PlusG _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus p setAndMult e2) in
		((Plus r_ih1 r_ih2) ** (PlusG _ e_ih1 e_ih2, ?MelimMinus1))
elimMinus {c} p setAndMult (VarG _ _ v) = (_ ** (VarG _ _ v, set_eq_undec_refl {c} _))    
elimMinus p setAndMult (MinusG _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus p setAndMult e2) in
		((Plus r_ih1 (Neg r_ih2)) ** (PlusG _ e_ih1 (NegG _ e_ih2), ?MelimMinus2)) 
elimMinus p setAndMult (NegG _ e1) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus p setAndMult e1) in
		(_ ** (NegG _ e_ih1, ?MelimMinus3))
  
  
-- Ex : -(a+b) becomes (-b) + (-a)
-- Not total for Idris, because recursive call with argument (NegG ei) instead of ei. Something can be done for this case with a natural number representing the size
propagateNeg : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
propagateNeg p setAndMult (NegG _ (PlusG _ e1 e2)) =
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg p setAndMult (NegG _ e1)) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg p setAndMult (NegG _ e2)) in
		((Plus r_ih2 r_ih1) ** (PlusG _ e_ih2 e_ih1, ?MpropagateNeg_1)) -- Carefull : - (a + b) = (-b) + (-a) in a group and *not* (-a) + (-b) in general. See mathsResults.bad_push_negation_IMPLIES_commutativeGroup for more explanations about this
propagateNeg p setAndMult (NegG _ (NegG _ e)) =
	-- We use the opportunity to remove this double negation (as this is what we'll have to do in the next treatement anyway)
	let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg p setAndMult e in
		(r_ih1 ** (e_ih1, ?MpropagateNeg_2))
propagateNeg {c} p setAndMult (NegG _ e) =
	-- Here 'e' can only be a constant or a variable as we've treated Plus and Neg before (and Minus has already been simplified)
	-- Therefore, we can let the Neg where it is (no need to do a recursive call)
	(_ ** (NegG _ e, set_eq_undec_refl {c} _))
propagateNeg p setAndMult (PlusG _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg p setAndMult e2) in
		((Plus r_ih1 r_ih2) ** (PlusG _ e_ih1 e_ih2, ?MpropagateNeg_3))
propagateNeg {c} p setAndMult e =
  (_ ** (e, set_eq_undec_refl {c} _)) 
  

-- I guess computing the fixpoint is no longer needed, as we no longer have the case of two consecutive Neg,
-- with the outermost that we initially treated afterwards. In the change of the above function, we now simplify
-- such a sequence of two Neg
{-
-- Needed because calling propagateNeg on -(-(a+b)) gives - [-b + -a] : we may need other passes
propagateNeg_fix : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
propagateNeg_fix p setAndMult e = 
	let (r_1 ** (e_1, p_1)) = propagateNeg p setAndMult e in
		-- Look for syntactical equality :
		-- have we done some simplification in the last pass ?
		case exprG_eq p _ _ e e_1 of
			-- Previous and current term are the same : 
			-- we stop here
			Just pr => (r_1 ** (e_1, p_1))
			-- Previous and current are different : 
			-- we do at least another pass
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg_fix p setAndMult e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?MpropagateNeg_fix_1))
-}  

total
elimDoubleNeg : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
elimDoubleNeg p setAndMult (NegG _ (NegG _ e1)) =
	let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg p setAndMult e1 in
    (_ ** (e_ih1, ?MelimDoubleNeg_1))
elimDoubleNeg p setAndMult (NegG _ e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg p setAndMult e in
    ((Neg r_ih1) ** (NegG _ e_ih1, ?MelimDoubleNeg_2))
elimDoubleNeg p setAndMult (PlusG _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimDoubleNeg p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimDoubleNeg p setAndMult e2) in
    ((Plus r_ih1 r_ih2) ** (PlusG _ e_ih1 e_ih2, ?MelimDoubleNeg_3))        
elimDoubleNeg {c} p setAndMult e1 = 
    (_ ** (e1, set_eq_undec_refl {c} _))
    

-- Ex : -5 + -8 becomes -13
-- it's needed because before reaching the level of computations (magma), negative constants will be wrapped into fake variables, and
-- that will prevent computations to happen if we don't do this first simplification here.
total
fold_negative_constant : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
fold_negative_constant p setAndMult (PlusG _ (NegG _ (ConstG _ _ _ c1)) (NegG _ (ConstG _ _ _ c2))) = (_ ** (NegG _ (ConstG _ _ _ (Plus c2 c1)), ?Mfold_negative_constant_1)) -- -- carefull here to the order which has to be reversed : -(a+b) is (-b + -a) but not (-a + -b) in the general case (when it's not an abelian (commutative) group)
fold_negative_constant p setAndMult (NegG _ e) = 
	let (r_ih ** (e_ih, p_ih)) = fold_negative_constant p setAndMult e in
        (_ ** (NegG _ e_ih, ?Mfold_negative_constant_2))
--fold_negative_constant p (PlusG _ _ (ConstG _ _ _ p _ _ const1) (VarG _ _ _ (EncodingGroupTerm_const _ _ _ const2))) = (_ ** (ConstG _ _ _ p _ _ (Plus const1 (Neg const2)), refl))
--fold_negative_constant p (PlusG _ _ (VarG _ _ _ (EncodingGroupTerm_const _ _ _ const1)) (ConstG _ _ _ p _ _ const2)) = (_ ** (ConstG _ _ _ p _ _ (Plus (Neg const1) const2), refl))
fold_negative_constant p setAndMult (PlusG _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (fold_negative_constant p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (fold_negative_constant p setAndMult e2) in
        ((Plus r_ih1 r_ih2) ** (PlusG _ e_ih1 e_ih2, ?Mfold_negative_constant_3)) 
-- Note : not needed to do it recursively for MinusG, since they have already been removed at this point
fold_negative_constant {c} p setAndMult e = 
    (_ ** (e, set_eq_undec_refl {c} _))


-- As for propagateNeg, we need the fixpoint
fold_negative_constant_fix : {c:Type} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
fold_negative_constant_fix p setAndMult e = 
	let (r_1 ** (e_1, p_1)) = fold_negative_constant p setAndMult e in
		case exprG_eq p _ _ e e_1 of -- Look for syntactical equality (ie, if we have done some simplification in the last passe)!
			Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = fold_negative_constant_fix p setAndMult e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?Mfold_negative_constant_fix_1))


------------------------------------------------------------------------ 
-- --------- Part concerning the encoding from Group to Monoid ---------
------------------------------------------------------------------------   

-- Can't be tagged as total because of the missing cases (like one for Minus) (they have been deleted when we reach this point)
encode : (c:Type) -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (e:ExprG p setAndMult g c1) -> (c2 ** (ExprMo {n=n} (group_to_monoid_class p) Neg setAndMult g c2, c1~=c2))
encode c p setAndMult g (ConstG _ _ _ c1) = (c1 ** (ConstMo (group_to_monoid_class p) _ _ _ c1, set_eq_undec_refl {c} _))
encode c p setAndMult g (PlusG _ e1 e2) = 
	let (c2_ih1 ** (e_ih1, p_ih1)) = encode c p setAndMult g e1 in 
	let (c2_ih2 ** (e_ih2, p_ih2)) = encode c p setAndMult g e2 in 
    (_ ** (PlusMo _ _ e_ih1 e_ih2, ?Mencode_1))
encode c p setAndMult g (VarG _ _ v) = (_ ** ((VarMo (group_to_monoid_class p) _ _ v), set_eq_undec_refl {c} _))
-- For the (NegG _ e) (where e can only be a variable or a constant), we encode the variable or the constant
--encode c p g (NegG _ _ (ConstG _ _ _ c1)) = ((Neg c1) ** (VarMo (group_to_monoid_class p) _ (EncodingGroupTerm_const _ _ _ c1), refl))
encode c p setAndMult g (NegG _ (ConstG _ _ _ c1)) = ((Neg c1) ** (ConstMo _ _ _ _ (Neg c1), set_eq_undec_refl {c} _)) 
encode c p setAndMult g (NegG _ (VarG _ _ (RealVariable _ _ _ _ i))) = (_ ** (VarMo (group_to_monoid_class p) _ _ (EncodingGroupTerm_var _ _ _ _ i), set_eq_undec_refl {c} _))
-- New case : we may have to pass on a Neg of an encoding from the Ring level (the case where it's not a Neg has been done above generically with the v which might be an encoding)
-- so this is the encoding (for the Monoid level) of the encoding (generated by the Ring level)
encode c p setAndMult g (NegG _ (VarG _ _ (EncodingProductOfMonomials _ _ _ prodOfMon))) = (_ ** (VarMo (group_to_monoid_class p) _ _ (EncodingNegProductOfMonomials _ _ _ prodOfMon), set_eq_undec_refl {c} _))
{-
-- We should not have the two cases just under : we create the "groupTermEncoding", so they are not supposed to be already here
encode c n p g (NegG _ _ (VarG _ _ _ (EncodingGroupTerm_const _ _ _ c1))) = ?total_test_1
encode c n p g (NegG _ _ (VarG _ _ _ (EncodingGroupTerm_var _ _ _ i))) = ?total_test_2
-- we should not have something else ! we can only have NegG _ of constant or variable at this point !
encode c n p g (NegG _ _ e) = ?total_test_3
-- and we should not have Minus either (since it has been replace with Neg)
encode c n p g (MinusG _ e1 e2) = ?total_test_4
-}


total
decode : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (e:ExprMo (group_to_monoid_class p) Neg setAndMult g c1) -> (c2 ** (ExprG {n=n} p setAndMult g c2, c1~=c2))
decode {c} p setAndMult g (ConstMo _ _ _ _ c1) = (c1 ** (ConstG p _ g c1, set_eq_undec_refl {c} _))
decode {c} p setAndMult g (VarMo _ _ _ (RealVariable _ _ _ _ i)) = (_ ** (VarG _ _ (RealVariable _ _ _ _ i), set_eq_undec_refl {c} _))
--decode p setAndMult g (VarMo _ _ (EncodingGroupTerm_const _ _ _ c1)) = (_ ** (NegG _ _ (ConstG _ _ _ c1), refl))
decode {c} p setAndMult g (VarMo _ _ _ (EncodingGroupTerm_var _ _ _ _ i)) = (_ ** (NegG _ (VarG _ _ (RealVariable _ _ _ _ i)), set_eq_undec_refl {c} _))
-- New : decoding of a ring-encoded term, which was also encoded for the monoid level
decode {c} p setAndMult g (VarMo _ _ _ (EncodingNegProductOfMonomials _ _ _ prodOfMon)) = (_ ** (NegG _ (VarG _ _ (EncodingProductOfMonomials _ _ _ prodOfMon)), set_eq_undec_refl {c} _))
-- Just for being total
decode {c} p setAndMult g (VarMo _ _ _ (EncodingProductOfMonomials _ _ _ prodOfMon)) = (_ ** (VarG _ _ (EncodingProductOfMonomials _ _ _ prodOfMon), set_eq_undec_refl {c} _))
decode p setAndMult g (PlusMo _ _ e1 e2) = 
	let (c2_ih1 ** ((e_ih1, p_ih1))) = decode p setAndMult g e1 in 
	let (c2_ih2 ** ((e_ih2, p_ih2))) = decode p setAndMult g e2 in 
		(_** (PlusG _ e_ih1 e_ih2, ?Mdecode_1))



code_reduceM_andDecode : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
code_reduceM_andDecode {c} p setAndMult g e = 
	let (c2 ** (e2, pEncode)) = encode _ _ _ _ e in
	let (c3 ** (e3, pReduce)) = monoidReduce (group_to_monoid_class p) (MkSetWithNeg Neg (\x => \y => \peq:x~=y => Neg_preserves_equiv {c} peq)) e2 in
	let (c4 ** (e4, pDecode)) = decode p _ _ e3 in
		(c4 ** (e4, ?Mcode_reduceM_andDecode_1))
                                              
                                             
                                              		
mutual
--------------------------------------------
-- Simplify (+e) + (-e) at *one* level of +
--------------------------------------------
	elim_plusInverse : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
	elim_plusInverse p setAndMult g (ConstG _ _ _ const) = (_ ** (ConstG _ _ _ const, set_eq_undec_refl const))
	elim_plusInverse p setAndMult g (VarG _ _ {c1=c1} v) = (_ ** (VarG _ _ v, set_eq_undec_refl c1))
	-- Reminder : e1 and e2 can't be a Neg themselves, because you are suppose to call elimDoubleNeg before calling this function...
	elim_plusInverse p setAndMult g (PlusG _ (NegG _ e1) (NegG _ e2)) = 
		let (r_e1' ** (e1', p_e1')) = elim_plusInverse p setAndMult g e1 in
		let (r_e2' ** (e2', p_e2')) = elim_plusInverse p setAndMult g e2 in
		(_ ** ((PlusG _ (NegG _ e1') (NegG _ e2')), ?Melim_plusInverse_1))
	-- If e2 is not a Neg !
	elim_plusInverse p setAndMult g (PlusG _ (NegG _ e1) e2) with (groupDecideEq p e1 e2) -- compare les versions simplifiees de e1 et de e2
		elim_plusInverse p setAndMult g (PlusG _ (NegG _ e1) e2) | (Just e1_equiv_e2) = (_ ** ((ConstG _ _ _ Zero), ?Melim_plusInverse_2))
		elim_plusInverse p setAndMult g (PlusG _ (NegG _ e1) e2) | _ = 
			let (r_e1' ** (e1', p_e1')) = elim_plusInverse p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = elim_plusInverse p setAndMult g e2 in
			(_ ** ((PlusG _ (NegG _ e1') e2'), ?Melim_plusInverse_2))
	-- If e1 is not a Neg !
	elim_plusInverse p setAndMult g (PlusG _ e1 (NegG _ e2)) with (groupDecideEq p e1 e2) -- compare les versions simplifiees de e1 et de e2
		elim_plusInverse p setAndMult g (PlusG _ e1 (NegG _ e2)) | (Just e1_equiv_e2) = (_ ** ((ConstG _ _ _ Zero), ?Melim_plusInverse_3))
		elim_plusInverse p setAndMult g (PlusG _ e1 (NegG _ e2)) | _ = 
			let (r_e1' ** (e1', p_e1')) = elim_plusInverse p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = elim_plusInverse p setAndMult g e2 in
			(_ ** ((PlusG _ e1' (NegG _ e2')), ?Melim_plusInverse_4))
	-- If e1 and e2 are not Neg 
	elim_plusInverse p setAndMult g (PlusG _ e1 e2) = 
		let (r_e1' ** (e1', p_e1')) = elim_plusInverse p setAndMult g e1 in
		let (r_e2' ** (e2', p_e2')) = elim_plusInverse p setAndMult g e2 in
		(_ ** ((PlusG _ e1' e2'), ?Melim_plusInverse_5))
	elim_plusInverse p setAndMult g {c1=c1} e = (_ ** (e, set_eq_undec_refl c1))
		
            
--------------------------------------------------------------------------
-- Simplifying (+e) + (-e) with associativity (at two levels of +) !
--------------------------------------------------------------------------
	plusInverse_assoc : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
	-- (e1 + (-e2 + e3))
	plusInverse_assoc p setAndMult g (PlusG _ e1 (PlusG _ (NegG _ e2) e3)) with (groupDecideEq p e1 e2)
		plusInverse_assoc p setAndMult g (PlusG _ e1 (PlusG _ (NegG _ e2) e3)) | (Just e1_equiv_e2) = 
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in
				(_ ** (e3', ?MplusInverse_assoc_1))
		plusInverse_assoc p setAndMult g (PlusG _ e1 (PlusG _ (NegG _ e2) e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in
				(_ ** ((PlusG _ e1' (PlusG _ (NegG _ e2') e3')), ?MplusInverse_assoc_2))
	
	-- (-e1 + (e2+e3))
	plusInverse_assoc p setAndMult g (PlusG _ (NegG _ e1) (PlusG _ e2 e3)) with (groupDecideEq p e1 e2)
		plusInverse_assoc p setAndMult g (PlusG _ (NegG _ e1) (PlusG _ e2 e3)) | (Just e1_equiv_e2) = 
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in 
				(_ ** (e3', ?MplusInverse_assoc_3))
		plusInverse_assoc p setAndMult g (PlusG _ (NegG _ e1) (PlusG _ e2 e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in
				(_ ** ((PlusG _ (NegG _ e1') (PlusG _ e2' e3')), ?MplusInverse_assoc_4))
	
	-- ((e1+e2) + -e3))
	plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 e2) (NegG _ e3)) with (groupDecideEq p e2 e3)
		plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 e2) (NegG _ e3)) | (Just e2_equiv_e3) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
				(_ ** (e1', ?MplusInverse_assoc_5))
		plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 e2) (NegG _ e3)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in
				(_ ** ((PlusG _ (PlusG _ e1' e2') (NegG _ e3')), ?MplusInverse_assoc_6))
				
	-- ((e1+(-e2)) + e3)		
	plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) e3) with (groupDecideEq p e2 e3)
		plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) e3) | (Just e2_equiv_e3) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
				(_ ** (e1', ?MplusInverse_assoc_7))
		plusInverse_assoc p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) e3) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc p setAndMult g e3 in
				(_ ** ((PlusG _ (PlusG _ e1' (NegG _ e2')) e3'), ?MplusInverse_assoc_8))
				
	plusInverse_assoc p setAndMult g (PlusG _ e1 e2) =
		let (r_ih1 ** (e_ih1, p_ih1)) = (plusInverse_assoc p setAndMult g e1) in
		let (r_ih2 ** (e_ih2, p_ih2)) = (plusInverse_assoc p setAndMult g e2) in
			((Plus r_ih1 r_ih2) ** (PlusG _ e_ih1 e_ih2, ?MplusInverse_assoc_9))
			
	-- Anything else
	plusInverse_assoc p setAndMult g {c1=c1} e =
		(_ ** (e, set_eq_undec_refl c1))

	
	-- NEW : 3 levels of +
	plusInverse_assoc' : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
	-- (a+b) + ((-c)+d)
	plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 e2) (PlusG _ (NegG _ e3) e4)) with (groupDecideEq p e2 e3)
		plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 e2) (PlusG _ (NegG _ e3) e4)) | (Just e2_equiv_e3) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p setAndMult g e1 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p setAndMult g e4 in
				(_ ** (PlusG _ e1' e4', ?MplusInverse_assoc'_1))
		plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 e2) (PlusG _ (NegG _ e3) e4)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc' p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc' p setAndMult g e3 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p setAndMult g e4 in
				(_ ** ((PlusG _ (PlusG _ e1' e2') (PlusG _ (NegG _ e3') e4')), ?MplusInverse_assoc'_2))
				
	-- (a+(-b)) + (c+d)
	plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) (PlusG _ e3 e4)) with (groupDecideEq p e2 e3)
		plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) (PlusG _ e3 e4)) | (Just e2_equiv_e3) = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p setAndMult g e1 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p setAndMult g e4 in
				(_ ** (PlusG _ e1' e4', ?MplusInverse_assoc'_3))
		plusInverse_assoc' p setAndMult g (PlusG _ (PlusG _ e1 (NegG _ e2)) (PlusG _ e3 e4)) | _ = 
			let (r_e1' ** (e1', p_e1')) = plusInverse_assoc' p setAndMult g e1 in
			let (r_e2' ** (e2', p_e2')) = plusInverse_assoc' p setAndMult g e2 in
			let (r_e3' ** (e3', p_e3')) = plusInverse_assoc' p setAndMult g e3 in
			let (r_e4' ** (e4', p_e4')) = plusInverse_assoc' p setAndMult g e4 in
				(_ ** ((PlusG _ (PlusG _ e1' (NegG _ e2')) (PlusG _ e3' e4')), ?MplusInverse_assoc'_4))
				
	-- Anything else
	plusInverse_assoc' p setAndMult g {c1=c1} e =
		(_ ** (e, set_eq_undec_refl c1))
				
			
	pre_groupReduce : (c:Type) -> {n:Nat} -> (p:dataTypes.Group c) -> (setAndMult:SetWithMult c (group_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
	pre_groupReduce c p setAndMult g e =
		let (r_1 ** (e_1, p_1)) = elimMinus p setAndMult e in
		let (r_2 ** (e_2, p_2)) = propagateNeg p setAndMult e_1 in -- changed : it's no longer the fixpoint as one pass should now be enough
		let (r_3 ** (e_3, p_3)) = elimDoubleNeg p setAndMult e_2 in
		let (r_4 ** (e_4, p_4)) = elim_plusInverse p setAndMult g e_3 in
		let (r_5 ** (e_5, p_5)) = plusInverse_assoc p setAndMult g e_4 in
		let (r_6 ** (e_6, p_6)) = plusInverse_assoc' p setAndMult g e_5 in -- NEW (assoc at 3 levels of +, for dealing with things like (x+y) + (-y + z)
		let (r_7 ** (e_7, p_7)) = fold_negative_constant_fix p setAndMult e_6 in
		-- IMPORTANT : At this stage, we only have negation on variables and constants.
		-- Thus, we can continue the reduction by calling the reduction for a monoid, with encoding for the minus :
		-- the expression (-c) is encoded as a constant c', and the variable (-x) as a varible x'
		let (r_8 ** (e_8, p_8)) = code_reduceM_andDecode p setAndMult g e_7 in
			(r_8 ** (e_8, ?Mpre_groupReduce_1))
			
			
	-- Computes the fixpoint of pre_groupReduce : do the entire serie of simplification as long as we've not finished (ie, as long as we don't loop on the same term)
	-- That's needed because some simplification done at the monoid level could lead to new simplification.
	-- Exemple : (0+(Y)) become (Y) at the Monoid level. And if this Y was encoding (-x), then at the toplevel we can have x + (-x) now,
	-- which need a new simplification at the group level
	groupReduce : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> {setAndMult:SetWithMult c (group_to_set p)} -> {g:Vect n c} -> {c1:c} -> (ExprG p setAndMult g c1) -> (c2 ** (ExprG p setAndMult g c2, c1~=c2))
	groupReduce p e = 
		let (c' ** (e', p')) = pre_groupReduce _ p _ _ e in
			case exprG_eq p _ _ e e' of 
				Just pr => (c' ** (e', p'))-- We stop here
				Nothing => let (c'' ** (e'', p'')) = groupReduce p e' in
							(c'' ** (e'', ?Mgroup_Reduce_1))
		
			
	total
	buildProofGroup : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> {setAndMult:SetWithMult c (group_to_set p)} -> {g:Vect n c} -> {x : c} -> {y : c} -> {c1:c} -> {c2:c} -> (ExprG p setAndMult g c1) -> (ExprG p setAndMult g c2) -> (x~=c1) -> (y~=c2) -> (Maybe (x~=y))
	buildProofGroup p e1 e2 lp rp with (exprG_eq p _ _ e1 e2)
		buildProofGroup p e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofGroup
		buildProofGroup p e1 e2 lp rp | Nothing = Nothing

		
	groupDecideEq : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> {setAndMult:SetWithMult c (group_to_set p)} -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprG p setAndMult g x) -> (ExprG p setAndMult g y) -> (Maybe (x~=y))
	-- e1 is the left side, e2 is the right side
	groupDecideEq p e1 e2 =
		let (r_e1 ** (e_e1, p_e1)) = groupReduce p e1 in
		let (r_e2 ** (e_e2, p_e2)) = groupReduce p e2 in
			buildProofGroup p e_e1 e_e2 p_e1 p_e2


  
---------- Proofs ----------
Provers.group_reduce.MelimMinus1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.group_reduce.MelimMinus2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Neg c2))
  exact (Plus c1 (Neg c2))
  mrefine Minus_simpl 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym -- Dammit, I can't do (exact (set_eq_undec_sym p_ih1)) because of some instances resolutions of typeclass, which is just a bug to me.
  mrefine Neg_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_sym -- Same remark here
  exact p_ih2
  
Provers.group_reduce.MelimMinus3 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1 
  
Provers.group_reduce.MpropagateNeg_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg c2) (Neg c1))
  exact (Plus (Neg c2) (Neg c1))
  mrefine push_negation 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_sym 
  exact p_ih2
  exact p_ih1

{-  
Provers.group_reduce.MpropagateNeg_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1  
  -}
  
Provers.group_reduce.MpropagateNeg_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

-- The fixpoint function for propagateNeg is in theory no longer needed  
{-  
Provers.group_reduce.MpropagateNeg_fix_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_1
  exact p_1
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact p_ih1 
-}
  
Provers.group_reduce.MelimDoubleNeg_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact c1
  exact c1
  mrefine group_doubleNeg 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p_ih1
   
Provers.group_reduce.MelimDoubleNeg_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1   
   
Provers.group_reduce.MelimDoubleNeg_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2
  
Provers.group_reduce.Mfold_negative_constant_1 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine push_negation
  
Provers.group_reduce.Mfold_negative_constant_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih      

Provers.group_reduce.Mfold_negative_constant_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.group_reduce.Mfold_negative_constant_fix_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_1
  exact p_1
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.group_reduce.Mencode_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.group_reduce.Mdecode_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.group_reduce.Mcode_reduceM_andDecode_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact c2
  exact c2
  exact pEncode 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  exact c3
  exact c3
  mrefine set_eq_undec_sym 
  exact pReduce 
  mrefine set_eq_undec_refl 
  exact pDecode   

Provers.group_reduce.Melim_plusInverse_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_e1'
  exact p_e2'

Provers.group_reduce.Melim_plusInverse_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg c1) c1)
  exact (Plus (Neg c1) c1)
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine right
  exact e1_equiv_e2 
  exact (Plus c1 (Neg c1) ~= Zero)
  mrefine Plus_inverse 

Provers.group_reduce.Melim_plusInverse_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_e2'
  exact p_e1' 

Provers.group_reduce.Melim_plusInverse_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Neg c1))
  exact (Plus c1 (Neg c1))
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine Neg_preserves_equiv 
  mrefine left
  mrefine set_eq_undec_sym 
  exact (Plus (Neg c1) c1 ~= Zero)
  mrefine Plus_inverse 
  mrefine e1_equiv_e2 

Provers.group_reduce.Melim_plusInverse_5 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine p_e2'
  exact p_e1'

Provers.group_reduce.Melim_plusInverse_6 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_e1'
  exact p_e2'
  
Provers.group_reduce.MplusInverse_assoc_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Plus (Neg c1) c3))
  exact (Plus c1 (Plus (Neg c1) c3))
  mrefine Plus_preserves_equiv 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact c3
  exact c3
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_e3'
  exact (Plus (Plus c1 (Neg c1)) c3)
  exact (Plus (Plus c1 (Neg c1)) c3)
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine Plus_assoc 
  mrefine eq_preserves_eq 
  mrefine  e1_equiv_e2 
  exact (Plus Zero c3)
  exact (Plus Zero c3)
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine left
  mrefine set_eq_undec_refl 
  mrefine Plus_neutral_1
  exact (Plus (Neg c1) c1 ~= Zero)
  mrefine Plus_inverse   

Provers.group_reduce.MplusInverse_assoc_2 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_e1'
  mrefine Plus_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_e3'
  exact p_e2'

Provers.group_reduce.MplusInverse_assoc_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus (Neg c2) c2) c3)
  exact (Plus (Plus (Neg c2) c2) c3)
  mrefine eq_preserves_eq 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  exact (Plus (Plus (Neg c1) c2) c3)
  exact (Plus (Plus (Neg c1) c2) c3)
  mrefine set_eq_undec_sym
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact (Plus Zero c3)
  exact (Plus Zero c3)
  mrefine eq_preserves_eq 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Plus_assoc 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  exact c3
  exact c3
  mrefine set_eq_undec_sym 
  mrefine Plus_neutral_1
  mrefine set_eq_undec_refl
  mrefine right
  mrefine set_eq_undec_refl
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_e3'
  exact (Plus c2 (Neg c2) ~= Zero)
  mrefine Plus_inverse 
  mrefine set_eq_undec_sym 
  exact e1_equiv_e2 

Provers.group_reduce.MplusInverse_assoc_4 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact p_e1'
  exact p_e2'
  exact p_e3'

Provers.group_reduce.MplusInverse_assoc_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Plus c2 (Neg c2)))
  exact (Plus c1 (Plus c2 (Neg c2)))
  mrefine eq_preserves_eq 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  exact (Plus c1 (Plus c2 (Neg c3)))
  exact (Plus c1 (Plus c2 (Neg c3)))
  mrefine Plus_assoc 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact c1
  exact c1
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact p_e1'
  exact (Plus c1 Zero)
  exact (Plus c1 Zero)
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl
  mrefine left
  mrefine Plus_neutral_2
  exact e2_equiv_e3 
  exact (Plus (Neg c2) c2 ~= Zero)
  mrefine Plus_inverse 
  
Provers.group_reduce.MplusInverse_assoc_6 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_e1'
  exact p_e2'
  exact p_e3'
	
Provers.group_reduce.MplusInverse_assoc_7 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Plus (Neg c2) c3))
  exact (Plus c1 (Plus (Neg c2) c3))
  mrefine Plus_assoc
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  exact c1
  exact c1
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl
  exact p_e1'
  exact (Plus c1 Zero)
  exact (Plus c1 Zero)
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine eq_preserves_eq 
  mrefine Plus_neutral_2
  exact (Plus (Neg c2) c2)
  exact (Plus (Neg c2) c2)
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine right
  exact e2_equiv_e3 
  exact (Plus c2 (Neg c2) ~= Zero)
  mrefine Plus_inverse 
  
Provers.group_reduce.MplusInverse_assoc_8 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact p_e3'
  exact p_e1'
  mrefine Neg_preserves_equiv 
  exact p_e2'
  
Provers.group_reduce.MplusInverse_assoc_9 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2
  
Provers.group_reduce.MplusInverse_assoc'_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus c1 c2) (Plus (Neg c2) c4))
  exact (Plus (Plus c1 c2) (Plus (Neg c2) c4))
  mrefine Plus_preserves_equiv 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact (Plus (Plus c1 (Plus c2 (Neg c2))) c4)
  exact (Plus (Plus c1 (Plus c2 (Neg c2))) c4)
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl
  exact (Plus (Plus c1 Zero) c4)
  exact (Plus (Plus c1 Zero) c4)
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl
  mrefine groupAssoc_4terms
  mrefine set_eq_undec_sym
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_sym
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl
  exact e2_equiv_e3 
  exact c1
  exact c1
  mrefine set_eq_undec_sym
  mrefine add_zero_right 
  mrefine set_eq_undec_refl
  exact p_e4' 
  mrefine set_eq_undec_refl
  mrefine left
  exact p_e1'
  mrefine set_eq_undec_refl
  exact (Plus (Neg c2) c2 ~= Zero)
  mrefine Plus_inverse 

Provers.group_reduce.MplusInverse_assoc'_2 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact p_e1' 
  exact p_e2'
  mrefine Neg_preserves_equiv 
  exact p_e4' 
  exact p_e3' 

Provers.group_reduce.MplusInverse_assoc'_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus c1 (Neg c2)) (Plus c2 c4))
  exact (Plus (Plus c1 (Neg c2)) (Plus c2 c4))
  mrefine Plus_preserves_equiv 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact (Plus (Plus c1 (Plus (Neg c2) c2)) c4)
  exact (Plus (Plus c1 (Plus (Neg c2) c2)) c4)
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  mrefine set_eq_undec_refl
  exact (Plus (Plus c1 Zero) c4)
  exact (Plus (Plus c1 Zero) c4)
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine groupAssoc_4terms
  exact e2_equiv_e3 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_sym 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl
  exact c1
  exact c1
  mrefine set_eq_undec_sym 
  mrefine add_zero_right 
  mrefine set_eq_undec_refl
  exact p_e4' 
  mrefine set_eq_undec_refl
  mrefine right
  exact p_e1' 
  mrefine set_eq_undec_refl
  exact (Plus c2 (Neg c2) ~= Zero)
  mrefine Plus_inverse 
  
Provers.group_reduce.MplusInverse_assoc'_4 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact p_e1'
  mrefine Neg_preserves_equiv 
  exact p_e3'
  exact p_e4'
  exact p_e2'
        
Provers.group_reduce.Mpre_groupReduce_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact c1
  exact r_7
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  mrefine eq_preserves_eq 
  exact p_8
  exact c1
  exact r_6
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  mrefine eq_preserves_eq 
  exact p_7
  exact r_5
  exact r_5
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact c1
  exact r_4
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  exact p_6
  exact p_5
  exact c1
  exact r_3
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  exact p_4
  exact c1
  exact r_2
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym
  mrefine eq_preserves_eq 
  exact p_3
  exact c1
  exact r_1
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym
  exact p_1
  exact p_2

Provers.group_reduce.Mgroup_Reduce_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact c'
  exact c'
  exact p'
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p'' 
    
Provers.group_reduce.MbuildProofGroup = proof
  intros
  refine Just
  mrefine eq_preserves_eq 
  exact c1
  exact c2
  exact lp
  exact rp
  exact e1_equiv_e2 
















