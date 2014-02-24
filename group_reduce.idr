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
                                              


                     
data SignedTerm : Type -> Type where
  NegationOfUnsigned : {c:Type} -> (r:c) -> SignedTerm c
  Unsigned : {c:Type} -> (r:c) -> SignedTerm c

{-
total
newPlus : {c:Type} -> {p:dataTypes.Group c} -> (r1:Monoid_from_Group c) -> (r2:Monoid_from_Group c) -> (Monoid_from_Group c)
newPlus (Normal e1) (Normal e2) = Normal (Plus e1 e2)	
newPlus x y = Addition x y
-}

{-
newPlus_assoc : {c:Type} -> {p:dataTypes.Group c} -> (r1:Monoid_from_Group c) -> (r2:Monoid_from_Group c) -> (r3:Monoid_from_Group c) -> 
		  (newPlus {p=p} r1 r2 = newPlus {p=p} r1 r2)
newPlus_assoc r1 r2 r3 = let 
-}


  
{-
  
-- Build a semiGroup from a Group      
--buildMonoid : {c:Type} -> (p:dataTypes.Group c) -> (c2 ** (dataTypes.SemiGroup c2))
--buildMonoid

-}

--group_to_monoid_value : {c:Type} -> (p:dataTypes.Group c) -> (c1:c) -> (Monoid_from_Group c)


-- To be completed with additional conditions, and with the correct operations
signedTerm_is_a_monoid : (c:Type) -> dataTypes.Monoid (SignedTerm c)
-- proof...

toSignedTerm : {c:Type} -> (r:c) -> SignedTerm c
toSignedTerm r = Unsigned r --Just an encoding

toSignedTerm_vector : {c:Type} -> {n:Nat} -> (g:Vect n c) -> (Vect n (SignedTerm c))
toSignedTerm_vector Nil = Nil
toSignedTerm_vector (h::t) = (toSignedTerm h)::(toSignedTerm_vector t)

{-
group_get_r : {c:Type} -> {p:dataTypes.Group c} -> {n:Nat}-> {g:Vect n c} -> {r:c} -> (ExprG p g r) -> c
group_get_r (ConstG p r) = r
group_get_r (PlusG e1 e2) = 
  let r1 = group_get_r e1 in
  let r2 = group_get_r e2 in
    (Plus r1 r2)
group_get_r (MinusG e1 e2) = 
  let r1 = group_get_r e1 in
  let r2 = group_get_r e2 in
    (Minus c1 c2)
group_get_r (NegG e) = 
  let r = group_get_r e in 
    (Neg r)
group_get_r (VarG p i) = (index i g)
-}

--pseudo total function : the element in the group should have been simplified before calling this function (no minus, and neg only to constant and variables)
code_group_to_monoid : (c:Type) -> {p:dataTypes.Group c} -> {n:Nat} -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> 
			  (c1' ** (ExprMo {c=SignedTerm c} {n} (signedTerm_is_a_monoid c) (toSignedTerm_vector g) c1'))
code_group_to_monoid c g (ConstG p cst) = (_ ** (ConstMo (signedTerm_is_a_monoid c) (Unsigned cst)))
code_group_to_monoid c g (PlusG e1 e2) = 
	let (r_ih1 ** e_ih1) = code_group_to_monoid c g e1 in
	let (r_ih2 ** e_ih2) = code_group_to_monoid c g e2 in
		(_ ** (PlusMo e_ih1 e_ih2))
-- total_group_to_monoid c (MinusG e1 e2) can't happen
code_group_to_monoid c g (NegG (ConstG p r)) = (_ ** (ConstMo (signedTerm_is_a_monoid c) (NegationOfUnsigned r)))
code_group_to_monoid c g (NegG (VarG p i b)) = (_ ** (VarMo (signedTerm_is_a_monoid c) i (not b))) -- We encode the negation *in* the variable 
-- Can't be a NegG of something else at this stage
code_group_to_monoid c g (VarG p i b) = (_ ** (VarMo (signedTerm_is_a_monoid c) i b))


toUnsignedTerm : {c:Type} -> (r:SignedTerm c) -> c
toUnsignedTerm (Unsigned r) = r
-- toUnsignedTerm (NegationOfUnsigned r) should never happen but we need it for totality
toUnsignedTerm (NegationOfUnsigned r) = r -- Am I sure that it won't be a problem ?


toUnsignedTerm_vector : {c:Type} -> {n:Nat} -> (g:Vect n (SignedTerm c)) -> (Vect n c)
toUnsignedTerm_vector Nil = Nil
toUnsignedTerm_vector (h::t) = (toUnsignedTerm h)::(toUnsignedTerm_vector t)


decode_monoid_to_group : (c:Type) -> {pm : dataTypes.Monoid (SignedTerm c)} -> (pg:dataTypes.Group c) -> {n:Nat} -> (g:Vect n (SignedTerm c)) -> {c1:SignedTerm c} -> (ExprMo pm g c1) ->
			    (c1' ** (ExprG pg (toUnsignedTerm_vector g) c1'))
decode_monoid_to_group c pg g (ConstMo p (Unsigned cst)) = (_ ** (ConstG pg cst))
decode_monoid_to_group c pg g (ConstMo p (NegationOfUnsigned cst)) = (_ ** (NegG (ConstG pg cst)))
decode_monoid_to_group c pg g (PlusMo e1 e2) = 
	let (r_ih1 ** e_ih1) = decode_monoid_to_group c pg g e1 in
	let (r_ih2 ** e_ih2) = decode_monoid_to_group c pg g e2 in
		(_ ** (PlusG e_ih1 e_ih2))
decode_monoid_to_group c pg g (VarMo p i True) = (_ ** (VarG pg i True))
decode_monoid_to_group c pg g (VarMo p i False) = (_ ** (NegG (VarG pg i True)))

toUnsignedTerm_toSignedTerm_id : {c:Type} -> (r:c) -> (toUnsignedTerm (toSignedTerm r) = r)
toUnsignedTerm_toSignedTerm_id r = refl


{-
-- auxiliary result
toUnsignedTerm_of_Nil : {c:Type} -> (toUnsignedTerm_vector {c=c} (Prelude.Vect.Nil {a=SignedTerm c}) = Prelude.Vect.Nil {a=c})
toUnsignedTerm_of_Nil = ?MtoUnsignedTerm_of_Nil_1
-}


{-
aux : {c:Type} -> {n:Nat} -> {h:c} -> {t:Vect n c} -> toUnsignedTerm_vector (Unsigned h :: (toSignedTerm_vector t)) = (toUnsignedTerm (Unsigned h)) :: (toUnsignedTerm_vector (toSignedTerm_vector t))
aux = ?Maux
-}


toUnsignedTerm_toSignedTerm_vector_id : {c:Type} -> {n:Nat} -> (g:Vect n c) -> (toUnsignedTerm_vector (toSignedTerm_vector g) = g)
toUnsignedTerm_toSignedTerm_vector_id Nil = ?MtoUnsignedTerm_toSignedTerm_vector_id_1
toUnsignedTerm_toSignedTerm_vector_id (h::t) = 
    let p_aux = toUnsignedTerm_toSignedTerm_vector_id t in
        ?MtoUnsignedTerm_toSignedTerm_vector_id_2


{-
code_decode_id : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {r1:c} -> (e:ExprG p g r1) -> (code_decode c p g 
code_decode_id c p g (ConstG p cst) = 
code_decode_id c p g (PlusG e1 e2) = 
code_decode_id c p g (NegG (Const
-}

sameExpr : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> (r1:c) -> (ExprG p (toUnsignedTerm_vector (toSignedTerm_vector g)) r1) -> ExprG p g r1
sameExpr c p g r1 e = ?MsameExpr_1


code_decode : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {r1:c} -> (ExprG p g r1) -> (r2 ** (ExprG p g r2, r1=r2))
code_decode c p g e =
  let (r_2 ** e_2) = code_group_to_monoid c g e in
    let (r_3 ** e_3) = decode_monoid_to_group c p (toSignedTerm_vector g) e_2 in
      --?Mcode_decode_1 -- Just returns (r_3 ** e_3) but uses the fact that the "gs" are compatible, because of the lemma toUnsignedTerm_toSignedTerm_vector_id 
        (r_3 ** ((sameExpr _ _ _ _ e_3), ?Mcode_decode_1))


convert : {c:Type} -> {p:dataTypes.Monoid c} -> {g:Vect n c} -> (r1:c) -> (r2:c) -> (r1_eq_e2:r1=r2) -> (ExprMo p g r1) -> (ExprMo p g r2)
convert r1 r2 r1_eq_e2 e = ?Mconvert_1


code_reduceM_andDecode : (c:Type) -> (p:dataTypes.Group c) -> (g:Vect n c) -> {r1:c} -> (ExprG p g r1) -> (r2 ** (ExprG p g r2, r1=r2))
code_reduceM_andDecode c p g e = 
    let (r_2 ** e_2) = (code_group_to_monoid _ _ e) in
	let (r_3 ** (e_3, p_3)) = monoidReduce (signedTerm_is_a_monoid _) (toSignedTerm_vector g) e_2 in
	let (r_4 ** e_4) = decode_monoid_to_group c p _ (convert r_3 r_2 (sym p_3) e_3) in
		(r_4 ** ((sameExpr _ _ _ _ e_4), ?Mcode_reduceM_andDecode_1))

		
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
		let (r_6 ** (e_6, p_6)) = code_reduceM_andDecode c p g e_5 in
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
  
{-  
group_reduce.MtoUnsignedTerm_toSignedTerm_id_1 = proof
  intro
  exact toUnsignedTerm_of_Nil 
-}  
  
{-  
group_reduce.Mcode_decode_1 = proof
  intros
  rewrite toUnsignedTerm_toSignedTerm_vector_id g
  exact (r_3 ** e_3)  
  -}
  
group_reduce.MtoUnsignedTerm_toSignedTerm_vector_id_1 = proof
  intros
  mrefine refl
  
{-  
group_reduce.MtoUnsignedTerm_of_Nil_1 = proof
  intros
  mrefine refl  
-}  
  
group_reduce.MtoUnsignedTerm_toSignedTerm_vector_id_2 = proof
  intros
  rewrite p_aux
  mrefine refl  

group_reduce.MsameExpr_1 = proof
  intros
  rewrite (toUnsignedTerm_toSignedTerm_vector_id g)
  exact e

group_reduce.Mconvert_1 = proof
  intros
  rewrite r1_eq_e2 
  exact e
  
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
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  










