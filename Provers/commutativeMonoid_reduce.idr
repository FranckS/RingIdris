-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_reduce.idr
-- Normalize an expression reflecting an element in a commutative monoid
-------------------------------------------------------------------

module Provers.commutativeMonoid_reduce

import Decidable.Equality
import Data.Vect
import Data.Fin
import Provers.dataTypes
import Provers.tools
import Provers.monoid_reduce




-- A usufel lemma for most rewriting in this section
assoc_commute_and_assoc' : {c:Type} -> {p:CommutativeMonoid c} -> (x : c) -> (y : c) -> (z : c) -> (Plus (Plus x y) z ~= Plus (Plus x z) y)
assoc_commute_and_assoc' x y z = let aux : (Plus (Plus x y) z ~= Plus x (Plus y z)) = Plus_assoc x y z in
								let aux2 : (Plus x (Plus y z) ~= Plus x (Plus z y)) = ?Massoc_commute_and_assoc'_1 in
								let aux3 : (Plus x (Plus z y) ~= Plus (Plus x z) y) = (set_eq_undec_sym (Plus_assoc x z y)) in
									?Massoc_commute_and_assoc'_2


-- 2 FUNCTIONS WHICH ADD A TERM TO AN EXPRESSION ALREADY "SORTED" (of the right forme)
-- -----------------------------------------------------------------------------------
								
--%default total
-- The expression is already in the form a + (b + (c + ...)) where a,b,c can only be constants, variables, and negations of constants and variables
putVarOnPlace_cm : {c:Type} -> (p:CommutativeMonoid c) -> (setAndMult:SetWithMult c (commutativeMonoid_to_set p)) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCM p setAndMult g c1)
   -> (i:Fin n)
   -> (c2 ** (ExprCM p setAndMult g c2, Plus c1 (index i g) ~= c2))
putVarOnPlace_cm p setAndMult (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e) (i) =
    if minusOrEqual_Fin i0 i 
	   then let (r_ihn ** (e_ihn, p_ihn))= (putVarOnPlace_cm p setAndMult e i) in
            (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e_ihn, ?MputVarOnPlace_cm_1))
        else (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i)) (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e), ?MputVarOnPlace_cm_2))
putVarOnPlace_cm p setAndMult (PlusCM _ (ConstCM _ _ _ c0) e) (i) = 
	(_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i)) (PlusCM _ (ConstCM _ _ _ c0) e), ?MputVarOnPlace_cm_3)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
-- Basic cases : cases without Plus
putVarOnPlace_cm p setAndMult (ConstCM _ _ _ c0) i = (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i)) (ConstCM _ _ _ c0), ?MputVarOnPlace_cm_4))
putVarOnPlace_cm p setAndMult (VarCM p _ (RealVariable _ _ _ _ i0)) i = 
	    if minusOrEqual_Fin i0 i then (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) (VarCM p _ (RealVariable _ _ _ _ i)), set_eq_undec_refl _))
		else (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i)) (VarCM p _ (RealVariable _ _ _ _ i0)), ?MputVarOnPlace_cm_5))


putConstantOnPlace_cm : {c:Type} -> (p:CommutativeMonoid c) -> (setAndMult:SetWithMult c (commutativeMonoid_to_set p)) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCM p setAndMult g c1) -> (constValue:c) 
   -> (c2 ** (ExprCM p setAndMult g c2, Plus c1 constValue~=c2))
putConstantOnPlace_cm p setAndMult (PlusCM _ (ConstCM _ _ _ c0) e) constValue = (_ ** (PlusCM _ (ConstCM _ _ _ (Plus c0 constValue)) e, ?MputConstantOnPlace_cm_1))
putConstantOnPlace_cm p setAndMult (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e) constValue = 
	let (r_ihn ** (e_ihn, p_ihn)) = putConstantOnPlace_cm p setAndMult e constValue in
		(_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e_ihn, ?MputConstantOnPlace_cm_2))
-- Basic cases : cases without Plus
putConstantOnPlace_cm p setAndMult (ConstCM _ _ _ c0) constValue = (_ ** (ConstCM _ _ _ (Plus c0 constValue), set_eq_undec_refl _))
putConstantOnPlace_cm p setAndMult (VarCM p _ (RealVariable _ _ _ _ i0)) constValue = (_ ** (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) (ConstCM _ _ _ constValue), set_eq_undec_refl _))


-- FUNCTION WHICH REORGANIZE AN EXPRESSION	
-- -----------------------------------------

-- That's the reorganize function for a Commutative Monoid
-- The general pattern is reorganize (Plus term exp) = putTermOnPlace (reorganize exp) term
reorganize_cm : {c:Type} -> (p:CommutativeMonoid c) -> (setAndMult:SetWithMult c (commutativeMonoid_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprCM p setAndMult g c1) -> (c2 ** (ExprCM p setAndMult g c2, c1~=c2))
reorganize_cm p setAndMult (PlusCM _ (VarCM p _ (RealVariable _ _ _ _ i0)) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize_cm p setAndMult e in
	let (r_add ** (e_add, p_add)) = putVarOnPlace_cm p setAndMult e_ihn i0 in
		(_ ** (e_add, ?Mreorganize_cm_1))
reorganize_cm p setAndMult (PlusCM _ (ConstCM _ _ _ c0) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize_cm p setAndMult e in
	let (r_add ** (e_add, p_add)) = putConstantOnPlace_cm p setAndMult e_ihn c0 in
		(_ ** (e_add, ?Mreorganize_cm_2))	
reorganize_cm p setAndMult e = (_ ** (e, set_eq_undec_refl _))



--WHY DO WE NEED THIS IN THE FUNCTION elimZeroCM JUST UNDER ? THAT'S CRAP !
getZero_cm : {c:Type} -> (p:dataTypes.CommutativeMonoid c) -> c
getZero_cm p = Zero


elimZeroCM : {c:Type} -> (p:dataTypes.CommutativeMonoid c) -> (setAndMult:SetWithMult c (commutativeMonoid_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprCM p setAndMult g c1) -> (c2 ** (ExprCM p setAndMult g c2, c1~=c2))
elimZeroCM p setAndMult (ConstCM p _ _ const) = (_ ** (ConstCM p _ _ const, set_eq_undec_refl const))
elimZeroCM p setAndMult (PlusCM _ (ConstCM p _ _ const1) (VarCM p _ v)) with (commutativeMonoid_eq_as_elem_of_set p Zero const1)
    elimZeroCM p setAndMult (PlusCM _ (ConstCM p _ _ const1) (VarCM p _ v)) | (Just const1_eq_zero) = (_ ** (VarCM p _ v, ?MelimZeroCM1))
    elimZeroCM p setAndMult (PlusCM _ (ConstCM p _ _ const1) (VarCM p _ v)) | _ = (_ ** (PlusCM _ (ConstCM p _ _ const1) (VarCM p _ v), set_eq_undec_refl _))
elimZeroCM p setAndMult (PlusCM _ (VarCM _ _ v) (ConstCM _ _ _ const2)) with (commutativeMonoid_eq_as_elem_of_set p Zero const2) 
    elimZeroCM p setAndMult (PlusCM _ (VarCM _ _ v) (ConstCM _ _ _ const2)) | (Just const2_eq_zero) = (_ ** (VarCM _ _ v, ?MelimZeroCM2))
    elimZeroCM p setAndMult (PlusCM _ (VarCM _ _ v) (ConstCM _ _ _ const2)) | _ = (_ ** (PlusCM _ (VarCM _ _ v) (ConstCM _ _ _ const2), set_eq_undec_refl _))
elimZeroCM p setAndMult (PlusCM _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimZeroCM p setAndMult e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimZeroCM p setAndMult e2) in
        ((Plus r_ih1 r_ih2) ** (PlusCM _ e_ih1 e_ih2, ?MelimZeroCM3))
elimZeroCM p setAndMult (VarCM _ _ v) = (_ ** (VarCM _ _ v, set_eq_undec_refl _))
-- No treatment for Minus since they have already been simplified
-- and no treatment for Neg since we should not find a constant inside a Neg at this point
elimZeroCM p setAndMult e = (_ ** (e, set_eq_undec_refl _))


commutativeMonoidReduce : (p:CommutativeMonoid c) -> {setAndMult:SetWithMult c (commutativeMonoid_to_set p)} -> {g:Vect n c} -> {c1:c} -> (ExprCM p setAndMult g c1) -> (c2 ** (ExprCM p setAndMult g c2, c1~=c2))
commutativeMonoidReduce p e =
	let e_1 = commutativeMonoid_to_monoid e in
	let (r_2 ** (e_2, p_2)) = monoidReduce _ e_1 in
	let e_3 = monoid_to_commutativeMonoid p e_2 in
	let (r_4 ** (e_4, p_4)) = reorganize_cm p _ e_3 in
	let (r_5 ** (e_5, p_5)) = elimZeroCM p _ e_4 in
            (_ ** (e_5, ?McommutativeMonoidReduce_1))


buildProofCommutativeMonoid : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {setAndMult:SetWithMult c (commutativeMonoid_to_set p)} -> {g:Vect n c} -> {x : c} -> {y : c} -> {c1:c} -> {c2:c} -> (ExprCM p setAndMult g c1) -> (ExprCM p setAndMult g c2) -> (x ~= c1) -> (y ~= c2) -> (Maybe (x ~= y))
buildProofCommutativeMonoid p e1 e2 lp rp with (exprCM_eq p _ _ e1 e2)
	buildProofCommutativeMonoid p e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofCommutativeMonoid
	buildProofCommutativeMonoid p e1 e2 lp rp | Nothing = Nothing


commutativeMonoidDecideEq : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {setAndMult:SetWithMult c (commutativeMonoid_to_set p)} -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprCM p setAndMult g x) -> (ExprCM p setAndMult g y) -> (Maybe (x~=y))
-- e1 is the left side, e2 is the right side
commutativeMonoidDecideEq p e1 e2 =
	let (r_e1 ** (e_e1, p_e1)) = commutativeMonoidReduce p e1 in
	let (r_e2 ** (e_e2, p_e2)) = commutativeMonoidReduce p e2 in
		buildProofCommutativeMonoid p e_e1 e_e2 p_e1 p_e2	
        


---------- Proofs ----------  
Provers.commutativeMonoid_reduce.Massoc_commute_and_assoc'_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl
  mrefine Plus_comm'
  
Provers.commutativeMonoid_reduce.Massoc_commute_and_assoc'_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus x (Plus y z))
  exact (Plus (Plus x z) y)
  exact aux
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact (Plus x (Plus y z))
  exact (Plus x (Plus z y))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact aux2
  exact aux3 
  
Provers.commutativeMonoid_reduce.MputVarOnPlace_cm_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus (index i0 g) c2) (index i g))
  exact (Plus (index i0 g) (Plus c2 (index i g)))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Plus_assoc 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p_ihn   
     
Provers.commutativeMonoid_reduce.MputVarOnPlace_cm_2 = proof
  intros
  mrefine Plus_comm'
        
Provers.commutativeMonoid_reduce.MputVarOnPlace_cm_3 = proof
  intros
  mrefine Plus_comm'

Provers.commutativeMonoid_reduce.MputVarOnPlace_cm_4 = proof
  intros
  mrefine Plus_comm'
        
Provers.commutativeMonoid_reduce.MputVarOnPlace_cm_5 = proof
  intros
  mrefine Plus_comm'

Provers.commutativeMonoid_reduce.MputConstantOnPlace_cm_1 = proof
  intros
  mrefine assoc_commute_and_assoc'

Provers.commutativeMonoid_reduce.MputConstantOnPlace_cm_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus (index i0 g) c2) constValue)
  exact (Plus (index i0 g) (Plus c2 constValue))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Plus_assoc 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  exact p_ihn 

Provers.commutativeMonoid_reduce.Mreorganize_cm_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (index i0 g) r_ihn)
  exact r_add
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p_ihn 
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  exact (Plus r_ihn (index i0 g))
  exact r_add
  mrefine Plus_comm'
  mrefine set_eq_undec_refl
  exact p_add  

Provers.commutativeMonoid_reduce.Mreorganize_cm_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c0 r_ihn)
  exact r_add
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl
  exact p_ihn
  exact (Plus r_ihn c0)
  exact r_add
  mrefine Plus_comm'
  mrefine set_eq_undec_refl
  exact p_add

Provers.commutativeMonoid_reduce.MelimZeroCM1 = proof
  intros
  mrefine eq_preserves_eq
  exact (Plus Zero c2)
  exact c2
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Plus_neutral_1
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact const1_eq_zero  

Provers.commutativeMonoid_reduce.MelimZeroCM2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 Zero)
  exact c1
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Plus_neutral_2
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  exact const2_eq_zero 

Provers.commutativeMonoid_reduce.MelimZeroCM3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2  
  
Provers.commutativeMonoid_reduce.McommutativeMonoidReduce_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_2
  exact r_5
  exact p_2 
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_4
  exact r_5
  exact p_4
  mrefine set_eq_undec_refl 
  exact p_5   

Provers.commutativeMonoid_reduce.MbuildProofCommutativeMonoid = proof
  intros
  refine Just
  mrefine eq_preserves_eq 
  exact c1
  exact c2
  exact lp
  exact rp
  exact e1_equiv_e2   
  

  
  
  
  
  
  
  
  
  
  
  
  