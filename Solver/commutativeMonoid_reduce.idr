-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_reduce.idr
-- Normalize an expression reflecting an element in a commutative monoid
-------------------------------------------------------------------

module Solver.commutativeMonoid_reduce

import Decidable.Equality
import Solver.dataTypes
import Solver.monoid_reduce
import Solver.tools
import Prelude.Vect



-- A usufel lemma for most rewriting in this section
assoc_commute_and_assoc' : {c:Type} -> {p:CommutativeMonoid c} -> (x : c) -> (y : c) -> (z : c) -> (Plus (Plus x y) z = Plus (Plus x z) y)
assoc_commute_and_assoc' x y z = let aux : (Plus (Plus x y) z = Plus x (Plus y z)) = Plus_assoc x y z in
								let aux2 : (Plus x (Plus y z) = Plus x (Plus z y)) = (rewrite Plus_comm' y z in refl) in
								let aux3 : (Plus x (Plus z y) = Plus (Plus x z) y) = (sym (Plus_assoc x z y)) in
									?Massoc_commute_and_assoc'_1


-- 2 FUNCTIONS WHICH ADD A TERM TO AN EXPRESSION ALREADY "SORTED" (of the right forme)
-- -----------------------------------------------------------------------------------
								
--%default total
-- The expression is already in the form a + (b + (c + ...)) where a,b,c can only be constants, variables, and negations of constants and variables
putVarOnPlace_cm : {c:Type} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCM p g c1)
   -> (i:Fin n)
   -> (c2 ** (ExprCM p g c2, Plus c1 (index i g) = c2))
putVarOnPlace_cm p (PlusCM (VarCM p i0) e) (i) =
    if minusOrEqual_Fin i0 i 
        then let (r_ihn ** (e_ihn, p_ihn))= (putVarOnPlace_cm p e i) in
            (_ ** (PlusCM (VarCM p i0) e_ihn, ?MputVarOnPlace_cm_1))
        else (_ ** (PlusCM (VarCM p i) (PlusCM (VarCM p i0) e), ?MputVarOnPlace_cm_2))
putVarOnPlace_cm p (PlusCM (ConstCM _ _ c0) e) (i) = 
	(_ ** (PlusCM (VarCM p i) (PlusCM (ConstCM _ _ c0) e), ?MputVarOnPlace_cm_3)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
-- Basic cases : cases without Plus
putVarOnPlace_cm p (ConstCM _ _ c0) i = (_ ** (PlusCM (VarCM p i) (ConstCM _ _ c0), ?MputVarOnPlace_cm_4))
putVarOnPlace_cm p (VarCM p i0) i = 
	    if minusOrEqual_Fin i0 i then (_ ** (PlusCM (VarCM p i0) (VarCM p i), refl))
		else (_ ** (PlusCM (VarCM p i) (VarCM p i0), ?MputVarOnPlace_cm_5))


putConstantOnPlace_cm : {c:Type} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCM p g c1) -> (constValue:c) 
   -> (c2 ** (ExprCM p g c2, Plus c1 constValue=c2))
putConstantOnPlace_cm p (PlusCM (ConstCM _ _ c0) e) constValue = (_ ** (PlusCM (ConstCM _ _ (Plus c0 constValue)) e, ?MputConstantOnPlace_cm_1))
putConstantOnPlace_cm p (PlusCM (VarCM p i0) e) constValue = 
	let (r_ihn ** (e_ihn, p_ihn)) = putConstantOnPlace_cm p e constValue in
		(_ ** (PlusCM (VarCM p i0) e_ihn, ?MputConstantOnPlace_cm_2))
-- Basic cases : cases without Plus
putConstantOnPlace_cm p (ConstCM _ _ c0) constValue = (_ ** (ConstCM _ _ (Plus c0 constValue), refl))
putConstantOnPlace_cm p (VarCM p i0) constValue = (_ ** (PlusCM (VarCM p i0) (ConstCM _ _ constValue), refl))


-- FUNCTION WHICH REORGANIZE AN EXPRESSION	
-- -----------------------------------------

-- That's the reorganize function for a Commutative Monoid
-- The general pattern is reorganize (Plus term exp) = putTermOnPlace (reorganize exp) term
reorganize_cm : {c:Type} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} -> (ExprCM p g c1) -> (c2 ** (ExprCM p g c2, c1=c2))
reorganize_cm p (PlusCM (VarCM p i0) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize_cm p e in
	let (r_add ** (e_add, p_add)) = putVarOnPlace_cm p e_ihn i0 in
		(_ ** (e_add, ?Mreorganize_cm_1))
reorganize_cm p (PlusCM (ConstCM _ _ c0) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize_cm p e in
	let (r_add ** (e_add, p_add)) = putConstantOnPlace_cm p e_ihn c0 in
		(_ ** (e_add, ?Mreorganize_cm_2))	
reorganize_cm p e = (_ ** (e, refl))



--WHY DO WE NEED THIS IN THE FUNCTION elimZeroCM JUST UNDER ? THAT'S CRAP !
getZero_cm : {c:Type} -> (p:dataTypes.CommutativeMonoid c) -> c
getZero_cm p = Zero


elimZeroCM : {c:Type} -> (p:dataTypes.CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} -> (ExprCM p g c1) -> (c2 ** (ExprCM p g c2, c1=c2))
elimZeroCM p (ConstCM p _ const) = (_ ** (ConstCM p _ const, refl))
elimZeroCM p (PlusCM (ConstCM p _ const1) (VarCM p v)) with (commutativeMonoid_eq_as_elem_of_set p Zero const1)
    elimZeroCM p (PlusCM (ConstCM p _ (getZero_cm p)) (VarCM p v)) | (Just refl) = (_ ** (VarCM p v, ?MelimZeroCM1))
    elimZeroCM p (PlusCM (ConstCM p _ const1) (VarCM p v)) | _ = (_ ** (PlusCM (ConstCM p _ const1) (VarCM p v), refl))
elimZeroCM p (PlusCM (VarCM _ v) (ConstCM _ _ const2)) with (commutativeMonoid_eq_as_elem_of_set p Zero const2) 
    elimZeroCM p (PlusCM (VarCM _ v) (ConstCM _ _ (getZero_cm p))) | (Just refl) = (_ ** (VarCM _ v, ?MelimZeroCM2))
    elimZeroCM p (PlusCM (VarCM _ v) (ConstCM _ _ const2)) | _ = (_ ** (PlusCM (VarCM _ v) (ConstCM _ _ const2), refl))
elimZeroCM p (PlusCM e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (elimZeroCM p e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (elimZeroCM p e2) in
        ((Plus r_ih1 r_ih2) ** (PlusCM e_ih1 e_ih2, ?MelimZeroCM3))
elimZeroCM p (VarCM _ v) = (_ ** (VarCM _ v, refl))
-- No treatment for Minus since they have already been simplified
-- and no treatment for Neg since we should not find a constant inside a Neg at this point
elimZeroCM p e = (_ ** (e, refl))


commutativeMonoidReduce : (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} -> (ExprCM p g c1) -> (c2 ** (ExprCM p g c2, c1=c2))
commutativeMonoidReduce p e =
    let e_1 = commutativeMonoid_to_monoid e in
    let (r_2 ** (e_2, p_2)) = monoidReduce _ e_1 in
    let e_3 = monoid_to_commutativeMonoid p e_2 in
    let (r_4 ** (e_4, p_4)) = reorganize_cm p e_3 in
    let (r_5 ** (e_5, p_5)) = elimZeroCM p e_4 in
            (_ ** (e_5, ?McommutativeMonoidReduce_1))


buildProofCommutativeMonoid : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {x : c} -> {y : c} -> {c1:c} -> {c2:c} -> (ExprCM p g c1) -> (ExprCM p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofCommutativeMonoid p e1 e2 lp rp with (exprCM_eq p _ e1 e2)
	buildProofCommutativeMonoid p e1 e1 lp rp | Just refl = ?MbuildProofCommutativeMonoid
	buildProofCommutativeMonoid p e1 e2 lp rp | Nothing = Nothing


commutativeMonoidDecideEq : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprCM p g x) -> (ExprCM p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
commutativeMonoidDecideEq p e1 e2 =
	let (r_e1 ** (e_e1, p_e1)) = commutativeMonoidReduce p e1 in
	let (r_e2 ** (e_e2, p_e2)) = commutativeMonoidReduce p e2 in
		buildProofCommutativeMonoid p e_e1 e_e2 p_e1 p_e2	
        


---------- Proofs ----------  

Solver.commutativeMonoid_reduce.Massoc_commute_and_assoc'_1 = proof
  intros
  rewrite (sym aux)
  rewrite (sym aux2)
  rewrite (sym aux3)
  exact refl

Solver.commutativeMonoid_reduce.MputVarOnPlace_cm_1 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc         
        
Solver.commutativeMonoid_reduce.MputVarOnPlace_cm_2 = proof
  intros
  mrefine Plus_comm'
        
Solver.commutativeMonoid_reduce.MputVarOnPlace_cm_3 = proof
  intros
  mrefine Plus_comm'

Solver.commutativeMonoid_reduce.MputVarOnPlace_cm_4 = proof
  intros
  mrefine Plus_comm'
        
Solver.commutativeMonoid_reduce.MputVarOnPlace_cm_5 = proof
  intros
  mrefine Plus_comm'

Solver.commutativeMonoid_reduce.MputConstantOnPlace_cm_1 = proof
  intros
  mrefine assoc_commute_and_assoc'

Solver.commutativeMonoid_reduce.MputConstantOnPlace_cm_2 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc

Solver.commutativeMonoid_reduce.Mreorganize_cm_1 = proof
  intros
  rewrite p_add
  rewrite p_ihn
  mrefine Plus_comm'

Solver.commutativeMonoid_reduce.Mreorganize_cm_2 = proof
  intros
  rewrite p_add
  rewrite p_ihn
  mrefine Plus_comm'

Solver.commutativeMonoid_reduce.MelimZeroCM1 = proof
  intros
  mrefine Plus_neutral_1

Solver.commutativeMonoid_reduce.MelimZeroCM2 = proof
  intros
  mrefine Plus_neutral_2

Solver.commutativeMonoid_reduce.MelimZeroCM3 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  exact refl

Solver.commutativeMonoid_reduce.McommutativeMonoidReduce_1 = proof
  intros
  rewrite p_5
  rewrite p_4
  rewrite p_2
  exact refl

Solver.commutativeMonoid_reduce.MbuildProofCommutativeMonoid = proof
  intros
  refine Just
  rewrite (sym lp)
  rewrite (sym rp)
  exact refl


  
  
  
  
  




