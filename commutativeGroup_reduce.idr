-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeGroup_reduce.idr
-- Normalize an expression reflecting an element in a commutative group
-------------------------------------------------------------------

module commutativeGroup_reduce

import Decidable.Equality
import dataTypes
import group_reduce
import tools
import Prelude.Vect


--%default total
-- The expression is already in the form a + (b + (c + ...)) where a,b,c can only be constants, variables, and negations of constants and variables
putVarOnPlace : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> {varValue:c} 
   -> (Variable (commutativeGroup_eq_as_elem_of_set p) Neg g varValue) 
   -> (c2 ** (ExprCG p g c2, Plus c1 varValue=c2))
putVarOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) (RealVariable _ _ _ i) = 
    if minusOrEqual_Fin i0 i 
        then let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
             (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?M1))
        else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (VarCG p (RealVariable _ _ _ i0)) e), ?M1'))
putVarOnPlace p (PlusCG (ConstCG _ _ c0) e) (RealVariable _ _ _ i) = 
    let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
        (_ ** (PlusCG e_ihn (ConstCG _ _ c0), ?M2))
putVarOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) (RealVariable _ _ _ i) = ?M3
putVarOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) (RealVariable _ _ _ i) = ?M4






reorganize : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))
--reorganize p (PlusCG (


---------- Proofs ----------
commutativeGroup_reduce.M1 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc
  
commutativeGroup_reduce.M1' = proof
  intros
  mrefine Plus_comm 
  
  
  