-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File magma_reduce.idr
-- Normalize an expression reflecting an element in a magma
-------------------------------------------------------------------

module Solver.magma_reduce

import Decidable.Equality
import Solver.dataTypes


%default total

-- Normalization
magmaReduce : {c:Type} -> {n:Nat} -> {p:Magma c} -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> (ExprMa p neg g c1) -> (c2 ** (ExprMa p neg g c2, c1=c2))
magmaReduce (ConstMa p neg g const) = (_ ** (ConstMa p neg g const, refl))
magmaReduce (PlusMa neg {g=g} (ConstMa p _ _ const1) (ConstMa p _ _ const2)) = (_ ** (ConstMa p neg g (Plus const1 const2), refl))
magmaReduce (PlusMa neg e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (magmaReduce e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (magmaReduce e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMa neg e_ih1 e_ih2, ?MmagmaReduce1))                    
magmaReduce (VarMa p neg v) = (_ ** (VarMa p neg v, refl))


buildProofMagma : {c:Type} -> {n:Nat} -> (p:Magma c) -> {neg:c->c} -> {g:Vect n c} -> {x:c} -> {y:c} -> {c1:c} -> {c2:c} -> (ExprMa p neg g c1) -> (ExprMa p neg g c2) -> (x = c1) -> (y = c2) -> (Maybe (set_eq_undec x y))
buildProofMagma p e1 e2 lp rp with (exprMa_eq p _ _ e1 e2)
    buildProofMagma p e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofMagma
    buildProofMagma p e1 e2 lp rp | Nothing = Nothing


magmaDecideEq : {c:Type} -> {n:Nat} -> (p:Magma c) -> {neg:c->c} -> {g:Vect n c} -> {x:c} -> {y:c} -> (ExprMa p neg g x) -> (ExprMa p neg g y) -> Maybe (set_eq_undec x y)
-- e1 is the left side, e2 is the right side
magmaDecideEq p e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = magmaReduce e1 in
    let (r_e2 ** (e_e2, p_e2)) = magmaReduce e2 in
    buildProofMagma p e_e1 e_e2 p_e1 p_e2
                


---------- Proofs ----------                
Solver.magma_reduce.MmagmaReduce1 = proof {
  intros;
  rewrite p_ih1;
  rewrite p_ih2;
  trivial;
}

Solver.magma_reduce.MbuildProofMagma = proof {
  intros;
  refine Just;
  rewrite( sym lp);
  rewrite( sym rp);
  exact e1_equiv_e2;
}






