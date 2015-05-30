-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File magma_reduce.idr
-- Normalize an expression reflecting an element in a magma
-------------------------------------------------------------------

module Provers.magma_reduce

import Decidable.Equality
import Provers.dataTypes


%default total


-- Normalization
magmaReduce : {c:Type} -> {n:Nat} -> {p:Magma c} -> {neg:c->c} -> {setAndMult:SetWithMult c (magma_to_set_class p)} -> {g:Vect n c} -> {c1:c} -> (ExprMa p neg setAndMult g c1) -> (c2 ** (ExprMa p neg setAndMult g c2, c1~=c2))
magmaReduce (ConstMa p neg setAndMult g const) = (_ ** (ConstMa p neg setAndMult g const, set_eq_undec_refl const))
magmaReduce (PlusMa neg setAndMult {g=g} (ConstMa p _ _ _ const1) (ConstMa p _ _ _ const2)) = (_ ** (ConstMa p neg setAndMult g (Plus const1 const2), set_eq_undec_refl (Plus const1 const2)))
magmaReduce (PlusMa neg setAndMult e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (magmaReduce e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (magmaReduce e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMa neg setAndMult e_ih1 e_ih2, ?MmagmaReduce1))                    
magmaReduce (VarMa p neg setAndMult {c1=c1} v) = (_ ** (VarMa p neg setAndMult v, set_eq_undec_refl c1))


buildProofMagma : {c:Type} -> {n:Nat} -> (p:Magma c) -> (setAndNeg:SetWithNeg c (magma_to_set_class p)) -> {setAndMult:SetWithMult c (magma_to_set_class p)} -> {g:Vect n c} -> {x:c} -> {y:c} -> {c1:c} -> {c2:c} -> (ExprMa p (neg setAndNeg) setAndMult g c1) -> (ExprMa p (neg setAndNeg) setAndMult g c2) -> (x ~= c1) -> (y ~= c2) -> (Maybe (x~=y))
buildProofMagma p setAndNeg e1 e2 lp rp with (exprMa_eq p setAndNeg _ _ e1 e2)
    buildProofMagma p setAndNeg e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofMagma
    buildProofMagma p setAndNeg e1 e2 lp rp | Nothing = Nothing


magmaDecideEq : {c:Type} -> {n:Nat} -> (p:Magma c) -> (setAndNeg:SetWithNeg c (magma_to_set_class p)) -> {setAndMult:SetWithMult c (magma_to_set_class p)} -> {g:Vect n c} -> {x:c} -> {y:c} -> (ExprMa p (neg setAndNeg) setAndMult g x) -> (ExprMa p (neg setAndNeg) setAndMult g y) -> Maybe (x~=y)
-- e1 is the left side, e2 is the right side
magmaDecideEq p setAndNeg e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = magmaReduce e1 in
    let (r_e2 ** (e_e2, p_e2)) = magmaReduce e2 in
    buildProofMagma p setAndNeg e_e1 e_e2 p_e1 p_e2

     
---------- Proofs ----------                
Provers.magma_reduce.MmagmaReduce1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.magma_reduce.MbuildProofMagma = proof
  intros
  refine Just
  mrefine eq_preserves_eq 
  exact c1
  exact c2
  exact lp
  exact rp
  exact e1_equiv_e2 



  
  
  