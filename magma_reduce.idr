-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File magma_reduce.idr
-- Normalize an expression reflecting an element in a magma
-------------------------------------------------------------------

module magma_reduce

import Decidable.Equality
import dataTypes


%default total

-- Normalization
magmaReduce : {p:Magma c} -> {g:Vect n c} -> {c1:c} -> (ExprMa p g c1) -> (c2 ** (ExprMa p g c2, c1=c2))
magmaReduce (ConstMa p const) = (_ ** (ConstMa p const, refl))
magmaReduce (PlusMa (ConstMa p const1) (ConstMa p const2)) = (_ ** (ConstMa p (Plus const1 const2), refl))
magmaReduce (PlusMa e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (magmaReduce e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (magmaReduce e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMa e_ih1 e_ih2, ?MmagmaReduce1))                    
magmaReduce (VarMa p v) = (_ ** (VarMa p v, refl))



    

buildProofMagma : (p:dataTypes.Magma c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprMa p g c1) -> (ExprMa p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofMagma p e1 e2 lp rp with (exprMa_eq p e1 e2)
    buildProofMagma p e1 e1 lp rp | Just refl = ?MbuildProofMagma
    buildProofMagma p e1 e2 lp rp | Nothing = Nothing


magmaDecideEq : (p:dataTypes.Magma c) -> {g:Vect n c} -> (ExprMa p g x) -> (ExprMa p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
magmaDecideEq p e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = magmaReduce e1 in
    let (r_e2 ** (e_e2, p_e2)) = magmaReduce e2 in
    buildProofMagma p e_e1 e_e2 p_e1 p_e2
                
           
                
---------- Proofs ----------                

magma_reduce.MbuildProofMagma = proof {
  intros;
  rewrite lp;
  rewrite( sym lp);
  rewrite( sym rp);
  mrefine Just;
  mrefine refl;
}

magma_reduce.MmagmaReduce1 = proof {
  intros;
  rewrite p_ih1;
  rewrite p_ih2;
  trivial;
}

