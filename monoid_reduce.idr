-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File monoid_reduce.idr
-- Normalize an expression reflecting an element in a monoid
-------------------------------------------------------------------

module monoid_reduce

import Decidable.Equality
import dataTypes
import semiGroup_reduce
import tools


--%default total



total
elimZero : (c:Type) -> (p:dataTypes.Monoid c) -> (neg:c->c) -> (g:Vect n c) -> {c1:c} -> (ExprMo p neg g c1) -> (c2 ** (ExprMo p neg g c2, c1=c2))

elimZero c p neg g (ConstMo _ _ _ const) = (_ ** (ConstMo _ _ _ const, refl))
-- elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) = ?foo --with (monoid_get_setEq p Zero const1) 
elimZero c p neg g (PlusMo _ (ConstMo _ _ _ const1) (VarMo _ _ v)) with (monoid_eq_as_elem_of_set p Zero const1)
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | with_pat = ?elimZero_rhs
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | (Just prf) = ?elimZero_rhs_2
    elimZero c p neg g (PlusMo _ (ConstMo _ _ _ dataTypes.Zero) (VarMo _ _ v)) | (Just refl) = (_ ** (VarMo _ _ v, ?MelimZero1))
    elimZero c p neg g (PlusMo _ (ConstMo _ _ _ const1) (VarMo _ _ v)) | _ = (_ ** (PlusMo _ (ConstMo _ _ _ const1) (VarMo _ _ v), refl)) 
elimZero c p neg g (PlusMo _ (VarMo _ _ v) (ConstMo _ _ _ const2)) with (monoid_eq_as_elem_of_set p Zero const2) 
    elimZero c p neg g (PlusMo _ (VarMo _ _ v) (ConstMo _ _ _ dataTypes.Zero)) | (Just refl) = (_ ** (VarMo _ _ v, ?MelimZero2))
    elimZero c p neg g (PlusMo _ (VarMo _ _ v) (ConstMo _ _ _ const2)) | _ = (_ ** (PlusMo _ (VarMo _ _ v) (ConstMo _ _ _ const2), refl))
elimZero c p neg g (PlusMo _ e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (elimZero c p neg g e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (elimZero c p neg g e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMo _ e_ih1 e_ih2, ?MelimZero3))  
elimZero c p neg g (VarMo _ _ v) = (_ ** (VarMo _ _ v, refl))


monoidReduce : (p:dataTypes.Monoid c) -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> (ExprMo p neg g c1) -> (c2 ** (ExprMo p neg g c2, c1=c2))
monoidReduce p e = 
    let (r_SGred ** (e_SGred,  p_SGred)) = semiGroupReduce (monoid_to_semiGroup_class p) (monoid_to_semiGroup e) in
        let (r_elim ** (e_elim, p_elim)) = elimZero _ p _ _ (semiGroup_to_monoid p e_SGred) in
            (_ ** (e_elim, ?MmonoidReduce1))

            
total
buildProofMonoid : (p:dataTypes.Monoid c) -> {neg:c->c} -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprMo p neg g c1) -> (ExprMo p neg g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofMonoid p e1 e2 lp rp with (exprMo_eq p _ _ e1 e2)
    buildProofMonoid p e1 e1 lp rp | Just refl = ?MbuildProofMonoid
    buildProofMonoid p e1 e2 lp rp | Nothing = Nothing


monoidDecideEq : (p:dataTypes.Monoid c) -> {neg:c->c} -> {g:Vect n c} -> (ExprMo p neg g x) -> (ExprMo p neg g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
monoidDecideEq p e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = monoidReduce p e1 in
    let (r_e2 ** (e_e2, p_e2)) = monoidReduce p e2 in
    buildProofMonoid p e_e1 e_e2 p_e1 p_e2            


---------- Proofs ----------
monoid_reduce.MmonoidReduce1 = proof
  intros
  rewrite p_elim
  rewrite p_SGred
  trivial


monoid_reduce.MelimZero1 = proof
  intros
  mrefine Plus_neutral_1

monoid_reduce.MelimZero2 = proof
  intros
  mrefine Plus_neutral_2
  
monoid_reduce.MelimZero3 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  trivial  

monoid_reduce.MbuildProofMonoid = proof
  intros;
  refine Just;
  rewrite( sym lp);
  rewrite( sym rp);
  exact refl;


  
  


  
  
  
  
  
  
  
  
  
  
