-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File monoid_reduce.idr
-- Normalize an expression reflecting an element in a monoid
-------------------------------------------------------------------

module Provers.monoid_reduce

import Decidable.Equality
import Provers.dataTypes
import Provers.semiGroup_reduce
import Provers.tools


--%default total



total
elimZero : (c:Type) -> (p:dataTypes.Monoid c) -> (neg:c->c) -> (setAndMult:SetWithMult c (monoid_to_set p)) -> (g:Vect n c) -> {c1:c} -> (ExprMo p neg setAndMult g c1) -> (c2 ** (ExprMo p neg setAndMult g c2, c1~=c2))
elimZero c p neg setAndMult g (ConstMo _ _ _ _ const) = (_ ** (ConstMo _ _ _ _ const, set_eq_undec_refl {c} _))
-- elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) = ?foo --with (monoid_get_setEq p Zero const1) 
elimZero c p neg setAndMult g (PlusMo _ _ (ConstMo _ _ _ _ const1) (VarMo _ _ _ v)) with (monoid_eq_as_elem_of_set p Zero const1)
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | with_pat = ?elimZero_rhs~~
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | (Just prf) = ?elimZero_rhs_2
    elimZero c p neg setAndMult g (PlusMo _ _ (ConstMo _ _ _ _ const1) (VarMo _ _ _ v)) | (Just const1_eq_zero) = (_ ** (VarMo _ _ _ v, ?MelimZero1))
    elimZero c p neg setAndMult g (PlusMo _ _ (ConstMo _ _ _ _ const1) (VarMo _ _ _ v)) | _ = (_ ** (PlusMo _ _ (ConstMo _ _ _ _ const1) (VarMo _ _ _ v), set_eq_undec_refl {c} _)) 
elimZero c p neg setAndMult g (PlusMo _ _ (VarMo _ _ _ v) (ConstMo _ _ _ _ const2)) with (monoid_eq_as_elem_of_set p Zero const2) 
    elimZero c p neg setAndMult g (PlusMo _ _ (VarMo _ _ _ v) (ConstMo _ _ _ _ const2)) | (Just const2_eq_zero) = (_ ** (VarMo _ _ _ v, ?MelimZero2))
    elimZero c p neg setAndMult g (PlusMo _ _ (VarMo _ _ _ v) (ConstMo _ _ _ _ const2)) | _ = (_ ** (PlusMo _ _ (VarMo _ _ _ v) (ConstMo _ _ _ _ const2), set_eq_undec_refl {c} _))
elimZero c p neg setAndMult g (PlusMo _ _ e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimZero c p neg setAndMult g e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimZero c p neg setAndMult g e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMo _ _ e_ih1 e_ih2, ?MelimZero3))  
elimZero c p neg setAndMult g (VarMo _ _ _ v) = (_ ** (VarMo _ _ _ v, set_eq_undec_refl {c} _))


monoidReduce : (p:dataTypes.Monoid c) -> {neg:c->c} -> {setAndMult:SetWithMult c (monoid_to_set p)} -> {g:Vect n c} -> {c1:c} -> (ExprMo p neg setAndMult g c1) -> (c2 ** (ExprMo p neg setAndMult g c2, c1~=c2))
monoidReduce p e = 
    let (r_SGred ** (e_SGred,  p_SGred)) = semiGroupReduce (monoid_to_semiGroup_class p) (monoid_to_semiGroup e) in
		let (r_elim ** (e_elim, p_elim)) = elimZero _ p _ _ _ (semiGroup_to_monoid p e_SGred) in
            (_ ** (e_elim, ?MmonoidReduce1))

            
total
buildProofMonoid : (p:dataTypes.Monoid c) -> {neg:c->c} -> {setAndMult:SetWithMult c (monoid_to_set p)} -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprMo p neg setAndMult g c1) -> (ExprMo p neg setAndMult g c2) -> (x ~= c1) -> (y ~= c2) -> (Maybe (x~=y))
buildProofMonoid p e1 e2 lp rp with (exprMo_eq p _ _ _ e1 e2)
    buildProofMonoid p e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofMonoid
    buildProofMonoid p e1 e2 lp rp | Nothing = Nothing


monoidDecideEq : (p:dataTypes.Monoid c) -> {neg:c->c} -> {setAndMult:SetWithMult c (monoid_to_set p)} -> {g:Vect n c} -> (ExprMo p neg setAndMult g x) -> (ExprMo p neg setAndMult g y) -> (Maybe (x~=y))
-- e1 is the left side, e2 is the right side
monoidDecideEq p e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = monoidReduce p e1 in
    let (r_e2 ** (e_e2, p_e2)) = monoidReduce p e2 in
    buildProofMonoid p e_e1 e_e2 p_e1 p_e2            


---------- Proofs ----------
Provers.monoid_reduce.MmonoidReduce1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_SGred
  exact r_SGred
  exact p_SGred 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p_elim 

Provers.monoid_reduce.MelimZero1 = proof
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

Provers.monoid_reduce.MelimZero2 = proof
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
  
Provers.monoid_reduce.MelimZero3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2 

Provers.monoid_reduce.MbuildProofMonoid = proof
  intros
  refine Just
  mrefine eq_preserves_eq 
  exact c1
  exact c2
  exact lp
  exact rp
  exact e1_equiv_e2 


  
  


  
  
  
  
  
  
  
  
  
  
