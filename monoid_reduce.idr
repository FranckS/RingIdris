-- Edwin Brady, Franck SlaMo
-- University of St Andrews
-- File monoid_reduce.idr
-- Normalize an expression reflecting an element in a monoid
-------------------------------------------------------------------

module monoid_reduce

import Decidable.Equality
import dataTypes
import tools


--%default total

total
exprMo_eq : (p:dataTypes.Monoid c) -> {g:Vect n c} -> {c1 : c} -> {c2 : c} -> (e1:ExprMo p g c1) -> (e2:ExprMo p g c2) -> (Maybe (e1=e2))
exprMo_eq p (PlusMo x y) (PlusMo x' y') with (exprMo_eq p x x', exprMo_eq p y y')
  exprMo_eq p (PlusMo x y) (PlusMo x y) | (Just refl, Just refl) = Just refl
  exprMo_eq p (PlusMo x y) (PlusMo x' y') | _ = Nothing
exprMo_eq p (VarMo p i b1) (VarMo p j b2) with (decEq i j, decEq b1 b2)
  exprMo_eq p (VarMo p i b1) (VarMo p i b1) | (Yes refl, Yes refl) = Just refl
  exprMo_eq p (VarMo p i b1) (VarMo p j b2) | _ = Nothing
exprMo_eq p (ConstMo p const1) (ConstMo p const2) with ((monoid_eq_as_elem_of_set p) const1 const2)
    exprMo_eq p (ConstMo p const1) (ConstMo p const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprMo_eq p (ConstMo p const1) (ConstMo p const2) | _ = Nothing
exprMo_eq p _ _  = Nothing

total
elimZero : (c:Type) -> (p:dataTypes.Monoid c) -> {g:Vect n c} -> {c1:c} -> (ExprMo p g c1) -> (c2 ** (ExprMo p g c2, c1=c2))
elimZero c p (ConstMo p const) = (_ ** (ConstMo p const, refl))
-- elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) = ?foo --with (monoid_get_setEq p Zero const1) 
elimZero c p (PlusMo (ConstMo p const1) (VarMo p v b)) with (monoid_eq_as_elem_of_set p Zero const1)
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | with_pat = ?elimZero_rhs
--  elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | (Just prf) = ?elimZero_rhs_2
    elimZero c p (PlusMo (ConstMo p dataTypes.Zero) (VarMo p v b)) | (Just refl) = (_ ** (VarMo p v b, ?MelimZero1))
    elimZero c p (PlusMo (ConstMo p const1) (VarMo p v b)) | _ = (_ ** (PlusMo (ConstMo p const1) (VarMo p v b), refl)) 
elimZero c p (PlusMo (VarMo p v b) (ConstMo p const2)) with (monoid_eq_as_elem_of_set p Zero const2) 
    elimZero c p (PlusMo (VarMo p v b) (ConstMo p dataTypes.Zero)) | (Just refl) = (_ ** (VarMo p v b, ?MelimZero2))
    elimZero c p (PlusMo (VarMo p v b) (ConstMo p const2)) | _ = (_ ** (PlusMo (VarMo p v b) (ConstMo p const2), refl))
elimZero c p (PlusMo e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (elimZero c p e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (elimZero c p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMo e_ih1 e_ih2, ?MelimZero3))  
elimZero c p (VarMo p v b) = (_ ** (VarMo p v b, refl))


monoidReduce : (p:dataTypes.Monoid c) -> (g:Vect n c) -> {c1:c} -> (ExprMo p g c1) -> (c2 ** (ExprMo p g c2, c1=c2))
monoidReduce p g e = 
    let (r_SGred ** (e_SGred,  p_SGred)) = semiGroupReduce (monoid_to_semiGroup_class p) g (monoid_to_semiGroup e) in
        let (r_elim ** (e_elim, p_elim)) = elimZero _ p (semiGroup_to_monoid p e_SGred) in
            (_ ** (e_elim, ?MmonoidReduce1))
            
buildProofMonoid : (p:dataTypes.Monoid c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprMo p g c1) -> (ExprMo p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofMonoid p e1 e2 lp rp with (exprMo_eq p e1 e2)
    buildProofMonoid p e1 e1 lp rp | Just refl = ?MbuildProofMonoid
    buildProofMonoid p e1 e2 lp rp | Nothing = Nothing


monoidDecideEq : (p:dataTypes.Monoid c) -> (g:Vect n c) -> (ExprMo p g x) -> (ExprMo p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
monoidDecideEq p g e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = monoidReduce p g e1 in
    let (r_e2 ** (e_e2, p_e2)) = monoidReduce p g e2 in
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
  intros
  rewrite lp
  rewrite (sym lp)
  rewrite (sym rp)
  mrefine Just
  trivial

  
  

  
  
  
  
  
  
  
  
  
  
