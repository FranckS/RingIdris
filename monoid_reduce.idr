-- Edwin Brady, Franck SlaMo
-- University of St Andrews
-- File monoid_reduce.idr
-- NorMolize an expression reflecting an element in a monoid
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
exprMo_eq p (VarMo p i) (VarMo p j) with (decEq i j)
  exprMo_eq p (VarMo p i) (VarMo p i) | (Yes refl) = Just refl
  exprMo_eq p (VarMo p i) (VarMo p j) | _ = Nothing
exprMo_eq p (ConstMo p const1) (ConstMo p const2) with ((monoid_get_setEq p) const1 const2)
    exprMo_eq p (ConstMo p const1) (ConstMo p const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprMo_eq p (ConstMo p const1) (ConstMo p const2) | _ = Nothing
exprMo_eq p _ _  = Nothing

--%logging 2
elimZero : (c:Type) -> (p:dataTypes.Monoid c) -> {g:Vect n c} -> {c1:c} -> (ExprMo p g c1) -> (c2 ** (ExprMo p g c2, c1=c2))
elimZero c p (ConstMo p const) = (_ ** (ConstMo p const, refl))
elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) with (monoid_get_setEq p Zero const1) 
    elimZero c p (PlusMo (ConstMo p Zero) (VarMo p v)) | (Just refl) = (_ ** (VarMo p v, ?MelimZero1))
    --elimZero c p (PlusMo (ConstMo p const1) (VarMo p v)) | _ = (_ ** (PlusMo (ConstMo p const1) (VarMo p v), refl)) 
--%logging 0    
{-      
elimZero c p (PlusMo (VarMo p v) (ConstMo p const2)) with (monoid_get_setEq p const2 (the c Zero)) 
    elimZero c p (PlusMo (VarMo p v) (ConstMo p (the c Zero))) | (Just refl) = (_ ** (VarMo p v, ?MelimZero2))
    elimZero c p (PlusMo (VarMo p v) (ConstMo p const2)) | _ = (_ ** (PlusMo (VarMo p v) (ConstMo p const2), refl))
elimZero c p (PlusMo e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (elimZero c p e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (elimZero c p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusMo e_ih1 e_ih2, ?MelimZero3))  
elimZero c p (VarMo p v) = (_ ** (VarMo p v, refl))
-}



