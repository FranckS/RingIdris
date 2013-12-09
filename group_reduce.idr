-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_reduce.idr
-- Normalize an expression reflecting an element in a group
-------------------------------------------------------------------

module group_reduce

import Decidable.Equality
import dataTypes
import tools


--%default total

total
exprG_eq : (p:dataTypes.Group c) -> {g:Vect n c} -> {c1 : c} -> {c2 : c} -> (e1:ExprG p g c1) -> (e2:ExprG p g c2) -> (Maybe (e1=e2))
exprG_eq p (PlusG x y) (PlusG x' y') with (exprG_eq p x x', exprG_eq p y y')
  exprG_eq p (PlusG x y) (PlusG x y) | (Just refl, Just refl) = Just refl
  exprG_eq p (PlusG x y) (PlusG x' y') | _ = Nothing
exprG_eq p (VarG p i) (VarG p j) with (decEq i j)
  exprG_eq p (VarG p i) (VarG p i) | (Yes refl) = Just refl
  exprG_eq p (VarG p i) (VarG p j) | _ = Nothing
exprG_eq p (ConstG p const1) (ConstG p const2) with ((group_eq_as_elem_of_set p) const1 const2)
    exprG_eq p (ConstG p const1) (ConstG p const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprG_eq p (ConstG p const1) (ConstG p const2) | _ = Nothing
exprG_eq p _ _  = Nothing


total
elimMinus : (c:Type) -> (p:dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
elimMinus c p (ConstG p const) = (_ ** (ConstG p const, refl))
elimMinus c p (PlusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus c p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus c p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MelimMinus1))
elimMinus c p (VarG p v) = (_ ** (VarG p v, refl))    
elimMinus c p (MinusG e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus c p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus c p e2) in
    ((Plus r_ih1 (Neg r_ih2)) ** (PlusG e_ih1 (NegG e_ih2), ?MelimMinus2)) 
elimMinus c p (NegG e1) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus c p e1) in
    (_ ** (e_ih1, ?Melim3))
    
    
{-
elimZero c p (PlusG (VarMo p v) (ConstG p const2)) with (monoid_eq_as_elem_of_set p Zero const2) 
    elimZero c p (PlusG (VarMo p v) (ConstG p dataTypes.Zero)) | (Just refl) = (_ ** (VarMo p v, ?MelimZero2))
    elimZero c p (PlusG (VarMo p v) (ConstG p const2)) | _ = (_ ** (PlusG (VarMo p v) (ConstG p const2), refl))
elimZero c p (PlusG e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (elimZero c p e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (elimZero c p e2) in
      ((Plus r_ih1 r_ih2) ** (PlusG e_ih1 e_ih2, ?MelimZero3))  
elimZero c p (VarMo p v) = (_ ** (VarMo p v, refl))

-}















