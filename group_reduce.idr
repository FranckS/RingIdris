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
assoc_plusInverse : (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
assoc_plusInverse p g (ConstSG p const) = (_ ** (ConstSG p const, refl))
assoc_plusInverse p g (VarSG p v) = (_ ** (VarSG p v, refl))
assoc p g (PlusSG (PlusSG e1 (ConstSG p c1)) (PlusSG (ConstSG p c2) e2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (assoc p g e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (assoc p g e2) in 
    let (r_3 ** (e_3, p_3)) = magmaReduce (semiGroup_to_magma {p} {g} (PlusSG (ConstSG p c1) (ConstSG p c2))) in
    let e_3' = magma_to_semiGroup p e_3 in
    (_ ** ((PlusSG (PlusSG e_ih1 e_3') e_ih2), ?Massoc1))
-- (x + c1) + c2 -> x + (res c1+c2)
assoc p g (PlusSG (PlusSG e1 (ConstSG p c1)) (ConstSG p c2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (assoc p g e1) in
    let (r_2 ** (e_2, p_2)) = magmaReduce (semiGroup_to_magma {p} {g} (PlusSG (ConstSG p c1) (ConstSG p c2))) in
    let e_2' = magma_to_semiGroup p e_2 in
    (_ ** ((PlusSG e_ih1 e_2'), ?Massoc2))
-- c1 + (c2 + x) -> (res c1 +c c2) + x                                 
assoc p g (PlusSG (ConstSG p c1) (PlusSG (ConstSG p c2) e1)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (assoc p g e1) in
    let (r_2 ** (e_2, p_2)) = magmaReduce (semiGroup_to_magma {p} {g} (PlusSG (ConstSG p c1) (ConstSG p c2))) in
    let e_2' = magma_to_semiGroup p e_2 in
    (_ ** ((PlusSG e_2' e_ih1), ?Massoc3))                                        
                                                    
assoc p g (PlusSG e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = (assoc p g e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = (assoc p g e2) in 
    let (r_3 ** (e_3, p_3)) = magmaReduce (semiGroup_to_magma {p} {g} e1) in
    let (r_4 ** (e_4, p_4)) = magmaReduce (semiGroup_to_magma {p} {g} e2) in
    let e_3' = magma_to_semiGroup p e_3 in
    let e_4' = magma_to_semiGroup p e_4 in
        case (exprSG_eq p (PlusSG e1 e2) (PlusSG e_3' e_4')) of
        Just _ => (_ ** ((PlusSG  e_3' e_4'), ?Massoc4)) -- Fixed point reached
        Bothing => let (r_final ** (e_final, p_final)) = assoc p g (PlusSG e_3' e_4') in -- Need to continue
                    (_ ** (e_final, ?Massoc5))

 -}                    
    










