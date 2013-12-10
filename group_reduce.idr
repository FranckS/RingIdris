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
    (_ ** (NegG e_ih1, ?MelimMinus3))

  
elimDoubleNeg : (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
elimDoubleNeg p g (NegG (NegG e1)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg p g e1 in
        (_ ** (e_ih1, ?MelimDoubleNeg_1))
elimDoubleNeg n p e1 = 
    (_ ** (e1, refl))


exprG_simpl_eq  : (p:dataTypes.Group c) -> (g:Vect n c) -> (c1:c) -> (c2:c) -> (e1:ExprG p g c1) -> (e2:ExprG p g c2) -> (Maybe (e1=e2))
exprG_simpl_eq p g c1 c2 e1 e2 = 
    let (c1' ** (e1', p1')) = elimMinus _ p e1 in
    let (c2' ** (e2', p2')) = elimMinus _ p e2 in
        let (c1'' ** (e1'', p1'')) = elimDoubleNeg p g e1' in
        let (c2'' ** (e2'', p2'')) = elimDoubleNeg p g e2' in
            let (c1''' ** (e1''', p1''')) = monoidReduce (group_to_monoid_class p) g (partial_group_to_monoid e1'') in
            let (c2''' ** (e2''', p2''')) = monoidReduce (group_to_monoid_class p) g (partial_group_to_monoid e2'') in
                let test = exprMo_eq (group_to_monoid_class p) e1''' e2''' in
                    -- Suis-je sur que c'est tout ce qu'il y a à faire ici ?
                    ?MexprG_simpl_eq
            

--------------------------------------------
-- Simplify (+e) + (-e) at *one* level of +
--------------------------------------------
elim_plusInverse : (p:dataTypes.Group c) -> (g:Vect n c) -> {c1:c} -> (ExprG p g c1) -> (c2 ** (ExprG p g c2, c1=c2))
elim_plusInverse p g (ConstG p const) = (_ ** (ConstG p const, refl))
elim_plusInverse p g (VarG p v) = (_ ** (VarG p v, refl))
-- Reminder : e1 and e2 can't be a Neg themselves, because you are suppose to call elimDoubleNeg before calling this function...
elim_plusInverse p g (PlusG (NegG e1) (NegG e2)) = (_ ** ((PlusG (NegG e1) (NegG e2)), refl))
-- If e2 is not a Neg !
elim_plusInverse p g (PlusG (NegG e1) e2) with (exprG_simpl_eq p g _ _ e1 e2) -- compare les versions simplifiees de e1 et de e2
    elim_plusInverse p g (PlusG (NegG e1) e1) | (Just refl) = (_ ** ((ConstG _ Zero), ?Melim_plusInverse_1))
    elim_plusInverse p g (PlusG (NegG e1) e2) | _ = (_ ** ((PlusG (NegG e1) e2), refl))
-- If e1 is not a Neg !
elim_plusInverse p g (PlusG e1 (NegG e2)) with (exprG_simpl_eq p g _ _ e1 e2) -- compare les versions simplifiees de e1 et de e2
    elim_plusInverse p g (PlusG e1 (NegG e1)) | (Just refl) = (_ ** ((ConstG _ Zero), ?Melim_plusInverse_2))
    elim_plusInverse p g (PlusG e1 (NegG e2)) | _ = (_ ** ((PlusG e1 (NegG e2)), refl))
-- If e1 and e2 are not Neg 
elim_plusInverse p g (PlusG e1 e2) = (_ ** ((PlusG e1 e2), refl))
elim_plusInverse p g e = (_ ** (e, refl))
                        

--------------------------------------------------------------------------
-- To do : Simplify (+e) + (-e) with associativity (at two levels of +) !
--------------------------------------------------------------------------
        
    
---------- Proofs ----------
group_reduce.MelimMinus1 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  trivial

group_reduce.MelimMinus2 = proof
  intros
  rewrite p_ih1
  rewrite p_ih2
  mrefine Minus_simpl
  
group_reduce.MelimMinus3 = proof
  intros
  rewrite p_ih1 
  trivial
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  








