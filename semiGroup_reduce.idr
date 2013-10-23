-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File semiGroup_reduce.idr
-- Normalize expression reflecting an element of a semi-group
-------------------------------------------------------------------

module semiGroup_reduce


import Decidable.Equality

import dataTypes
import tools

--%default total

-- Normalization
total
semiGroupReduce : (p:SemiGroup c) -> (g:Vect n c) -> {c1:c} -> (ExprSG p g c1) -> (c2 ** (ExprSG p g c2, c1=c2))
semiGroupReduce p g (ConstSG p const) = (_ ** (ConstSG p const, refl))
semiGroupReduce p g (VarSG p v) = (_ ** (VarSG p v, refl))
semiGroupReduce p g (PlusSG (PlusSG e1 (ConstSG p c1)) (PlusSG (ConstSG p c2) e2)) = let (r_ih1 ** (e_ih1, p_ih1)) = (semiGroupReduce p g e1) in
                                                                                        let (r_ih2 ** (e_ih2, p_ih2)) = (semiGroupReduce p g e2) in 
                                                                                            let (r_3 ** (e_3, p_3)) = magmaReduce (semiGroup_to_magma {p} {g} (PlusSG (ConstSG p c1) (ConstSG p c2))) in
                                                                                                let e_3' = magma_to_semiGroup p e_3 in
                                                                                                    (_ ** ((PlusSG (PlusSG e_ih1 e_3') e_ih2), ?MsemiGroupReduce1))
semiGroupReduce p g (PlusSG e1 e2) = let (r_ih1 ** (e_ih1, p_ih1)) = (semiGroupReduce p g e1) in
                                    let (r_ih2 ** (e_ih2, p_ih2)) = (semiGroupReduce p g e2) in 
                                        let (r_3 ** (e_3, p_3)) = magmaReduce (semiGroup_to_magma {p} {g} e1) in
                                            let (r_4 ** (e_4, p_4)) = magmaReduce (semiGroup_to_magma {p} {g} e2) in
                                                let e_3' = magma_to_semiGroup p e_3 in
                                                    let e_4' = magma_to_semiGroup p e_4 in
                                                        (_ ** ((PlusSG  e_3' e_4'), ?MsemiGroupReduce2))



exprSG_eq : (p:SemiGroup c) -> {g:Vect n c} -> {c1 : c} -> {c2 : c} -> (e1:ExprSG p g c1) -> (e2:ExprSG p g c2) -> (Maybe (e1=e2))
exprSG_eq p (PlusSG x y) (PlusSG x' y') with (exprSG_eq p x x', exprSG_eq p y y')
  exprSG_eq p (PlusSG x y) (PlusSG x y) | (Just refl, Just refl) = Just refl
  exprSG_eq p (PlusSG x y) (PlusSG x' y') | _ = Nothing
exprSG_eq p (VarSG p i) (VarSG p j) with (decEq i j)
  exprSG_eq p (VarSG p i) (VarSG p i) | (Yes refl) = Just refl
  exprSG_eq p (VarSG p i) (VarSG p j) | _ = Nothing
exprSG_eq p (ConstSG p const1) (ConstSG p const2) with ((SemiGroup_getSet_eq p) const1 const2)
    exprSG_eq p (ConstSG p const1) (ConstSG p const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprSG_eq p (ConstSG p const1) (ConstSG p const2) | _ = Nothing


buildProofSemiGroup : (p:SemiGroup c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprSG p g c1) -> (ExprSG p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofSemiGroup p e1 e2 lp rp with (exprSG_eq p e1 e2)
    buildProofSemiGroup p e1 e1 lp rp | Just refl = ?MbuildProofSemiGroup
    buildProofSemiGroup p e1 e2 lp rp | Nothing = Nothing


semiGroupDecideEq : (p:SemiGroup c) -> (g:Vect n c) -> (ExprSG p g x) -> (ExprSG p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
semiGroupDecideEq p g e1 e2 = let (r_e1 ** (e_e1, p_e1)) = semiGroupReduce p g e1 in
                                let (r_e2 ** (e_e2, p_e2)) = semiGroupReduce p g e2 in
                                    buildProofSemiGroup p e_e1 e_e2 p_e1 p_e2
                



---------- Proofs ----------  
semiGroup_reduce.MsemiGroupReduce1 = proof {
  intros;
  rewrite p_ih1;
  rewrite p_ih2;
  rewrite p_3;
  rewrite (plusSym_4v c p c1 c2 c4 c3);
  rewrite (plusSym_4v' c p c1 c2 c4 c3);
  trivial;
}

semiGroup_reduce.MsemiGroupReduce2 = proof {
  intros;
  rewrite p_3;
  rewrite p_4;
  trivial;
}



































