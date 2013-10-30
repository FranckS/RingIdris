-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File semiGroup_reduce.idr
-- Normalize an expression reflecting an element in a semi-group
-------------------------------------------------------------------

module semiGroup_reduce

import Decidable.Equality
import dataTypes
import tools


--%default total

total
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
exprSG_eq p _ _  = Nothing


-- Normalization
-- No longer total due to fixed point to reach (non structural recursivity) (see last line of function)
assoc : (p:SemiGroup c) -> (g:Vect n c) -> {c1:c} -> (ExprSG p g c1) -> (c2 ** (ExprSG p g c2, c1=c2))
assoc p g (ConstSG p const) = (_ ** (ConstSG p const, refl))
assoc p g (VarSG p v) = (_ ** (VarSG p v, refl))
-- (x + c1) + (c2 + y) -> (x + (res c1+c2)) + y
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
                                                        

total
addAfter : (p:SemiGroup c) -> (g:Vect n c) -> {c1:c} -> {c2:c} -> (ExprSG p g c1) -> (ExprSG p g c2) -> (c3 ** (ExprSG p g c3, c3=Plus c1 c2))  
addAfter p g (ConstSG p c1) e = (_ ** (PlusSG (ConstSG p c1) e, refl)) 
addAfter p g (VarSG p v) e = (_ ** (PlusSG (VarSG p v) e, refl))
addAfter p g (PlusSG e11 e12) e2 = let (r_ih1 ** (e_ih1, p_ih1)) = addAfter p g e12 e2
                                    in (_ ** (PlusSG e11 e_ih1, ?MaddAfter1))


-- Transforms an expression in the form x + (y + (z + ...))
-- can't be assert as total (non structural recursion)
shuffleRight : (p:SemiGroup c) -> (g:Vect n c) -> {c1:c} -> (ExprSG p g c1) -> (c2 ** (ExprSG p g c2, c1=c2))  
shuffleRight p g (ConstSG p c) = (_ ** (ConstSG p c, refl))
shuffleRight p g (VarSG p v) = (_  ** (VarSG p v, refl))

shuffleRight p g (PlusSG (ConstSG p c1) (ConstSG p c2)) = (_ ** (PlusSG (ConstSG p c1) (ConstSG p c2), refl))
shuffleRight p g (PlusSG (ConstSG p c1) (VarSG p v)) = (_ ** (PlusSG (ConstSG p c1) (VarSG p v), refl))
shuffleRight p g (PlusSG (ConstSG p c1) (PlusSG e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleRight p g (PlusSG e21 e22) in
    (_ ** (PlusSG (ConstSG p c1) e_ih1, ?MshuffleRight1))
    -- Previously : PlusSG (ConstSG c1) (addAfter (shuffleRight p21) (shuffleRight p22)) 

shuffleRight p g (PlusSG (VarSG p v1) (ConstSG p c2)) = (_ ** (PlusSG (VarSG p v1) (ConstSG p c2), refl))
shuffleRight p g (PlusSG (VarSG p v1) (VarSG p v2)) = (_ ** (PlusSG (VarSG p v1) (VarSG p v2), refl))
shuffleRight p g (PlusSG (VarSG p v1) (PlusSG e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleRight p g (PlusSG e21 e22) in
    (_ ** (PlusSG (VarSG p v1) e_ih1, ?MshuffleRight2))
    -- PlusSG (VarSG v1) (addAfter (shuffleRight p21) (shuffleRight p22)) -- ok with me
    
shuffleRight p g (PlusSG (PlusSG e11 e12) (ConstSG p c2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleRight p g (PlusSG e11 e12) in
    let (r_2 ** (e_2, p_2)) = addAfter p g e_ih1 (ConstSG p c2) in
    (_ ** (e_2, ?MshuffleRight3))                                
shuffleRight p g (PlusSG (PlusSG e11 e12) (VarSG p v2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleRight p g (PlusSG e11 e12) in
    let (r_2 ** (e_2, p_2)) = addAfter p g e_ih1 (VarSG p v2) in
    (_ ** (e_2, ?MshuffleRight4))
shuffleRight p g (PlusSG (PlusSG e11 e12) (PlusSG e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleRight p g (PlusSG e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleRight p g (PlusSG e21 e22) in
    let (r_3 ** (e_3, p_3)) = addAfter p g e_ih1 e_ih2 in
    (_ ** (e_3, ?MshuffleRight5))
    -- Previously : addAfter (addAfter (shuffleRight p11) (shuffleRight p12)) (addAfter (shuffleRight p21) (shuffleRight p22))
    -- Note : equivalent to "addAfter (addAfter (addAfter (shuffleRight p11) (shuffleRight p12)) (shuffleRight p21)) (shuffleRight p22)"


semiGroupReduce : (p:SemiGroup c) -> (g:Vect n c) -> {c1:c} -> (ExprSG p g c1) -> (c2 ** (ExprSG p g c2, c1=c2))    
semiGroupReduce p g e = 
    let (r_assoc ** (e_assoc,  p_assoc)) = assoc p g e in
    let (r_shuffle ** (e_shuffle, p_shuffle)) = shuffleRight p g e_assoc in
    (_ ** (e_shuffle, ?MsemiGroupReduce1))
		

buildProofSemiGroup : (p:SemiGroup c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprSG p g c1) -> (ExprSG p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofSemiGroup p e1 e2 lp rp with (exprSG_eq p e1 e2)
    buildProofSemiGroup p e1 e1 lp rp | Just refl = ?MbuildProofSemiGroup
    buildProofSemiGroup p e1 e2 lp rp | Nothing = Nothing


semiGroupDecideEq : (p:SemiGroup c) -> (g:Vect n c) -> (ExprSG p g x) -> (ExprSG p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
semiGroupDecideEq p g e1 e2 = 
    let (r_e1 ** (e_e1, p_e1)) = semiGroupReduce p g e1 in
    let (r_e2 ** (e_e2, p_e2)) = semiGroupReduce p g e2 in
    buildProofSemiGroup p e_e1 e_e2 p_e1 p_e2
                


---------- Proofs ----------  
semiGroup_reduce.Massoc1 = proof {
  intros;
  rewrite p_ih1;
  rewrite p_ih2;
  rewrite p_3;
  rewrite (plusSym_4v c p c1 c2 c4 c3);
  rewrite (plusSym_4v' c p c1 c2 c4 c3);
  trivial;
}

semiGroup_reduce.Massoc2 = proof {
  intros;
  rewrite p_ih1 ;
  rewrite p_2;
  mrefine Plus_assoc;
}

semiGroup_reduce.Massoc3 = proof {
  intros;
  rewrite p_ih1 ;
  rewrite p_2;
  rewrite (sym (Plus_assoc c1 c3 c2));
  trivial;
}

semiGroup_reduce.Massoc4 = proof {
  intros;
  rewrite p_3;
  rewrite p_4;
  trivial;
}

semiGroup_reduce.Massoc5 = proof {
  intros;
  rewrite p_final ;
  rewrite p_3;
  rewrite p_4;
  trivial;
}

semiGroup_reduce.MaddAfter1 = proof {
  intros;
  rewrite (sym p_ih1);
  rewrite (Plus_assoc c1 c3 c2);
  trivial;
}

semiGroup_reduce.MshuffleRight1 = proof {
  intros;
  rewrite p_ih1 ;
  trivial;
}

semiGroup_reduce.MshuffleRight2 = proof {
  intros;
  rewrite p_ih1 ;
  trivial;
}

semiGroup_reduce.MshuffleRight3 = proof {
  intros;
  rewrite p_2;
  rewrite (sym p_2);
  rewrite p_ih1 ;
  trivial;
}

semiGroup_reduce.MshuffleRight4 = proof {
  intros;
  rewrite p_2;
  rewrite (sym p_2);
  rewrite p_ih1 ;
  trivial;
}

semiGroup_reduce.MshuffleRight5 = proof {
  intros;
  rewrite (sym p_3);
  rewrite p_ih1;
  rewrite p_ih2;
  trivial;
}

semiGroup_reduce.MsemiGroupReduce1 = proof {
  intros;
  rewrite p_shuffle ;
  rewrite p_assoc ;
  trivial;
}

semiGroup_reduce.MbuildProofSemiGroup = proof {
  intros;
  rewrite (sym lp);
  rewrite (sym rp);
  mrefine Just;
  trivial;
}





















