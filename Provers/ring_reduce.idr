-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File ring_reduce.idr
-- Normalize an expression reflecting an element in a ring
-------------------------------------------------------------------

module Provers.ring_reduce

import Decidable.Equality
import Data.Fin
import Data.Vect
import Provers.dataTypes
import Provers.tools
import Provers.commutativeGroup_reduce

import Data.Vect



--%logging 2
-- Should be total, but can't be asserted to be, since Idris runs into an infinite loop at typecheck with 41 pattern matched cases
--total
develop : {c:Type} -> {p:dataTypes.Ring c} -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
develop (ConstR _ _ const) = (_ ** (ConstR _ _ const, set_eq_undec_refl _))
develop (VarR p v) = (_ ** (VarR p v, set_eq_undec_refl _))
develop (PlusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (develop e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (develop e2) in
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?Mdevelop_1))
-- Because Idris can't handle 41 cases, we remove this one, which means we'll have to simplify the Minus before calling this function   
{-
develop (MinusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (develop e1) in	
  let (r_ih2 ** (e_ih2, p_ih2)) = (develop e2) in
    ((Minus r_ih1 r_ih2) ** (MinusR e_ih1 e_ih2, ?Mdevelop_2))
-}
develop (NegR e) = 
  let (r_ih ** (e_ih, p_ih)) = (develop e) in
    (r_ih ** (e_ih, ?Mdevelop_3))

      
develop (MultR (ConstR _ _ c1) (ConstR _ _ c2)) = (_ ** (MultR (ConstR _ _ c1) (ConstR _ _ c2), set_eq_undec_refl _))     
develop (MultR (ConstR _ _ c1) (VarR p v)) = (_ ** (MultR (ConstR _ _ c1) (VarR p v), set_eq_undec_refl _))
develop (MultR (ConstR _ _ c1) (PlusR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l = (MultR (ConstR _ _ c1) e_ih_e21) in
  let e_ih_r = (MultR (ConstR _ _ c1) e_ih_e22) in
    (_ ** (PlusR e_ih_l e_ih_r, ?Mdevelop_4))
develop (MultR (ConstR _ _ c1) (MinusR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l = (MultR (ConstR _ _ c1) e_ih_e21) in
  let e_ih_r = (MultR (ConstR _ _ c1) e_ih_e22) in
    (_ ** (MinusR e_ih_l e_ih_r, ?Mdevelop_5))    
develop (MultR (ConstR _ _ c1) (NegR e)) = 
  let (r_ih ** (e_ih, p_ih)) = (develop e) in
    (_ ** (MultR (ConstR _ _ c1) (NegR e_ih), ?Mdevelop_6))
develop (MultR (ConstR _ _ c1) (MultR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih = (MultR e_ih_e21 e_ih_e22) in
    (_ ** ({- develop -} (MultR (ConstR _ _ c1) e_ih), ?Mdevelop_7))

develop (MultR (VarR p v1) (ConstR _ _ c2)) = (_ ** (MultR (VarR p v1) (ConstR _ _ c2), set_eq_undec_refl _))
develop (MultR (VarR p v1) (VarR p v2)) = (_ ** (MultR (VarR p v1) (VarR p v2), set_eq_undec_refl _))
develop (MultR (VarR p v1) (PlusR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l = (MultR (VarR p v1) e_ih_e21) in
  let e_ih_r = (MultR (VarR p v1) e_ih_e22) in
    (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop_8))
develop (MultR (VarR p v1) (MinusR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l = (MultR (VarR p v1) e_ih_e21) in
  let e_ih_r = (MultR (VarR p v1) e_ih_e22) in
    (_ ** ((MinusR e_ih_l e_ih_r), ?Mdevelop_9))    
develop (MultR (VarR p v1) (NegR e)) = 
  let (r_ih ** (e_ih, p_ih)) = (develop e) in
    (_ ** (MultR (VarR p v1) (NegR e_ih), ?Mdevelop_10))    
develop (MultR (VarR p v1) (MultR e21 e22)) = 
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih = (MultR e_ih_e21 e_ih_e22) in
  let e_ih' = (MultR (VarR p v1) e_ih) in
    (_ ** (e_ih', ?Mdevelop_11))
                              
develop (MultR (PlusR {p} e11 e12) (ConstR _ _ c2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih_l = (MultR e_ih_e11 (ConstR _ _ c2)) in
  let e_ih_r = (MultR e_ih_e12 (ConstR _ _ c2)) in
    (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop_12))                         
develop (MultR (PlusR {p} e11 e12) (VarR p v2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih_l = (MultR e_ih_e11 (VarR p v2)) in
  let e_ih_r = (MultR e_ih_e12 (VarR p v2)) in
    (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop_13))
develop (MultR (PlusR e11 e12) (PlusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
    -- Note : we could also decide to do immediately more developpment : (x+y) * (z+u) -> xz + xu + yz + yu
    -- But since we need to compute the fixpoint of this treatment anyway, we decide to do "just a bit" of simplification
  let e_ih_a = (MultR e_ih_e11 (PlusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (PlusR e_ih_e21 e_ih_e22)) in
    (_ ** (PlusR e_ih_a e_ih_b, ?Mdevelop_14))
develop (MultR (PlusR e11 e12) (MinusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e11 (PlusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (PlusR e_ih_e21 e_ih_e22)) in
    (_ ** (MinusR e_ih_a e_ih_b, ?Mdevelop_15))    
develop (MultR (PlusR e11 e12) (NegR e2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
    (_ ** (PlusR (MultR e_ih_e11 (NegR e_ih_e2)) (MultR e_ih_e12 (NegR e_ih_e2)), ?Mdevelop_16))
develop (MultR (PlusR e11 e12) (MultR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e21 e_ih_e22) in
  let e_ih_b = (MultR e_ih_e11 e_ih_a) in
  let e_ih_c = (MultR e_ih_e12 e_ih_a) in
    (_ ** (PlusR e_ih_b e_ih_c, ?Mdevelop_17)) 

develop (MultR (MinusR {p} e11 e12) (ConstR _ _ c2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih_l = (MultR e_ih_e11 (ConstR _ _ c2)) in
  let e_ih_r = (MultR e_ih_e12 (ConstR _ _ c2)) in
    (_ ** ((MinusR e_ih_l e_ih_r), ?Mdevelop_12))                         
develop (MultR (MinusR {p} e11 e12) (VarR p v2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih_l = (MultR e_ih_e11 (VarR p v2)) in
  let e_ih_r = (MultR e_ih_e12 (VarR p v2)) in
    (_ ** ((MinusR e_ih_l e_ih_r), ?Mdevelop_13))
develop (MultR (MinusR e11 e12) (PlusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
    -- Note : we could also decide to do immediately more developpment : (x+y) * (z+u) -> xz + xu + yz + yu
    -- But since we need to compute the fixpoint of this treatment anyway, we decide to do "just a bit" of simplification
  let e_ih_a = (MultR e_ih_e11 (PlusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (PlusR e_ih_e21 e_ih_e22)) in
    (_ ** (MinusR e_ih_a e_ih_b, ?Mdevelop_14))
develop (MultR (MinusR e11 e12) (MinusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e11 (MinusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (MinusR e_ih_e21 e_ih_e22)) in
    (_ ** (MinusR e_ih_a e_ih_b, ?Mdevelop_15))    
develop (MultR (MinusR e11 e12) (NegR e2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
    (_ ** (MinusR (MultR e_ih_e11 e_ih_e2) (MultR e_ih_e12 e_ih_e2), ?Mdevelop_16))
develop (MultR (MinusR e11 e12) (MultR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e21 e_ih_e22) in
  let e_ih_b = (MultR e_ih_e11 e_ih_a) in
  let e_ih_c = (MultR e_ih_e12 e_ih_a) in
    (_ ** (MinusR e_ih_b e_ih_c, ?Mdevelop_17))
    
develop (MultR (NegR e1) (ConstR _ _ c2)) = 
  let (r_ih ** (e_ih, p_ih)) = develop e1 in
      (_ ** (MultR e_ih (ConstR _ _ c2), ?Mdevelop_18))
develop (MultR (NegR e1) (VarR p v)) = 
  let (r_ih ** (e_ih, p_ih)) = develop e1 in
      (_ ** (MultR e_ih (VarR p v), ?Mdevelop_19))
develop (MultR (NegR e1) (PlusR e21 e22)) =
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (PlusR (MultR (NegR e_ih_e1) e_ih_e21) (MultR (NegR e_ih_e1) e_ih_e22), ?Mdevelop_20))
develop (MultR (NegR e1) (MinusR e21 e22)) =   
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (PlusR (MinusR (NegR e_ih_e1) e_ih_e21) (MultR (NegR e_ih_e1) e_ih_e22), ?Mdevelop_21))
-- Not 100% sure here
develop (MultR (NegR e1) (NegR e2)) = 
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
      (_ ** (MultR (NegR e_ih_e1) (NegR e_ih_e2), ?Mdevelop_22))
-- PROBLEM HERE : ADDING THIS CASE HAS CREATED 41 CASES, AND IDRIS RUNS INTO AN INFINITE LOOP AT TYPECHECK...
develop (MultR (NegR e1) (MultR e21 e22)) =
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (MultR (NegR e_ih_e1) (MultR e_ih_e21 e_ih_e22), ?Mdevelop_23))
 
develop (MultR (MultR {p} e11 e12) (ConstR _ _ c2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih = (MultR e_ih_e11 e_ih_e12) in
    (_ ** ({- develop -} (MultR e_ih (ConstR _ _ c2)), ?Mdevelop_24))
develop (MultR (MultR {p} e11 e12) (VarR p v2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih = (MultR e_ih_e11 e_ih_e12) in
    (_ ** ({- develop -} (MultR e_ih (VarR p v2)), ?Mdevelop_25))                 
develop (MultR (MultR e11 e12) (PlusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_l1 e_ih_e21) in
  let e_ih_r2 = (MultR e_ih_l1 e_ih_e22) in
    (_ ** (PlusR e_ih_l2 e_ih_r2, ?Mdevelop_26))
develop (MultR (MultR e11 e12) (MinusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_l1 e_ih_e21) in
  let e_ih_r2 = (MultR e_ih_l1 e_ih_e22) in
    (_ ** (MinusR e_ih_l2 e_ih_r2, ?Mdevelop_27))    
develop (MultR (MultR e11 e12) (NegR e2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
    (_ ** (MultR (MultR e_ih_e11 e_ih_e12) e_ih_e2, ?Mdevelop_28))  
develop (MultR (MultR e11 e12) (MultR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_e21 e_ih_e22) in
  let e_ih_l3 = (MultR e_ih_l1 e_ih_l2) in
    (_ ** (e_ih_l3, ?Mdevelop_29))
    
--%logging 0
    

-- Compute the fixpoint of the function just above
develop_fix : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
develop_fix p e = 
  let (r_1 ** (e_1, p_1)) = develop e in
    case exprR_eq p _ e e_1 of -- Look for syntactical equality (ie, if we have done some simplification in the last passe)!
      Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
      Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = develop_fix p e_1 in -- We do another passe
						  (r_ih1 ** (e_ih1, ?Mdevelop_fix_1))	 
	 

 
-- same as elimMinus, but typed for an element of a Ring instead of a Group	 
total
elimMinus' : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
elimMinus' p (ConstR _ _ const) = (_ ** (ConstR _ _ const, set_eq_undec_refl _))
elimMinus' p (PlusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?Melim'Minus1))
elimMinus' p (VarR _ v) = (_ ** (VarR _ v, set_eq_undec_refl _))    
elimMinus' p (MinusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Plus r_ih1 (Neg r_ih2)) ** (PlusR e_ih1 (NegR e_ih2), ?MelimMinus'2)) 
elimMinus' p (NegR e1) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
    (_ ** (NegR e_ih1, ?MelimMinus'3))
elimMinus' p (MultR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?Melim'Minus1))



-- Not tagged as total since we have no case for Minus (but they have been all removed at the previous step)
multAfter : (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> {c2:c} -> (ExprR p g c1) -> (ExprR p g c2) -> (c3 ** (ExprR p g c3, c3~=Mult c1 c2))
multAfter p g (ConstR _ _ const1) e = (_ ** (MultR (ConstR _ _ const1) e, set_eq_undec_refl _))
multAfter p g (VarR _ v) e = (_ ** (MultR (VarR _ v) e, set_eq_undec_refl _))
multAfter p g (PlusR e11 e12) e2 = (_ ** (MultR (PlusR e11 e12) e2, set_eq_undec_refl _))
multAfter p g (NegR e1) e2 = (_ ** (MultR (NegR e1) e2, set_eq_undec_refl _))
multAfter p g (MultR e11 e12) e2 = 
    let (r_ih1 ** (e_ih1, p_ih1)) = multAfter p g e12 e2
    in (_ ** (MultR e11 e_ih1, ?MmultAfter1))



shuffleProductRight : (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
shuffleProductRight p g (ConstR _ _ const1) = (_ ** (ConstR _ _ const1, set_eq_undec_refl _))
shuffleProductRight p g (VarR _ v) = (_ ** (VarR _ v, set_eq_undec_refl _))
shuffleProductRight p g (NegR e) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e) in
    (_ ** (e_ih1, ?MshuffleProductRight1))
shuffleProductRight p g (PlusR e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g e1 in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g e2 in
    (_ ** (PlusR e_ih1 e_ih2, ?MshuffleProductRight2))

shuffleProductRight p g (MultR (ConstR _ _ const1) (ConstR _ _ const2)) = (_ ** (MultR (ConstR _ _ const1) (ConstR _ _ const2), set_eq_undec_refl _))
shuffleProductRight p g (MultR (ConstR _ _ const1) (VarR _ v)) = (_ ** (MultR (ConstR _ _ const1) (VarR _ v), set_eq_undec_refl _))
shuffleProductRight p g (MultR (ConstR _ _ const1) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e21 e22) in -- Will do it for e21 and e22 separately during the recursive call
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight3))
shuffleProductRight p g (MultR (ConstR _ _ const1) (NegR e)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e) in
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight4))
shuffleProductRight p g (MultR (ConstR _ _ const1) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e21 e22) in
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight5))


shuffleProductRight p g (MultR (VarR _ v1) (ConstR _ _ const2)) = (_ ** (MultR (VarR _ v1) (ConstR _ _ const2), set_eq_undec_refl _))
shuffleProductRight p g (MultR (VarR _ v1) (VarR _ v2)) = (_ ** (MultR (VarR _ v1) (VarR _ v2), set_eq_undec_refl _))
shuffleProductRight p g (MultR (VarR _ v1) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e21 e22) in -- Will do it for e21 and e22 separately during the recursive call
    (_ ** (MultR (VarR _ v1) e_ih1, ?MshuffleProductRight6))
shuffleProductRight p g (MultR (VarR _ v1) (NegR e)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e) in
    (_ ** (MultR (VarR _ v1) e_ih1, ?MshuffleProductRight7))
shuffleProductRight p g (MultR (VarR _ v1) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e21 e22) in
    (_ ** (MultR (VarR _ v1) e_ih1, ?MshuffleProductRight8))
    
shuffleProductRight p g (MultR (PlusR e11 e12) (ConstR _ _ const2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e11 e12) in
    (_ ** (MultR e_ih1 (ConstR _ _ const2), ?MshuffleProductRight9))
shuffleProductRight p g (MultR (PlusR e11 e12) (VarR _ v2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e11 e12) in
    (_ ** (MultR e_ih1 (VarR _ v2), ?MshuffleProductRight10))
shuffleProductRight p g (MultR (PlusR e11 e12) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (PlusR e21 e22) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight11))
shuffleProductRight p g (MultR (PlusR e11 e12) (NegR e2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (NegR e2) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight12))    
shuffleProductRight p g (MultR (PlusR e11 e12) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (MultR e21 e22) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight13))
    
shuffleProductRight p g (MultR (NegR e1) (ConstR _ _ const2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e1) in
    (_ ** (MultR e_ih1 (ConstR _ _ const2), ?MshuffleProductRight14))
shuffleProductRight p g (MultR (NegR e1) (VarR _ v2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e1) in
    (_ ** (MultR e_ih1 (VarR _ v2), ?MshuffleProductRight15))
shuffleProductRight p g (MultR (NegR e1) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (PlusR e21 e22) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight16))
shuffleProductRight p g (MultR (NegR e1) (NegR e2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (NegR e2) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight17))    
shuffleProductRight p g (MultR (NegR e1) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e1) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (MultR e21 e22) in
    (_ ** (MultR e_ih1 e_ih2, ?MshuffleProductRight18))
      
shuffleProductRight p g (MultR (MultR e11 e12) (ConstR _ _ const2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e11 e12) in
    let (r_2 ** (e_2, p_2)) = multAfter p g e_ih1 (ConstR _ _ const2) in
    (_ ** (e_2, ?MshuffleProductRight19))
shuffleProductRight p g (MultR (MultR e11 e12) (VarR _ v2)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e11 e12) in
    let (r_2 ** (e_2, p_2)) = multAfter p g e_ih1 (VarR _ v2) in
    (_ ** (e_2, ?MshuffleProductRight20))
shuffleProductRight p g (MultR (MultR e11 e12) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (PlusR e21 e22) in
    let (r_3 ** (e_3, p_3)) = multAfter p g e_ih1 e_ih2 in
    (_ ** (e_3, ?MshuffleProductRight21))
shuffleProductRight p g (MultR (MultR e11 e12) (NegR e2)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (NegR e2) in
    let (r_3 ** (e_3, p_3)) = multAfter p g e_ih1 e_ih2 in
    (_ ** (e_3, ?MshuffleProductRight22))    
shuffleProductRight p g (MultR (MultR e11 e12) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e11 e12) in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g (MultR e21 e22) in
    let (r_3 ** (e_3, p_3)) = multAfter p g e_ih1 e_ih2 in
    (_ ** (e_3, ?MshuffleProductRight23))


-- Ex : -(a+b) becomes (-b) + (-a), -(a*b) becomes (-a) * b
-- Not total for Idris, because recursive call with argument (NegG ei) instead of ei. Something can be done for this case with a natural number representing the size
propagateNeg' : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
propagateNeg' p (NegR (PlusR e1 e2)) =
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p (NegR e1)) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p (NegR e2)) in
		((Plus r_ih2 r_ih1) ** (PlusR e_ih2 e_ih1, ?MpropagateNeg'_1)) -- Carefull : - (a + b) = (-b) + (-a) in a group and *not* (-a) + (-b) in general. See mathsResults.bad_push_negation_IMPLIES_commutativeGroup for more explanations about this
propagateNeg' p (NegR (MultR e1 e2)) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p (NegR e1)) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?MpropagateNeg'_2))
propagateNeg' p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg' p e in
		((Neg r_ih1) ** (NegR e_ih1, ?MpropagateNeg'_3))
propagateNeg' p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?MpropagateNeg_4))
propagateNeg' p (MultR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?MpropagateNeg_4))		
propagateNeg' p e =
  (_ ** (e, set_eq_undec_refl _))     
    

    
-- Needed because calling propagateNeg on -(-(a+b)) gives - [-b + -a] : we may need other passes
propagateNeg_fix' : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
propagateNeg_fix' p e = 
	let (r_1 ** (e_1, p_1)) = propagateNeg' p e in
		case exprR_eq p _ e e_1 of -- Look for syntactical equality (ie, if we have done some simplification in the last passe)!
			Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg_fix' p e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?MpropagateNeg_fix'_1))    
    

total
elimDoubleNeg' : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
elimDoubleNeg' p (NegR (NegR e1)) =
	let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg' p e1 in
    (_ ** (e_ih1, ?MelimDoubleNeg'_1))
elimDoubleNeg' p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = elimDoubleNeg' p e in
    ((Neg r_ih1) ** (NegR e_ih1, ?MelimDoubleNeg'_2))
elimDoubleNeg' p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimDoubleNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimDoubleNeg' p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?MelimDoubleNeg'_3))  
elimDoubleNeg' p (MultR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (elimDoubleNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (elimDoubleNeg' p e2) in
    ((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?MelimDoubleNeg'_4))  
elimDoubleNeg' p e1 = 
    (_ ** (e1, set_eq_undec_refl _))    
    


-- Is forced to take a MultR in input    
removeMultipleNegInMonomial : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
--removeMultipleNegInMonomial p (MultR

    
removeMultipleNegInPolynomial : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
removeMultipleNegInPolynomial p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (removeMultipleNegInPolynomial p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (removeMultipleNegInPolynomial p e2) in
		(_ ** (PlusR e_ih1 e_ih2, ?MLLL))
removeMultipleNegInPolynomial p (ConstR	_ _ const1) = 
	(_ ** (ConstR _ _ const1, ?MMMM))
removeMultipleNegInPolynomial p (VarR _ v) = 
	(_ ** (VarR _ v, ?MNNN))
removeMultipleNegInPolynomial p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (removeMultipleNegInPolynomial p e) in
		(_ ** (NegR e_ih1, ?MOOO))
removeMultipleNegInPolynomial p (MultR e1 e2) = 
	let (rprod ** (eprod, pprod)) = removeMultipleNegInMonomial p (MultR e1 e2) in
		(_ ** (eprod, pprod))
    
encodeMonomial : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (Monomial (MkSetWithMult (ring_to_set p) Mult Mult_preserves_equiv) g c2, c1~=c2))
encodeMonomial = ?HHHH



-- Returns a product of monomial that can be composed of either only one monomial (if they were concatenable together), or a product of two monomials
multiplyMonomialAndProductOfMonomials : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> {c2:c} -> (Monomial (MkSetWithMult (ring_to_set p) Mult Mult_preserves_equiv) g c1) -> (ProductOfMonomials _ g c2) -- If I give the _ parameter to the ProductOfMonomial, I've got a senseless error message...
	-> (c3 ** (ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult Mult_preserves_equiv) g c3, Mult c1 c2 ~=c3))
multiplyMonomialAndProductOfMonomials = ?KKKKK





-- The "e" here can't be a Plus, a Neg or a Minus
encodeProductOfMonomials : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult Mult_preserves_equiv) g c2, c1~=c2))
-- At this stage, the only thing we should receive is a real variable, but let's write it on a complete fashions
-- This case gives only one monomial (base case)
encodeProductOfMonomials c p g (VarR _ v) = 
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (VarR _ v) in
        (_ ** (LastMonomial _ mon1, ?MO))
-- This case gives only one monomial (base case)
encodeProductOfMonomials c p g (ConstR _ _ const) = 
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (ConstR _ _ const) in
        (_ ** (LastMonomial _ mon1, ?MO))

-- For a mult, we now that the left part is forced to be an atom (variable or constant), since we've put eveything in right-associative form before calling the encoding function
-- This case gives only one monomial (base case)
encodeProductOfMonomials c p g (MultR (ConstR _ _ const1) (ConstR _ _ const2)) = 
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (ConstR _ _ (Mult const1 const2)) in
        (_ ** (LastMonomial _ mon1, ?MO))
-- This case gives only one monomial (base case)
encodeProductOfMonomials c p g (MultR (ConstR _ _ const1) (VarR _ v)) =
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (MultR (ConstR _ _ const1) (VarR _ v)) in
        (_ ** (LastMonomial _ mon1, ?MO))
-- Case with n>=2monomials
-- Case with the second argument of the Mult being a Neg is not possible since we are supposed to have move the Neg to the front.
encodeProductOfMonomials c p g (MultR (ConstR _ _ const1) e2) = 
	let (r_1 ** (monomial, p_1)) = encodeMonomial c p g (ConstR _ _ const1) in
	let (r_ih2 ** (productOfMonomials, p_ih2)) = encodeProductOfMonomials c p g e2 in
	let (r_3 ** (e_3, p_3)) = multiplyMonomialAndProductOfMonomials c p g monomial productOfMonomials in
		(_ ** (e_3, ?MJ))
        
        
-- This case gives a product of 2 monomials
encodeProductOfMonomials c p g (MultR (VarR _ v) (ConstR _ _ const2)) = 
	-- The variable v is going to be part of a first monomial, and the const2 of another one
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (VarR _ v) in
    let (r_2 ** (mon2, p_2)) = encodeMonomial c p g (ConstR _ _ const2) in
	-- Wrapp the second monomial into a product of monomial
	let prod = LastMonomial _ mon2 in
		(_ ** (MonomialMultProduct _ mon1 prod, ?MP))
-- This case gives only one monomial (base case)
encodeProductOfMonomials c p g (MultR (VarR _ v1) (VarR _ v2)) = 
    let (r_1 ** (mon1, p_1)) = encodeMonomial c p g (MultR (VarR _ v1) (VarR _ v2)) in
        (_ ** (LastMonomial _ mon1, ?MN))
        


encode : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (ExprCG {n=n} (ring_to_commutativeGroup_class p) (MkSetWithMult (ring_to_set p) Mult Mult_preserves_equiv) g c2, c1~=c2))
-- Sum of product of monomials
encode c p g (PlusR e1 e2) = 
    let (r_1 ** (e_1, p_1)) = encode c p g e1 in
    let (r_2 ** (e_2, p_2)) = encode c p g e2 in
        (_ ** (PlusCG _ e_1 e_2, ?MA))
-- Neg of product of monomials
encode c p g (NegR e) = 
    let (r ** (e, p)) = encode c p g e in
        (_ ** (NegCG _ e, ?MB))
-- In the case of a mult, a constant or a var, we know that we have a "product of monomials"
encode c p g e =
    let (r_1 ** (pdtOfMon, p_1)) = encodeProductOfMonomials c p g e in
        (_ ** (VarCG _ _ (EncodingProductOfMonomials _ Neg _ pdtOfMon), ?MFFF))

	

ring_reduce : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
ring_reduce p e = 
  let (r_1 ** (e_1, p_1)) = elimMinus' p e in
  let (r_2 ** (e_2, p_2)) = propagateNeg_fix' p e_1 in
  let (r_3 ** (e_3, p_3)) = elimDoubleNeg' p e_2 in
  let (r_4 ** (e_4, p_4)) = develop_fix p e_3 in
  let (r_5 ** (e_5, p_5)) = shuffleProductRight p _ e_4 in
  -- Here we need to treat every product of monomial that that they contain at most ONE Neg
  -- Then encoding
    (_ **(e_5, ?MX))

	

---------- Proofs ----------


