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
    (_ ** (MultR (ConstR _ _ c1) e_ih, ?Mdevelop_6))
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
    (_ ** (MultR (VarR p v1) e_ih, ?Mdevelop_10))    
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
    (_ ** (PlusR (MultR e_ih_e11 e_ih_e2) (MultR e_ih_e12 e_ih_e2), ?Mdevelop_16))
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




	
{-
ring_reduce : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
ring_reduce p e = 
  let (r_1 ** (e_1, p_1)) = removeMinus e in
  let (r_2 ** (e_2, p_2)) = develop_fix e_1 in
  let (r_3 ** (
-}	
	
	
	
	
	

