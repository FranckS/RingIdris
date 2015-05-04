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
develop {c} (ConstR _ _ const) = (_ ** (ConstR _ _ const, set_eq_undec_refl {c} _))
develop {c} (VarR p v) = (_ ** (VarR p v, set_eq_undec_refl {c} _))
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

      
develop {c} (MultR (ConstR _ _ c1) (ConstR _ _ c2)) = (_ ** (MultR (ConstR _ _ c1) (ConstR _ _ c2), set_eq_undec_refl {c} _))     
develop {c} (MultR (ConstR _ _ c1) (VarR p v)) = (_ ** (MultR (ConstR _ _ c1) (VarR p v), set_eq_undec_refl {c} _))
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

develop {c} (MultR (VarR p v1) (ConstR _ _ c2)) = (_ ** (MultR (VarR p v1) (ConstR _ _ c2), set_eq_undec_refl {c} _))
develop {c} (MultR (VarR p v1) (VarR p v2)) = (_ ** (MultR (VarR p v1) (VarR p v2), set_eq_undec_refl {c} _))
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
elimMinus' {c} p (ConstR _ _ const) = (_ ** (ConstR _ _ const, set_eq_undec_refl {c} _))
elimMinus' p (PlusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?Melim'Minus1))
elimMinus' {c} p (VarR _ v) = (_ ** (VarR _ v, set_eq_undec_refl {c} _))    
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
multAfter : {c:Type} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> {c2:c} -> (ExprR p g c1) -> (ExprR p g c2) -> (c3 ** (ExprR p g c3, c3~=Mult c1 c2))
multAfter {c} p g (ConstR _ _ const1) e = (_ ** (MultR (ConstR _ _ const1) e, set_eq_undec_refl {c} _))
multAfter {c} p g (VarR _ v) e = (_ ** (MultR (VarR _ v) e, set_eq_undec_refl {c} _))
multAfter {c} p g (PlusR e11 e12) e2 = (_ ** (MultR (PlusR e11 e12) e2, set_eq_undec_refl {c} _))
multAfter {c} p g (NegR e1) e2 = (_ ** (MultR (NegR e1) e2, set_eq_undec_refl {c} _))
multAfter p g (MultR e11 e12) e2 = 
    let (r_ih1 ** (e_ih1, p_ih1)) = multAfter p g e12 e2
    in (_ ** (MultR e11 e_ih1, ?MmultAfter1))



shuffleProductRight : {c:Type} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
shuffleProductRight {c} p g (ConstR _ _ const1) = (_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
shuffleProductRight {c} p g (VarR _ v) = (_ ** (VarR _ v, set_eq_undec_refl {c} _))
shuffleProductRight p g (NegR e) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e) in
    (_ ** (e_ih1, ?MshuffleProductRight1))
shuffleProductRight p g (PlusR e1 e2) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g e1 in
    let (r_ih2 ** (e_ih2, p_ih2)) = shuffleProductRight p g e2 in
    (_ ** (PlusR e_ih1 e_ih2, ?MshuffleProductRight2))

shuffleProductRight {c} p g (MultR (ConstR _ _ const1) (ConstR _ _ const2)) = (_ ** (MultR (ConstR _ _ const1) (ConstR _ _ const2), set_eq_undec_refl {c} _))
shuffleProductRight {c} p g (MultR (ConstR _ _ const1) (VarR _ v)) = (_ ** (MultR (ConstR _ _ const1) (VarR _ v), set_eq_undec_refl {c} _))
shuffleProductRight p g (MultR (ConstR _ _ const1) (PlusR e21 e22)) =
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (PlusR e21 e22) in -- Will do it for e21 and e22 separately during the recursive call
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight3))
shuffleProductRight p g (MultR (ConstR _ _ const1) (NegR e)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (NegR e) in
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight4))
shuffleProductRight p g (MultR (ConstR _ _ const1) (MultR e21 e22)) = 
    let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g (MultR e21 e22) in
    (_ ** (MultR (ConstR _ _ const1) e_ih1, ?MshuffleProductRight5))


shuffleProductRight {c} p g (MultR (VarR _ v1) (ConstR _ _ const2)) = (_ ** (MultR (VarR _ v1) (ConstR _ _ const2), set_eq_undec_refl {c} _))
shuffleProductRight {c} p g (MultR (VarR _ v1) (VarR _ v2)) = (_ ** (MultR (VarR _ v1) (VarR _ v2), set_eq_undec_refl {c} _))
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
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p (NegR e1)) in -- We do not forget to propate the Neg inside of the product (we chose the first argument)
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
propagateNeg' {c} p e =
  (_ ** (e, set_eq_undec_refl {c} _))     
    

    
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
elimDoubleNeg' {c} p e1 = 
    (_ ** (e1, set_eq_undec_refl {c} _))    
    

    
    
    
-- For a product A * B, we decide to move the neg before the prodct if there is one
-- Ex : (-c * v) -> -(c*v)
-- Ex : (v1 * -v2) -> -(v1*c2)
-- Is forced to take a MultR in input    
moveNegInMonomial : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegInMonomial p (MultR (NegR a) (ConstR _ _ const1)) =
	(_ ** (NegR (MultR a (ConstR _ _ const1)), ?MmoveNegInMonomial_1))
moveNegInMonomial p (MultR (NegR a) (VarR _ v)) = 
	(_ ** (NegR (MultR a (VarR _ v)), ?MmoveNegInMonomial_2))
moveNegInMonomial p (MultR (NegR a) (NegR b)) = -- I think that b here can only be a constant or variable
	(_ ** (MultR a b, ?MmoveNegInMonomial_3))
moveNegInMonomial p (MultR (NegR a) b) = -- Here, b is a MultR (reminder : we've put everything in the form right-associative)
	let (r_ih1 ** (e_ih1, p_ih1)) = moveNegInMonomial p b in -- We do it for b first, and perhaps we will end up with a Neg on the left
	let (r_ih2 ** (e_ih2, p_ih2)) = moveNegInMonomial p (MultR (NegR a) e_ih1) in -- We do the analyze again, but with the new b
		(_ ** (e_ih2, ?MmoveNegInMonomial_4))

moveNegInMonomial {c} p (MultR a (ConstR _ _ const1)) =
	(_ ** (MultR a (ConstR _ _ const1), set_eq_undec_refl {c} _))
moveNegInMonomial {c} p (MultR a (VarR _ v)) = 
	(_ ** (MultR a (VarR _ v), set_eq_undec_refl {c} _))
moveNegInMonomial p (MultR a (NegR b)) = -- I think that b here can only be a constant or variable
	(_ ** (NegR (MultR a b), ?MmoveNegInMonomial_5))
moveNegInMonomial p (MultR a b) = -- Here, b is a MultR (reminder : we've put everything in the form right-associative)
	let (r_ih1 ** (e_ih1, p_ih1)) = moveNegInMonomial p b in -- We do it for b first, and perhaps we will end up with a Neg on the left
	let (r_ih2 ** (e_ih2, p_ih2)) = moveNegInMonomial p (MultR a e_ih1) in -- We do the analyze again, but with the new b
		(_ ** (e_ih2, ?MmoveNegInMonomial_6))

    
moveNegInPolynomial : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegInPolynomial p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegInPolynomial p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (moveNegInPolynomial p e2) in
		(_ ** (PlusR e_ih1 e_ih2, ?MmoveNegInPolynomial_1))
moveNegInPolynomial {c} p (ConstR _ _ const1) = 
	(_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
moveNegInPolynomial {c} p (VarR _ v) = 
	(_ ** (VarR _ v, set_eq_undec_refl {c} _))
moveNegInPolynomial p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegInPolynomial p e) in
		(_ ** (NegR e_ih1, ?MmoveNegInPolynomial_2))
moveNegInPolynomial p (MultR e1 e2) = 
	moveNegInMonomial p (MultR e1 e2)

    
encodeToMonomial : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (Monomial (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2, c1~=c2))
-- The only thing we can get are : 
-- a Var, a Constant, a Mult between a const and a var and a Mult between a var and a var
-- (Mult between const and const is impossible because we could have deal with that directly, and Mult between var and const would not make a monomial so we would have already deal with it as well) 
encodeToMonomial c p g (ConstR _ _ const1) = (_ ** (ConstantMonomial _ _ const1, set_eq_undec_refl {c} _))
encodeToMonomial c p g (VarR _ (RealVariable _ _ _ _ i)) = (_ ** (ProdOfVar _ (LastVar _ _ i), set_eq_undec_refl {c} _))
encodeToMonomial c p g (MultR (ConstR _ _ const1) (VarR _ (RealVariable _ _ _ _ i))) = (_ ** (ProdOfVarWithConst _ const1 (LastVar _ _ i), set_eq_undec_refl {c} _))
encodeToMonomial c p g (MultR (VarR _ (RealVariable _ _ _ _ i)) (VarR _ (RealVariable _ _ _ _ j))) = (_ ** (ProdOfVar _ (VarMultProduct _ i (LastVar _ _ j)), set_eq_undec_refl {c} _))



--%logging 3 
multiplyProdOfVar : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> {c2:c} 
								-> (ProductOfVariables {c=c} {n=n} {c_set=ring_to_set p} (MkSetWithMult {c=c} (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -- I don't understand why I get an error message if I give Mult_preserves_equiv here... I suspect a problem in Idris
								-> (ProductOfVariables {c=c} {n=n} {c_set=ring_to_set p} (MkSetWithMult {c=c} (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2) -- Since the problem arises when the 2 SetWithMult are the same. So be carefull, this function now expects a fake unused argument
								-> (c3 ** ((ProductOfVariables {c=c} {n=n} {c_set=ring_to_set p} (MkSetWithMult {c=c} (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c3), Mult c1 c2 ~= c3))
                                
multiplyProdOfVar {c} p (LastVar _ _ k1) (LastVar _ _ k2) = (_ ** (VarMultProduct _ k1 (LastVar _ _ k2), set_eq_undec_refl {c} _))                
multiplyProdOfVar {c} p (LastVar _ _ k1) (VarMultProduct _ k2 pdv) = (_ ** (VarMultProduct _ k1 (VarMultProduct _ k2 pdv), set_eq_undec_refl {c} _))
multiplyProdOfVar p (VarMultProduct _ k1 pdv) (LastVar _ _ k2) = 
	let (r_ih1 ** (newpdv, p_ih1)) = multiplyProdOfVar p pdv (LastVar _ _ k2) in
		(_ ** (VarMultProduct _ k1 newpdv, ?MmultiplyProdOfVar_1))
multiplyProdOfVar p (VarMultProduct _ k1 pdv1) (VarMultProduct _ k2 pdv2) = 
	let (r_ih1 ** (newpdv, p_ih1)) = multiplyProdOfVar p pdv1 (VarMultProduct _ k2 pdv2) in
		(_ ** (VarMultProduct _ k1 newpdv, ?MmultiplyProdOfVar_2))

--%logging 0                

-- Returns a product of monomial that can be composed of either only one monomial (if they were concatenable together), or a product of two monomials
multiplyMonomialAndProductOfMonomials : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> {c2:c} -> (Monomial (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -> (ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2) -- If I give the _ parameter to the ProductOfMonomial, I've got a senseless error message...
	-> (c3 ** (ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c3, Mult c1 c2 ~= c3))
-- This case will give only one monomial
multiplyMonomialAndProductOfMonomials p (ProdOfVar _ prodVar1) (LastMonomial _ (ProdOfVar _ prodVar2)) = 
	let (r_1 ** (prodVar1Var2, p_1)) = multiplyProdOfVar p prodVar1 prodVar2 in
        (_ ** (LastMonomial _ (ProdOfVar _ prodVar1Var2), p_1))
-- This case gives two monomials
multiplyMonomialAndProductOfMonomials p (ProdOfVar _ prodVar1) (LastMonomial _ (ProdOfVarWithConst _ const prodVar2)) = 
    (_ ** (MonomialMultProduct _ (ProdOfVar _ prodVar1) (LastMonomial _ (ProdOfVarWithConst _ const prodVar2)), ?MmultiplyMonomialAndProductOfMonomials_2)) -- FIX ME : Why does Idris refuses (set_eq_undec_refl _) for the proof (I have to do the same in proof mode...)
-- To see
multiplyMonomialAndProductOfMonomials p (ProdOfVar _ prodVar1) (MonomialMultProduct _ (ProdOfVar _ prodVar2) prodOfMon) = 
    let (r1 ** (mon1, p1)) = multiplyProdOfVar p prodVar1 prodVar2 in  
        (_ ** (MonomialMultProduct _ (ProdOfVar _ mon1) prodOfMon, ?MmultiplyMonomialAndProductOfMonomials_3))
multiplyMonomialAndProductOfMonomials p (ProdOfVar _ prodVar1) (MonomialMultProduct _ (ProdOfVarWithConst _ const2 prodVar2) prodOfMon) = 
    (_ **(MonomialMultProduct _ (ProdOfVar _ prodVar1) (MonomialMultProduct _ (ProdOfVarWithConst _ const2 prodVar2) prodOfMon), ?MmultiplyMonomialAndProductOfMonomials_4))
multiplyMonomialAndProductOfMonomials p (ProdOfVar _ prodVar1) (MonomialMultProduct _ (ConstantMonomial _ _ const2) prodOfMon) = 
	(_ ** (MonomialMultProduct _ (ProdOfVar _ prodVar1) (MonomialMultProduct _ (ConstantMonomial _ _ const2) prodOfMon), ?MmultiplyMonomialAndProductOfMonomials_5))
    
multiplyMonomialAndProductOfMonomials p (ProdOfVarWithConst _ const1 prodVar1) (LastMonomial _ (ProdOfVar _ prodVar2)) = 
	let (r_1 ** (prodVar1Var2, p_1)) = multiplyProdOfVar p prodVar1 prodVar2 in
		(_ ** (LastMonomial _ (ProdOfVarWithConst _ const1 prodVar1Var2), ?MmultiplyMonomialAndProductOfMonomials_6))
multiplyMonomialAndProductOfMonomials p (ProdOfVarWithConst _ const1 prodVar1) (LastMonomial _ (ProdOfVarWithConst _ const2 prodVar2)) = 
	(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ const1 prodVar1) (LastMonomial _ (ProdOfVarWithConst _ const2 prodVar2)), ?MmultiplyMonomialAndProductOfMonomials_7))
multiplyMonomialAndProductOfMonomials p (ProdOfVarWithConst _ const1 prodVar1) (MonomialMultProduct _ (ProdOfVar _ prodVar2) prodOfMon) = 
	let (r_1 ** (prodVar1Var2, p_1)) = multiplyProdOfVar p prodVar1 prodVar2 in
		(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ const1 prodVar1Var2) prodOfMon, ?MmultiplyMonomialAndProductOfMonomials_8))
multiplyMonomialAndProductOfMonomials p (ProdOfVarWithConst _ const1 prodVar1) (MonomialMultProduct _ (ProdOfVarWithConst _ const2 prodVar2) prodOfMon) = 
	(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ const1 prodVar1) (MonomialMultProduct _ (ProdOfVarWithConst _ const2 prodVar2) prodOfMon), ?MmultiplyMonomialAndProductOfMonomials_9))
multiplyMonomialAndProductOfMonomials p (ProdOfVarWithConst _ const1 prodVar1) (MonomialMultProduct _ (ConstantMonomial _ _ const2) prodOfMon) = 
	(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ const1 prodVar1) (MonomialMultProduct _ (ConstantMonomial _ _ const2) prodOfMon), ?MmultiplyMonomialAndProductOfMonomials_10))
    
multiplyMonomialAndProductOfMonomials p (ConstantMonomial _ _ const1) (LastMonomial _ (ProdOfVar _ prodVar)) = 
	(_ ** (LastMonomial _ (ProdOfVarWithConst _ const1 prodVar), ?MmultiplyMonomialAndProductOfMonomials_11))
multiplyMonomialAndProductOfMonomials p (ConstantMonomial _ _ const1) (LastMonomial _ (ProdOfVarWithConst _ const2 prodVar)) = 
	(_ ** (LastMonomial _ (ProdOfVarWithConst _ (Mult const1 const2) prodVar), ?MmultiplyMonomialAndProductOfMonomials_12))
multiplyMonomialAndProductOfMonomials p (ConstantMonomial _ _ const1) (MonomialMultProduct _ (ProdOfVar _ prodVar) prodOfMon) =
	(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ const1 prodVar) prodOfMon, ?MmultiplyMonomialAndProductOfMonomials_13))
multiplyMonomialAndProductOfMonomials p (ConstantMonomial _ _ const1) (MonomialMultProduct _ (ProdOfVarWithConst _ const2 prodVar) prodOfMon) = 
	(_ ** (MonomialMultProduct _ (ProdOfVarWithConst _ (Mult const1 const2) prodVar) prodOfMon, ?MmultiplyMonomialAndProductOfMonomials_14))
-- For this case, the output is weird (with a product of two constant monomial), but so was the input
multiplyMonomialAndProductOfMonomials p (ConstantMonomial _ _ const1) (MonomialMultProduct _ (ConstantMonomial _ _ const2) prodOfMon) = 
	(_ ** (MonomialMultProduct _ (ConstantMonomial _ _ (Mult const1 const2)) prodOfMon, ?MmultiplyMonomialAndProductOfMonomials_15))
    
    
    
    

-- The "e" here can't be a Plus, a Neg or a Minus
encodeToProductOfMonomials : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2, c1~=c2))
-- This case gives only one monomial (base case)
encodeToProductOfMonomials c p g (VarR _ v) = 
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (VarR _ v) in
        (_ ** (LastMonomial _ mon1, p_1))
-- This case gives only one monomial (base case)
encodeToProductOfMonomials c p g (ConstR _ _ const) = 
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (ConstR _ _ const) in
        (_ ** (LastMonomial _ mon1, p_1))

-- IMPORTANT : In the case of a mult, we know that no operand can be a Neg, since we've move all the Neg before the product (thanks to MoveNegInPolynomial, which does moveNegInMonomial for all monomials)
-- For a mult, we now that the left part is forced to be an atom (variable or constant), since we've put eveything in right-associative form before calling the encoding function
-- This case gives only one monomial (base case)
encodeToProductOfMonomials c p g (MultR (ConstR _ _ const1) (ConstR _ _ const2)) = 
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (ConstR _ _ (Mult const1 const2)) in
        (_ ** (LastMonomial _ mon1, p_1))
-- This case gives only one monomial (base case)
encodeToProductOfMonomials c p g (MultR (ConstR _ _ const1) (VarR _ v)) =
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (MultR (ConstR _ _ const1) (VarR _ v)) in
        (_ ** (LastMonomial _ mon1, p_1))
-- Case with n>=2monomials
-- Case with the second argument of the Mult being a Neg is not possible since we are supposed to have move the Neg to the front.
encodeToProductOfMonomials c p g (MultR (ConstR _ _ const1) e2) = 
	let (r_1 ** (monomial, p_1)) = encodeToMonomial c p g (ConstR _ _ const1) in
	let (r_ih2 ** (productOfMonomials, p_ih2)) = encodeToProductOfMonomials c p g e2 in
	let (r_3 ** (e_3, p_3)) = multiplyMonomialAndProductOfMonomials p monomial productOfMonomials in
		(_ ** (e_3, ?MencodeToProductOfMonomials_5))
        
-- This case gives a product of 2 monomials
encodeToProductOfMonomials c p g (MultR (VarR _ v) (ConstR _ _ const2)) = 
	-- The variable v is going to be part of a first monomial, and the const2 of another one
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (VarR _ v) in
    let (r_2 ** (mon2, p_2)) = encodeToMonomial c p g (ConstR _ _ const2) in
	-- Wrapp the second monomial into a product of monomial
	let prod = LastMonomial _ mon2 in
		(_ ** (MonomialMultProduct _ mon1 prod, ?MencodeToProductOfMonomials_6))
-- This case gives only one monomial (base case)
encodeToProductOfMonomials c p g (MultR (VarR _ v1) (VarR _ v2)) = 
    let (r_1 ** (mon1, p_1)) = encodeToMonomial c p g (MultR (VarR _ v1) (VarR _ v2)) in
        (_ ** (LastMonomial _ mon1, ?MencodeToProductOfMonomials_7))
-- Case with n>=2monomials
-- Case with the second argument of the Mult being a Neg is not possible since we are supposed to have move the Neg to the front.
encodeToProductOfMonomials c p g (MultR (VarR _ v1) e2) =
	let (r_1 ** (monomial, p_1)) = encodeToMonomial c p g (VarR _ v1) in
	let (r_ih2 ** (productOfMonomials, p_ih2)) = encodeToProductOfMonomials c p g e2 in
	let (r_3 ** (e_3, p_3)) = multiplyMonomialAndProductOfMonomials p monomial productOfMonomials in
		(_ ** (e_3, ?MencodeToProductOfMonomials_8))
            


encodeToCG : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (ExprCG {n=n} (ring_to_commutativeGroup_class p) (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2, c1~=c2))
encodeToCG c p g (ConstR _ _ const1) = 
	(_ ** (ConstCG _ _ _ const1, ?MencodeToCG_1))
encodeToCG c p g (VarR _ v1) = 
	(_ ** (VarCG _ _ v1, ?MencodeToCG_2))
-- Sum of product of monomials
encodeToCG c p g (PlusR e1 e2) = 
    let (r_1 ** (e_1, p_1)) = encodeToCG c p g e1 in
    let (r_2 ** (e_2, p_2)) = encodeToCG c p g e2 in
        (_ ** (PlusCG _ e_1 e_2, ?MencodeToCG_3))
-- Neg of product of monomials
encodeToCG c p g (NegR e) = 
    let (r ** (e, p)) = encodeToCG c p g e in
        (_ ** (NegCG _ e, ?MencodeToCG_4))
-- In the case of a mult, we know that we have a "product of monomials", we just need to encode to it
encodeToCG c p g (MultR e1 e2) =
	let (r_1 ** (pdtOfMon, p_1)) = encodeToProductOfMonomials c p g (MultR e1 e2) in
        (_ ** (VarCG _ _ (EncodingProductOfMonomials _ Neg _ pdtOfMon), ?MencodeToCG_5))

	

ring_reduce : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
ring_reduce p e = 
  let (r_1 ** (e_1, p_1)) = elimMinus' p e in
  let (r_2 ** (e_2, p_2)) = propagateNeg_fix' p e_1 in 
  let (r_3 ** (e_3, p_3)) = elimDoubleNeg' p e_2 in -- Needed because we've propagated some Neg just before
	  
  let (r_4 ** (e_4, p_4)) = develop_fix p e_3 in
	  
  let (r_5 ** (e_5, p_5)) = shuffleProductRight p _ e_4 in -- Needed for the encoding
  let (r_6 ** (e_6, p_6)) = moveNegInPolynomial p e_5 in -- Needed for the encoding, because we want each product of monomials to start with the Neg (if any), and not to contain Negs in the middle of them
  let (r_7 ** (e_7, p_7)) = elimDoubleNeg' p e_6 in -- Needed because we've moved some Neg just before
  -- Then encoding
    (_ **(e_5, ?MX))

	

---------- Proofs ----------
Provers.ring_reduce.MencodeToProductOfMonomials_8 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult r_1 r_ih2)
  exact r_3
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_3
  exact p_1
  exact p_ih2

Provers.ring_reduce.MencodeToProductOfMonomials_7 = proof
  intros
  exact p_1

Provers.ring_reduce.MencodeToProductOfMonomials_6 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_1
  exact p_2

Provers.ring_reduce.MencodeToProductOfMonomials_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult r_1 r_ih2)
  exact r_3
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_3
  exact p_1
  exact p_ih2

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_15 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_assoc 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_14 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  exact (Mult (Mult const1 (Mult const2 c_prod)) c_prod1)
  exact (Mult const1 (Mult (Mult const2 c_prod) c_prod1))
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_assoc 
  mrefine Mult_assoc 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_13 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_assoc 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_12 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_assoc 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_11 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_10 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_9 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_8 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult const1 (Mult c_prod (Mult c_mon c_prod1)))
  exact (Mult (Mult const1 r_1) c_prod1)
  mrefine Mult_assoc 
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact (Mult const1 (Mult (Mult c_prod c_mon) c_prod1))
  exact (Mult (Mult const1 r_1) c_prod1)
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  mrefine Mult_assoc 
  exact (Mult (Mult const1 r_1) c_prod1)
  exact (Mult const1 (Mult r_1 c_prod1))
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  mrefine Mult_assoc 
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  exact p_1
  mrefine set_eq_undec_refl   

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_7 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_6 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult const1 (Mult c_prod c2))
  exact (Mult const1 r_1)
  mrefine Mult_assoc
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_1

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_5 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_4 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c_mon) c_prod)
  exact (Mult r1 c_prod)
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine Mult_preserves_equiv 
  mrefine Mult_assoc 
  exact p1
  mrefine set_eq_undec_refl
 
Provers.ring_reduce.MmultiplyMonomialAndProductOfMonomials_2 = proof
  intros
  mrefine set_eq_undec_refl  
  
Provers.ring_reduce.MmultiplyProdOfVar_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (index k1 g) (Mult c_prod (Mult (index k2 g) (c_prod1))))
  exact (Mult (index k1 g) r_ih1)
  mrefine Mult_assoc 
  mrefine set_eq_undec_refl
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_ih1
  
Provers.ring_reduce.MmultiplyProdOfVar_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (index k1 g) (Mult c_prod (index k2 g)))
  exact (Mult (index k1 g) r_ih1)
  mrefine Mult_assoc 
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1


Provers.ring_reduce.MmoveNegInPolynomial_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1


Provers.ring_reduce.MmoveNegInPolynomial_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2


Provers.ring_reduce.MmoveNegInMonomial_6 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult c1 r_ih1)
  exact (Mult c1 r_ih1)
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  exact p_ih1
  exact p_ih2


Provers.ring_reduce.MmoveNegInMonomial_5 = proof
  intros
  mrefine lemmaRing1


Provers.ring_reduce.MmoveNegInMonomial_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Neg c1) r_ih1)
  exact (Mult (Neg c1) r_ih1)
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  exact p_ih1
  exact p_ih2


Provers.ring_reduce.MmoveNegInMonomial_3 = proof
  intros
  mrefine lemmaRing4


Provers.ring_reduce.MmoveNegInMonomial_2 = proof
  intros
  mrefine lemmaRing2
  
Provers.ring_reduce.MmoveNegInMonomial_1 = proof
  intros
  mrefine lemmaRing2

