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


dist_minus : {c:Type} -> (p:dataTypes.Ring c) -> (c1:c) -> (c2:c) -> (c3:c) -> (Mult c1 (Minus c2 c3) ~= Minus (Mult c1 c2) (Mult c1 c3))
dist_minus p c1 c2 c3 = ?Mdist_minus

dist_minus_2 : {c:Type} -> (p:dataTypes.Ring c) -> (c1:c) -> (c2:c) -> (c3:c) -> (Mult (Minus c1 c2) c3 ~= Minus (Mult c1 c3) (Mult c2 c3))
dist_minus_2 p c1 c2 c3 = ?Mdist_minus_2


dist_plus_minus : {c:Type} -> (p:dataTypes.Ring c) -> (c1:c) -> (c2:c) -> (c3:c) -> (c4:c) -> (Mult (Plus c1 c2) (Minus c3 c4) ~= Minus (Plus (Mult c1 c3) (Mult c2 c3)) (Plus (Mult c1 c4) (Mult c2 c4)))
dist_plus_minus = ?Mdist_plus_minus_1


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
    (Neg r_ih ** (NegR e_ih, ?Mdevelop_3))

      
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
	  let e_ih_a = (MultR e_ih_e11 e_ih_e21) in
	  let e_ih_b = (MultR e_ih_e11 e_ih_e22) in
	  let e_ih_c = (MultR e_ih_e12 e_ih_e21) in
	  let e_ih_d = (MultR e_ih_e12 e_ih_e22) in
		(_ ** (MinusR (PlusR e_ih_a e_ih_c) (PlusR e_ih_b e_ih_d), ?Mdevelop_15))    
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
    (_ ** ((MinusR e_ih_l e_ih_r), ?Mdevelop_18))                         
develop (MultR (MinusR {p} e11 e12) (VarR p v2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih_l = (MultR e_ih_e11 (VarR p v2)) in
  let e_ih_r = (MultR e_ih_e12 (VarR p v2)) in
    (_ ** ((MinusR e_ih_l e_ih_r), ?Mdevelop_19))
develop (MultR (MinusR e11 e12) (PlusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
    -- Note : we could also decide to do immediately more developpment : (x+y) * (z+u) -> xz + xu + yz + yu
    -- But since we need to compute the fixpoint of this treatment anyway, we decide to do "just a bit" of simplification
    -- Note to myself : this is not the approach we've followed for (x+y) * (z-u) where we do immediately all the simplifications
	-- That should not be an issue, but that's perhaps not really nice...
  let e_ih_a = (MultR e_ih_e11 (PlusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (PlusR e_ih_e21 e_ih_e22)) in
    (_ ** (MinusR e_ih_a e_ih_b, ?Mdevelop_20))
develop (MultR (MinusR e11 e12) (MinusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e11 (MinusR e_ih_e21 e_ih_e22)) in
  let e_ih_b = (MultR e_ih_e12 (MinusR e_ih_e21 e_ih_e22)) in
    (_ ** (MinusR e_ih_a e_ih_b, ?Mdevelop_21))    
develop (MultR (MinusR e11 e12) (NegR e2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
    (_ ** (MinusR (MultR e_ih_e11 (NegR e_ih_e2)) (MultR e_ih_e12 (NegR e_ih_e2)), ?Mdevelop_22))
develop (MultR (MinusR e11 e12) (MultR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_a = (MultR e_ih_e21 e_ih_e22) in
  let e_ih_b = (MultR e_ih_e11 e_ih_a) in
  let e_ih_c = (MultR e_ih_e12 e_ih_a) in
    (_ ** (MinusR e_ih_b e_ih_c, ?Mdevelop_23))
    
develop (MultR (NegR e1) (ConstR _ _ c2)) = 
  let (r_ih ** (e_ih, p_ih)) = develop e1 in
      (_ ** (MultR (NegR e_ih) (ConstR _ _ c2), ?Mdevelop_24))
develop (MultR (NegR e1) (VarR p v)) = 
  let (r_ih ** (e_ih, p_ih)) = develop e1 in
      (_ ** (MultR (NegR e_ih) (VarR p v), ?Mdevelop_25))
develop (MultR (NegR e1) (PlusR e21 e22)) =
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (PlusR (MultR (NegR e_ih_e1) e_ih_e21) (MultR (NegR e_ih_e1) e_ih_e22), ?Mdevelop_26))
develop (MultR (NegR e1) (MinusR e21 e22)) =   
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (MinusR (MultR (NegR e_ih_e1) e_ih_e21) (MultR (NegR e_ih_e1) e_ih_e22), ?Mdevelop_27))
-- Not 100% sure here
develop (MultR (NegR e1) (NegR e2)) = 
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
      (_ ** (MultR (NegR e_ih_e1) (NegR e_ih_e2), ?Mdevelop_28))
-- PROBLEM HERE : ADDING THIS CASE HAS CREATED 41 CASES, AND IDRIS RUNS INTO AN INFINITE LOOP AT TYPECHECK...
develop (MultR (NegR e1) (MultR e21 e22)) =
  let (r_ih_e1 ** (e_ih_e1, p_ih_e1)) = develop e1 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
      (_ ** (MultR (NegR e_ih_e1) (MultR e_ih_e21 e_ih_e22), ?Mdevelop_29))
 
develop (MultR (MultR {p} e11 e12) (ConstR _ _ c2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih = (MultR e_ih_e11 e_ih_e12) in
    (_ ** ({- develop -} (MultR e_ih (ConstR _ _ c2)), ?Mdevelop_30))
develop (MultR (MultR {p} e11 e12) (VarR p v2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let e_ih = (MultR e_ih_e11 e_ih_e12) in
    (_ ** ({- develop -} (MultR e_ih (VarR p v2)), ?Mdevelop_31))                 
develop (MultR (MultR e11 e12) (PlusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_l1 e_ih_e21) in
  let e_ih_r2 = (MultR e_ih_l1 e_ih_e22) in
    (_ ** (PlusR e_ih_l2 e_ih_r2, ?Mdevelop_32))
develop (MultR (MultR e11 e12) (MinusR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_l1 e_ih_e21) in
  let e_ih_r2 = (MultR e_ih_l1 e_ih_e22) in
    (_ ** (MinusR e_ih_l2 e_ih_r2, ?Mdevelop_33))    
develop (MultR (MultR e11 e12) (NegR e2)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e2 ** (e_ih_e2, p_ih_e2)) = develop e2 in
    (_ ** (MultR (MultR e_ih_e11 e_ih_e12) (NegR e_ih_e2), ?Mdevelop_34))  
develop (MultR (MultR e11 e12) (MultR e21 e22)) = 
  let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
  let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
  let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
  let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
  let e_ih_l1 = (MultR e_ih_e11 e_ih_e12) in
  let e_ih_l2 = (MultR e_ih_e21 e_ih_e22) in
  let e_ih_l3 = (MultR e_ih_l1 e_ih_l2) in
    (_ ** (e_ih_l3, ?Mdevelop_35))
    
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
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?MelimMinus'_1))
elimMinus' {c} p (VarR _ v) = (_ ** (VarR _ v, set_eq_undec_refl {c} _))    
elimMinus' p (MinusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Plus r_ih1 (Neg r_ih2)) ** (PlusR e_ih1 (NegR e_ih2), ?MelimMinus'_2)) 
elimMinus' p (NegR e1) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
    (_ ** (NegR e_ih1, ?MelimMinus'_3))
elimMinus' p (MultR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (elimMinus' p e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (elimMinus' p e2) in
    ((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?MelimMinus'_4))



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
	let (r_ih1 ** (e_ih1, p_ih1)) = shuffleProductRight p g e in -- I think there was a big problem here...
    (_ ** (NegR e_ih1, ?MshuffleProductRight1))
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
total
propagateNeg' : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
propagateNeg' p (NegR (PlusR e1 e2)) =
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in -- I've changed this so that every call is on something (syntactically) smaller. The output should still be exactly the same, as I've basically just unfolded the previous recursive call
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in -- I've changed this so that every call is on something (syntactically) smaller. The output should still be exactly the same, as I've basically just unfolded the previous recursive call
		((Plus (Neg r_ih2) (Neg r_ih1)) ** (PlusR (NegR e_ih2) (NegR e_ih1), ?MpropagateNeg'_1)) -- Carefull : - (a + b) = (-b) + (-a) in a group and *not* (-a) + (-b) in general. See mathsResults.bad_push_negation_IMPLIES_commutativeGroup for more explanations about this
propagateNeg' p (NegR (MultR e1 e2)) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in -- We do not forget to propate the Neg inside of the product (we chose the first argument)
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Mult (Neg r_ih1) r_ih2) ** (MultR (NegR e_ih1) e_ih2, ?MpropagateNeg'_2)) -- I've changed this so that every call is on something (syntactically) smaller. The output should still be exactly the same, as I've basically just unfolded the previous recursive call which was done on (NegR e1)
propagateNeg' p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = propagateNeg' p e in
		((Neg r_ih1) ** (NegR e_ih1, ?MpropagateNeg'_3))
propagateNeg' p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?MpropagateNeg'_4))
propagateNeg' p (MultR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (propagateNeg' p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (propagateNeg' p e2) in
		((Mult r_ih1 r_ih2) ** (MultR e_ih1 e_ih2, ?MpropagateNeg'_5))		
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
    



moveNegToFront_Left_mon : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegToFront_Left_mon {c} p (ConstR _ _ const1) = 
	(_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
moveNegToFront_Left_mon {c} p (VarR _ v) = 
	(_ ** (VarR _ v, set_eq_undec_refl {c} _))
moveNegToFront_Left_mon {c} p (NegR e) = 
        (_ ** (NegR e, set_eq_undec_refl {c} _))
moveNegToFront_Left_mon p (MultR (NegR a) b) = 
        let (r_ih1 ** (e_ih1, p_ih1)) = moveNegToFront_Left_mon p (MultR a b) in
        (_ ** (NegR e_ih1, ?MmoveNegToFront_Left_mon_1))
moveNegToFront_Left_mon {c} p (MultR a b) = 
        (_ ** (MultR a b, set_eq_undec_refl {c} _))


moveNegToFront_Left_pol : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegToFront_Left_pol p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegToFront_Left_pol p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (moveNegToFront_Left_pol p e2) in
		(_ ** (PlusR e_ih1 e_ih2, ?MmoveNegToFront_Left_pol_1))
moveNegToFront_Left_pol {c} p (ConstR _ _ const1) = 
	(_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
moveNegToFront_Left_pol {c} p (VarR _ v) = 
	(_ ** (VarR _ v, set_eq_undec_refl {c} _))
moveNegToFront_Left_pol p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegToFront_Left_pol p e) in
            (_ ** (NegR e_ih1, ?MmoveNegToFront_Left_pol_2))
moveNegToFront_Left_pol p (MultR a b) = moveNegToFront_Left_mon p (MultR a b)
    
   
moveNegToFront_Right_mon : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegToFront_Right_mon {c} p (ConstR _ _ const1) = 
	(_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
moveNegToFront_Right_mon {c} p (VarR _ v) = 
	(_ ** (VarR _ v, set_eq_undec_refl {c} _))
moveNegToFront_Right_mon {c} p (NegR e) = 
        (_ ** (NegR e, set_eq_undec_refl {c} _))
moveNegToFront_Right_mon p (MultR a (NegR b)) = 
        let (r_ih1 ** (e_ih1, p_ih1)) = moveNegToFront_Right_mon p (MultR a b) in
        (_ ** (NegR e_ih1, ?MmoveNegToFront_Right_mon_1))
moveNegToFront_Right_mon {c} p (MultR a b) = 
        (_ ** (MultR a b, set_eq_undec_refl {c} _))


moveNegToFront_Right_pol : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegToFront_Right_pol p (PlusR e1 e2) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegToFront_Right_pol p e1) in
	let (r_ih2 ** (e_ih2, p_ih2)) = (moveNegToFront_Right_pol p e2) in
		(_ ** (PlusR e_ih1 e_ih2, ?MmoveNegToFront_Right_pol_1))
moveNegToFront_Right_pol {c} p (ConstR _ _ const1) = 
	(_ ** (ConstR _ _ const1, set_eq_undec_refl {c} _))
moveNegToFront_Right_pol {c} p (VarR _ v) = 
	(_ ** (VarR _ v, set_eq_undec_refl {c} _))
moveNegToFront_Right_pol p (NegR e) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = (moveNegToFront_Right_pol p e) in
            (_ ** (NegR e_ih1, ?MmoveNegToFront_Right_pol_2))
moveNegToFront_Right_pol p (MultR a b) = moveNegToFront_Right_mon p (MultR a b)
    
    
    
moveNegToFrontInAllMonomials : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
moveNegToFrontInAllMonomials p e = 
	let (r_1 ** (e_1, p_1)) = (moveNegToFront_Left_pol p e) in
	let (r_2 ** (e_2, p_2)) = (moveNegToFront_Right_pol p e_1) in
            (_ ** (e_2, ?MmoveNegToFrontInAllMonomials_1))
        
{-    
-- For a product A * B, we decide to move the neg before the product if there is one
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

-}
	
	
-- Moved here because simplifyWithConstant_ProdOfMon needs it
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
	
	
	
total
simplifyWithConstant_Monomial : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {setAndMult:SetWithMult c (ring_to_set p)} -> (proofZero : (x:c) -> mult setAndMult Zero x ~= Zero) -> (proofOne : (x:c) -> mult setAndMult One x ~= x) -> {c1:c} -> (monomial:Monomial setAndMult g c1) -> (c2 ** (Monomial setAndMult g c2, c1~=c2))
simplifyWithConstant_Monomial c p g proofZero proofOne (ProdOfVar _ prodOfVar) = (_ ** (ProdOfVar _ prodOfVar, ?MsimplifyWithConstant_Monomial_1))
simplifyWithConstant_Monomial c p g proofZero proofOne (ProdOfVarWithConst _ const1 prodOfVar) = 
	case set_eq const1 Zero of
		-- 0 * v1v2v3 -> 0
		Just prEqualZero => (_ ** (ConstantMonomial g _ Zero, ?MsimplifyWithConstant_Monomial_2))
		Nothing => 
		case set_eq const1 One of
			-- 1 * v1v2v3... -> v1*v2v*v3...
			Just prEqualOne => (_ ** (ProdOfVar _ prodOfVar, ?MsimplifyWithConstant_Monomial_3))
			Nothing => (_ ** (ProdOfVarWithConst _ const1 prodOfVar, ?MsimplifyWithConstant_Monomial_4))
simplifyWithConstant_Monomial c p g proofZero proofOne (ConstantMonomial g _ const1) = (_ ** (ConstantMonomial g _ const1, ?MsimplifyWithConstant_Monomial_5))
	

total
simplifyWithConstant_ProdOfMon : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {setAndMult:SetWithMult c (ring_to_set p)} -> (proofZero : (x:c) -> mult setAndMult Zero x ~= Zero) -> (proofOne : (x:c) -> mult setAndMult One x ~= x) -> {c1:c} -> (prodOfMon:ProductOfMonomials setAndMult g c1) -> (c2 ** (ProductOfMonomials setAndMult g c2, c1~=c2))
simplifyWithConstant_ProdOfMon c p g proofZero proofOne (LastMonomial _ monomial) = 
	let (r1 ** (e1, p1)) = simplifyWithConstant_Monomial c p g proofZero proofOne monomial in
		(_ ** (LastMonomial _ e1, ?MsimplifyWithConstant_ProdOfMon_1)) -- Because of this, we might finish with  just a constant monomial equal to Zero, so we will need to check that any expression containing a productOfMonomials can't be simplified by removing this prodOfMon.
-- New part added
simplifyWithConstant_ProdOfMon c p g proofZero proofOne (MonomialMultProduct _ monomial1 (LastMonomial _ monomial2)) = 
	let (r1 ** (e1, p1)) = simplifyWithConstant_Monomial c p g proofZero proofOne monomial1 in
	let (r2 ** (e2, p2)) = simplifyWithConstant_Monomial c p g proofZero proofOne monomial2 in
		case e2 of
			(ConstantMonomial g _ r2) =>
			case set_eq r2 Zero of
				Just prEqualZero => (_ ** (LastMonomial _ (ConstantMonomial g _ Zero), ?MNEW))
				Nothing => case set_eq r2 One of
								Just prEqualOne => (_ ** (LastMonomial _ monomial1, ?MNEW2))
								Nothing => case set_eq r2 (Neg One) of
											Just prEqualNegOne => let eHead = ConstantMonomial _ _ (Provers.dataTypes.Neg One) in
																	let (rProd ** (eProd, pProd)) = multiplyMonomialAndProductOfMonomials _ eHead (LastMonomial _ e1) in
																	(_ ** (eProd, ?MNEW3))
											Nothing => (_ ** (MonomialMultProduct _ monomial1 (LastMonomial _ monomial2), set_eq_undec_refl {c} _))
			_ => (_ ** (MonomialMultProduct _ e1 (LastMonomial _ e2), ?MNEW4))
-- Old part
simplifyWithConstant_ProdOfMon c p g proofZero proofOne (MonomialMultProduct _ monomial prodOfMon) = 
	let (r1 ** (e1, p1)) = simplifyWithConstant_Monomial c p g proofZero proofOne monomial in
	let (r_ih2 ** (e_ih2, p_ih2)) = simplifyWithConstant_ProdOfMon c p g proofZero proofOne prodOfMon in
	case e1 of
		(ConstantMonomial g _ r1) =>
		-- we return the constant monomial Zero
		case set_eq r1 Zero of
			Just prEqualZero => (_ ** (LastMonomial _ (ConstantMonomial g _ Zero), ?MsimplifyWithConstant_ProdOfMon_2))
			Nothing => (_ ** (MonomialMultProduct _ e1 e_ih2, ?MsimplifyWithConstant_ProdOfMon_3))
		-- nothing to simplify here for a ProdOfVar or for a ProfOfVarWithConst
		_ => ( _ ** (MonomialMultProduct _ e1 e_ih2, ?MsimplifyWithConstant_ProdOfMon_4))
    -- Should I do the simplification for One here as well ? 
	-- No, it's not needed because something like 1*(1*x) has been "parsed" as a unique monomial (1*1)*x
	
	
	
	
	
decodeProdOfVar : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (prodOfVar:ProductOfVariables (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
decodeProdOfVar c p g (LastVar g _ k) = (_ ** (VarR p (RealVariable _ _ _ g k), ?MdecodeProdOfVar_1))
decodeProdOfVar c p g (VarMultProduct _ k prodOfVar) = 
	let (r_ih1 ** (e_ih1, p_ih1)) = decodeProdOfVar c p g prodOfVar in
		(_ ** (MultR (VarR p (RealVariable _ _ _ g k)) e_ih1, ?MdecodeProdOfVar_2))
	
	
    
encodeToMonomial : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (e:ExprR p g c1) -> (c2 ** (Monomial (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c2, c1~=c2))
-- The only thing we can get are : 
-- a Var, a Constant, a Mult between a const and a var and a Mult between a var and a var
-- (Mult between const and const is impossible because we would have deal with that directly, and Mult between var and const would not make a monomial so we would have already deal with it as well) 
encodeToMonomial c p g (ConstR _ _ const1) = (_ ** (ConstantMonomial _ _ const1, set_eq_undec_refl {c} _))
encodeToMonomial c p g (VarR _ (RealVariable _ _ _ _ i)) = (_ ** (ProdOfVar _ (LastVar _ _ i), set_eq_undec_refl {c} _))
encodeToMonomial c p g (MultR (ConstR _ _ const1) (VarR _ (RealVariable _ _ _ _ i))) = (_ ** (ProdOfVarWithConst _ const1 (LastVar _ _ i), set_eq_undec_refl {c} _))
encodeToMonomial c p g (MultR (VarR _ (RealVariable _ _ _ _ i)) (VarR _ (RealVariable _ _ _ _ j))) = (_ ** (ProdOfVar _ (VarMultProduct _ i (LastVar _ _ j)), set_eq_undec_refl {c} _))



decodeMonomial : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (monomial:Monomial (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
decodeMonomial c p g (ProdOfVar _ prodOfVar) = decodeProdOfVar c p g prodOfVar
decodeMonomial c p g (ProdOfVarWithConst _ const1 prodOfVar) = 
	let (r1 ** (e1, p1)) = decodeProdOfVar c p g prodOfVar in
		(_ ** (MultR (ConstR _ _ const1) e1, ?MdecodeMonomial_1))
decodeMonomial c p g (ConstantMonomial g _ const1) = (_ ** (ConstR _ _ const1, ?MdecodeMonomial_2))


    
    

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
            

decodeProductOfMonomials : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (prodOfMon:ProductOfMonomials (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
decodeProductOfMonomials c p g (LastMonomial _ mon) = decodeMonomial c p g mon
decodeProductOfMonomials c p g (MonomialMultProduct _ mon prod) =
	let (r1 ** (e1, p1)) = decodeMonomial c p g mon in
	let (r_ih2 ** (e_ih2, p_ih2)) = decodeProductOfMonomials c p g prod in
		(_ ** (MultR e1 e_ih2, ?MdecodeProductOfMonomials_1))


		
-- NEW : If an encoding is just a constant, we "decrypt" it, so that the CommutativeGroup level will be able to simplify it with other constants		
total
decryptConstantAndVariable : {c:Type} -> (p:CommutativeGroup c) -> (setAndMult:SetWithMult c (commutativeGroup_to_set p)) -> {g:Vect n c} -> {c1:c} -> (ExprCG p setAndMult g c1) -> (c2 ** (ExprCG p setAndMult g c2, c1~=c2))		
decryptConstantAndVariable p setAndMult (VarCG _ _ (EncodingProductOfMonomials _ _ _ (LastMonomial _ (ConstantMonomial _ _ const1)))) = (_ ** (ConstCG _ _ _ const1, ?MdecryptConstant_1))
decryptConstantAndVariable p setAndMult (VarCG _ _ (EncodingProductOfMonomials _ _ _ (LastMonomial _ (ProdOfVar _ (LastVar _ _ i))))) = (_ ** (VarCG _ _ (RealVariable _ _ _ _ i), ?MNEWTEST))
decryptConstantAndVariable p setAndMult e = (_ ** (e, ?MdecryptConstant_2))
		
		
-- NEW : does a bit of simplification after having encoded the product of monomials : 1 * v1v2v3 -> v1v2v3 and 0*v1v2v3 -> 0
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
	let (r_2 ** (pdtOfMon2, p_2)) = simplifyWithConstant_ProdOfMon c p g (\x => zeroAbsorbant2 c p x) (\x => right (Mult_neutral x)) pdtOfMon in -- NEW : simplifications in the product of monomials
	let (r_3 ** (res, p_3)) = decryptConstantAndVariable (ring_to_commutativeGroup_class p) _ (VarCG _ _ (EncodingProductOfMonomials _ Neg _ pdtOfMon2)) in -- NEW : if the resulted product of monomial is a constant, we transform it into a real constant, so that constant will be able to be simplified at the CG level
        (_ ** (res, ?MencodeToCG_5))

	
	
decodeFromCG : (c:Type) -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1:c} -> (ExprCG {n=n} (ring_to_commutativeGroup_class p) (MkSetWithMult (ring_to_set p) Mult (\a1,a2,a3,a4,px,py => Mult_preserves_equiv {c1=a1} {c2=a2} {c1'=a3} {c2'=a4} px py)) g c1) -> (c2 ** (ExprR {n=n} p g c2, c1~=c2))
decodeFromCG c p g (ConstCG _ _ g const1) = (_ ** (ConstR p _ const1, ?MdecodeFromCG_1)) -- Fix Idris : we can't simply give (set_eq_undec_refl _) which is exactly the proof we do in the proof mode !
decodeFromCG c p g (PlusCG _ e1 e2) = 
    let (r_ih1 ** ((e_ih1, p_ih1))) = decodeFromCG c p g e1 in 
    let (r_ih2 ** ((e_ih2, p_ih2))) = decodeFromCG c p g e2 in 
        (_ ** (PlusR e_ih1 e_ih2, ?MdecodeFromCG_2))
decodeFromCG c p g (MinusCG _ e1 e2) = 
    let (r_ih1 ** ((e_ih1, p_ih1))) = decodeFromCG c p g e1 in 
    let (r_ih2 ** ((e_ih2, p_ih2))) = decodeFromCG c p g e2 in 
        (_ ** (MinusR e_ih1 e_ih2, ?MdecodeFromCG_3))
decodeFromCG c p g (NegCG _ e) = 
    let (r_ih ** ((e_ih, p_ih))) = decodeFromCG c p g e in 
        (_ ** (NegR e_ih, ?MdecodeFromCG_4))
decodeFromCG c p g (VarCG _ _ (RealVariable _ _ _ _ i)) = (_ ** (VarR _ (RealVariable _ _ _ _ i), ?MdecodeFromCG_5))
-- I should not have "encoding of group terms" at this point, so I just do this identity (I don't decode them, in order to avoid hiding potential problems from the Group level)
decodeFromCG c p g (VarCG _ _ (EncodingGroupTerm_var _ _ _ _ i)) = (_ ** (VarR _ (EncodingGroupTerm_var _ _ _ _ i), ?MdecodeFromCG_6))
decodeFromCG c p g (VarCG _ _ (EncodingProductOfMonomials _ _ _ productOfMonomials)) = 
    let (r_1 ** ((e_1, p_1))) = decodeProductOfMonomials c p g productOfMonomials in
        (_ ** (e_1, ?MdecodeFromCG_7))
    

code_reduceCG_andDecode : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))    
code_reduceCG_andDecode p e = 	
	let (c2 ** (e2, pEncode)) = encodeToCG _ p _ e in
	let (c3 ** (e3, pReduce)) = commutativeGroupReduce (ring_to_commutativeGroup_class p) e2 in
	let (c4 ** (e4, pDecode)) = decodeFromCG _ p _ e3 in
		(c4 ** (e4, ?Mcode_reduceCG_andDecode_1))    
    
    

ring_reduce : {c:Type} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
ring_reduce p e = 
  let (r_1 ** (e_1, p_1)) = elimMinus' p e in
  let (r_2 ** (e_2, p_2)) = propagateNeg_fix' p e_1 in 
  let (r_3 ** (e_3, p_3)) = elimDoubleNeg' p e_2 in -- Needed because we've propagated some Neg just before
	  
  let (r_4 ** (e_4, p_4)) = develop_fix p e_3 in
	  
  let (r_5 ** (e_5, p_5)) = shuffleProductRight p _ e_4 in -- Needed for the encoding
  let (r_6 ** (e_6, p_6)) = moveNegToFrontInAllMonomials p e_5 in -- Needed for the encoding, because we want each product of monomials to start with the Neg (if any), and not to contain Negs in the middle of them
  let (r_7 ** (e_7, p_7)) = elimDoubleNeg' p e_6 in -- Needed because we've moved some Neg just before
  -- Then encoding, call to commutativeGroup prover, and decoding
  let (r_8 ** (e_8, p_8)) = code_reduceCG_andDecode p e_7 in
    (_ **(e_8, ?Mring_reduce_1))


    
buildProofRing : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {x : c} -> {y : c} -> {c1:c} -> {c2:c} -> (ExprR p g c1) -> (ExprR p g c2) -> (x~=c1) -> (y~=c2) -> (Maybe (x~=y))
buildProofRing p e1 e2 lp rp with (exprR_eq p _ e1 e2)
	buildProofRing p e1 e2 lp rp | Just e1_equiv_e2 = ?MbuildProofRing
	buildProofRing p e1 e2 lp rp | Nothing = Nothing

		
ringDecideEq : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprR p g x) -> (ExprR p g y) -> (Maybe (x~=y))
-- e1 is the left side, e2 is the right side
ringDecideEq p e1 e2 =
	let (r_e1 ** (e_e1, p_e1)) = ring_reduce p e1 in
	let (r_e2 ** (e_e2, p_e2)) = ring_reduce p e2 in
		buildProofRing p e_e1 e_e2 p_e1 p_e2    
    

debugRing : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> (c_show : Show c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprR p g x) -> (ExprR p g y) -> String
debugRing p c_show e1 e2 = 
	let (r_e1 ** (e_e1, p_e1)) = ring_reduce p e1 in
	let (r_e2 ** (e_e2, p_e2)) = ring_reduce p e2 in
	let leftSideNormalised = print_ExprR show e_e1 in
	let rightSideNormalised = print_ExprR show e_e2 in
		"left side normalised = " ++ leftSideNormalised ++ " ############### Right side normalised = " ++ rightSideNormalised
    
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


Provers.ring_reduce.MmoveNegToFrontInAllMonomials_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_2
  exact p_1
  mrefine set_eq_undec_refl 
  exact p_2


Provers.ring_reduce.MmoveNegToFront_Right_pol_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1 


Provers.ring_reduce.MmoveNegToFront_Right_pol_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2


Provers.ring_reduce.MmoveNegToFront_Right_mon_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Neg (Mult c1 c2))
  exact (Neg r_ih1)
  mrefine lemmaRing1
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  exact p_ih1


Provers.ring_reduce.MmoveNegToFront_Left_pol_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1


Provers.ring_reduce.MmoveNegToFront_Left_pol_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2


Provers.ring_reduce.MmoveNegToFront_Left_mon_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Neg (Mult c1 c2))
  exact (Neg r_ih1)
  mrefine lemmaRing2
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  exact p_ih1

{-
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

-}

Provers.ring_reduce.MpropagateNeg'_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg c2) (Neg c1))
  exact (Plus (Neg c2) (Neg c1))
  mrefine push_negation 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym
  mrefine set_eq_undec_sym
  mrefine Neg_preserves_equiv
  mrefine Neg_preserves_equiv
  exact p_ih2
  exact p_ih1

Provers.ring_reduce.MpropagateNeg'_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Neg (Mult r_ih1 r_ih2))
  exact (Mult (Neg r_ih1) r_ih2)
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine Mult_preserves_equiv 
  mrefine lemmaRing2
  exact p_ih1
  exact p_ih2
  
Provers.ring_reduce.MpropagateNeg'_3 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1

Provers.ring_reduce.MpropagateNeg'_4 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MpropagateNeg'_5 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MpropagateNeg_fix'_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_ih1
  exact p_1
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MelimDoubleNeg'_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Neg (Neg r_ih1))
  exact r_ih1
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine group_doubleNeg 
  mrefine Neg_preserves_equiv 
  exact p_ih1

Provers.ring_reduce.MelimDoubleNeg'_2 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1

Provers.ring_reduce.MelimDoubleNeg'_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MelimDoubleNeg'_4 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MencodeToCG_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_3
  exact p_1
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_2
  exact r_3
  exact p_2
  mrefine set_eq_undec_refl 
  exact p_3
  
Provers.ring_reduce.MencodeToCG_4 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p1

Provers.ring_reduce.MencodeToCG_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_1
  exact p_2

Provers.ring_reduce.MencodeToCG_2 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MencodeToCG_1 = proof
  intros
  mrefine set_eq_undec_refl 
  
Provers.ring_reduce.MdecodeProdOfVar_1 = proof
  intros
  mrefine set_eq_undec_refl 
  
Provers.ring_reduce.MdecodeProdOfVar_2 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MdecodeMonomial_1 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p1  
  
Provers.ring_reduce.MdecodeMonomial_2 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MdecodeProductOfMonomials_1 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p1
  exact p_ih2  
  
Provers.ring_reduce.MdecryptConstant_2 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MdecryptConstant_1 = proof
  intros
  mrefine set_eq_undec_refl 
  
Provers.ring_reduce.MdecodeFromCG_7 = proof
  intros
  exact p_1

Provers.ring_reduce.MdecodeFromCG_6 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MdecodeFromCG_5 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MdecodeFromCG_4 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih

Provers.ring_reduce.MdecodeFromCG_3 = proof
  intros
  mrefine Minus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MdecodeFromCG_2 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MdecodeFromCG_1 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MmultAfter1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult c1 (Mult c2 c3))
  exact (Mult (Mult c1 c2) c3)
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact p_ih1
  mrefine Mult_assoc 

Provers.ring_reduce.MshuffleProductRight23 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c2) (Mult c3 c4))
  exact (Mult r_ih1 r_ih2)
  mrefine set_eq_undec_refl 
  exact p_3
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight22 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c2) (Neg c3))
  exact (Mult r_ih1 r_ih2)
  mrefine set_eq_undec_refl 
  exact p_3
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight21 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c2) (Plus c3 c4))
  exact (Mult r_ih1 r_ih2)
  mrefine set_eq_undec_refl 
  exact p_3
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight20 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c2) c3)
  exact (Mult r_ih1 c3)
  mrefine set_eq_undec_refl 
  exact p_2
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MshuffleProductRight19 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Mult c1 c2) const2)
  exact (Mult r_ih1 const2)
  mrefine set_eq_undec_refl 
  exact p_2
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MshuffleProductRight18 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight17 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight16 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight15 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MshuffleProductRight14 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MshuffleProductRight13 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight12 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight11 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight10 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl

Provers.ring_reduce.MshuffleProductRight9 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_refl

Provers.ring_reduce.MshuffleProductRight8 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_ih1

Provers.ring_reduce.MshuffleProductRight7 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_ih1

Provers.ring_reduce.MshuffleProductRight6 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1 

Provers.ring_reduce.MshuffleProductRight5 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MshuffleProductRight4 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MshuffleProductRight3 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MshuffleProductRight2 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.MshuffleProductRight1 = proof
  intros
  mrefine Neg_preserves_equiv
  exact p_ih1

Provers.ring_reduce.Mdevelop_fix_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_ih1
  exact p_1
  mrefine set_eq_undec_refl 
  exact p_ih1

Provers.ring_reduce.MelimMinus'_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2
  
Provers.ring_reduce.MelimMinus'_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus c1 c2)
  exact (Plus c1 (Neg c2))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Minus_simpl 
  mrefine set_eq_undec_sym 
  mrefine Neg_preserves_equiv 
  exact p_ih1
  mrefine set_eq_undec_sym 
  exact p_ih2  
  
Provers.ring_reduce.MelimMinus'_3 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih1
  
Provers.ring_reduce.MelimMinus'_4 = proof
  intros
  mrefine Mult_preserves_equiv 
  exact p_ih1
  exact p_ih2  

Provers.ring_reduce.Mdist_minus = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult c1 (Plus c2 (Neg c3)))
  exact (Plus (Mult c1 c2) (Mult c1 (Neg c3)))
  mrefine Mult_preserves_equiv 
  mrefine eq_preserves_eq 
  mrefine Mult_dist
  mrefine set_eq_undec_refl 
  mrefine Minus_simpl 
  exact (Plus (Mult c1 c2) (Neg (Mult c1 c3)))
  exact (Plus (Mult c1 c2) (Mult c1 (Neg c3)))
  mrefine Minus_simpl 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine lemmaRing1

Provers.ring_reduce.Mdist_minus_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Plus c1 (Neg c2)) c3)
  exact (Plus (Mult c1 c3) (Neg (Mult c2 c3)))
  mrefine Mult_preserves_equiv 
  mrefine Minus_simpl 
  mrefine eq_preserves_eq 
  mrefine Minus_simpl 
  mrefine set_eq_undec_refl 
  exact (Mult (Plus c1 (Neg c2)) c3)
  exact (Plus (Mult c1 c3) (Mult (Neg c2) c3))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_dist_2
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine lemmaRing2  
  
Provers.ring_reduce.Mdist_plus_minus_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult (Plus c2 c3) c4) (Mult (Plus c2 c3) c5))
  exact (Minus (Plus (Mult c2 c4) (Mult c3 c4)) (Plus (Mult c2 c5) (Mult c3 c5)))
  mrefine dist_minus 
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact (Minus (Plus (Mult c2 c4) (Mult c3 c4)) (Plus (Mult c2 c5) (Mult c3 c5)))
  exact (Minus (Plus (Mult c2 c4) (Mult c3 c4)) (Plus (Mult c2 c5) (Mult c3 c5)))
  mrefine Minus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_refl 
  mrefine Mult_dist_2 
  mrefine Mult_dist_2  

Provers.ring_reduce.Mdevelop_35 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  exact p_ih_e12
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_34 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_ih_e11
  exact p_ih_e12
  exact p_ih_e2

Provers.ring_reduce.Mdevelop_33 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult (Mult c1 c2) c3) (Mult (Mult c1 c2) c4))
  exact (Minus (Mult (Mult r_ih_e11 r_ih_e12) r_ih_e21) (Mult (Mult r_ih_e11 r_ih_e12) r_ih_e22))
  mrefine dist_minus
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  mrefine Mult_preserves_equiv 
  exact p_ih_e22
  exact p_ih_e11
  exact p_ih_e12
  exact p_ih_e11
  exact p_ih_e12

Provers.ring_reduce.Mdevelop_32 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult (Mult c1 c2) c3) (Mult (Mult c1 c2) c4))
  exact (Plus (Mult (Mult r_ih_e11 r_ih_e12) r_ih_e21) (Mult (Mult r_ih_e11 r_ih_e12) r_ih_e22))
  mrefine Mult_dist
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  mrefine Mult_preserves_equiv 
  exact p_ih_e22
  exact p_ih_e11
  exact p_ih_e12
  exact p_ih_e11
  exact p_ih_e12

Provers.ring_reduce.Mdevelop_31 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih_e11
  exact p_ih_e12

Provers.ring_reduce.Mdevelop_30 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  exact p_ih_e11
  exact p_ih_e12

Provers.ring_reduce.Mdevelop_29 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e1
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_28 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_ih_e1
  exact p_ih_e2
  
Provers.ring_reduce.Mdevelop_27 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult (Neg c1) c2) (Mult (Neg c1) c3))
  exact (Minus (Mult (Neg r_ih_e1) r_ih_e21) (Mult (Neg r_ih_e1) r_ih_e22))
  mrefine dist_minus
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_ih_e21
  mrefine Neg_preserves_equiv 
  exact p_ih_e22
  exact p_ih_e1
  exact p_ih_e1

Provers.ring_reduce.Mdevelop_26 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult (Neg c1) c2) (Mult (Neg c1) c3))
  exact (Plus (Mult (Neg r_ih_e1) r_ih_e21) (Mult (Neg r_ih_e1) r_ih_e22))
  mrefine Mult_dist
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  exact p_ih_e21
  mrefine Neg_preserves_equiv 
  exact p_ih_e22
  exact p_ih_e1
  exact p_ih_e1

Provers.ring_reduce.Mdevelop_25 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih

Provers.ring_reduce.Mdevelop_24 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih

Provers.ring_reduce.Mdevelop_23 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult c1 (Mult c3 c4)) (Mult c2 (Mult c3 c4)))
  exact (Minus (Mult r_ih_e11 (Mult r_ih_e21 r_ih_e22)) (Mult r_ih_e12 (Mult r_ih_e21 r_ih_e22)))
  mrefine dist_minus_2
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine Mult_preserves_equiv 
  exact p_ih_e12
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_22 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult c1 (Neg c3)) (Mult c2 (Neg c3)))
  exact (Minus (Mult r_ih_e11 (Neg r_ih_e2)) (Mult r_ih_e12 (Neg r_ih_e2)))
  mrefine dist_minus_2
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine Neg_preserves_equiv 
  exact p_ih_e12
  mrefine Neg_preserves_equiv 
  exact p_ih_e2
  exact p_ih_e2

Provers.ring_reduce.Mdevelop_21 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult c1 (Minus c3 c4)) (Mult c2 (Minus c3 c4)))
  exact (Minus (Mult r_ih_e11 (Minus r_ih_e21 r_ih_e22)) (Mult r_ih_e12 (Minus r_ih_e21 r_ih_e22)))
  mrefine dist_minus_2
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine Minus_preserves_equiv 
  exact p_ih_e12
  mrefine Minus_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22
  exact p_ih_e21
  exact p_ih_e22  
  
Provers.ring_reduce.Mdevelop_20 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Minus r_ih_e11 r_ih_e12) (Plus r_ih_e21 r_ih_e22))
  exact (Minus (Mult r_ih_e11 (Plus r_ih_e21 r_ih_e22)) (Mult r_ih_e12 (Plus r_ih_e21 r_ih_e22)))
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine dist_minus_2
  mrefine Minus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  exact p_ih_e11
  exact p_ih_e12
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_19 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Minus r_ih_e11 r_ih_e12) c3)
  exact (Minus (Mult r_ih_e11 c3) (Mult r_ih_e12 c3))
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine dist_minus_2
  mrefine Minus_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih_e11
  exact p_ih_e12

Provers.ring_reduce.Mdevelop_18 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Minus r_ih_e11 r_ih_e12) c3)
  exact (Minus (Mult r_ih_e11 c3) (Mult r_ih_e12 c3))
  mrefine Mult_preserves_equiv 
  mrefine Minus_preserves_equiv 
  mrefine dist_minus_2
  mrefine Minus_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  exact p_ih_e12
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_refl  
  
Provers.ring_reduce.Mdevelop_17 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult c1 (Mult c3 c4)) (Mult c2 (Mult c3 c4)))
  exact (Plus (Mult r_ih_e11 (Mult r_ih_e21 r_ih_e22)) (Mult r_ih_e12 (Mult r_ih_e21 r_ih_e22)))
  mrefine Mult_dist_2
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine Mult_preserves_equiv 
  exact p_ih_e12
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22
  exact p_ih_e21
  exact p_ih_e22  
  
-- FIX IDRIS ! A simpler proof would start immediately by applying Mult_dist_2 with {c1=c1} {c2=c2} and {c3=Neg c3}  
-- BUT if we use mrefine then idris picks {c3=c3} (which is not what we want!)
Provers.ring_reduce.Mdevelop_16 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Plus c1 c2) (Neg c3))
  exact (Plus (Mult c1 (Neg c3)) (Mult c2 (Neg c3)))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_dist_2
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine Neg_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine Neg_preserves_equiv 
  exact p_ih_e11
  mrefine set_eq_undec_sym 
  exact p_ih_e12
  mrefine set_eq_undec_sym 
  exact p_ih_e2
  exact p_ih_e2
    
Provers.ring_reduce.Mdevelop_15 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Plus (Mult c1 c3) (Mult c2 c3)) (Plus (Mult c1 c4) (Mult c2 c4)))
  exact (Minus (Plus (Mult r_ih_e11 r_ih_e21) (Mult r_ih_e12 r_ih_e21)) (Plus (Mult r_ih_e11 r_ih_e22) (Mult r_ih_e12 r_ih_e22)))
  mrefine dist_plus_minus 
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  exact p_ih_e21
  exact p_ih_e12
  exact p_ih_e21
  exact p_ih_e11
  exact p_ih_e22
  exact p_ih_e12
  exact p_ih_e22  
  
Provers.ring_reduce.Mdevelop_14 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult c1 (Plus c3 c4)) (Mult c2 (Plus c3 c4)))
  exact (Plus (Mult r_ih_e11 (Plus r_ih_e21 r_ih_e22)) (Mult r_ih_e12 (Plus r_ih_e21 r_ih_e22)))
  mrefine Mult_dist_2
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine Plus_preserves_equiv 
  exact p_ih_e12
  mrefine Plus_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_13 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult c1 c3) (Mult c2 c3))
  exact (Plus (Mult r_ih_e11 c3) (Mult r_ih_e12 c3))
  mrefine Mult_dist_2 
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine set_eq_undec_refl 
  exact p_ih_e12
  mrefine set_eq_undec_refl 

Provers.ring_reduce.Mdevelop_12 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult c1 c3) (Mult c2 c3))
  exact (Plus (Mult r_ih_e11 c3) (Mult r_ih_e12 c3))
  mrefine Mult_dist_2 
  mrefine set_eq_undec_refl
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p_ih_e11
  mrefine set_eq_undec_refl 
  exact p_ih_e12
  mrefine set_eq_undec_refl 

Provers.ring_reduce.Mdevelop_11 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_10 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  exact p_ih

Provers.ring_reduce.Mdevelop_9 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Minus (Mult c1 c2) (Mult c1 c3))
  exact (Minus (Mult c1 r_ih_e21) (Mult c1 r_ih_e22))
  mrefine dist_minus 
  mrefine set_eq_undec_refl 
  mrefine Minus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih_e21
  mrefine set_eq_undec_refl 
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_8 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult c1 c2) (Mult c1 c3))
  exact (Plus (Mult c1 r_ih_e21) (Mult c1 r_ih_e22))
  mrefine Mult_dist
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact p_ih_e21
  mrefine set_eq_undec_refl
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_7 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Mult_preserves_equiv 
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_6 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  exact p_ih

Provers.ring_reduce.Mdevelop_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult c1 (Minus c2 c3))
  exact (Minus (Mult c1 c2) (Mult c1 c3))
  mrefine set_eq_undec_refl
  mrefine Minus_preserves_equiv 
  mrefine eq_preserves_eq 
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact (Mult c1 (Plus c2 (Neg c3)))
  exact (Plus (Mult c1 c2) (Neg (Mult c1 c3)))
  mrefine Mult_preserves_equiv 
  mrefine Minus_simpl 
  mrefine eq_preserves_eq 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine Minus_simpl 
  exact (Mult c1 (Plus c2 (Neg c3)))
  exact (Plus (Mult c1 c2) (Mult c1 (Neg c3)))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  mrefine Mult_dist
  exact p_ih_e21
  exact p_ih_e22
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine lemmaRing1

Provers.ring_reduce.Mdevelop_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult c1 (Plus c2 c3))
  exact (Plus (Mult c1 c2) (Mult c1 c3))
  mrefine set_eq_undec_refl
  mrefine Plus_preserves_equiv 
  mrefine Mult_dist
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym
  exact p_ih_e21
  exact p_ih_e22

Provers.ring_reduce.Mdevelop_3 = proof
  intros
  mrefine Neg_preserves_equiv 
  exact p_ih 

Provers.ring_reduce.Mdevelop_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact p_ih1
  exact p_ih2

Provers.ring_reduce.Mcode_reduceCG_andDecode_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact c2
  exact c4
  exact pEncode 
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact c3
  exact c4
  exact pReduce 
  mrefine set_eq_undec_refl 
  exact pDecode 

Provers.ring_reduce.MsimplifyWithConstant_ProdOfMon_4 = proof
  intros
  mrefine mult_preserves_equiv 
  exact p1
  exact p_ih2

Provers.ring_reduce.MsimplifyWithConstant_ProdOfMon_3 = proof
  intros
  mrefine mult_preserves_equiv 
  exact p1
  exact p_ih2 

Provers.ring_reduce.MsimplifyWithConstant_ProdOfMon_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (mult setAndMult r1 c_prod)
  exact Zero
  mrefine mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact p1
  mrefine set_eq_undec_refl 
  exact (mult setAndMult Zero c_prod)
  exact Zero
  mrefine mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact (proofZero c_prod)
  exact prEqualZero 
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MsimplifyWithConstant_ProdOfMon_1 = proof
  intros
  exact p1

Provers.ring_reduce.MsimplifyWithConstant_Monomial_5 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MsimplifyWithConstant_Monomial_4 = proof
  intros
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MsimplifyWithConstant_Monomial_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (mult setAndMult One c_prod)
  exact c_prod
  mrefine mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact (proofOne c_prod)
  exact prEqualOne 
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MsimplifyWithConstant_Monomial_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (mult setAndMult Zero c_prod)
  exact Zero
  mrefine mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine proofZero 
  exact c_prod
  exact prEqualZero 
  mrefine set_eq_undec_refl 

Provers.ring_reduce.MsimplifyWithConstant_Monomial_1 = proof
  intros
  mrefine set_eq_undec_refl
  
Provers.ring_reduce.Mring_reduce_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact r_1
  exact r_8
  exact p_1
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_2
  exact r_8
  exact p_2
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_3
  exact r_8
  exact p_3
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_4
  exact r_8
  exact p_4
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_5
  exact r_8
  exact p_5
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_6
  exact r_8
  exact p_6
  mrefine set_eq_undec_refl 
  mrefine eq_preserves_eq 
  exact r_7
  exact r_8
  exact p_7
  mrefine set_eq_undec_refl 
  exact p_8  
  
Provers.ring_reduce.MbuildProofRing = proof
  intros
  refine Just
  mrefine eq_preserves_eq 
  exact c1
  exact c2
  exact lp
  exact rp
  exact e1_equiv_e2   