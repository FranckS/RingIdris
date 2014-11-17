-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File ring_reduce.idr
-- Normalize an expression reflecting an element in a ring
-------------------------------------------------------------------

module Solver.ring_reduce

import Decidable.Equality
import Solver.dataTypes
import Solver.commutativeGroup_reduce
import Solver.tools
import Prelude.Vect


--%logging 2
-- Should be total, but can't be asserted to be, since Idris runs into an infinite loop at typecheck with 41 patterncases
--total
develop : {c:Type} -> {p:dataTypes.Ring c} -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1~=c2))
--develop (ConstR _ _ const) = (_ ** (ConstR _ _ const, set_eq_undec_refl _))
develop (VarR p v) = (_ ** (VarR p v, set_eq_undec_refl _))
develop (PlusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (develop e1) in
  let (r_ih2 ** (e_ih2, p_ih2)) = (develop e2) in
    ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?Mdevelop_1))
develop (MinusR e1 e2) = 
  let (r_ih1 ** (e_ih1, p_ih1)) = (develop e1) in	
  let (r_ih2 ** (e_ih2, p_ih2)) = (develop e2) in
    ((Minus r_ih1 r_ih2) ** (MinusR e_ih1 e_ih2, ?Mdevelop_2))    
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
	 
	 
	
	
	
	
	
	
	
	
	
	
	

