-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_reduce.idr
-- Normalize an expression reflecting an element in a commutative monoid
-------------------------------------------------------------------

module commutativeMonoid_reduce

import Decidable.Equality
import dataTypes
import monoid_reduce
import tools
import Prelude.Vect


-- 4 FUNCTIONS WHICH ADD A TERM TO AN EXPRESSION ALREADY "SORTED" (of the right forme)
-- -----------------------------------------------------------------------------------
{-									
--%default total
-- The expression is already in the form a + (b + (c + ...)) where a,b,c can only be constants, variables, and negations of constants and variables
putVarOnPlace : {c:Type} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> {varValue:c} 
   -> (Variable (commutativeGroup_eq_as_elem_of_set p) Neg g varValue) 
   -> (c2 ** (ExprCG p g c2, Plus c1 varValue=c2))
putVarOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) (RealVariable _ _ _ i) = 
    if minusOrEqual_Fin i0 i 
        then let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
             (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?MputVarOnPlace_1))
        else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (VarCG p (RealVariable _ _ _ i0)) e), ?MputVarOnPlace_2))
putVarOnPlace p (PlusCG (ConstCG _ _ c0) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (ConstCG _ _ c0) e), ?MputVarOnPlace_3)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
        
putVarOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) (RealVariable _ _ _ i) = 
	 if minusOrEqual_Fin i0 i 
		then let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
			 (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, ?MputVarOnPlace_4))
		else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e), ?MputVarOnPlace_5))
putVarOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (NegCG (ConstCG _ _ c0)) e), ?MputVarOnPlace_6)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
-- Basic cases : cases without Plus
putVarOnPlace p (ConstCG _ _ c0) (RealVariable _ _ _ i) = (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (ConstCG _ _ c0), ?MputVarOnPlace_7))
putVarOnPlace p (NegCG (ConstCG _ _ c0)) (RealVariable _ _ _ i) = (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (ConstCG _ _ (Neg c0)), ?MputVarOnPlace_8))
putVarOnPlace p (VarCG p (RealVariable _ _ _ i0)) (RealVariable _ _ _ i) = 
	    if minusOrEqual_Fin i0 i then (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) (VarCG p (RealVariable _ _ _ i)), refl))
		else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (VarCG p (RealVariable _ _ _ i0)), ?MputVarOnPlace_9))
putVarOnPlace p (NegCG (VarCG p (RealVariable _ _ _ i0))) (RealVariable _ _ _ i) = 
		if minusOrEqual_Fin i0 i then (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (VarCG p (RealVariable _ _ _ i)), refl))
		else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (NegCG (VarCG p (RealVariable _ _ _ i0))), ?MputVarOnPlace_10))
-}