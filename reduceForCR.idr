-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reduceForCR.idr
-- Reduce a term of a commutative ring
-------------------------------------------------------------------

module reduceForCR

import dataTypes
import develop


-- Call all the functions (develop, ...) in the correct order
reduceForCR : {p:CommutativeRing c} -> {g:Vect n c} -> {c1:c} -> (ExprCR p g c1) -> (c2 ** (ExprCR p g c2, c1=c2))
--reduceForCR ZeroE = (Zero ** (ZeroE, refl))
