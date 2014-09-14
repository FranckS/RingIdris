-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commRing_reduce.idr
-- Reduce a term of a commutative ring
-------------------------------------------------------------------

module commRing_reduce

import dataTypes
import develop


-- Call all the functions (develop, ...) in the correct order
CR_reduce : {p:CommutativeRing c} -> {g:Vect n c} -> {c1:c} -> (ExprCR p g c1) -> (c2 ** (ExprCR p g c2, c1=c2))
--reduceForCR ZeroE = (Zero ** (ZeroE, refl))
