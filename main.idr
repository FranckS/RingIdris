-- Edwin Brady, Franck Slama
-- University of St Andrews

-- Implementation of a RING tactic, in Idris, for Idris.
-- To solve equalities over an abstract ring, we normalize both sides of the 
-- equality and check that their normal forms are equal (with Leibniz equality).
-- The normalization is done by using dependent types, which enable to write
-- the algorithm and the proof of correctness at the same time, and step by step

-- File main.idr
-- Implements the main
-------------------------------------------------------------------

module Main

import Solver.tools
import Solver.mathsResults
import Solver.dataTypes
import Solver.magma_reduce
import Solver.semiGroup_reduce
import Solver.monoid_reduce
import Solver.commutativeMonoid_reduce -- NEW
import Solver.group_reduce
import Solver.commutativeGroup_reduce
import Solver.ring_reduce

import Solver.magma_test
import Solver.semiGroup_test
import Solver.monoid_test
import Solver.commutativeMonoid_test
import Solver.group_test
import Solver.commutativeGroup_test




--reduceForCG : {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))

--reduceForR : {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1=c2))



main : IO()
main = putStrLn "coucou!"


{-
bla : (x:Nat) -> Maybe (x+0 = x)
bla x = Just (rewrite (a_plus_zero x) in refl)
-}


---------- Proofs ----------






























