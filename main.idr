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

import Provers.tools
import Provers.mathsResults
import Provers.dataTypes
import Provers.magma_reduce
import Provers.semiGroup_reduce
import Provers.monoid_reduce
import Provers.commutativeMonoid_reduce -- NEW
import Provers.group_reduce
import Provers.commutativeGroup_reduce
import Provers.ring_reduce

import Provers.magma_test
import Provers.semiGroup_test
import Provers.monoid_test
import Provers.commutativeMonoid_test
import Provers.group_test
import Provers.commutativeGroup_test
--import Provers.ring_test





main : IO()
main = putStrLn "coucou!"


{-
bla : (x:Nat) -> Maybe (x+0 = x)
bla x = Just (rewrite (a_plus_zero x) in refl)
-}


---------- Proofs ----------




































































































































































