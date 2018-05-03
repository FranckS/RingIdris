-- Edwin Brady, Franck Slama
-- University of St Andrews

-- Implementation of tactics that prove equivalences in algebraic structures (Rings, Groups, Monoids, etc), written in Idris, for Idris.
-- To prove equalities over an abstract structure, we normalize both sides of the potential equality and check that these normal forms are syntactically the same.
-- The normalization is implemented following a correct-by-construction approach, enabled by a type-safe reflection mechanism.

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
-- import Provers.ring_test -- The test file for Ring is not added now (even if it works!) because of the few auxiliary lemmas about * 
			    -- needed for the definition of the instance of the typeclass Ring which aren't proven yet

import Provers.reflection



main : IO()
main = putStrLn "The collection of tactics for proving equivalences in algebraic structures seems to be ready to prove stuff!"


{-
bla : (x:Nat) -> Maybe (x+0 = x)
bla x = Just (rewrite (a_plus_zero x) in refl)
-}


---------- Proofs ----------








































































































































































































