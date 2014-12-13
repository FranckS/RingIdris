-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_test.idr
-- test the normalization for commutative monoid
-------------------------------------------------------------------

module Solver.commutativeMonoid_test

import Prelude.Vect
import Solver.globalDef
import Solver.dataTypes
import Solver.commutativeMonoid_reduce
import Solver.monoid_test -- For the instance of the level under (Monoid Nat)
--import Data.ZZ



instance dataTypes.CommutativeMonoid Nat where
    Plus_comm' x y = plusCommutative x y
