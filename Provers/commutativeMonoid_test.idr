-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_test.idr
-- test the normalization for commutative monoid
-------------------------------------------------------------------

module Provers.commutativeMonoid_test

import Prelude.Vect
import Provers.globalDef
import Provers.dataTypes
import Provers.commutativeMonoid_reduce
import Provers.monoid_test -- For the instance of the level under (Monoid Nat)
--import Data.ZZ



instance dataTypes.CommutativeMonoid Nat where
    Plus_comm' x y = plusCommutative x y
