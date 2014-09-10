-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeMonoid_test.idr
-- test the normalization for commutative monoid
-------------------------------------------------------------------

module commutativeMonoid_test

import Prelude.Vect
import globalDef
import dataTypes
import commutativeMonoid_reduce
import monoid_test -- For the instance of the level under (Monoid Nat)
--import Data.ZZ



instance dataTypes.CommutativeMonoid Nat where
    Plus_comm' x y = plusCommutative x y
