-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File semiGroup_test.idr
-- test the normalization for semiGroup
-------------------------------------------------------------------

module semiGroup_test

import Prelude.Vect
import globalDef
import dataTypes
import semiGroup_reduce
import magma_test



instance SemiGroup Nat where
    Plus_assoc c1 c2 c3 = sym (plusAssociative c1 c2 c3)


test1' : (x:Nat) -> ExprSG (%instance) [x] (Plus 2 (Plus 3 x)) 
test1' x = PlusSG (ConstSG _ 2) (PlusSG (ConstSG _ 3) (VarSG _ fZ))

test2' : (x:Nat) -> ExprSG (%instance) [x] (Plus 5 x)
test2' x = PlusSG (PlusSG (ConstSG _ 2) (ConstSG _ 3)) (VarSG _ fZ)

test3' : (x:Nat) -> ExprSG (%instance) [x] (Plus 5 x)
test3' x = PlusSG (ConstSG _ 5) (VarSG _ fZ)


-- Normalisation of 2 + (3 + x) that should give 5 + x this time, since now we are working with semiGroup 
compare_test1'_test3' : (x:Nat) -> Maybe (2 + (3 + x) = 5 + x)
compare_test1'_test3' x = semiGroupDecideEq (%instance) [x] (test1' x) (test3' x) 



