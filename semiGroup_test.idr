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


test1' : (x:Nat) -> ExprSG (%instance) [x] (2 + (3 + x)) 
test1' x = PlusSG (ConstSG _ 2) (PlusSG (ConstSG _ 3) (VarSG _ fZ))

test2' : (x:Nat) -> ExprSG (%instance) [x] (5 + x)
test2' x = PlusSG (PlusSG (ConstSG _ 2) (ConstSG _ 3)) (VarSG _ fZ)

test3' : (x:Nat) -> ExprSG (%instance) [x] (5 + x)
test3' x = PlusSG (ConstSG _ 5) (VarSG _ fZ)

test4' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) [x, y] ((x + (1+1)) + (2 + y))
test4' x y = (PlusSG (PlusSG (VarSG _ fZ) 
                             (PlusSG (ConstSG _ 1) (ConstSG _ 1)))
                     (PlusSG (ConstSG _ 2) (VarSG _ (fS fZ))))
             
test5' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) [x, y] (x + (4 + y))
test5' x y = PlusSG (VarSG _ fZ) (PlusSG (ConstSG _ 4) (VarSG _ (fS fZ)))           
             
-- Normalisation of 2 + (3 + x) that should give 5 + x this time, since now we are working with semiGroup 
compare_test1'_test3' : (x:Nat) -> Maybe (2 + (3 + x) = 5 + x)
compare_test1'_test3' x = semiGroupDecideEq (%instance) [x] (test1' x) (test3' x) 

-- Later, we will have a real tactic which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
test : (x:Nat) -> (2 + (3 + x) = 5 + x)
test x = let (Just ok) = compare_test1'_test3' x in ok


-- SECOND TEST : WE NORMALIZE TEST4' AND TEST5'

get_r : {pr: SemiGroup c} -> {r1:c} -> (r ** (ExprSG pr [x, y] r, r1=r)) -> c
get_r (r ** (e, p)) = r

pre_get_e : {pr: SemiGroup c} -> {r1:c} -> (r ** (ExprSG pr [x, y] r, r1=r)) -> ExprSG pr [x, y] r
pre_get_e (r ** (e, p)) = e

get_e : {pr: SemiGroup c} -> {r1:c} -> (big:(r ** (ExprSG pr [x, y] r, r1=r))) -> ExprSG pr [x, y] (get_r big)
get_e (r ** (e, p)) = e


-- Result of normalization for test4'
test4'_norm : (x:Nat) -> (y:Nat) -> (ExprSG (%instance) [x, y] (get_r (semiGroupReduce (%instance) [x, y] (test4' x y))))
test4'_norm x y = get_e (semiGroupReduce (%instance) [x, y] (test4' x y))

test_4'_norm_print : (x:Nat) -> (y:Nat) -> String
test_4'_norm_print x y = print_ExprSG show (test4'_norm x y)


-- Result of normalization for test5'
test5'_norm : (x:Nat) -> (y:Nat) -> (ExprSG (%instance) [x, y] (get_r (semiGroupReduce (%instance) [x, y] (test5' x y))))
test5'_norm x y = get_e (semiGroupReduce (%instance) [x, y] (test5' x y))

test_5'_norm_print : (x:Nat) -> (y:Nat) -> String -- Question : how to normalize without having to instanciate the variable ? That's not nice, and not needed.
test_5'_norm_print x y = print_ExprSG show (test5'_norm x y)

-- Result of the automatic equality solver for test4' and test5'
secondTest : (x:Nat) -> (y:Nat) -> (((x + (1+1)) + (2 + y)) = (x + (4 + y)))
secondTest x y = let (Just ok) = semiGroupDecideEq (%instance) [x, y] (test4' x y) (test5' x y) in ok








