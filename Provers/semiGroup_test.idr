-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File semiGroup_test.idr
-- test the normalization for semiGroup
-------------------------------------------------------------------

module Provers.semiGroup_test

import Data.Vect
import Data.Fin
import Provers.globalDef
import Provers.dataTypes
import Provers.tools
import Provers.semiGroup_reduce
import Provers.magma_test


instance SemiGroup Nat where
    Plus_assoc c1 c2 c3 = sym (plusAssociative c1 c2 c3)


test1' : (x:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x] (2 + (3 + x))
test1' x = PlusSG _ _ (ConstSG _ _ _ _ 2) (PlusSG _ _ (ConstSG _ _ _ _ 3) (VarSG _ _ _ (RealVariable _ _ _ _ FZ)))

test2' : (x:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x] (5 + x)
test2' x = PlusSG _ _ (PlusSG _ _ (ConstSG _ _ _ _ 2) (ConstSG _ _ _ _ 3)) (VarSG _ _ _ (RealVariable _ _ _ _ FZ))

test3' : (x:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x] (5 + x)
test3' x = PlusSG _ _ (ConstSG _ _ _ _ 5) (VarSG _ _ _ (RealVariable _ _ _ _ FZ))

test4' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] ((x + (1+1)) + (2 + y))
test4' x y = (PlusSG _ _ (PlusSG _ _ (VarSG _ _ _ (RealVariable _ _ _ _ FZ))
                                 (PlusSG _ _ (ConstSG _ _ _ _ 1) (ConstSG _ _ _ _ 1)))
                       (PlusSG _ _ (ConstSG _ _ _ _ 2) (VarSG _ _ _ (RealVariable _ _ _ _ (FS FZ)))))
             
test5' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] (x + (4 + y))
test5' x y = PlusSG _ _ (VarSG _ _ _ (RealVariable _ _ _ _ FZ)) (PlusSG _ _ (ConstSG _ _ _ _ 4) (VarSG _ _ _ (RealVariable _ _ _ _ (FS FZ))))
             
-- Normalisation of 2 + (3 + x) that should give 5 + x this time, since now we are working with semiGroup
compare_test1'_test3' : (x:Nat) -> Maybe (2 + (3 + x) = 5 + x)
compare_test1'_test3' x = semiGroupDecideEq (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (test1' x) (test3' x)

-- Later, we will have a real tactic which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
test : (x:Nat) -> (2 + (3 + x) = 5 + x)
test x = let (Just ok) = compare_test1'_test3' x in ok
-- WORKS FOR ALL X !!


-- SECOND TEST : WE NORMALIZE TEST4' AND TEST5'

{-
get_r : {pr: SemiGroup c} -> {r1:c} -> (r ** (ExprSG pr neg [x, y] r, r1=r)) -> c
get_r (r ** (e, p)) = r

pre_get_e : {pr: SemiGroup c} -> {r1:c} -> (r ** (ExprSG pr neg [x, y] r, r1=r)) -> ExprSG pr neg [x, y] r
pre_get_e (r ** (e, p)) = e

get_e : {pr: SemiGroup c} -> {r1:c} -> (big:(r ** (ExprSG pr neg [x, y] r, r1=r))) -> ExprSG pr neg [x, y] (get_r big)
get_e (r ** (e, p)) = e
-}


-- Result of the automatic equality solver for test4' and test5'
secondTest : (x:Nat) -> (y:Nat) -> (((x + (1+1)) + (2 + y)) = (x + (4 + y)))
secondTest x y = let (Just ok) = semiGroupDecideEq (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (test4' x y) (test5' x y) in ok
-- RESULT : WORKS  FOR ALL X AND Y !


-- Code to debug secondTest
print_test4'_norm : Nat -> Nat -> String
print_test4'_norm = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce  (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (test4' x y)))))

print_test5'_norm : Nat -> Nat -> String
print_test5'_norm = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce  (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (test5' x y)))))


-- new test

new_a : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] (x + 4)
new_a x y = PlusSG _ _ (VarSG _ _ _ (RealVariable _ _ _ _ FZ)) (ConstSG _ _ _ _ 4)

newTest_a : (x:Nat) -> (y:Nat) -> (x+4 = x+4)
newTest_a x y = let (Just ok) = semiGroupDecideEq (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (new_a x y) (new_a x y) in ok
-- ok


new_b : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] (4 + y)
new_b x y = PlusSG _ _ (ConstSG _ _ _ _ 4) (VarSG _ _ _ (RealVariable _ _ _ _ (FS FZ)))

newTest_b : (x:Nat) -> (y:Nat) -> (4+y = 4+y)
newTest_b x y = let (Just ok) = semiGroupDecideEq (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (new_b x y) (new_b x y) in ok
-- ok


new_c : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] (x + (4 + y))
new_c x y = PlusSG _ _ (VarSG _ _ _ (RealVariable _ _ _ _ FZ)) 
                    (PlusSG _ _ (ConstSG _ _ _ _ 4) (VarSG _ _ _ (RealVariable _ _ _ _ (FS FZ))))
            
new_d : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) (FakeSetAndMult (semiGroup_to_set (%instance))) [x, y] (x + (4 + y))
new_d x y = PlusSG _ _ (VarSG _ _ _ (RealVariable _ _ _ _ FZ)) 
                    (PlusSG _ _ (ConstSG _ _ _ _ 4) (VarSG _ _ _ (RealVariable _ _ _ _ (FS FZ))))
            
newTest_c_d : (x:Nat) -> (y:Nat) -> (x+(4+y) = x+(4+y))
newTest_c_d x y = let (Just ok) = semiGroupDecideEq (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (new_c x y) (new_d x y) in ok
-- ok


print_test_c : Nat -> Nat -> String
print_test_c = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce (%instance) (FakeSetAndNeg (semiGroup_to_set _)) (new_c x y)))))
-- ok, as expected


{-
but_they_are_equal : (x:Nat) -> (y:Nat) -> Maybe (left (rightDep (semiGroupReduce (%instance) (test4' x y))) = (left (rightDep (semiGroupReduce (%instance) (test5' x y)))))
but_they_are_equal = \x => \y => exprSG_eq {c=Nat} (%instance) _ _ (left (rightDep (semiGroupReduce (%instance) (test4' x y)))) (left (rightDep (semiGroupReduce (%instance) (test5' x y))))
-}







