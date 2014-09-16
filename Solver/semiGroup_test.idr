-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File semiGroup_test.idr
-- test the normalization for semiGroup
-------------------------------------------------------------------

module Solver.semiGroup_test

import Prelude.Vect
import Solver.globalDef
import Solver.dataTypes
import Solver.semiGroup_reduce
import Solver.magma_test


instance SemiGroup Nat where
    Plus_assoc c1 c2 c3 = sym (plusAssociative c1 c2 c3)


test1' : (x:Nat) -> ExprSG (%instance) (\x => x) [x] (2 + (3 + x))
test1' x = PlusSG _ (ConstSG _ _ _ 2) (PlusSG _ (ConstSG _ _ _ 3) (VarSG _ _ (RealVariable _ _ _ fZ)))

test2' : (x:Nat) -> ExprSG (%instance) (\x => x) [x] (5 + x)
test2' x = PlusSG _ (PlusSG _ (ConstSG _ _ _ 2) (ConstSG _ _ _ 3)) (VarSG _ _ (RealVariable _ _ _ fZ))

test3' : (x:Nat) -> ExprSG (%instance) (\x => x) [x] (5 + x)
test3' x = PlusSG _ (ConstSG _ _ _ 5) (VarSG _ _ (RealVariable _ _ _ fZ))

test4' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] ((x + (1+1)) + (2 + y))
test4' x y = (PlusSG _ (PlusSG _ (VarSG _ _ (RealVariable _ _ _ fZ))
                                 (PlusSG _ (ConstSG _ _ _ 1) (ConstSG _ _ _ 1)))
                       (PlusSG _ (ConstSG _ _ _ 2) (VarSG _ _ (RealVariable _ _ _ (fS fZ)))))
             
test5' : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] (x + (4 + y))
test5' x y = PlusSG _ (VarSG _ _ (RealVariable _ _ _ fZ)) (PlusSG _ (ConstSG _ _ _ 4) (VarSG _ _ (RealVariable _ _ _ (fS fZ))))
             
-- Normalisation of 2 + (3 + x) that should give 5 + x this time, since now we are working with semiGroup
compare_test1'_test3' : (x:Nat) -> Maybe (2 + (3 + x) = 5 + x)
compare_test1'_test3' x = semiGroupDecideEq (%instance) (test1' x) (test3' x)

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
secondTest x y = let (Just ok) = semiGroupDecideEq (%instance) (test4' x y) (test5' x y) in ok
-- RESULT : WORKS  FOR ALL X AND Y !


-- Code to debug secondTest
print_test4'_norm : Nat -> Nat -> String
print_test4'_norm = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce  (%instance) (test4' x y)))))

print_test5'_norm : Nat -> Nat -> String
print_test5'_norm = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce  (%instance) (test5' x y)))))


-- new test

new_a : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] (x + 4)
new_a x y = PlusSG _ (VarSG _ _ (RealVariable _ _ _ fZ)) (ConstSG _ _ _ 4)

newTest_a : (x:Nat) -> (y:Nat) -> (x+4 = x+4)
newTest_a x y = let (Just ok) = semiGroupDecideEq (%instance) (new_a x y) (new_a x y) in ok
-- ok


new_b : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] (4 + y)
new_b x y = PlusSG _ (ConstSG _ _ _ 4) (VarSG _ _ (RealVariable _ _ _ (fS fZ)))

newTest_b : (x:Nat) -> (y:Nat) -> (4+y = 4+y)
newTest_b x y = let (Just ok) = semiGroupDecideEq (%instance) (new_b x y) (new_b x y) in ok
-- ok


new_c : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] (x + (4 + y))
new_c x y = PlusSG _ (VarSG _ _ (RealVariable _ _ _ fZ)) 
                    (PlusSG _ (ConstSG _ _ _ 4) (VarSG _ _ (RealVariable _ _ _ (fS fZ))))
            
new_d : (x:Nat) -> (y:Nat) -> ExprSG (%instance) (\x => x) [x, y] (x + (4 + y))
new_d x y = PlusSG _ (VarSG _ _ (RealVariable _ _ _ fZ)) 
                    (PlusSG _ (ConstSG _ _ _ 4) (VarSG _ _ (RealVariable _ _ _ (fS fZ))))
            
newTest_c_d : (x:Nat) -> (y:Nat) -> (x+(4+y) = x+(4+y))
newTest_c_d x y = let (Just ok) = semiGroupDecideEq (%instance) (new_c x y) (new_d x y) in ok
-- ok


print_test_c : Nat -> Nat -> String
print_test_c = (\x => \y => print_ExprSG show (left (rightDep (semiGroupReduce (%instance) (new_c x y)))))
-- ok, as expected


{-
but_they_are_equal : (x:Nat) -> (y:Nat) -> Maybe (left (rightDep (semiGroupReduce (%instance) (test4' x y))) = (left (rightDep (semiGroupReduce (%instance) (test5' x y)))))
but_they_are_equal = \x => \y => exprSG_eq {c=Nat} (%instance) _ _ (left (rightDep (semiGroupReduce (%instance) (test4' x y)))) (left (rightDep (semiGroupReduce (%instance) (test5' x y))))
-}







