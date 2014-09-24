-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File magma_test.idr
-- test the normalization for magma
-------------------------------------------------------------------

module Solver.magma_test

import Prelude.Vect
import Solver.globalDef
import Solver.dataTypes
import Solver.magma_reduce



instance Set Nat where
    -- The relation is just the (syntactical) equality
    (~=) x y = (x = y)

    set_eq x y with (decEq x y)
        set_eq x x | Yes refl = Just refl
        set_eq x y | _ = Nothing
    
    -- proof that the relation of equality is an equivalence relation
    set_eq_undec_refl x = refl
    set_eq_undec_sym p = sym p
    set_eq_undec_trans p1 p2 = rewrite p1 in rewrite p2 in refl
    
    
instance Magma Nat where
    Plus x y = plus x y
    
    -- proof that this plus preserves the (syntactical) equality
    Plus_preserves_equiv p1 p2 = ?MPlus_preserves_equiv_1


test1 : (x:Nat) -> ExprMa (%instance) (\x =>x) [x] (Plus 2 (Plus 3 x))
test1 x = PlusMa _ (ConstMa _ _ _ 2) (PlusMa _ (ConstMa _ _ _ 3) (VarMa _ _ (RealVariable _ _ _ fZ)))

test2 : (x:Nat) -> ExprMa (%instance) (\x => x) [x] (Plus 5 x)
test2 x = PlusMa _ (PlusMa _ (ConstMa _ _ _ 2) (ConstMa _ _ _ 3)) (VarMa _ _ (RealVariable _ _ _ fZ))

test3 : (x:Nat) -> ExprMa (%instance) (\x => x) [x] (Plus 5 x)
test3 x = PlusMa _ (ConstMa _ _ _ 5) (VarMa _ _ (RealVariable _ _ _ fZ))

--First test : 2 + (3 + x) =\= 5 + x
total -- cool !
compare_test1_test3 : (x:Nat) -> Maybe (2 + (3 + x) = 5 + x)
compare_test1_test3 x = magmaDecideEq (%instance) (test1 x) (test3 x)


test1_not_equal_to_test3 : (x:Nat) -> (2 + (3 + x) = 5 + x)
test1_not_equal_to_test3 x = let (Just pr) = magmaDecideEq (%instance) (test1 x) (test3 x) in pr --A "non regression test", unfortunately not using the type checker (need to compute this term and to see if it crashs or not)
-- Should crash if we use the value !
-- AND EFECTIVELY CRASHES FOR ALL X

-- Second test : (2 + 3) + x = 5 + x
total -- cool !
compare_test2_test3 : (x:Nat) -> Maybe ((2 + 3) + x = 5 + x)
compare_test2_test3 x = magmaDecideEq (%instance) (test2 x) (test3 x)

test2_equal_test3 : (x:Nat) -> ((2 + 3) + x = 5 + x)
test2_equal_test3 = \x => let (Just pr) = magmaDecideEq (%instance) (test2 x) (test3 x) in pr --A second "non regression test", unfortunately not using the type checker (need to compute this term and to see if it crashs or not)
-- WORKS FOR ALL X !!

-- JUST A STUPID TEST TO UNDERSTAND WHAT HAPPEN IF I A CONSTANT IS IN FACT A VARIABLE 
-- Of course, it won't give the proof we want for all x (because the algorithm waits for the value of x since we're supposed to have a _constant_), 
-- but it works for specific values of x, which is what we would expect


termX : (x:Nat) -> ExprMa (%instance) (\x => x) [x] x
termX x = ConstMa _ _ _ x

total -- cool !
compare_termX_termX : (x:Nat) -> Maybe (x = x)
compare_termX_termX x = magmaDecideEq (%instance) (termX x) (termX x)

result_termX_termX : (x:Nat) -> (x = x)
result_termX_termX x = let (Just pr) = magmaDecideEq (%instance) (termX x) (termX x) in pr









