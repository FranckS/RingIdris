module commutativeGroup_test

import Prelude.Vect
import globalDef
import dataTypes
import commutativeGroup_reduce
import group_test
-- import Data.ZZ


instance dataTypes.CommutativeGroup ZZ where
    Plus_comm x y = plusCommutativeZ x y
    
    

-- x + (-x)
expA : (x:ZZ) -> ExprCG (%instance) [x] (x + (- x))
expA x = PlusCG (VarCG _ (RealVariable _ _ _ fZ)) (NegCG (VarCG _ (RealVariable _ _ _ fZ)))


-- (-x) + x
expB : (x:ZZ) -> ExprCG (%instance) [x] ((-x) + x)
expB x = PlusCG (NegCG (VarCG _ (RealVariable _ _ _ fZ))) (VarCG _ (RealVariable _ _ _ fZ))


-- 0
expC : (x:ZZ) -> ExprCG (%instance) [x] (Pos 0)
expC x = ConstCG _ _ (Pos 0)


-- ---------------------------------
-- TEST 1 : Test if x + -x = -x + x
-- ---------------------------------
-- Normalisation of (x+(-x)) that should give Zero, since now we are working on a cgroup
compare_expA_expB : (x:ZZ) -> Maybe (x + (-x) = (-x) + x)
compare_expA_expB x = commutativeGroupDecideEq (%instance) (expA x) (expB x) 

-- Later, we will have a real tactic "CommutativeGroup" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_expA_expB : (x:ZZ) -> (x + (-x) = (-x) + x)
proof_expA_expB x = let (Just ok) = compare_expA_expB x in ok
-- RESULT : Ok, works for all x !

-- ---------------------------------
-- TEST 2 : Test if x + -x = 0
-- ---------------------------------
compare_expA_expC : (x:ZZ) -> Maybe (x + (-x) = Pos 0)
compare_expA_expC x = commutativeGroupDecideEq (%instance) (expA x) (expC x)
-- RESULT : Ok, works for all x !



 
    



