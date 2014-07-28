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

-- --------------------------------------------------------------
-- TEST 3 : Test if ((u + (x + (-y)))) + ((-x + z) + y) = z + u
-- --------------------------------------------------------------
expD : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> ExprCG (%instance) [x, y, z, u] (((u + (x + (Neg y)))) + ((-x + z) + y))
expD x y z u = PlusCG 
            (PlusCG
                (VarCG _ (RealVariable _ _ _ fZ))
                (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) (NegCG (VarCG _ (RealVariable _ _ _ (fS (fS fZ)))))))
            (PlusCG
                (PlusCG (NegCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ)))))) (VarCG _ (RealVariable _ _ _ (fS fZ))))
                (VarCG _ (RealVariable _ _ _ (fS (fS fZ)))))

 
expE : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> ExprCG (%instance) [x, y, z, u] (z + u)
expE x y z y = PlusCG
                (VarCG _ (RealVariable _ _ _ (fS fZ)))
                (VarCG _ (RealVariable _ _ _ fZ))


compare_expD_expE : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> Maybe (((u + (x + (-y)))) + ((-x + z) + y) = z + u)
compare_expD_expE x y z u = commutativeGroupDecideEq (%instance) (expD x y z u) (expE x y z u) 

-- Later, we will have a real tactic "CommutativeGroup" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_expD_expE : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> (((u + (x + (-y)))) + ((-x + z) + y) = z + u)
proof_expD_expE x y z u = let (Just ok) = compare_expD_expE x y z u in ok
-- RESULT : Ok, works for all x !

{-
-- Debugging

expD' : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> ExprCG (%instance) [x, y, z, u] (leftDep (commutativeGroupReduce _ (expD x y z u)))
expD' x y z u = left (rightDep (commutativeGroupReduce _ (expD x y z u)))

-- Use this to test : \x => \y =>  \z =>  \u => print_ExprCG show (expD' x y z u)

expE' : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (u:ZZ) -> ExprCG (%instance) [x, y, z, u] (leftDep (commutativeGroupReduce _ (expE x y z u)))
expE' x y z u = left (rightDep (commutativeGroupReduce _ (expE x y z u)))
-}






