-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_test.idr
-- test the normalization for group
-------------------------------------------------------------------

module Solver.group_test

import Prelude.Vect
import Solver.globalDef
import Solver.dataTypes
import Solver.group_reduce
import Solver.monoid_reduce
import Solver.monoid_test
import Solver.magma_test
--import Data.ZZ


instance dataTypes.Set ZZ where
    set_eq x y with (decEq x y)
        set_eq x x | Yes refl = Just refl
        set_eq x y | _ = Nothing

instance Magma ZZ where
    Plus x y = x + y 
    
instance SemiGroup ZZ where
    Plus_assoc c1 c2 c3 = sym (plusAssociativeZ c1 c2 c3)    
        
 
instance ZeroC ZZ where
    Zero = Pos Z

instance dataTypes.Monoid ZZ where
    Plus_neutral_1 c = plusZeroLeftNeutralZ c
    
    Plus_neutral_2 c = plusZeroRightNeutralZ c
 
instance dataTypes.NegMinus ZZ where
    Neg x = -x
    Minus x y = x - y

    
plus_Z_simpl : (x:ZZ) -> (y:ZZ) -> (x - y = x + (-y))
plus_Z_simpl x (Pos Z) = refl
plus_Z_simpl x (Pos (S x)) = refl
plus_Z_simpl x (NegS Z) = refl
plus_Z_simpl x (NegS (S x)) = refl

minusNat_Z_Zero : (x:Nat) -> (minusNatZ x x = Pos Z)
minusNat_Z_Zero Z = refl
minusNat_Z_Zero (S px) = minusNat_Z_Zero px

plus_inverse : (x:ZZ) -> (Plus x (Neg x) = Pos Z, Plus (Neg x) x = the ZZ (Pos Z))
plus_inverse (Pos Z) = (refl, refl)
plus_inverse (Pos (S px)) = (minusNat_Z_Zero px, minusNat_Z_Zero px)
plus_inverse (NegS Z) = (refl, refl)
plus_inverse (NegS (S py)) = (minusNat_Z_Zero py, minusNat_Z_Zero py)


    
instance dataTypes.Group ZZ where
    Minus_simpl x y = plus_Z_simpl x y --Minus c1 c2 = Plus c1 (Neg c2) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse x = plus_inverse x --hasSymmetric c (%instance) c1 (Neg c1) -- Every element 'x' has a symmetric which is (Neg x)    
    
    

				 
-- ----------------------
-- TEST 1 THAT SHOULD WORK
-- ----------------------
termC : (x:ZZ) -> ExprG (%instance) [x] ((2 + (0-2))+x)
termC x = PlusG (PlusG (ConstG _ _ (Pos 2))
                                         (MinusG (ConstG _ _ (Pos 0)) (ConstG _ _ (Pos 2))))
				(VarG _ (RealVariable _ _ _ fZ))

termD : (x:ZZ) -> ExprG (%instance) [x] x
termD x = VarG _ (RealVariable _ _ _ fZ)


-- Normalisation of ((2 + (0-2))+x) that should give x, since now we are working on a group
compare_termC_termD : (x:ZZ) -> Maybe (((2 + (0-2))+x) = x)
compare_termC_termD x = groupDecideEq (%instance) (termC x) (termD x) 

-- Later, we will have a real tactic "Group" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_termC_termD : (x:ZZ) -> (((2 + (0-2))+x) = x)
proof_termC_termD x = let (Just ok) = compare_termC_termD x in ok
-- RESULT : WORKS FOR ALL X !
  

termE : (x:ZZ) -> ExprG (%instance) [x] ((3 + (0-2))+x)
termE x = PlusG (PlusG (ConstG _ _ (Pos 3))
                           (MinusG (ConstG _ _ (Pos 0)) (ConstG _ _ (Pos 2))))
                  (VarG _ (RealVariable _ _ _ fZ))

termF : (x:ZZ) -> ExprG (%instance) [x] (1+x)
termF x = PlusG (ConstG _ _ (Pos 1)) (VarG _ (RealVariable _ _ _ fZ))


termG : (x:ZZ) -> ExprG (%instance) [x] x
termG x = VarG _ (RealVariable _ _ _fZ)

-- ----------------------
-- TEST 2 THAT SHOULD WORK
-- ----------------------
-- Normalisation of ((2 + (0-2))+x) that should give (1+x), since now we are working on a group
compare_termE_termF : (x:ZZ) -> Maybe (((3 + (0-2))+x) = (1+x))
compare_termE_termF x = groupDecideEq (%instance) (termE x) (termF x) 

-- Later, we will have a real tactic "Group" which can fail...
proof_termE_termF : (x:ZZ) -> (((3 + (0-2))+x) = (1+x))
proof_termE_termF x = let (Just ok) = compare_termE_termF x in ok
-- RESULT : WORKS FOR ALL X !

print_termE_norm : ZZ -> String
print_termE_norm = (\x => print_ExprG show (left (rightDep (groupReduce  (%instance) (termE x)))))

print_termF_norm : ZZ -> String
print_termF_norm = (\x => print_ExprG show (left (rightDep (groupReduce  (%instance) (termF x)))))

-- ----------------------
-- TEST 3 THAT SHOULD FAIL
-- ----------------------
-- Normalisation of ((2 + (0-2))+x) that should NOT give x, since now we are working on a group
compare_termE_termG : (x:ZZ) -> Maybe (((3 + (0-2))+x) = x)
compare_termE_termG x = groupDecideEq (%instance) (termE x) (termG x) 

-- Later, we will have a real tactic "Group" which can fail...
proof_termE_termG : (x:ZZ) -> (((3 + (0-2))+x) = x)
proof_termE_termG x = let (Just ok) = compare_termE_termG x in ok
-- RESULT : WORKS FOR ALL X (CAREFUL, it works because it gives Nothing : the two things are NOT equal here!)


-- ----------------------
-- TEST 4 THAT SHOULD WORK
-- ----------------------

termH : (x:ZZ) -> ExprG (%instance) [x] ((-2 + (0 + (-(-2)))) + x)
termH x = PlusG (PlusG (NegG (ConstG _ _ (Pos 2)))
                           (PlusG (ConstG _ _ (Pos 0)) (NegG (NegG (ConstG _ _ (Pos 2))))))
                  (VarG _ (RealVariable _ _ _ fZ))


-- Reminder : termG represents just "x"

compare_termH_termG : (x:ZZ) -> Maybe (((-2 + (0 + (-(-2)))) + x) = x)
compare_termH_termG x = groupDecideEq (%instance) (termH x) (termG x) 

-- Later, we will have a real tactic "Group" which can fail...
proof_termH_termG : (x:ZZ) -> (((-2 + (0 + (-(-2)))) + x) = x)
proof_termH_termG x = let (Just ok) = compare_termH_termG x in ok
-- RESULT : WORKS FOR ALL X !


-- ----------------------
-- TEST 5 THAT SHOULD WORK
-- ----------------------


-- Test for (e1 + e2) + -e3 when e2 = e3. It then gives e1.
-- Here : e1 - y
--        e2 = ((3 + (0-2))+x)
--        e3 = 1+x
termJ : (x:ZZ) -> (y:ZZ)-> ExprG (%instance) [x, y] ((y + ((3 + (0-2))+x)) + (-(1+x)))
termJ x y = PlusG (PlusG (VarG _ (RealVariable _ _ _ (fS fZ))) 
                             (PlusG (PlusG (ConstG _ _ (Pos 3))
                                               (MinusG (ConstG _ _ (Pos 0)) (ConstG _ _ (Pos 2))))
                                      (VarG _ (RealVariable _ _ _ fZ))))
                    (NegG (PlusG (ConstG _ _ (Pos 1)) (VarG _ (RealVariable _ _ _ fZ))))


termK : (x:ZZ) -> (y:ZZ)-> ExprG (%instance) [x, y] y
termK x y = VarG _ (RealVariable _ _ _ (fS fZ))

termL :  (x:ZZ) -> (y:ZZ)-> ExprG (%instance) [x, y] ((y + (1+x)) + (-(1+x)))
termL x y = PlusG (PlusG (VarG _ (RealVariable _ _ _ (fS fZ))) 
                             (PlusG (ConstG _ _ (Pos 1))
                                      (VarG _ (RealVariable _ _ _ fZ))))
                    (NegG (PlusG (ConstG _ _ (Pos 1)) (VarG _ (RealVariable _ _ _ fZ))))

compare_termJ_termK : (x:ZZ) -> (y:ZZ) -> Maybe (((y + ((3 + (0-2))+x)) + (-(1+x))) = y)
compare_termJ_termK x y = groupDecideEq (%instance) (termJ x y) (termK x y) 

-- Later, we will have a real tactic "Group" which can fail...
-- A quite complicated example
proof_termJ_termK : (x:ZZ) -> (y:ZZ) -> (((y + ((3 + (0-2))+x)) + (-(1+x))) = y)
proof_termJ_termK x y = let (Just ok) = compare_termJ_termK x y in ok
-- RESULT : WORKS FOR ALL X AND Y !


-- Old stuff for debugging, no longer needed

-- A)

compare_termJ_termL : (x:ZZ) -> (y:ZZ) -> Maybe (((y + ((3 + (0-2))+x)) + (-(1+x))) = ((y + (1+x)) + (-(1+x))))
compare_termJ_termL x y = groupDecideEq (%instance) (termJ x y) (termL x y) 

-- Later, we will have a real tactic "Group" which can fail...
proof_termJ_termL : (x:ZZ) -> (y:ZZ) -> (((y + ((3 + (0-2))+x)) + (-(1+x))) = ((y + (1+x)) + (-(1+x))))
proof_termJ_termL x y = let (Just ok) = compare_termJ_termL x y in ok
-- OK

-- B)

-- get the "real value"
{-
getC : {c:Type} -> {p:dataTypes.Group c} -> {n:Nat} -> {g:Vect n c} -> (ExprG p g c1) -> c
getC (ConstG p c1) = c1
getC (PlusG e1 e2) = Plus (getC e1) (getC e2)
getC (MinusG e1 e2) = Minus (getC e1) (getC e2)
getC (NegG e) = Neg (getC e)
getC (VarG p i b) = (index i g)
-}


{-
termJ_norm : (x:ZZ) -> (y:ZZ) -> (n2 ** (g2 ** (c1 ** ((((ExprG {n=2} (%instance) [x, y] c1)), (((y + ((3 + (0-2))+x)) + (-(1+x))) = c1)), SubSet [x,y] g2))))
termJ_norm x y = groupReduce _ _ [x, y] (termJ x y)
-}










