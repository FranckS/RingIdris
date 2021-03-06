-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File group_test.idr
-- test the normalization for group
-------------------------------------------------------------------

module Provers.group_test

import Data.ZZ
import Data.Vect
import Data.Fin

import Provers.globalDef
import Provers.dataTypes
import Provers.tools
import Provers.group_reduce
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test


%access public export


implementation dataTypes.Set ZZ where
    -- The relation is just the equality
    (~=) x y = (x=y)

    set_eq x y with (decEq x y)
        set_eq x x | Yes Refl = Just Refl
        set_eq x y | _ = Nothing
    
    set_eq_undec_refl x = Refl
    set_eq_undec_sym p = sym p
    set_eq_undec_trans p1 p2 = rewrite p1 in rewrite p2 in Refl

implementation Magma ZZ where
    Plus x y = x + y 
    
    Plus_preserves_equiv p1 p2 = ?MPlusZZ_preserves_equiv_1
    
implementation SemiGroup ZZ where
    Plus_assoc c1 c2 c3 = sym (plusAssociativeZ c1 c2 c3)    

implementation dataTypes.Monoid ZZ where
    Zero = Pos Z
    
    Plus_neutral_1 c = plusZeroLeftNeutralZ c
    
    Plus_neutral_2 c = plusZeroRightNeutralZ c
 

    
plus_Z_simpl : (x:ZZ) -> (y:ZZ) -> (x - y = x + (-y))
plus_Z_simpl x (Pos Z) = Refl
plus_Z_simpl x (Pos (S y)) = Refl
plus_Z_simpl x (NegS Z) = Refl
plus_Z_simpl x (NegS (S y)) = Refl

minusNat_Z_Zero : (x:Nat) -> (minusNatZ x x = Pos Z)
minusNat_Z_Zero Z = Refl
minusNat_Z_Zero (S px) = minusNat_Z_Zero px

plus_inverse : (x:ZZ) -> (x + (- x) = Pos Z, (- x) + x = the ZZ (Pos Z))
plus_inverse (Pos Z) = (Refl, Refl)
plus_inverse (Pos (S px)) = (minusNat_Z_Zero px, minusNat_Z_Zero px)
plus_inverse (NegS Z) = (Refl, Refl)
plus_inverse (NegS (S py)) = (minusNat_Z_Zero py, minusNat_Z_Zero py)


    
implementation dataTypes.Group ZZ where
    Neg x = -x
    Minus x y = x - y
    
    Neg_preserves_equiv p = ?MNeg_preserves_equiv_1
    
    Minus_simpl x y = plus_Z_simpl x y --Minus c1 c2 = Plus c1 (Neg c2) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse x = plus_inverse x --hasSymmetric c (%instance) c1 (Neg c1) -- Every element 'x' has a symmetric which is (Neg x)    
    
    


-- ----------------------
-- TEST 1 THAT SHOULD WORK
-- ----------------------
termC : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] ((2 + (0-2))+x)
termC x = PlusG _ (PlusG _ (ConstG _ _ _ (Pos 2))
                                         (MinusG _ (ConstG _ _ _ (Pos 0)) (ConstG _ _ _ (Pos 2))))
				(VarG _ _ (RealVariable _ _ _ _ FZ))

termD : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] x
termD x = VarG _ _ (RealVariable _ _ _ _ FZ)


-- Normalisation of ((2 + (0-2))+x) that should give x, since now we are working on a group
compare_termC_termD : (x:ZZ) -> Maybe (((2 + (0-2))+x) = x)
compare_termC_termD x = groupDecideEq (%instance) (termC x) (termD x) 

-- Later, we will have a real tactic "Group" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_termC_termD : (x:ZZ) -> (((2 + (0-2))+x) = x)
proof_termC_termD x = let (Just ok) = compare_termC_termD x in ok
-- RESULT : WORKS FOR ALL X !
  

termE : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] ((3 + (0-2))+x)
termE x = PlusG _ (PlusG _ (ConstG _ _ _ (Pos 3))
                           (MinusG _ (ConstG _ _ _ (Pos 0)) (ConstG _ _ _ (Pos 2))))
                  (VarG _ _ (RealVariable _ _ _ _ FZ))

termF : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] (1+x)
termF x = PlusG _ (ConstG _ _ _ (Pos 1)) (VarG _ _ (RealVariable _ _ _ _ FZ))


termG : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] x
termG x = VarG _ _ (RealVariable _ _ _ _ FZ)



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
print_termE_norm = (\x => print_ExprG show (left (rightDep (groupReduce (%instance) (termE x)))))

print_termF_norm : ZZ -> String
print_termF_norm = (\x => print_ExprG show (left (rightDep (groupReduce (%instance) (termF x)))))

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

termH : (x:ZZ) -> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x] ((-2 + (0 + (-(-2)))) + x)
termH x = PlusG _ (PlusG _ (NegG _ (ConstG _ _ _ (Pos 2)))
                           (PlusG _ (ConstG _ _ _ (Pos 0)) (NegG _ (NegG _ (ConstG _ _ _ (Pos 2))))))
                  (VarG _ _ (RealVariable _ _ _ _ FZ))


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
termJ : (x:ZZ) -> (y:ZZ)-> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x, y] ((y + ((3 + (0-2))+x)) + (-(1+x)))
termJ x y = PlusG _ (PlusG _ (VarG _ _ (RealVariable _ _ _ _ (FS FZ))) 
                             (PlusG _ (PlusG _ (ConstG _ _ _ (Pos 3))
                                               (MinusG _ (ConstG _ _ _ (Pos 0)) (ConstG _ _ _ (Pos 2))))
                                      (VarG _ _ (RealVariable _ _ _ _ FZ))))
                    (NegG _ (PlusG _ (ConstG _ _ _ (Pos 1)) (VarG _ _ (RealVariable _ _ _ _ FZ))))


termK : (x:ZZ) -> (y:ZZ)-> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x, y] y
termK x y = VarG _ _ (RealVariable _ _ _ _ (FS FZ))

termL :  (x:ZZ) -> (y:ZZ)-> ExprG (%instance) (FakeSetAndMult (group_to_set (%instance))) [x, y] ((y + (1+x)) + (-(1+x)))
termL x y = PlusG _ (PlusG _ (VarG _ _ (RealVariable _ _ _ _ (FS FZ))) 
                             (PlusG _ (ConstG _ _ _ (Pos 1))
                                      (VarG _ _ (RealVariable _ _ _ _ FZ))))
                    (NegG _ (PlusG _ (ConstG _ _ _ (Pos 1)) (VarG _ _ (RealVariable _ _ _ _ FZ))))

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
getC (ConstG _ p c1) = c1
getC (PlusG _ e1 e2) = Plus (getC e1) (getC e2)
getC (MinusG _ e1 e2) = Minus (getC e1) (getC e2)
getC (NegG _ e) = Neg (getC e)
getC (VarG _ p i b) = (index i g)
-}


{-
termJ_norm : (x:ZZ) -> (y:ZZ) -> (n2 ** (g2 ** (c1 ** ((((ExprG {n=2} (%instance) [x, y] c1)), (((y + ((3 + (0-2))+x)) + (-(1+x))) = c1)), SubSet [x,y] g2))))
termJ_norm x y = groupReduce _ _ [x, y] (termJ x y)
-}




---------- Proofs ----------  
Provers.group_test.MPlusZZ_preserves_equiv_1 = proof
  intros
  rewrite p1
  rewrite p2
  exact Refl

Provers.group_test.MNeg_preserves_equiv_1 = proof
  intros
  rewrite p
  exact Refl

  
