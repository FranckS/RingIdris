-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File testZZ.idr
-- Contain a test with ZZ (relatives number)
-------------------------------------------------------------------

module testZZ

import Prelude.Vect
import Data.ZZ
import globalDef
import tools
import dataTypes
import reduceForCR


-- A simple test for the typeclass hierarchy
instance ZeroPlus ZZ where
    Zero = Pos O
    Plus x y = plusZ x y

        
instance {- ZeroPlus Nat => -} dataTypes.Group ZZ where
    Plus_assoc x y z = ?Mplus_assoc_ZZ -- Will use the lemma plusAssociative
    Plus_neutral x = (?Mplus_neutral_ZZ_1, ?Mplus_neutral_ZZ_2)
    
    Plus_inverse (Pos O) = ((Pos O) ** (?Mplus_inverse_ZZ_1, ?Mplus_inverse_ZZ_2)) -- PB HERE : What is this weird problem that prevent from reducing (plus O O) to O ???? 
    Plus_inverse (Pos (S x)) = ((NegS x) **(?Mplus_inverse_ZZ_3, ?Mplus_inverse_ZZ_4)) 
    Plus_inverse (NegS O) = ((Pos (S O)) ** (?Mplus_inverse_ZZ_5, ?Mplus_inverse_ZZ_6)) -- Because (negS O) denotes -1, and -(-1) = +1
    Plus_inverse (NegS (S x)) = ((Pos (S (S x))) ** (?Mplus_inverse_ZZ_7, ?Mplus_inverse_ZZ_8))
    
    --Plus_inverse x = (?MV ** (?Mplus_inverse_ZZ_1, ?Mplus_inverse_ZZ_2))
    
instance CommutativeGroup ZZ where
    Plus_comm x y = ?Mplus_comm_nat

instance OneMult ZZ where
    One = Pos (S O)
    Mult x y = multZ x y
    
instance dataTypes.Ring ZZ where
    Mult_assoc x y z = ?Mmult_assoc_ZZ    
    Mult_dist x y z = ?Mmult_dist_ZZ
    Mult_dist_2 x y z = ?Mmult_dist_ZZ_2
    Mult_neutral x = (?Mmult_neutral_ZZ_1, ?Mmult_neutral_ZZ_2)
    
instance CommutativeRing ZZ where
    Mult_comm x y = ?Mmult_comm_ZZ


test1 : ExprCR (%instance) [Pos O, Pos (S O)] (Pos O) 
test1 = VarCR _ fZ

test2 : ExprCR (%instance) [Pos O, Pos (S O)] (Pos (S O))
test2 = VarCR _ (fS fZ)

test3 : ExprCR (%instance) [Pos O, Pos (S O)] (Pos (S O))
test3 = PlusCR (PlusCR test1 test2) (ConstCR _ (Pos O)) -- Previously ZeroCR (when it was with zero and one instead of a general constant)


-- Test of a development
-------------------------
-- The original expression
test_e1 : ExprR (%instance) [Pos O, Pos (S O), Pos (S (S O))] (Pos O) 
-- The expression is Mult (Plus x (Mult y (Plus 0 0)) z
test_e1 = MultR (PlusR (VarR _ fZ) (MultR (VarR _ (fS fZ)) (PlusR (ConstR _ (Pos O)) (ConstR _ (Pos O))))) (VarR _ (fS (fS fZ)))
-- Printed
test_e1_print : String
test_e1_print = print_ExprR show test_e1



-- Function for printing the result of a transformation
print_transform : {c1:ZZ} -> {c2:ZZ} -> {g:Vect n ZZ} -> (c2 ** (ExprR (%instance) g c2, c1=c2)) -> String
print_transform (val**(exp,pr)) = print_ExprR show exp -- WHY IMPOSSIBLE TO NAME "pr" BY "proof" ???

-- And now, the expression developped, printed
test_e1_dev_print : String
--test_e1_dev_print = print_transform (develop test_e1)





testZZ.Mplus_assoc_ZZ = proof {
  intros;
  compute;
  mrefine sym;
  mrefine plusAssociativeZ;
}

testZZ.Mplus_neutral_ZZ_1 = proof {
  intros;
  compute;
  mrefine sym;
  mrefine plusCommutativeZ;
}

testZZ.Mplus_neutral_ZZ_2 = proof {
  intros;
  compute;
  mrefine plusZeroRightNeutralZ;
}

testZZ.Mplus_inverse_ZZ_1 = proof {
  intros;
  compute;
  trivial;
}












