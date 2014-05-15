-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File monoid_test.idr
-- test the normalization for monoid
-------------------------------------------------------------------

module monoid_test

import Prelude.Vect
import globalDef
import dataTypes
import monoid_reduce
import semiGroup_reduce
import semiGroup_test
import magma_test


instance ZeroC Nat where
    Zero = O

instance dataTypes.Monoid Nat where
    Plus_neutral_1 c = ?M_Nat_Monoid_1
    
    Plus_neutral_2 Z = ?M_Nat_Monoid_2
    Plus_neutral_2 (S pc) = let px = Plus_neutral_2 pc in ?M_Nat_Monoid_3

aaa : (x:Nat) -> ExprMo (%instance) [x] (2 + (0 + x)) 
aaa x = PlusMo (ConstMo _ 2 True) (PlusMo (ConstMo _ 0 True) (VarMo _ fZ True))

bbb : (x:Nat) -> ExprMo (%instance) [x] (2 + x)
bbb x = PlusMo (ConstMo _ 2 True) (VarMo _ fZ True)


-- Normalisation of 2 + (0 + x) that should give 2 + x, since now we are working on a monoid
compare_aaa_bbb : (x:Nat) -> Maybe (2 + (0 + x) = 2 + x)
compare_aaa_bbb x = monoidDecideEq (%instance) [x] (aaa x) (bbb x) 

-- Later, we will have a real tactic "Monoid" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_aaa_bbb : (x:Nat) -> (2 + (0 + x) = 2 + x)
proof_aaa_bbb x = let (Just ok) = compare_aaa_bbb x in ok

---------- Proofs ----------
monoid_test.M_Nat_Monoid_1 = proof
  intro
  trivial

monoid_test.M_Nat_Monoid_2 = proof
  trivial

monoid_test.M_Nat_Monoid_3 = proof
  intros
  rewrite px
  trivial


  
  
  




