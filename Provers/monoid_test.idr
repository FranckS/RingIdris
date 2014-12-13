-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File monoid_test.idr
-- test the normalization for monoid
-------------------------------------------------------------------

module Provers.monoid_test

import Prelude.Vect
import Provers.globalDef
import Provers.dataTypes
import Provers.monoid_reduce
import Provers.semiGroup_test



instance dataTypes.Monoid Nat where
    Zero = O
    
    Plus_neutral_1 c = ?M_Nat_Monoid_1
    
    Plus_neutral_2 Z = ?M_Nat_Monoid_2
    Plus_neutral_2 (S pc) = let px = Plus_neutral_2 pc in ?M_Nat_Monoid_3

a : (x:Nat) -> ExprMo (%instance) (\x => x) [x] (2 + (0 + x)) 
a x = PlusMo _ (ConstMo _ _ _ 2) (PlusMo _ (ConstMo _ _ _ 0) (VarMo _ _ (RealVariable _ _ _ FZ)))

b : (x:Nat) -> ExprMo (%instance) (\x => x) [x] (2 + x)
b x = PlusMo _ (ConstMo _ _ _ 2) (VarMo _ _ (RealVariable _ _ _ FZ))


-- Normalisation of 2 + (0 + x) that should give 2 + x, since now we are working on a monoid
compare_a_b : (x:Nat) -> Maybe (2 + (0 + x) = 2 + x)
compare_a_b x = monoidDecideEq (%instance) (a x) (b x) 

-- Later, we will have a real tactic "Monoid" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_a_b : (x:Nat) -> (2 + (0 + x) = 2 + x)
proof_a_b x = let (Just ok) = compare_a_b x in ok
-- WORKS FOR ALL X !!


---------- Proofs ----------
Provers.monoid_test.M_Nat_Monoid_1 = proof
  intro
  trivial

Provers.monoid_test.M_Nat_Monoid_2 = proof
  trivial

Provers.monoid_test.M_Nat_Monoid_3 = proof
  intros
  rewrite px
  trivial


  
  
  




