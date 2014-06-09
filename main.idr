-- Edwin Brady, Franck Slama
-- University of St Andrews

-- Implementation of a RING tactic, in Idris, for Idris.
-- To solve equalities over an abstract ring, we normalize both sides of the 
-- equality and check that their normal forms are equal (with Leibniz equality).
-- The normalization is done by using dependent types, which enable to write
-- the algorithm and the proof of correctness at the same time, and step by step

-- File main.idr
-- Implements the main
-------------------------------------------------------------------

module Main

import tools
import mathsResults
import dataTypes
import magma_reduce
import semiGroup_reduce
import monoid_reduce
import group_reduce
--import commRing_reduce
--import testNat
--import testZZ
import magma_test
import semiGroup_test
import monoid_test
import group_test




--reduceForCG : {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))

--reduceForR : {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1=c2))



main : IO()
main = putStrLn "coucou!"



        {-
        Nat_from_Bool : Bool -> Nat
        Nat_from_Bool True = Z
        Nat_from_Bool False = (S Z)
      
        data A : (b:Bool) -> (if b then Nat else Bool) -> Nat -> Type where
            A1 : (n:Nat) -> A True n n
            A2 : (b:Bool) -> A False b (Nat_from_Bool b)
      
        g : (b1:Bool) -> (if b1 then Nat else Bool) -> Nat
        g True n = n
        g False b = Nat_from_Bool b
      
        f : (b1:Bool) -> (b2:Bool) -> (n1:Nat) -> (A b1 (if b1 then n1 else b1) (if b1 then n1 else (Nat_from_Bool b1))) -> (A b2 (if b2 then n2 else b2) (if b2 then n2 else (Nat_from_Bool b2))) -> Bool
        -}



---------- Proofs ----------




























{-
intros
rewrite (sym(switch_negS pa pb (S pc)))
-}

















































{-
intros
rewrite (sym(plusCommutativeZ (NegS (S pu)) (minusNatZ pw (S pv))))
rewrite (minusSucc pw (S pv) (S pu))
rewrite (sym(plus_succ_right pu (S pv)))
-}

















{-
intros
rewrite (plus_succ_right (plus pa 1) (S pc))
rewrite (plus_succ_left (plus pa 0) (S (S pc)))
rewrite (sym(plus_succ_left (plus pa 0) (S (S pc))))
rewrite (plus_succ_left (plus pa 0) (S (S pc)))
rewrite (plus_succ_right pa 0)
rewrite (plus_succ_left pa 0)
undo

rewrite (sym(plus_succ_left pa 0))
undo
rewrite (plus_succ_left (plus pa 0) (S (S pc)))
undo
rewrite (sym(plus_succ_left (plus pa 0) (S (S pc))))
undo
rewrite (plus_succ_left (plus pa 0) (S (S pc)))
-}












{-
((ExprMo (@@constructor of dataTypes.Group#Monoid c) (g_ih2 ++ g_ih1 ++ g) (Plus c1 c2), Plus c1 c2 = Plus c1 c2), SubSet g (g_ih2 ++ g_ih1 ++ g))
-}




{-
intros
mrefine Ex_intro
exact (x_ih2+x_ih1)
mrefine Ex_intro
exact (g_ih2++g_ih1)
mrefine Ex_intro
exact (Plus cWeak2 c2_ih2)
exact _
rewrite p_ih2
rewrite pWeak2
rewrite p_ih1
rewrite pWeak
exact ((PlusMo eWeak2 e_ih2, refl), ?MA)

-}








































































































































































































































































