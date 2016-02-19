module tests


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect
import ordering


%access public export

%default total


total
leftDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> A
leftDep (a ** b) = a


total
rightDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> B (leftDep x)
rightDep (a ** b) = b


data isSorted : {T:Type} -> (Tord : PartialOrder T) 
                 -> (l:List T) -> Type where
    NilIsSorted : {T:Type} -> (Tord : PartialOrder T) -> isSorted Tord []
    SingletonIsSorted : {T:Type} -> (Tord : PartialOrder T) -> (x:T) -> isSorted Tord [x]
    ConsSorted : {T:Type} -> {Tord : PartialOrder T} -> (h1:T) -> (h2:T) -> (t:List T) 
		 -> (isSorted Tord (h2::t)) -> ((<~=) {p=Tord} h1 h2) 
                 -> (isSorted Tord (h1::(h2::t)))
  
  
instance [nat_set] Set Nat where
  (~=) x y = (x = y)
  
  eqDec x y = decEq x y
  
  eq_refl x = Refl
  
  eq_sym p = sym p
  
  eq_trans p1 p2 = ?Mnat_set_1
  
  
  
data lowerThan : Nat -> Nat -> Type where
  -- It seems to be easier for deciding this predicate to say that 0 << x and that (px < py) -> (S px < S py)
  -- than saying that (x < S px) (lower than the value immediately after) and that (x < py) -> (x << S py)
  ZeroLowerAll : (pn:Nat) -> lowerThan Z (S pn)
  LowerSucc : {px:Nat} -> {py:Nat} -> (lowerThan px py) -> lowerThan (S px) (S py)  
  
  
-- I can say that I want to extend the existing instance nat_set and it causes problems because then I can't use a proof of (x ~= x') as a rewritable proof of (x = x')   
instance [nat_partialStrictOrder] Set Nat => PartialStrictOrder Nat where
  
  (<<) x y = lowerThan x y
  
  -- I can't do these two at the moment because of Idris' design for interface and instance
  lower_compat_equivalence_L p1 p2 = ?Mnat_partialStrictOrder_1
  
  lower_compat_equivalence_R p1 p2 = ?Mnat_partialStrictOrder_2

  lowerDec Z Z = No ?Mnat_partialStrictOrder_3
  lowerDec Z (S py) = Yes (ZeroLowerAll py)
  lowerDec (S px) Z = No ?Mnat_partialStrictOrder_4
  lowerDec (S px) (S py) with (lowerDec px py)
    lowerDec (S px) (S py) | (Yes p_ihn) = ?Mnat_partialStrictOrder_5 -- Yes (LowerSucc p_ihn)
    lowerDec (S px) (S py) | (No p_no) = ?Mnat_partialStrictOrder_6

  lower_antisym p1 p2 = ?Mnat_partialStrictOrder_7
  
  lower_trans p1 p2 = ?Mnat_partialStrictOrder_8
    
    
instance [nat_partialOrder] PartialStrictOrder Nat => PartialOrder Nat where
  
  
total
T_or_Unit : (T:Type) -> (b:Bool) -> Type
T_or_Unit T True = T
T_or_Unit T False = Unit



total  
tryDec : {T:Type} -> (x:Dec T) -> (b:Bool ** (T_or_Unit T b))
tryDec (Yes prYes) = (True ** prYes)
tryDec (No prNo) = (False ** MkUnit)




-- First test to our predicate
total
isSorted_test1 : isSorted nat_partialOrder [3, 5, 7]
isSorted_test1 = let p1 : ((<~=) {p=nat_partialOrder} 3 5) = ?MA in -- rightDep (tryDec (lowerEqDec nat_partialOrder 3 5)) in
		 let p2 : ((<~=) {p=nat_partialOrder} 5 7) = ?MB in
		    ConsSorted 3 5 [7] (ConsSorted 5 7 [] (SingletonIsSorted _ 7) p2) p1



---------- Proofs ----------
{-
tests.MX = proof
  intros
  mrefine ConsSorted 
  mrefine ConsSorted 
  exact p1
  mrefine SingletonIsSorted 
  exact p2
  -}

tests.Mnat_partialStrictOrder_5 = proof
  intros
  mrefine Yes
  mrefine LowerSucc 
  exact p_ihn 


tests.Mnat_set_1 = proof
  intros
  rewrite (sym p1)
  rewrite p2
  exact Refl


