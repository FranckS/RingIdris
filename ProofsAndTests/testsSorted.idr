-- Franck Slama
-- University of St Andrews
-- ------------------------------

module testsSorted


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect
import ordering
import LList
import sorted


%access public export

%default total


total
leftDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> A
leftDep (a ** b) = a


total
rightDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> B (leftDep x)
rightDep (a ** b) = b


-- ---------------------------------------------------------------
--            Test of the usual approach (with Nat)            ---
-- ---------------------------------------------------------------

  
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




-- First test to our predicate, where the proof is done by hand
total
isSorted_test1 : isSorted nat_partialOrder [3, 5, 7]
isSorted_test1 = let p1 : ((<~=) {p=nat_partialOrder} 3 5) = ?MA in -- rightDep (tryDec (lowerEqDec nat_partialOrder 3 5)) in
		 let p2 : ((<~=) {p=nat_partialOrder} 5 7) = ?MB in
		    ConsSorted 3 5 [7] (ConsSorted 5 7 [] (SingletonIsSorted _ 7) p2) p1

		    
		    
		    
		    
isSorted_wkn : {T:Type} -> (TisOrdered : PartialOrder T) -> (h1 : T) -> (h2 : T) -> (l:List T) -> (isSorted TisOrdered (h1::(h2::l))) -> (isSorted TisOrdered (h2::l))
isSorted_wkn TisOrdered h1 h2 l (NilIsSorted TisOrdered) impossible
isSorted_wkn TisOrdered h1 h2 l (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn TisOrdered h1 h2 l (ConsSorted h1 h2 l h2_tail_sorted h1_lower_h2) = h2_tail_sorted


isSorted_wkn2 : {T:Type} -> (TisOrdered : PartialOrder T) -> (h1 : T) -> (h2 : T) -> (l:List T) -> (isSorted TisOrdered (h1::(h2::l))) -> ((<~=) {p=TisOrdered} h1 h2)
isSorted_wkn2 TisOrdered h1 h2 l (NilIsSorted TisOrdered) impossible
isSorted_wkn2 TisOrdered h1 h2 l (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn2 TisOrdered h1 h2 l (ConsSorted h1 h2 l h2_tail_sorted h1_lower_h2) = h1_lower_h2



-- We will now decide the predicate isSorted automatically

	    
test_isSorted_1 : Dec (isSorted nat_partialOrder [3,5,7])
test_isSorted_1 = decideIsSorted nat_partialOrder [3,5,7] 
	    
	    
	    
	    
-- ----------------------------------------------------------------------
--            Test of the our predicate testing mechanism             ---
-- ----------------------------------------------------------------------	    
	    
	    
data ThreeLeters : Type where
   A : ThreeLeters
   B : ThreeLeters
   C : ThreeLeters
   

instance [ThreeLetersIsRecursivelyEnumarable] RecursivelyEnumerable ThreeLeters where

  -- computableMap : Nat -> Maybe ThreeLeters
  computableMap Z = Just A
  computableMap (S Z) = Just B
  computableMap (S (S Z)) = Just C
  computableMap _ = Nothing
  
  
  -- map_is_surjective : (y:ThreeLeters) -> (x:Nat ** (computableMap x = Just y))
  map_is_surjective A = (Z ** Refl)
  map_is_surjective B = ((S Z) ** Refl)
  map_is_surjective C = ((S (S Z)) ** Refl)
 

	

-- Produces the first n vectors of size 3
testGen : (n:Nat) -> Maybe(Vect n (List ThreeLeters))
testGen n = let x = generateList ThreeLeters ThreeLetersIsRecursivelyEnumarable (S (S (S Z)))
	 in unfold_n_times x n
 

 
-- ask for the evalutation of (testGen 27) for example 
 
 
 
decEqThreeLeters : (l1:ThreeLeters) -> (l2:ThreeLeters) -> Dec(l1=l2)
decEqThreeLeters A A = Yes Refl
decEqThreeLeters A B = No ?MJ1
decEqThreeLeters A C = No ?MJ2

decEqThreeLeters B A = No ?MJ3
decEqThreeLeters B B = Yes Refl
decEqThreeLeters B C = No ?MJ4

decEqThreeLeters C A = No ?MJ5
decEqThreeLeters C B = No ?MJ6
decEqThreeLeters C C = Yes Refl
 
 
 
 
instance [ThreeLeters_set] Set ThreeLeters where
  (~=) x y = (x = y)
  
  eqDec x y = decEqThreeLeters x y
  
  eq_refl x = Refl
  
  eq_sym p = sym p
  
  eq_trans p1 p2 = ?MthreeLeters_set_1
 
 
total
lowerThan_bool : (l1 : ThreeLeters) -> (l2 : ThreeLeters) -> Bool
lowerThan_bool A A = False
lowerThan_bool A _ = True -- A is lower than everything appart from A itself
lowerThan_bool B C = True
lowerThan_bool B _ = False -- B is only lower than C
lowerThan_bool C _ = False -- C is lower than nothing



-- the same as a proposition
data lowerThan_prop : (l1 : ThreeLeters) -> (l2 : ThreeLeters) -> Type where
  MkLowerThan_prop : (l1 : ThreeLeters) -> (l2 : ThreeLeters) -> (proofByComputation : (lowerThan_bool l1 l2 = True)) -> lowerThan_prop l1 l2


instance [ThreeLeters_partialStrictOrder] Set ThreeLeters => PartialStrictOrder ThreeLeters where
  (<<) x y = lowerThan_prop x y
  
  lower_compat_equivalence_L p1 p2 = ?MthreeLeters_partialStrictOrder_1
  
  lower_compat_equivalence_R p1 p2 = ?MthreeLeters_partialStrictOrder_2

  lowerDec A A = No ?MthreeLeters_partialStrictOrder_3
  lowerDec A B = Yes (MkLowerThan_prop A B Refl)
  lowerDec A C = Yes (MkLowerThan_prop A C Refl)
  lowerDec B A = No ?MthreeLeters_partialStrictOrder_4
  lowerDec B B = No ?MthreeLeters_partialStrictOrder_5
  lowerDec B C = Yes (MkLowerThan_prop B C Refl)
  lowerDec C y = No ?MthreeLeters_partialStrictOrder_6
  
  
  lower_antisym p1 p2 = ?MthreeLeters_partialStrictOrder_7
  
  lower_trans p1 p2 = ?MthreeLeters_partialStrictOrder_8
  
  
instance [ThreeLeters_partialOrder] PartialStrictOrder ThreeLeters => PartialOrder ThreeLeters where


-- FIX IDRIS HERE ! I basically need to do the instance resolution by hand
fixMe_aux : Set ThreeLeters -> PartialStrictOrder ThreeLeters
fixMe_aux x = ThreeLeters_partialStrictOrder

fixMe : PartialStrictOrder ThreeLeters -> PartialOrder ThreeLeters
fixMe x = ThreeLeters_partialOrder
 

testGenSorted : (n:Nat) -> Maybe(Vect n (List ThreeLeters))
testGenSorted n = let x = generateSortedList ThreeLeters ThreeLetersIsRecursivelyEnumarable (fixMe (fixMe_aux ThreeLeters_set)) (S (S (S Z)))
		in unfold_n_times x n
 

-- ask for the evalutation of (testGenSorted 10) to see the first 10 sorted list of size 3 
-- it works

-- ---------------------------------
-- Automatically generating n tests
-- ---------------------------------
testSorted : (n:Nat) -> Maybe(Vect n Bool)
testSorted n = 
  let x = generateSortedList ThreeLeters ThreeLetersIsRecursivelyEnumarable (fixMe (fixMe_aux ThreeLeters_set)) (S (S (S Z))) in
    let y = LLmap (\l => let res = decideIsSorted (fixMe (fixMe_aux ThreeLeters_set)) l in
			    case res of
			      Yes _ => True
			      No _ => False) x in
	unfold_n_times y n



-- ask for the evalutation of (testSorted 10) to see for example the result of testing the first 10 sorted list 
-- it works

---------- Proofs ----------

{-
testsSorted.MX = proof
  intros
  mrefine ConsSorted 
  mrefine ConsSorted 
  exact p1
  mrefine SingletonIsSorted 
  exact p2
  -}
  
-- Part about Nat  

testsSorted.Mnat_partialStrictOrder_5 = proof
  intros
  mrefine Yes
  mrefine LowerSucc 
  exact p_ihn 


testsSorted.Mnat_set_1 = proof
  intros
  rewrite (sym p1)
  rewrite p2
  exact Refl


-- Part aboutThreeLeters

testsSorted.MthreeLeters_set_1 = proof
  intros
  rewrite (sym p1)
  rewrite p2
  exact Refl
  
  
  