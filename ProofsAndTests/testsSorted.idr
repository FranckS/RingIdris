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


-- This is code that conforms to the description in the article
-- "Automatic predicate testing in formal certification" (accepted for Tests and Proofs 2016)
-- by the author


total
leftDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> A
leftDep (a ** b) = a


total
rightDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> B (leftDep x)
rightDep (a ** b) = b


-- ---------------------------------------------------------------
--                  Nat is a sorted structure                  ---
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
  
  
-- I can't say that I want to extend the specific existing instance nat_set and it causes problems because then I can't use a proof of (x ~= x') as a rewritable proof of (x = x')   
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


-- ---------------------------------------------------------------
--  Usual approaches : doing "tests by proof" on the predicate ---
--  (section 2 of the TAP 2016 paper)                          ---
-- ---------------------------------------------------------------

-- First we do 'test by proof' on the predicate, where the proof is done by hand
-- cf. section 2, page 3 and 4
total
isSorted_test1 : isSorted nat_partialOrder [3, 5, 7]
isSorted_test1 = let p1 : ((<~=) {p=nat_partialOrder} 3 5) = ?MA in -- rightDep (tryDec (lowerEqDec nat_partialOrder 3 5)) in
		 let p2 : ((<~=) {p=nat_partialOrder} 5 7) = ?MB in
		    ConsSorted 3 5 [7] (ConsSorted 5 7 [] (SingletonIsSorted _ 7) p2) p1
		    

-- Thanks to the fact that isSorted can be decided, we can test this predicate "semi-automatically"
-- cf. section 2, page 4
isSorted_test1' : Dec (isSorted nat_partialOrder [3,5,7])
isSorted_test1' = decideIsSorted nat_partialOrder [3,5,7] 
	    
	    	    
-- ----------------------------------------------------------------------
--       Testing the predicate by automatic generation of terms       ---
--       (section 3 of the TAP 2016 paper)                            ---
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
-- (not presented in the paper)
testGen : (n:Nat) -> Maybe(Vect n (List ThreeLeters))
testGen n = let x = generateList ThreeLeters ThreeLetersIsRecursivelyEnumarable (S (S (S Z)))
	 in unfold_n_times x n
 
-- (not presented in the paper) 
-- ask for the evalutation of (testGen 27) to test the automatic generation of the
-- first 27 lists of size 3
 
 
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
 

 -- ------------------------------------------------------------------------
-- "Let’s automatically generate the first m sorted lists of T, of size n, 
-- by unfolding m times the result of generateSortedList"
-- (section 3 of the TAP 2016 paper)
-- ------------------------------------------------------------------------
 
testGenerator : (m:Nat) -> (n:Nat) -> Maybe(Vect m (List ThreeLeters))
testGenerator m n = 
  let x = generateSortedList ThreeLeters ThreeLetersIsRecursivelyEnumarable (fixMe (fixMe_aux ThreeLeters_set)) n
    in unfold_n_times x m
 

-- ask for the evalutation of (testGenerator 8 4) to see the first 8 sorted list of size 4 
-- cf. section 3, page 5, at the bottom of the page
-- it works

-- ------------------------------------------------------------------------
-- "Now we run the decision procedure on all of these 'm' test in order to know
-- if the predicate and the generator agree on this portion"
-- (section 3 of the TAP 2016 paper)
-- ------------------------------------------------------------------------

testSorted : (m:Nat) -> (n:Nat) -> Vect m Bool
testSorted m n = 
  let x = generateSortedList ThreeLeters ThreeLetersIsRecursivelyEnumarable (fixMe (fixMe_aux ThreeLeters_set)) n in
    let y = LLmap (\l => let res = decideIsSorted (fixMe (fixMe_aux ThreeLeters_set)) l in
			    case res of
			      Yes _ => True
			      No _ => False) x in
	unfold_n_times_with_padding y m True -- If the result wasn't big enough, we obviously consider that them to be success

-- ask for the evalutation of (testSorted 8 4) to see the result of testing the predicate with the first 8 sorted list of size 4
-- cf. section 3, page 5 and 6 
-- it works	
	
	
-- ------------------------------------------------------------------------------------------
-- "We might not want to inspect manually the result of each test [...] so we write a function
-- that calls testSorted and does the boolean And on each element of the resulting vector" in
-- order to get the overall result
-- ------------------------------------------------------------------------------------------
	
testSorted_result : (m:Nat) -> (n:Nat) -> Bool
testSorted_result m n = let vectorRes = testSorted m n in aux_testSorted_result vectorRes where
  
	aux_testSorted_result : {m:Nat} -> (Vect m Bool) -> Bool
	aux_testSorted_result [] = True
	aux_testSorted_result (h::t) = h && (aux_testSorted_result t) -- Does the logical 'and' on the entire vector result

	
-- When if you want to test the predicate against a very big number of automatically generated sorted list, ie when m is big 
-- and you can't check the result by hand, run for example (testSorted_result 50 9)
-- to see if the predicate agrees with the first 50 automatically generated list of size 9
-- cf section 3, page 6
-- it works

-- If you want to test with an 'm' even bigger (which is only useful when 'n' is also big), 
-- you can run it over night and get the final result without inspecting
-- the result of every test

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
  
  
  