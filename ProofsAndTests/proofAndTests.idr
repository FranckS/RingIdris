module proofAndTests


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect
import ordering


%access public export

%default total



data isSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> {n:Nat} -> (v:Vect n T) -> Type where
    NilIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> isSorted TisOrdered []
    SingletonIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> (x:T) -> isSorted TisOrdered [x]
    ConsSorted : {T:Type} -> {TisOrdered : PartialOrder T} -> (h1:T) -> (h2:T) -> {n:Nat} -> (t:Vect n T) -> (isSorted TisOrdered (h2::t)) -> ((<~=) {p=TisOrdered} h1 h2) -> (isSorted TisOrdered (h1::(h2::t)))

    
    
isSorted_wkn : {T:Type} -> (TisOrdered : PartialOrder T) -> {n:Nat} -> (h1 : T) -> (h2 : T) -> (t:Vect n T) -> (isSorted TisOrdered (h1::(h2::t))) -> (isSorted TisOrdered (h2::t))
isSorted_wkn TisOrdered h1 h2 t (NilIsSorted TisOrdered) impossible
isSorted_wkn TisOrdered h1 h2 t (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn TisOrdered h1 h2 t (ConsSorted h1 h2 t h2_tail_sorted h1_lower_h2) = h2_tail_sorted


isSorted_wkn2 : {T:Type} -> (TisOrdered : PartialOrder T) -> {n:Nat} -> (h1 : T) -> (h2 : T) -> (t:Vect n T) -> (isSorted TisOrdered (h1::(h2::t))) -> ((<~=) {p=TisOrdered} h1 h2)
isSorted_wkn2 TisOrdered h1 h2 t (NilIsSorted TisOrdered) impossible
isSorted_wkn2 TisOrdered h1 h2 t (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn2 TisOrdered h1 h2 t (ConsSorted h1 h2 t h2_tail_sorted h1_lower_h2) = h1_lower_h2



%assert_total -- FIX IDRIS : Idris should see this function as total with a bit of work
decideIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> {n:Nat} -> (v:Vect n T) -> Dec(isSorted TisOrdered v)
decideIsSorted TisOrdered [] = Yes (NilIsSorted TisOrdered)
decideIsSorted TisOrdered [x] = Yes (SingletonIsSorted TisOrdered x)
decideIsSorted TisOrdered (h1::(h2::t)) with (lowerEqDec TisOrdered h1 h2)
-- Does the first two elements are ordered ?
  decideIsSorted TisOrdered (h1::(h2::t)) | (Yes h1_lower_h2) with (decideIsSorted TisOrdered (h2::t))
    -- If so, we now need to check recursively
    decideIsSorted TisOrdered (h1::(h2::t)) | (Yes h1_lower_h2) | (Yes h2_tail_sorted) = Yes (ConsSorted h1 h2 t h2_tail_sorted h1_lower_h2)
    decideIsSorted TisOrdered (h1::(h2::t)) | (Yes h1_lower_h2) | (No h2_tail_not_sorted) = No ?MdecideIsSorted_1
-- If not, we know that the entire list isn't sorted
  decideIsSorted TisOrdered (h1::(h2::t)) | No h1_not_lower_h2 = No ?MdecideIsSorted_2
  


  
  
-- Now, the big question is, does the (indictive) predicate isSorted effectively represents what we consider to be a sorted list ?
-- 1) Does this predicate always hold for a sorted list ? ie, does intensionnaly_sorted -> formally_sorted
-- 2) When this predicate holds for a data, can we be sure that this data is indeed sorted? ie, does formally_sorted -> intensionally_sorted ?

-- The problem is that intentionaly_sorted is something outside of the theory. This is something usually writted in english, etc

-- My point of view is that in order to gain confidence about the predicate, we can write a function that generate all (intensionally) sorted list.
-- Generating what we try to qualify is easier than writting a property about it
    
    
    
codata LList : (T:Type) -> Type where    
  LLNil : {T:Type} -> LList T
  LLCons : {T:Type} -> (h:T) -> (t:LList T) -> LList T

  
LLappend : {T:Type} -> (LList T) -> (LList T) -> (LList T)
LLappend LLNil l2 = l2
LLappend (LLCons h1 t1) l2 = LLCons h1 (LLappend t1 l2)
  

interface RecursivelyEnumerable c where
    computableMap : Nat -> Maybe c
    map_is_surjective : (y:c) -> (x:Nat ** (computableMap x = Just y)) -- For all y in the image set, there is (at least) one 'x' in the domain, which is going to be associated to 'y' by the map
  
  
consAll : {T:Type} -> {n:Nat} -> (ts:LList (Vect n T)) -> (h:T) -> (LList (Vect (S n) T))
consAll LLNil h = LLNil
consAll (LLCons l1 ls) h = LLCons (h::l1) (consAll ls h)  


consWhenLower : {T:Type} -> {n:Nat} -> (ts:LList (Vect n T)) -> (h:T) -> (LList (Vect (S n) T))


{-
appendAll : {T:Type} -> {n:Nat} -> (l:LList (Vect n T)) -> (h:T) -> LList (Vect (n+1) T)
appendAll LLNil h = LLNil -- Am I sure here ?
appendAll (LLCons l1 ls) h = LLCons (l1++[h]) (appendAll ls h)
-}  

plus_one_equals_succ : (n:Nat) -> (n+1 = S n)
plus_one_equals_succ Z = Refl
plus_one_equals_succ (S pn) = let p_ihn : (pn + 1 = S pn) = plus_one_equals_succ pn in ?Mplus_one_equals_succ_1
  
  
mutual
  %assert_total -- Why Idris can't see that this definition is total ?
  -- This function should generate all Vect for a given size
  generateVect : (T:Type) -> (recEnu:RecursivelyEnumerable T) -> (n:Nat) -> LList (Vect n T)
  generateVect T recEnu Z = LLCons [] LLNil -- There's just one vector of size Zero to generate and its []
  generateVect T recEnu (S pn) = aux_generateVect recEnu pn Z
  
  %assert_total -- Why Idris can't see that this definition is total ?
  aux_generateVect : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (pn:Nat) -> (iCurrent:Nat) -> LList (Vect (S pn) T)
  aux_generateVect {T=T} recEnu pn iCurrent = 
    let ts = generateVect T recEnu pn in
    let maybeInit = computableMap {c=T} iCurrent in
	case maybeInit of
	Just init => let resultStart = consAll ts init in
			  LLappend resultStart (aux_generateVect recEnu pn (S iCurrent))
	Nothing => LLNil
	
	
mutual
  %assert_total -- Why Idris can't see that this definition is total ?
  -- This function should generate all Vect for a given size
  generateSortedVect : (T:Type) -> (recEnu:RecursivelyEnumerable T) -> (n:Nat) -> LList (Vect n T)
  generateSortedVect T recEnu Z = LLCons [] LLNil -- There's just one vector of size Zero to generate and its []
  generateSortedVect T recEnu (S pn) = aux_generateSortedVect recEnu pn Z
  
  %assert_total -- Why Idris can't see that this definition is total ?
  aux_generateSortedVect : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (pn:Nat) -> (iCurrent:Nat) -> LList (Vect (S pn) T)
  aux_generateSortedVect {T=T} recEnu pn iCurrent = 
    let ts = generateSortedVect T recEnu pn in
    let maybeInit = computableMap {c=T} iCurrent in
	case maybeInit of
	Just init => let resultStart = consWhenLower ts init in
			  LLappend resultStart (aux_generateSortedVect recEnu pn (S iCurrent))
	Nothing => LLNil	
	
	
	
	
 
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
 

 
unfold_n_times : {T:Type} -> (LList T) -> (n:Nat) -> Maybe(Vect n T)
-- Unfolding LLNil
unfold_n_times LLNil Z = Just []
unfold_n_times LLNil _ = Nothing
-- Unfolding an LLCons
unfold_n_times (LLCons h t) Z = Just []
unfold_n_times (LLCons h t) (S pn) = case (unfold_n_times t pn) of 
					Just vectResultRec => Just (h::vectResultRec)
					Nothing => Nothing
					

-- Produces the first n vectors of size 3
test : (n:Nat) -> Maybe(Vect n (Vect (S (S (S Z))) ThreeLeters))
test n = let x = generateVect ThreeLeters ThreeLetersIsRecursivelyEnumarable (S (S (S Z)))
	 in unfold_n_times x n
 

-- ask for the evalutation of (test 27) for example



---------- Proofs ----------

proofAndTests.Mplus_one_equals_succ_1 = proof
  intros
  rewrite p_ihn
  exact Refl

  
proofAndTests.MdecideIsSorted_2 = proof
  intros
  mrefine h1_not_lower_h2 
  exact (isSorted_wkn2 TisOrdered h1 h2 t __pi_arg)


proofAndTests.MdecideIsSorted_1 = proof
  intros
  mrefine h2_tail_not_sorted 
  exact (isSorted_wkn TisOrdered h1 h2 t __pi_arg)


  
  
  
