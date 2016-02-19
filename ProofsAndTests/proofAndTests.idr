module proofAndTests


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect
import ordering


%access public export

%default total



data isSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> (l:List T) -> Type where
    NilIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> isSorted TisOrdered []
    SingletonIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> (x:T) -> isSorted TisOrdered [x]
    ConsSorted : {T:Type} -> {TisOrdered : PartialOrder T} -> (h1:T) -> (h2:T) -> (t:List T) -> (isSorted TisOrdered (h2::t)) -> ((<~=) {p=TisOrdered} h1 h2) -> (isSorted TisOrdered (h1::(h2::t)))

    
    
isSorted_wkn : {T:Type} -> (TisOrdered : PartialOrder T) -> (h1 : T) -> (h2 : T) -> (t:List T) -> (isSorted TisOrdered (h1::(h2::t))) -> (isSorted TisOrdered (h2::t))
isSorted_wkn TisOrdered h1 h2 t (NilIsSorted TisOrdered) impossible
isSorted_wkn TisOrdered h1 h2 t (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn TisOrdered h1 h2 t (ConsSorted h1 h2 t h2_tail_sorted h1_lower_h2) = h2_tail_sorted


isSorted_wkn2 : {T:Type} -> (TisOrdered : PartialOrder T) -> (h1 : T) -> (h2 : T) -> (t:List T) -> (isSorted TisOrdered (h1::(h2::t))) -> ((<~=) {p=TisOrdered} h1 h2)
isSorted_wkn2 TisOrdered h1 h2 t (NilIsSorted TisOrdered) impossible
isSorted_wkn2 TisOrdered h1 h2 t (SingletonIsSorted TisOrdered _) impossible
isSorted_wkn2 TisOrdered h1 h2 t (ConsSorted h1 h2 t h2_tail_sorted h1_lower_h2) = h1_lower_h2



%assert_total -- FIX IDRIS : Idris should see this function as total with a bit of work
decideIsSorted : {T:Type} -> (TisOrdered : PartialOrder T) -> (l:List T) -> Dec(isSorted TisOrdered l)
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
  

LLmap : {T:Type} -> {U:Type} -> (f:T -> U) -> (LList T) -> LList U  
LLmap f LLNil = LLNil
LLmap f (LLCons h t) = LLCons (f h) (LLmap f t)
  
  
  
interface RecursivelyEnumerable c where
    computableMap : Nat -> Maybe c
    map_is_surjective : (y:c) -> (x:Nat ** (computableMap x = Just y)) -- For all y in the image set, there is (at least) one 'x' in the domain, which is going to be associated to 'y' by the map
  
  
consAll : {T:Type} -> (ts:LList (List T)) -> (h:T) -> (LList (List T))
consAll LLNil h = LLNil
consAll (LLCons l1 ls) h = LLCons (h::l1) (consAll ls h)  


%assert_total
consWhenLower : {T:Type} -> (Tord : PartialOrder T) -> (ts:LList (List T)) -> (h:T) -> (LList (List T))
consWhenLower Tord LLNil h = LLNil
consWhenLower Tord (LLCons Nil ls) h = LLCons [h] (consAll ls h) -- We can add h in front and continue recursively      
consWhenLower Tord (LLCons (curHead::tail) ls) h with (lowerEqDec Tord h curHead) -- We need to check if 'h' is lower or equal than the current head
  consWhenLower Tord (LLCons (curHead::tail) ls) h | (Yes pr_h_leq_currHead) = LLCons (h::(curHead::tail)) (consWhenLower Tord ls h)
  consWhenLower Tord (LLCons (curHead::tail) ls) h | (No pr_h_not_leq_currHead) = (consWhenLower Tord ls h)


{-
appendAll : {T:Type} -> {n:Nat} -> (l:LList (List T)) -> (h:T) -> LList (List T)
appendAll LLNil h = LLNil -- Am I sure here ?
appendAll (LLCons l1 ls) h = LLCons (l1++[h]) (appendAll ls h)
-}  

plus_one_equals_succ : (n:Nat) -> (n+1 = S n)
plus_one_equals_succ Z = Refl
plus_one_equals_succ (S pn) = let p_ihn : (pn + 1 = S pn) = plus_one_equals_succ pn in ?Mplus_one_equals_succ_1
  
  
mutual
  %assert_total -- Why Idris can't see that this definition is total ?
  -- This function should generate all Vect for a given size
  generateList : (T:Type) -> (recEnu:RecursivelyEnumerable T) -> (n:Nat) -> LList (List T)
  generateList T recEnu Z = LLCons [] LLNil -- There's just one list of size Zero to generate and its []
  generateList T recEnu (S pn) = aux_generateList recEnu pn Z
  
  %assert_total -- Why Idris can't see that this definition is total ?
  aux_generateList : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (pn:Nat) -> (iCurrent:Nat) -> LList (List T)
  aux_generateList {T=T} recEnu pn iCurrent = 
    let ts = generateList T recEnu pn in
    let maybeInit = computableMap {c=T} iCurrent in
	case maybeInit of
	Just init => let resultStart = consAll ts init in
			  LLappend resultStart (aux_generateList recEnu pn (S iCurrent))
	Nothing => LLNil
	
	
mutual
  %assert_total -- Why Idris can't see that this definition is total ?
  -- This function should generate all Vect for a given size
  generateSortedList : (T:Type) -> (recEnu:RecursivelyEnumerable T) -> (Tord : PartialOrder T) -> (n:Nat) -> LList (List T)
  generateSortedList T recEnu Tord Z = LLCons [] LLNil -- There's just one sorted list of size Zero to generate and its []
  generateSortedList T recEnu Tord (S pn) = aux_generateSortedList recEnu Tord pn Z
  
  %assert_total -- Why Idris can't see that this definition is total ?
  aux_generateSortedList : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (Tord : PartialOrder T) -> (pn:Nat) -> (iCurrent:Nat) -> LList (List T)
  aux_generateSortedList {T=T} recEnu Tord pn iCurrent = 
    let ts = generateSortedList T recEnu Tord pn in
    let maybeInit = computableMap {c=T} iCurrent in
	case maybeInit of
	Just init => let resultStart = consWhenLower Tord ts init in
			  LLappend resultStart (aux_generateSortedList recEnu Tord pn (S iCurrent))
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


-- -------------------------------------------------------------------
-- Automatically generating n tests
-- -------------------------------------------------------------------
testSorted : (n:Nat) -> Maybe(Vect n Bool)
testSorted n = 
  let x = generateSortedList ThreeLeters ThreeLetersIsRecursivelyEnumarable (fixMe (fixMe_aux ThreeLeters_set)) (S (S (S Z))) in
    let y = LLmap (\l => let res = decideIsSorted (fixMe (fixMe_aux ThreeLeters_set)) l in
			    case res of
			      Yes _ => True
			      No _ => False) x in
	unfold_n_times y n



-- ask for the evalutation of (testSorted 10) to see for example the result of testing the first 10 sorted list 




-- -------------------------------------------------------------------
-- Equivalence between the generated terms and the predicate isSorted
-- -------------------------------------------------------------------










---------- Proofs ----------

proofAndTests.MthreeLeters_set_1 = proof
  intros
  rewrite (sym p1)
  rewrite p2
  exact Refl


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


  
  
  
