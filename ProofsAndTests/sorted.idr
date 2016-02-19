-- Franck Slama
-- University of St Andrews
-- ------------------------------

module sorted


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect
import ordering
import LList


%access public export

%default total



data isSorted : {T:Type} -> (Tord : PartialOrder T) 
                 -> (l:List T) -> Type where
    NilIsSorted : {T:Type} -> (Tord : PartialOrder T) -> isSorted Tord []
    SingletonIsSorted : {T:Type} -> (Tord : PartialOrder T) -> (x:T) -> isSorted Tord [x]
    ConsSorted : {T:Type} -> {Tord : PartialOrder T} -> (h1:T) -> (h2:T) -> (t:List T) 
		 -> (isSorted Tord (h2::t)) -> ((<~=) {p=Tord} h1 h2) 
                 -> (isSorted Tord (h1::(h2::t)))
    
    
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

-- My point of view is that in order to gain confidence about the predicate, we can write a function that generate all (intentionally) sorted list.
-- Generating what we try to qualify is often easier than writting a property about it
    

-- In order to automatically generate all the sorted lists on T, we will require T to be recursively enumerable 
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


  
mutual
  %assert_total -- Why Idris can't see that this definition is total ?
  -- This function should generate all list for a given size
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
  -- This function should generate all sorted list for a given size
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
	
	
	
-- -------------------------------------------------------------------
-- Equivalence between the generated terms and the predicate isSorted
-- -------------------------------------------------------------------

-- all of the generated list of size n makes the predicate isSorted hold
generated_implies_predicate_holds : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (Tord : PartialOrder T) -> (n:Nat) 
				      -> (LLall (generateSortedList T recEnu Tord n) (\l => isSorted {T=T} Tord l))
generated_implies_predicate_holds {T=T} recEnu Tord Z = LLall_Cons _ Nil _ (NilIsSorted Tord) (LLall_Nil _)
generated_implies_predicate_holds {T=T} recEnu Tord (S pn) = let cofix = generated_implies_predicate_holds recEnu Tord pn in
								-- The argument is that for going from size pn to size (S pn) we've only added on
								-- the head of each list something smaller than the current head
								?Mgenerated_implies_predicate_holds_1

{-	
predicate_holds_implies_generated : {T:Type} -> (recEnu:RecursivelyEnumerable T) -> (Tord : PartialOrder T) -> (l:List T) 
				    -> (lisSorted : isSorted {T=T} Tord l) -> 
-}






---------- Proofs ----------
  
sorted.MdecideIsSorted_2 = proof
  intros
  mrefine h1_not_lower_h2 
  exact (isSorted_wkn2 TisOrdered h1 h2 t __pi_arg)


sorted.MdecideIsSorted_1 = proof
  intros
  mrefine h2_tail_not_sorted 
  exact (isSorted_wkn TisOrdered h1 h2 t __pi_arg)


  
  
  
