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



%assert_total -- FIX IDRIS : Why Idris doesn't see this function as total ?
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
  

    

-- This function should generate all sorted List
-- generateSortedList : Nat -> 





---------- Proofs ----------

proofAndTests.MdecideIsSorted_2 = proof
  intros
  mrefine h1_not_lower_h2 
  exact (isSorted_wkn2 TisOrdered h1 h2 t __pi_arg)


proofAndTests.MdecideIsSorted_1 = proof
  intros
  mrefine h2_tail_not_sorted 
  exact (isSorted_wkn TisOrdered h1 h2 t __pi_arg)


  
  
  
