

-- import Decidable.Equality
-- import Data.Fin
import Data.Vect




{-


data isSorted : {T:Type} -> (TisOrdered : Ord T) -> {n:Nat} -> (v:Vect n T) -> Type where
    NilIsSorted : {T:Type} -> (TisOrdered : Ord T) -> isSorted TisOrdered []
    SingletonIsSorted : {T:Type} -> (TisOrdered : Ord T) -> (x:T) -> isSorted TisOrdered [x]
    ConsSorted : {T:Type} -> {TisOrdered : Ord T} -> (h1:T) -> (h2:T) -> {n:Nat} -> (t:Vect n T) -> (isSorted TisOrdered (h2::t)) -> (LTE h1 h2) -> (isSorted TisOrdered (h1::(h2::t)))

-}



-- This function should generate all sorted List
-- generateSortedList : Nat -> 