interface Order c where
    (>=) : c -> c -> Type

-- Sorted lists (in decreasing order) by construction (with embedded proofs)
-- The (Maybe T) index is the current maximum, at the head of the list 
data SortedList : (T:Type) -> (Order T) -> (Maybe T) -> Type where
    Nil : {T:Type} -> {ord:Order T} -> SortedList T ord Nothing
    Singleton : {T:Type} -> {ord:Order T} -> (x:T) -> SortedList T ord (Just x)
    Cons : {T:Type} -> {ord:Order T} -> {max:T} -> (l:SortedList T ord (Just max)) -> (x:T) -> (pr:x >= max) 
            -> SortedList T ord (Just x)


-- Small example

implementation [natOrd] Order Nat where
    (>=) x y = GTE x y

-- 2 >= 1
pr1 : GTE 2 1
pr1 = LTESucc LTEZero

-- 3 >= 2
pr2 : GTE 3 2
pr2 = LTESucc (LTESucc LTEZero)

-- [3,2,1]
sortedList1 : SortedList Nat Main.natOrd (Just 3)
sortedList1 = Cons (Cons (Singleton 1) 2 pr1) 3 pr2

