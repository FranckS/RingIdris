import Data.Vect

{-
-- Just a try
myT : (A:Type) -> Type
myT A = (Sigma Nat (\n => Vect n Bool)) -- Weird, I can't use the ** syntax here. It's probably because of the fact that ** is used both at the type level and at the term level (unlike Coq)
-}

total
leftDep : {T:Type} -> {P:T->Type} -> (Sigma T P) -> T
leftDep (MkSigma t p) = t

total
allLeft : {T:Type} -> {P:T->Type} -> (ls : List(Sigma T P)) -> List T
allLeft [] = []
allLeft (h::t) = (leftDep h) :: (allLeft t)

total
concatList : {A:Type} -> (List (List A)) -> List A
concatList [] = []
concatList (h::t) = h ++ (concatList t)


concatListDepPair : {A:Type} -> {T:(List A)->Type} -> (ls : List(Sigma (List A) (\l => T l))) -> List A
concatListDepPair ls = let allTs = allLeft ls in concatList allTs


-- Tree (with elements of type A in the leaves) and elements of type B in the other nodes
data Tree : (A:Type) -> Type -> List A -> Type where
	Leaf : {A:Type} -> {B:Type} -> (a:A) -> Tree A B [a]
	Node : {A:Type} -> {B:Type} -> (b:B) -> (ls:List (Sigma (List A) (\l => Tree A B l))) -> Tree A B (concatListDepPair ls)

	
	
UnionOfTree : {A:Type} -> {B:Type} -> {ls1:List (Sigma (List A) (\l => Tree A B l))} -> {ls2:List (Sigma (List A) (\l => Tree A B l))} -> (Tree A B (concatListDepPair ls1)) -> (b:B) -> (Tree A B (concatListDepPair ls2)) -> Tree A B (concatListDepPair (ls1++ls2))
UnionOfTree t1 b t2 ?= Node b [(_ ** t1), (_ ** t2)]
	
	
	


