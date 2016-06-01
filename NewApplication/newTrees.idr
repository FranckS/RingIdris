import ordering


left : {A:Type} -> {B:Type} -> (A,B)  -> A
left (x,y) = x

right : {A:Type} -> {B:Type} -> (A,B) -> B
right (x,y) = y

leftDep : {A:Type} -> {B:A->Type} -> (x : DPair A B) -> A
leftDep (a ** b) = a

rightDep : {A:Type} -> {B:A->Type} -> (x : DPair A B) -> B (leftDep x)
rightDep (a ** b) = b



-- Just an insertion sort for lists
insert : {A:Type} -> (Aord : PartialOrder A) -> (elem:A) -> List A -> List A
insert Aord elem [] = [elem]
insert Aord elem (h::t) with (lowerEqDec Aord elem h)
	insert Aord elem (h::t) | (Yes elemIsLower) = elem::(h::t)
	insert Aord elem (h::t) | (No elemIsStrictlyGreater) = h::(insert Aord elem t)

sortList : {A:Type} -> (Aord : PartialOrder A) -> List A -> List A
sortList Aord [] = []
sortList Aord (h::t) = insert Aord h (sortList Aord t)

-- Now, we could prove that sort is indeed a sorting function...
-- To do
-- [...]


-- More interesting : Now, we want to talk about binary trees :

data Tree : (A:Type) -> List A -> Type where
	EmptyTree : {A:Type} -> Tree A []
	Node : {A:Type} -> {l1:List A} -> {l2:List A} -> (left:Tree A l1) -> (elem:A) -> (right:Tree A l2) -> Tree A (l1++[elem]++l2)
    
    
-- We want to define the function that builds a sorted binary tree from an (unsorted) list of elements
-- And we want to show in the type that the produced tree reflects the same elements, but sorted
-- And since we trust the sort function on list (because it has already been proven to be correct), we can therefore
-- trust this function that operated on trees.

-- That should brings problems as the index being built is certainly not the same as the one claimed in the type
-- -> we want to use one of our automatic prover for that

insertTree : {A:Type} -> (Aord : PartialOrder A) -> (x:A) -> {lindex:List A} -> Tree A lindex -> Tree A (sortList Aord lindex++[x])
insertTree {A=A} _ x EmptyTree ?= Node EmptyTree x EmptyTree
insertTree {A=A} Aord x (Node left elem right) with (lowerEqDec Aord x elem)
	insertTree {A=A} Aord x (Node left elem right) | (Yes xIsSmallerOrEqual) ?= Node (insertTree Aord x left) elem right
	insertTree {A=A} Aord x (Node left elem right) | (No xIsBigger) ?= Node left elem (insertTree Aord x right)

	
buildSortedTree : {A:Type} -> (Aord : PartialOrder A) -> (l:List A) -> Tree A (sortList Aord l)
buildSortedTree {A=A} Aord [] = EmptyTree
buildSortedTree {A=A} Aord (h::t) ?= aux_buildSortedTree (Node EmptyTree h EmptyTree) t where
	aux_buildSortedTree : {A:Type} -> {Aord : PartialOrder A} -> {lindex:List A} -> (tree:Tree A lindex) -> (l:List A) -> Tree A (sortList Aord (l++lindex))
	aux_buildSortedTree tree [] ?= tree
	aux_buildSortedTree {A=A} {Aord=Aord} tree (head::tail) ?= aux_buildSortedTree (insertTree Aord head tree) tail 
	
	
	
	
	