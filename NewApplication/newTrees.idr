import ordering

-- Just an insertion sort
insert : {A:Type} -> (Aord : PartialOrder A) -> (elem:A) -> List A -> List A
insert Aord elem [] = [elem]
insert Aord elem (h::t) with (lowerEqDec Aord elem h)
	insert Aord elem (h::t) | (Yes elemIsLower) = elem::(h::t)
	insert Aord elem (h::t) | (No elemIsStrictlyGreater) = h::(insert Aord elem t)

sortList : {A:Type} -> (Aord : PartialOrder A) -> List A -> List A
sortList Aord [] = []
sortList Aord (h::t) = insert Aord h (sortList Aord t)


data Tree : {A:Type} -> List A -> Type where
	Leaf : {A:Type} -> (a:A) -> Tree []
	Node : {A:Type} -> {l1:List A} -> {l2:List A} -> (left:Tree l1) -> (elem:A) -> (right:Tree l2) -> Tree (l1++[elem]++l2)
    
    

buildSortedTree : {A:Type} -> (Aord : PartialOrder A) -> (l:List A) -> Tree (sortList Aord l)
buildSortedTree Aord [] = Leaf
buildSortedTree Aord l = aux_buildSortedTree Aord l Leaf
			aux_buildSortedTree : {A:Type} -> (Aord : PartialOrder A) -> (l:List A) -> {lindex:List A} -> (currentTree:Tree lindex) -> Tree (sortList (l++lindex))
			aux_buildSortedTree Aord [] currentTree = currentTree -- Nothing more to add in the current tree
			aux_buildSortedTree Aord (h::t) Leaf = aux_buildSortedTree Aord t (Node Leaf h Leaf)
			aux_buildSortedTree Aord (h::t) (Node left elem right) with (lowerEqDec Aord h elem)
				aux_buildSortedTree Aord (h::t) (Node left elem right) | (Yes hIsLower) = aux_buildSortedTree Aord [h]
