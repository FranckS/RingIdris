-- Tree (with elements of type A in the leaves) and elements of type B in the other nodes
data Tree : (A:Type) -> Type -> List A -> Type where
	Leaf : {A:Type} -> {B:Type} -> (a:A) -> Tree A B [a]
	Node : {A:Type} -> {B:Type} -> {l1:List A} -> {l2:List A} -> (left:Tree A B l1) -> (elem:B) -> (right:Tree A B l2) -> Tree A B (l1++l2)

leavesOfTree : {A:Type} -> {B:Type} -> {l:List A} -> Tree A B l -> List A
leavesOfTree (Leaf a) = [a]
leavesOfTree (Node left elem right) = (leavesOfTree left) ++ (leavesOfTree right)

leavesOfTree_correct : {A:Type} -> {B:Type} -> {l:List A} -> (t:Tree A B l) -> leavesOfTree t = l
leavesOfTree_correct (Leaf a) = Refl
leavesOfTree_correct (Node {l1=l1} {l2=l2} left elem right) = 
	let left_correct : (leavesOfTree left = l1) = leavesOfTree_correct left in
	let right_correct : (leavesOfTree right = l2) = leavesOfTree_correct right in
		rewrite left_correct in (rewrite right_correct in Refl)

-- not a good example as we have no poblem with the index... ;)
linearise : {A:Type} -> {B:Type} -> {l:List A} -> (t:Tree A B l) -> Tree A Unit l
linearise {l=l} t = -- let leaves = leavesOfTree t in aux_linearise leaves where
	let leaves = l in aux_linearise leaves where
	aux_linearise : {A:Type} -> (l:List A) -> Tree A Unit l
	aux_linearise [h] = Leaf h
	aux_linearise (head::tail) = Node (Leaf head) MkUnit (aux_linearise tail)  

{-}
linearise2 : {A:Type} -> {B:Type} -> {l:List A} -> (t:Tree A B l) -> Tree A Unit l
linearise2 (Leaf a) = Leaf a 
linearise2 (Node (Leaf v0) A (Leaf v1)) = (Node (Leaf v0) A (Leaf v1))
linearise2 (Node (Node (Leaf v0) B (Leaf v1))
				  A
				 (Node (Leaf v2) C (Leaf v3))
			) = 
-}

addAtTheBottomRightCorner : {A:Type} -> {B:Type} -> {l:List A} -> (t:Tree A B l) -> (x:A) -> (inhabitantOfB : B) -> Tree A B (l++[x])
addAtTheBottomRightCorner (Leaf a) x inhabitantOfB = Node (Leaf a) inhabitantOfB (Leaf x)
addAtTheBottomRightCorner (Node left elem right) x inhabitantOfB ?= Node left elem (addAtTheBottomRightCorner right x inhabitantOfB)






-- Not a good example as we have no problem with the index... ;)
eraseTheBs : {A:Type} -> {B:Type} -> {l:List A} -> (Tree A B l) -> (Tree A Unit l)
eraseTheBs (Leaf a) = Leaf a
eraseTheBs (Node left elem right) = Node (eraseTheBs left) MkUnit (eraseTheBs right)

{-
linearise : {A:Type} -> {B:Type} -> {l:List A} -> (Tree A B l) -> (Tree A B l)
linearise (Leaf a) = Leaf a
linearise (Node left elem right) = 
-}

UnionOfTree : {A:Type} -> {B:Type} -> {l1:List A} -> {l2:List A} -> (Tree A B l1) -> (b:B) -> (Tree A B l2) -> Tree A B (l1++l2)
UnionOfTree t1 b t2 = Node t1 b t2





{-
flatten : {A:Type} -> {B:Type} -> (Tree A B) -> List A
flatten (Leaf a) = [a]
flatten (Node left right elem) = (flatten left) ++ (flatten right)
-}
