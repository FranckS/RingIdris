-- "set", with repetition allowed (ie, lists)
data Set : (A:Type) -> Type where
	EmptySet : {A:Type} -> Set A
	AddElem : {A:Type} -> (a:A) -> (subset:Set A) -> Set A

data In : {A:Type} -> (a:A) -> (Set A) -> Type where
	isHere : {A:Type} -> (a:A) -> (subset:Set A) -> (In a (AddElem a subset))
	isIn : {A:Type} -> (a:A) -> (subset:Set A) -> (In a subset) -> (head:A) -> In a (AddElem head subset)
	
		
data SubSet : {A:Type} -> (Set A) -> (Set A) -> Type where
	EmptySetEquiv : SubSet EmptySet EmptySet	
	SameFirstElemEquiv : {A:Type} -> (subset1:Set A) -> (subset2:Set A) -> (a:A) -> (subsetEq:SubSet subset1 subset2) -> SubSet (AddElem a subset1) (AddElem a subset2)
	DiffFirstElemQuiv : {A:Type} -> (subset1:Set A) -> (subset2:Set A) -> 
						(a1:A) -> (a2:A) -> (In a1 subset2) ->
						(SubSet subset1 (AddElem a2 subset2)) ->
						SubSet (AddElem a1 subset1) (AddElem a2 subset2)

SubSet_refl : {A:Type} -> (s:Set A) -> SubSet s s
SubSet_refl EmptySet = EmptySetEquiv
SubSet_refl (AddElem a subset) = SameFirstElemEquiv subset subset a (SubSet_refl subset)
	
(==) : {A:Type} -> (Set A) -> (Set A) -> Type
(==) s1 s2 = (SubSet s1 s2, SubSet s2 s1)


-- Equivalent to concat for lists
total
(++) : {A:Type} -> (Set A) -> (Set A) -> Set A
(++) Empty s2 = s2
(++) (AddElem a subset) s2 = AddElem a (subset++s2)


left : {A:Type} -> {B:Type} -> (x:(A,B)) -> A
left (a,b) = a

right : {A:Type} -> {B:Type} -> (x:(A,B)) -> B
right (a,b) = b

total
-- unionOfSet is commutative : s1++(s2++s3) == (s1++s2)++s3
unionOfSet_assoc : {A:Type} -> (s1:Set A) -> (s2:Set A) -> (s3:Set A) -> ((s1++(s2++s3)) == ((s1++s2)++s3))
unionOfSet_assoc EmptySet s2 s3 = (SubSet_refl (s2++s3), SubSet_refl (s2++s3)) -- Whaaat ? I could give only s3 !
--unionOfSet_assoc (AddElem a subset) s2 s3 = (SubSet_refl _, SubSet_refl _) -- Whaaaat ? I should prove that (a::subset)++(s2++s3) == ((a::subset)++s2)++s3
																		-- which by reduction is a::(subset++(s2++s3)) == (a::(subset++s2))++s3
																		-- which by a second reduction is a::(subset++(s2++s3)) == a::((subset++s2)++s3)
																		-- which means that I should REALLY prove that subset++(s2++s3) == (subset++s2)++s3 (by the induction hypothesis)
unionOfSet_assoc (AddElem a subset) s2 s3 = 
	let inductionHypothesis : (subset++(s2++s3) == (subset++s2)++s3) = unionOfSet_assoc subset s2 s3 in 
	let x = (SameFirstElemEquiv (subset++(s2++s3)) ((subset++s2)++s3) a (left inductionHypothesis)) in
	let y = (SameFirstElemEquiv ((subset++s2)++s3) (subset++(s2++s3)) a (right inductionHypothesis)) in -- Nonsense ! I could use left here
		?MO


unionOfSet_comm : {A:Type} -> (s1:Set A) -> (s2:Set A) -> ((s1++s2) == (s2++s1))
unionOfSet_comm EmptySet (AddElem a2 subset2) = ?MF -- (SubSet_refl _, SubSet_refl _)


	
data Tree : (A:Type) -> Set A -> Type where
	Leaf : {A:Type} -> (a:A) -> Tree A (AddElem a EmptySet)
	Node : {A:Type} -> {s1:Set A} -> {s2:Set A} -> (left:Tree A s1) -> (elem:A) -> (right:Tree A s2) -> Tree A (s1++s2)

	
sortTree : {A:Type} -> (Ord A) -> {s1:Set A} -> (Tree A s1) -> (s2 ** (Tree A s2, s1==s2))
sortTree ord (Leaf a) = (_ ** (Leaf a, (SameFirstElemEquiv EmptySet EmptySet a EmptySetEquiv)))
	
	
	