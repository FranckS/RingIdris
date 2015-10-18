import Data.Fin


eq_dec_fin : {n:Nat} -> (i:Fin n) -> (j:Fin n) -> (Maybe (i=j))
eq_dec_fin FZ FZ = Just Refl
eq_dec_fin FZ (FS j') = Nothing
eq_dec_fin (FS i') FZ = Nothing
eq_dec_fin (FS i') (FS j') with (eq_dec_fin i' j')
	eq_dec_fin (FS i') (FS i') | (Just Refl) = Just Refl
	eq_dec_fin (FS i') (FS j') | Nothing = Nothing



data RegularExpression : (A:Type) -> Type where -- A is the alphabet on which we are constructing regular expressions
	-- Two constants
	Epsilon : {A:Type} -> RegularExpression A -- Empty word
	Empty : {A:Type} -> RegularExpression A -- No word
	
	-- symbols of the alphabet
	Symbol : {A:Type} -> A -> RegularExpression A
	
	-- The union of languages, like "u + v"
	(+) : {A:Type} -> RegularExpression A -> RegularExpression A -> RegularExpression A
	
	-- The concatenation of languages, like "u.v"
	(.) : {A:Type} -> RegularExpression A -> RegularExpression A -> RegularExpression A
	
	-- Star operation, like r*
	Star : {A:Type} -> RegularExpression A -> RegularExpression A
	

infixr 5 ~=
-- The quivalence on Regular Expressions
data (~=) : {A:Type} -> RegularExpression A -> RegularExpression A -> Type where
	
	-- If the two things are the same, then they are equivalent
	SyntacticalEqual : {A:Type} -> (r:RegularExpression A) -> r ~= r

	-- Is it the best way to do it ?
	RE_eq_Symmetry : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (r ~= s) -> s ~= r
	
	-- --------- --
	-- SemiGroup --
	-- --------- --
	
	-- Union of languages is associative
	UnionAssociative : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (t:RegularExpression A) -> ((r+s) + t) ~= (r + (s+t))
	
	-- ------ --
	-- Monoid --
	-- ------ --
	
	-- Empty is neutral for the +
	UnionNeutral_1 : {A:Type} -> (r:RegularExpression A) -> (r + Empty) ~= r
	UnionNeutral_2 : {A:Type} -> (r:RegularExpression A) -> (Empty + r) ~= r
	
	-- ------------------ --
	-- Commutative Monoid --
	-- ------------------ --
	
	-- The union of languages is commutative
	UnionCommutative : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (r + s) ~= (s + r)
	
	-- ------------- --
	-- Pre Semi-Ring --
	-- ------------- --
	
	-- The product of languages is associative
	ProductAssociative : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (t:RegularExpression A) -> ((r.s) . t) ~= (r . (s.t))
	
	-- Epsilon is neutral for the product
	ProductNeutral_1 : {A:Type} -> (r:RegularExpression A) -> (r . Epsilon) ~= r
	ProductNeutral_2 : {A:Type} -> (r:RegularExpression A) -> (Epsilon . r) ~= r
	
	-- Distributivity of the product of languages over the Plus
	ProductDistributiveOverPlus_1 : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (t:RegularExpression A) -> (r . (s+t)) ~= ((r.s) + (s.t)) -- REALLY ? I have to spaces dots between the ".' otherwise it doesn't typecheck ?
	ProductDistributiveOverPlus_2 : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (t:RegularExpression A) -> ((s+t) . r) ~= ((s . r) + (t . r))	 -- This little problem doesn't happen here
	
	-- ------------------------------- --
	-- Pre Semi-Ring with extra axioms --
	-- ------------------------------- --
	
	-- Empty is also an absorbing element of the multiplication
	ProductAbsorbingElement_1 : {A:Type} -> (r:RegularExpression A) -> (r . Empty) ~= Empty -- I think it can be PROVED !
	ProductAbsorbingElement_2 : {A:Type} -> (r:RegularExpression A) -> (Empty . r) ~= Empty -- Same !
	
	-- Idempotence of +
	UnionIdempotence : {A:Type} -> (r:RegularExpression A) -> (r+r) ~= r
	
	-- For the star operator
	StarAx1 : {A:Type} -> (r:RegularExpression A) -> (Star (Star r)) ~= (Star r)            -- (r*)* = r*
	StarAx2 : {A:Type} -> (r:RegularExpression A) -> ((Star r).(Star r)) ~= (Star r)        -- r*.r* = r*
	StarAx3 : {A:Type} -> (r:RegularExpression A) -> (Star (Epsilon+r)) ~= (Star r)         -- (epsilon+r)* = r*
	StarAx4 : {A:Type} -> (r:RegularExpression A) -> ((Star r).(r+Epsilon)) ~= (Star r)     -- r*.(r+epsilon) = r*
	StarAx5 : {A:Type} -> (r:RegularExpression A) -> ((r+Epsilon).(Star r)) ~= (Star r)     -- (r+epsilon).r* = r* [needed even with StarEx4 as the product is NOT commutative]
	StarAx6 : {A:Type} -> (r:RegularExpression A) -> (Epsilon+(r . (Star r))) ~= (Star r)   -- epsilon + r.r* = r*
	StarAx7 : {A:Type} -> (r:RegularExpression A) -> (Epsilon+((Star r).r)) ~= (Star r)     -- epsilon + r*.r = r* [also needed even with StarAx6 as the product is NOT commutative]

	
	


-- Now, lemmas...
	
-- -----------------------------------
-- RE_eq is an equivalence relation --
-- -----------------------------------

-- Reflexivity : forall r, r=r
total
RE_eq_refl : {A:Type} -> (r:RegularExpression A) -> r ~= r
RE_eq_refl r = SyntacticalEqual r -- Easy, we have it by definition

-- Symmetry : forall r,s, r=s -> s=r
total
RE_eq_sym : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (r ~= s) -> (s ~= r)
RE_eq_sym r s p = RE_eq_Symmetry r s p -- Same here : it's easy as we have it by definition

-- Transitivity : forall r,s,t, r=s -> s=t -> r=t
RE_eq_transitivity : {A:Type} -> (r:RegularExpression A) -> (s:RegularExpression A) -> (t:RegularExpression A) -> (r ~= s) -> (s ~= t) -> (r ~= t)
-- RE_eq_transitivity r _ _ (SyntacticalEqual r) (SyntacticalEqual r) = SyntacticalEqual r
-- More generally :
RE_eq_transitivity _ _ _ (SyntacticalEqual _) p2 = p2
-- To be continued...


-- This thing should certainly be an axiom (ie, in the definition of "~=".
-- I don't think there's any way to prove it
Product_preserves_eq : {A:Type} -> (r1 : RegularExpression A) -> (r1' : RegularExpression A) -> 
	(r2 : RegularExpression A) -> (r2' : RegularExpression A) -> (r1 ~= r1') -> (r2 ~= r2') -> (r1 . r2 ~= r1' . r2')
Product_preserves_eq r1 r1' r2 r2' p1 p2 = ?MProduct_preserves_eq_1	

	
-- Huuum... Is it really better to have this axiom rather than ProductAbsorbingElement_2 ?
addLeft : {A:Type} -> (r1 : RegularExpression A) -> (r2 : RegularExpression A) -> (left : RegularExpression A) -> (left+r1 ~= left+r2) -> (r1~=r2)
addLeft _ _ left (SyntacticalEqual (left+r1)) = SyntacticalEqual r1
addLeft r1 r2 left (RE_eq_Symmetry (left+r2) (left+r1) p) = ?MX
-- Huuum...	
	
	
-- This is an attempt of proving one of the axioms (ProductAbsorbingElement_2) defining the equivalence relation on regular expression
pr_ProductAbsorbingElement_2 : {A:Type} -> (r:RegularExpression A) -> ((Empty . r) ~= Empty)
pr_ProductAbsorbingElement_2 r = let paux1 : (r . r ~= (r + Empty) . r) = ?Mpr_ProductAbsorbingElement_2_1 in
			let paux2 : ((r + Empty) . r ~= (r . r) + (Empty . r)) = ProductDistributiveOverPlus_2 _ _ _ in
			let paux3 : (r . r ~= (r . r) + (Empty . r)) = ?Mpr_ProductAbsorbingElement_2_2 in -- Uses the transitivity of eq with the two proofs paux1 and paux2
				?Mpr_ProductAbsorbingElement_2_3 -- Yes, I can do it without having the lemma x = x + y -> 0 = y ! (Reminder : we are in a pre semi-ring only, not a ring, we don't have Minus here)



data ProductionRule : (A:Type) -> (n:Nat) -> Type where -- A production rule for a grammar with at most n non-terminals symbols
	Prod1 : {A:Type} -> {n:Nat} -> (X:Fin n) -> (a:A) -> (Y:Fin n) -> ProductionRule A n -- X -> a Y
	Prod2 : {A:Type} -> {n:Nat} -> (X:Fin n) -> (a:A) -> ProductionRule A n -- X -> a
	Prod3 : {A:Type} -> {n:Nat} -> (X:Fin n) -> ProductionRule A n -- X -> Epsilon
	Prod4 : {A:Type} -> {n:Nat} -> (X:Fin n) -> (Y:Fin n) -> ProductionRule A n -- X -> Y
	

-- A (right regular) grammar (with n non terminals) is a collection of rules
data Grammar : (A:Type) -> (n:Nat) -> Type where
	AddProdRule : {A:Type} -> {n:Nat} -> (ProductionRule A n) -> (Grammar A n) -> Grammar A n 
	AddLastProdRule : {A:Type} -> {n:Nat} -> (ProductionRule A n) -> Grammar A n


-- Grammar -> regular expressions

{-
-- Given a grammar G, and a non terminal U in this grammar, simply computes the language (represented a regular expression) generated by the non terminal U
languageOfNonTerminal : {A:Type} -> {n:Nat} -> (Grammar A n) -> (U:Fin n) -> RegularExpression A
languageOfNonTerminal (AddProdRule (Prod1 X a Y) g) U with (eq_dec_fin U X)
	languageOfNonTerminal (AddProdRule (Prod1 X a Y) g) U | Just prEq = (Symbol a) . (languageOfNonTerminal (AddProdRule (Prod1 X a Y) g) Y) -- The problem here is that we can't ignore this production rule (Prod1 X Y a) now, as it might be needed for computing the language associated with the non terminal Y
	languageOfNonTerminal (AddProdRule (Prod1 X a Y) g) U | Nothing = languageOfNonTerminal (AddProdRule (Prod1 X a Y) g) U -- Same problem here ! And this will loop forever !
-- We can't do it directly ! Otherwise, that will almost always never terminate. We need to go through the equation of languages
-}

-- Either a terminal (from the alphabet A) or a non-terminal (which belongs to n non-terminals)
data TerminalOrNonTerminal : (A:Type) -> (n:Nat) -> Type where
	Terminal :  {A:Type} -> (a:A) -> TerminalOrNonTerminal A n
	NonTerminal : {A:Type} -> (U:Fin n) -> TerminalOrNonTerminal A n
	

-- Just gather all the equations associated with a non terminal
total
equationOfNonTerminal : {A:Type} -> {n:Nat} -> (Grammar A n) -> (U:Fin n) -> RegularExpression (TerminalOrNonTerminal A n)
equationOfNonTerminal (AddProdRule (Prod1 X a Y) g') U with (eq_dec_fin U X) 
	equationOfNonTerminal (AddProdRule (Prod1 X a Y) g') U | Just prEq = ((Symbol (Terminal a)) . (Symbol (NonTerminal Y))) + equationOfNonTerminal g' U -- All the difference is here : we don't unfold Y here
	equationOfNonTerminal (AddProdRule (Prod1 X a Y) g') U | Nothing = equationOfNonTerminal g' U
equationOfNonTerminal (AddProdRule (Prod2 X a) g') U with (eq_dec_fin U X)
	equationOfNonTerminal (AddProdRule (Prod2 X a) g') U | Just prEq = (Symbol (Terminal a)) + equationOfNonTerminal g' U
	equationOfNonTerminal (AddProdRule (Prod2 X a) g') U | Nothing = equationOfNonTerminal g' U
equationOfNonTerminal (AddProdRule (Prod3 X) g') U with (eq_dec_fin U X)
	equationOfNonTerminal (AddProdRule (Prod3 X) g') U | Just prEq = Epsilon + equationOfNonTerminal g' U
	equationOfNonTerminal (AddProdRule (Prod3 X) g') U | Nothing = equationOfNonTerminal g' U
equationOfNonTerminal (AddProdRule (Prod4 X Y) g') U with (eq_dec_fin U X)
	equationOfNonTerminal (AddProdRule (Prod4 X Y) g') U | Just prEq = (Symbol (NonTerminal Y)) + (equationOfNonTerminal g' U)
	equationOfNonTerminal (AddProdRule (Prod4 X Y) g') U | Nothing = (equationOfNonTerminal g' U)
-- For the last production rule
equationOfNonTerminal (AddLastProdRule (Prod1 X a Y)) U with (eq_dec_fin U X)
	equationOfNonTerminal (AddLastProdRule (Prod1 X a Y)) U | Just prEq = (Symbol (Terminal a)) . (Symbol (NonTerminal Y))
	equationOfNonTerminal (AddLastProdRule (Prod1 X a Y)) U | Nothing = Empty
equationOfNonTerminal (AddLastProdRule (Prod2 X a)) U with (eq_dec_fin U X)
	equationOfNonTerminal (AddLastProdRule (Prod2 X a)) U | Just prEq = Symbol (Terminal a)
	equationOfNonTerminal (AddLastProdRule (Prod2 X a)) U | Nothing = Empty
equationOfNonTerminal (AddLastProdRule (Prod3 X)) U with (eq_dec_fin U X)
	equationOfNonTerminal (AddLastProdRule (Prod3 X)) U | Just prEq = Epsilon
	equationOfNonTerminal (AddLastProdRule (Prod3 X)) U | Nothing = Empty
equationOfNonTerminal (AddLastProdRule (Prod4 X Y)) U with (eq_dec_fin U X)
	equationOfNonTerminal (AddLastProdRule (Prod4 X Y)) U | Just prEq = (Symbol (NonTerminal Y))
	equationOfNonTerminal (AddLastProdRule (Prod4 X Y)) U | Nothing = Empty
	

total
unwrap : {A:Type} -> {n:Nat} -> RegularExpression (TerminalOrNonTerminal A n) -> (RegularExpression A) 
unwrap (Symbol (Terminal a)) = Symbol a
unwrap (Symbol (NonTerminal N)) = ?AXIOM_UNWRAP_TOTAL
unwrap Epsilon = Epsilon
unwrap Empty = Empty
unwrap (e1+e2) = (unwrap e1) + (unwrap e2)
unwrap (e1 . e2) = (unwrap e1) . (unwrap e2)
unwrap (Star e) = Star (unwrap e)


-- Solves the equation X=eq where eq is an equation (a regular expression with terminals or the non terminal X)
total
ardenSolver : {A:Type} -> {n:Nat} -> (X:Fin n) -> (eq:RegularExpression (TerminalOrNonTerminal A n)) -> RegularExpression A
-- Solving equations live X = a.X + b, or X = b + a.X, or X = a.X (note : it can't be X = X.a because we deal with right regular grammars)
-- X = a.X + b -> X = a*.b by Arden theorem
ardenSolver X ((a . (Symbol (NonTerminal Y))) + b) = -- Y can only be X because we've unfolded all the non terminals which were not X
    (Star (unwrap a)) . (unwrap b)
-- X = b + a.X -> X = a*.b by Arden theorem
ardenSolver X (b + (a . (Symbol (NonTerminal Y)))) = -- Y can only be X because we've unfolded all the non terminals which were not X
    (Star (unwrap a)) . (unwrap b)
-- X = a.X -> X = Empty by Arden Theorem (because X = aX -> X = aX + Empty -> X = a*.Empty = Empty, which cas also be seen because there's no rule for stoping the recursivity)
ardenSolver X (a . (Symbol (NonTerminal Y))) = 
    -- the equation X = a.X has Empty for solution : "there's no rule for stoping the recursivity"
    Empty 
ardenSolver X other = unwrap other


total
wrap : {A:Type} -> {n:Nat} -> (RegularExpression A) -> RegularExpression (TerminalOrNonTerminal A n)
wrap (Symbol a) = Symbol (Terminal a)
wrap Epsilon = Epsilon
wrap Empty = Empty
wrap (e1+e2) = (wrap e1) + (wrap e2)
wrap (e1 . e2) = (wrap e1) . (wrap e2)
wrap (Star e) = Star (wrap e)


mutual
	-- Unfold all the non terminals in the regular expression, appart from the non terminal N
	unfold : {A:Type} -> {n:Nat} -> (Grammar A n) -> (RegularExpression (TerminalOrNonTerminal A n)) -> (N:Fin n) -> RegularExpression (TerminalOrNonTerminal A n)
	unfold g Epsilon N = Epsilon
	unfold g Empty N = Empty
	unfold g (Symbol (Terminal a)) N = Symbol (Terminal a)
	unfold g (Symbol (NonTerminal X)) N with (eq_dec_fin X N) 
		unfold g (Symbol (NonTerminal X)) N | Nothing = wrap (languageOfNonTerminal g X) 
		unfold g (Symbol (NonTerminal X)) N | Just prEq = Symbol (NonTerminal X) -- We don't unfold N !  
	unfold g (e1+e2) N = (unfold g e1 N) + (unfold g e2 N)
	unfold g (e1 . e2) N = (unfold g e1 N) . (unfold g e2 N)
	unfold g (Star e) N = Star (unfold g e N)

	
	languageOfNonTerminal : {A:Type} -> {n:Nat} -> (Grammar A n) -> (U:Fin n) -> RegularExpression A
	languageOfNonTerminal g U = let eq_U = equationOfNonTerminal g U in 
					ardenSolver U (unfold g eq_U U)
	

-- Computes the language generated by a grammar (which contains at least one non terminal, usually denoted S and called the axiom)
languageOfGrammar : {A:Type} -> {pn:Nat} -> (Grammar A (S pn)) -> RegularExpression A
languageOfGrammar g = languageOfNonTerminal g FZ



{- Just a simple testing
g1 = {
	p1 : S -> b U
	p2 : U -> a
	p3 : U -> epsilon
	}
The language should be simply b.(a+epsilon)
-}

-- A simple alphabet
data Alph : Type where
	A : Alph
	B : Alph
	C : Alph
 
-- The 3 simple production rules
-- Reminder : S (called the axiom of the grammar is considered to be FZ, so we have to obei this rule)
p1 : ProductionRule Alph 2
p1 = Prod1 FZ B (FS FZ) -- S -> b U

p2 : ProductionRule Alph 2
p2 = Prod2 (FS FZ) A -- U -> a

p3 : ProductionRule Alph 2
p3 = Prod3 (FS FZ) -- U -> epsilon

-- Grammar over the Alphabet Alph, with 2 non terminals
g1 : Grammar Alph 2
g1 = AddProdRule p1 (AddProdRule p2 (AddLastProdRule p3))


-- Computes automatically the language generated by the grammar g1
L_g1 : RegularExpression Alph
L_g1 = languageOfGrammar g1





{- Just a simple testing
g2 = {
	p1 : S -> a S
	p2 : S -> U
	p3 : U -> b U
	p3 : U -> epsilon
	}
The language should be a*.b*.epsilon (which is simplifiable to a*.b* but that does not matter) 
-}
 
-- The 4 production rules
-- Reminder : S (called the axiom of the grammar is considered to be FZ, so we have to obei this rule)
p1_2 : ProductionRule Alph 2
p1_2 = Prod1 FZ A FZ -- S -> a S

p2_2 : ProductionRule Alph 2
p2_2 = Prod4 FZ (FS FZ) -- S -> U

p3_2 : ProductionRule Alph 2
p3_2 = Prod1 (FS FZ) B (FS FZ) -- U -> b U

p4_2 : ProductionRule Alph 2
p4_2 = Prod3 (FS FZ) -- U -> epsilon

-- Grammar over the Alphabet Alph, with 2 non terminals
g2 : Grammar Alph 2
g2 = AddProdRule p1_2 (AddProdRule p2_2 (AddProdRule p3_2 (AddLastProdRule p4_2)))


-- Computes automatically the language generated by the grammar g2
L_g2 : RegularExpression Alph
L_g2 = languageOfGrammar g2










{-
languageOfNonTerminal' : {A:Type} -> {n:Nat} -> (Grammar A n) -> (U:Fin n) -> RegularExpression A
languageOfNonTerminal' g U = languageOfNonTerminal'_aux g U [] where
	languageOfNonTerminal'_aux : {A:Type} -> {n:Nat} -> (Grammar A n) -> (U:Fin n) -> (list (Fin n)) -> RegularExpression A
	languageOfNonTerminal'_aux g U l = 
		let eqU = equationOfnOnTerminal g U in
		case eqU of
-}		






---------- Proofs ----------

Main.Mpr_ProductAbsorbingElement_2_1 = proof
  intros
  mrefine Product_preserves_eq 
  mrefine RE_eq_sym 
  mrefine RE_eq_refl 
  mrefine UnionNeutral_1

Main.Mpr_ProductAbsorbingElement_2_2 = proof
  intros
  mrefine RE_eq_transitivity 
  exact (r + Empty) . r
  exact paux1
  exact paux2  

Main.Mpr_ProductAbsorbingElement_2_3 = proof
  intros
  mrefine addLeft 
  exact (r . r)
  mrefine RE_eq_transitivity 
  exact (r . r)
  mrefine RE_eq_sym 
  mrefine RE_eq_sym 
  exact paux3
  mrefine UnionNeutral_1
  
  
  
  
  