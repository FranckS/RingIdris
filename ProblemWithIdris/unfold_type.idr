
import Decidable.Equality
import Data.Fin
import Data.Vect


%default total


-- THE PROBLEM :
-- ---------------
-- we want to write and prove this, but we can't because that doesn't typecheck...
-- index_lemma : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vec : Vect n T) -> (eq:n=n') -> (index i vec = index (replace eq i) vec)


-- So my idea is to first define a function which produces the type that we want
-- (and we can write it thanks to a dependent pattern match on the proof of equality eq) :
index_lemma_type : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vec : Vect n T) -> (eq:n=n') -> Type
index_lemma_type i vec eq with (eq)
  index_lemma_type i vec eq | (Refl) = (index i vec = index (replace eq i) vec)
  
-- And now we can write the type of the function that we want
-- (but we can't define it well...)
index_lemma : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vec : Vect n T) -> (eq:n=n') -> (index_lemma_type i vec eq)
index_lemma i vec eq = ?THERE_IS_A_PROBLEM -- there is a problem because idris doesn't unfold index_lemma_type and seems to be stuck in a "with block in...",
					   -- like if index_lemma_type would not be total. But it is total. What's the problem ? How to solve it and to define this proof that I need ?
		   
-- However, it looks like I can prove it if I do again a pattern matching on the proof eq :
index_lemma' : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vec : Vect n T) -> (eq:n=n') -> (index_lemma_type i vec eq)
index_lemma' i vec eq with (eq)
  index_lemma i vec eq | (Refl) = Refl -- Here I can do it. But can I use this property now ? Have I effectively prove index i vec = index (replace eq i) vec ?
  
-- Just a little tool for a  test
plus_one_equals_succ : (n:Nat) -> (n+1 = S n)
plus_one_equals_succ Z = Refl
plus_one_equals_succ (S pn) = let p_ihn : (pn + 1 = S pn) = plus_one_equals_succ pn in ?Mplus_one_equals_succ_1
  

-- Can I use the property index_lemma into another lemma now ?
other_lemma : {T:Type} -> {pn:Nat} -> (i:Fin (S pn)) -> (vec: Vect (S pn) T) -> T
other_lemma {pn=pn} i vec = 
  let paux = index_lemma' i vec (sym(plus_one_equals_succ pn)) in ?NO_I_CANT_USE_IT
      -- No I can't : I don't get any information because Idris doesn't unfold the body of index_lemma_type
  
  
-- And what if I try this stupid thing ?
-- Well, that's not even accepted...
{-
other_lemma' : {T:Type} -> {pn:Nat} -> (i:Fin (S pn)) -> (vec: Vect (S pn) T) -> T
other_lemma' {pn=pn} i vec with (sym(plus_one_equals_succ pn)) 
  other_lemma' {pn=pn} i vec | (Refl) = 
    let paux = index_lemma' i vec (sym(plus_one_equals_succ pn)) in ?NO_I_CANT_USE_IT
-}   
  
  
  
  
-- Proofs  
  
Mplus_one_equals_succ_1 = proof
  intros
  rewrite p_ihn 
  exact Refl    