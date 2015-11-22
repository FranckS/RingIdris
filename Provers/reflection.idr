-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reflection.idr
-- Reflect the concrete values into the abstract syntax
-------------------------------------------------------------------

module Provers.reflection


import Decidable.Equality
import Data.Fin
import Provers.dataTypes
import Provers.tools

import Provers.magma_test

-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- PREVIOUS ATTEMPT WITH ELEM (Edwin's Idea)
-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------

{-
data Elem : c -> Vect n c -> Type where
	Stop : Elem x (x :: xs)
	Pop : Elem x ys -> Elem x (y :: xs)    
    

isElem : {c:Type} -> {n:Nat} -> (x : c) -> (g : Vect n c) -> Maybe (Elem x g)
isElem x [] = Nothing
isElem x (y :: ys) with (prim__syntactic_eq _ _ x y)
	isElem x (x :: ys) | Just Refl = [| Stop |]
	isElem x (y :: ys) | Nothing = [| Pop (isElem x ys) |]    

	
weakenElem : {c:Type} -> {n:Nat} -> {m:Nat} -> {g:Vect n c} -> (g' : Vect m c) -> Elem x g -> Elem x (g' ++ g)
weakenElem [] p = p
weakenElem (g'_head :: g'_tail) p = Pop (weakenElem g'_tail p)	
-}

{-
weakenElem : {n:Nat} -> (m:Nat) -> Fin n -> Fin (m+n)
weakenElem {n} m i = 
	let fin_n_m : Fin (n+m) = convertFin _ i m in
	let prAux1:(n+m=m+n) = plusCommutative n m in
		?MweakenElem_1
		-}	 


-- fin_to_elem : {c:Type} -> {n:Nat} -> (g:Vect n c) -> (x:c) -> 	
	
	
-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- My attempt : directly with Fin. Which is good since I've chosen to work with Fin at the start (not not with Elem). Unfortunately, that was certainly a little mistake) ---
-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------


total	
lemmaExtension : {c:Type} -> {n:Nat} ->	{m:Nat} -> (g:Vect n c) -> (g':Vect m c) -> (i:Fin n) -> (index i g = index (convertFin _ i m) (g++g'))
lemmaExtension Nil g' (FZ {k=k}) impossible
lemmaExtension (gh::gt) g' (FZ {k=k}) = Refl
lemmaExtension (gh::gt) g' (FS {k=Z} pi) = let proofOfFalse : Void = elimFinZero pi in -- Just elim the element of (Fin 0) that we have in the context to build an inhabitant of False (Void)
					       ?MlemmaExtension_1 -- Just elim the inhabitant of False that we have constructed in the context
lemmaExtension (gh::gt) g' (FS {k=S pk} pi) = let ih = lemmaExtension gt g' pi in ?MlemmaExtension_2
						  
	
-- NOT total : We don't treat if the variable is not a real variable, but we don't care since fake variables are only for encodings, and the user will never use them directly
weaken : {c:Type} -> {p:Magma c} -> {n:Nat} -> {m:Nat} -> {g:Vect n c} -> (g':Vect m c) -> (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) g x) -> (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) (g ++ g') x)
weaken g' (ConstMa _ _ _ g const1) = ConstMa _ _ _ (g++g') const1
weaken g' (PlusMa _ _ e1 e2) = PlusMa _ _ (weaken g' e1) (weaken g' e2)
weaken {n=n} {m=m} {g=g} g' (VarMa p _ _ (RealVariable _ _ _ _ i)) =
	let pExt = lemmaExtension g g' i in
		rewrite pExt in (VarMa {n=plus n m} p _ _ (RealVariable _ _ _ _ (convertFin _ i m))) 

    
total
convertVectInExprMa : {c:Type} -> {p:Magma c} -> {n:Nat} -> {g:Vect n c} -> {x:c} -> 
		      {n':Nat} -> {g':Vect n' c} -> (n'=n) -> (g'=g) ->
			  (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) g x) ->
			  (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) g' x)
convertVectInExprMa prEqN prEqG e with (prEqN)
  convertVectInExprMa prEqN prEqG e | (Refl) with (prEqG)
    convertVectInExprMa prEqN prEqG e | (Refl) | (Refl) = e -- Fix Idris : it works if I give directly e but if I put a metavariable, there's a bug when I try to prove it
    
-- Just a trivial try : Reflects only from Nat    
-- %logging 1   
%reflection
reflectTermNat : {n:Nat} -> (g : Vect n Nat) -> (x:Nat) -> (n' ** (g' ** (ExprMa {n=n+n'} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (g ++ g') x)))
reflectTermNat {n=n} g (a+b) with (reflectTermNat g a)
  reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) with (reflectTermNat (g ++ g') b) 
    reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusMa (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (weaken g'' a') b' in
	  ((n' + n'') ** ((g'++g'') ** (convertVectInExprMa (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
	  -- Fix Idris : Huge problem if convertVectInExprMa was taking proofs that (n=n') and (g=g') (instead of the other way arround) and if I give the "sym" for these proofs here.
-- %logging 0  
  
  

-- Generalized version
%reflection
reflectTerm : {c:Type} -> {n:Nat} -> (p:Magma c) -> (g : Vect n c) -> (x:c) -> (g' ** (ExprMa p (neg (FakeSetAndNeg (%instance))) (FakeSetAndMult (%instance)) (g ++ g') x))
reflectTerm p g (Plus a b) =
--	let (g' ** a') = reflectTerm p g a in
--	let (g'' ** ys') = reflectTerm p (g ++ g') b in
		?MZ 
{- ((g' ++ g'') **
							rewrite (sym (appendAssociative g g' g'')) in
								PlusMa (weaken g'' a') b')
   
   -}	
   
   

---------- Proofs ----------   

Provers.reflection.MlemmaExtension_1 = proof
  intros
  exact (void proofOfFalse)  
  
Provers.reflection.MlemmaExtension_2 = proof
  intros
  rewrite (sym ih)
  rewrite (pre_convertFin_proofIrr pi _ (LTESucc (GTE_plus pk m)) (GTE_plus (S pk) m))
  mrefine Refl


  
  
  