-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reflectionTools.idr
-- Tools for the reflection (used in reflection.idr and in reflectionForSpecificDataTypes.idr)
-------------------------------------------------------------------

module Provers.reflectionTools

import Decidable.Equality
import Data.ZZ
import Data.Fin
import Data.Vect
import Provers.dataTypes
import Provers.tools


%access public export



-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Notes about the reflection mechanism :
-- --------------------------------------
-- Edwin has switch from Fin to Elem in order to represent variables, which was a good idea, and which is particularly useful for the reflection machinery.
-- Unfortunately, I've developped the entire collection of provers with Fin. Instead of changing completely the provers (that would be a nightmare as Fin is present everywhere !), 
-- I'll just adapt the automatic reflection, which becomes a bit more complicated.
-- The key element of my reflection machinery is the usage of the function isElement, which returns an index AND the proof that this index effectively works. That enables
-- to simulate the behaviour of Elem that I haven't used. I would say that my approach for the reflection is therefore the usual Coq approach, in the sense that I use more external lemmas.
-- ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- --------------------------------------
-- GENERAL REFLECTION TOOLS FOR RING ---
-- --------------------------------------
total	
lemmaExtension : {c:Type} -> {n:Nat} ->	{m:Nat} -> (g:Vect n c) -> (g':Vect m c) -> (i:Fin n) -> (index i g = index (convertFin _ i m) (g++g'))
lemmaExtension Nil g' (FZ {k=k}) impossible
lemmaExtension (gh::gt) g' (FZ {k=k}) = Refl
lemmaExtension (gh::gt) g' (FS {k=Z} pi) = let proofOfFalse : Void = elimFinZero pi in -- Just elim the element of (Fin 0) that we have in the context to build an inhabitant of False (Void)
					       ?MlemmaExtension_1 -- Just elim the inhabitant of False that we have constructed in the context
lemmaExtension (gh::gt) g' (FS {k=S pk} pi) = let ih = lemmaExtension gt g' pi in ?MlemmaExtension_2
						  
	
	
total
isElement : {a:Type} -> {n:Nat} -> (x : a) -> (G : Vect n a) -> Maybe (i:Fin n ** (index i G = x))
isElement x [] = Nothing
isElement x (y :: ys) with (prim__syntactic_eq _ _ x y)
	isElement x (x :: ys) | Just Refl = Just (FZ ** Refl) -- [| Stop |]
	isElement x (y :: ys) | Nothing = let recCall = isElement x ys in 
				       -- [| Pop (isElem x ys) |]  
					case recCall of
						Nothing => Nothing
						Just (i' ** p') => Just ((FS i') ** ?MisElement_1) 	

						
						
-- ---------------------------------------
-- SPECIFIC REFLECTION TOOLS FOR MAGMA ---
-- ---------------------------------------	

-- NOT total : We don't treat if the variable is not a real variable, but we don't care since fake variables are only for encodings, and the user will never use them directly
weakenMa : {c:Type} -> {p:Magma c} -> {n:Nat} -> {m:Nat} -> {g:Vect n c} -> (g':Vect m c) -> (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) g x) -> (ExprMa p (neg (FakeSetAndNeg (magma_to_set_class p))) (FakeSetAndMult (magma_to_set_class p)) (g ++ g') x)
weakenMa g' (ConstMa _ _ _ g const1) = ConstMa _ _ _ (g++g') const1
weakenMa g' (PlusMa _ _ e1 e2) = PlusMa _ _ (weakenMa g' e1) (weakenMa g' e2)
weakenMa {n=n} {m=m} {g=g} g' (VarMa p _ _ (RealVariable _ _ _ _ i)) =
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
						
-- --------------------------------------
-- SPECIFIC REFLECTION TOOLS FOR RING ---
-- --------------------------------------

-- NOT total : We don't treat if the variable is not a real variable, but we don't care since fake variables are only for encodings, and the user will never use them directly
weakenR : {c:Type} -> {p:Ring c} -> {n:Nat} -> {m:Nat} -> {g:Vect n c} -> (g':Vect m c) -> (ExprR p g x) -> (ExprR p (g ++ g') x)
weakenR g' (ConstR _ g const1) = ConstR _ (g++g') const1
weakenR g' (PlusR e1 e2) = PlusR (weakenR g' e1) (weakenR g' e2)
weakenR {n=n} {m=m} {g=g} g' (VarR p (RealVariable _ _ _ _ i)) =
	let pExt = lemmaExtension g g' i in
		rewrite pExt in (VarR {n=plus n m} p (RealVariable _ _ _ _ (convertFin _ i m)))  
 
 
total
convertVectInExprR : {c:Type} -> {p:Ring c} -> {n:Nat} -> {g:Vect n c} -> {x:c} -> 
		      {n':Nat} -> {g':Vect n' c} -> (n'=n) -> (g'=g) ->
			  (ExprR p g x) ->
			  (ExprR p g' x)
convertVectInExprR prEqN prEqG e with (prEqN)
  convertVectInExprR prEqN prEqG e | (Refl) with (prEqG)
    convertVectInExprR prEqN prEqG e | (Refl) | (Refl) = e -- Fix Idris : it works if I give directly e but if I put a metavariable, there's a bug when I try to prove it
    
total
TypeReflectConstants : {c:Type} -> (p:Ring c) -> Type
TypeReflectConstants {c=c} p = ({n:Nat} -> (g:Vect n c) -> (x:c) -> Maybe (ExprR p g x))	

						
---------- Proofs ----------

Provers.reflectionTools.MlemmaExtension_1 = proof
  intros
  exact (void proofOfFalse)  
  
Provers.reflectionTools.MlemmaExtension_2 = proof
  intros
  rewrite (sym ih)
  rewrite (pre_convertFin_proofIrr pi _ (LTESucc (GTE_plus pk m)) (GTE_plus (S pk) m))
  mrefine Refl

Provers.reflectionTools.MisElement_1 = proof
  intros
  compute
  exact p'  						
  
  
