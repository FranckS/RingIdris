-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reflection.idr
-- Reflect the concrete values into the abstract syntax
-------------------------------------------------------------------

module Provers.reflection


import Decidable.Equality
import Data.ZZ
import Data.Fin
import Provers.dataTypes
import Provers.tools

import Provers.ring_reduce

import Provers.ring_test
import Provers.commutativeGroup_test
import Provers.group_test
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test


-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Notes about the refleciton mechanism :
-- --------------------------------------
-- Edwin has switch from Fin to Elem in order to represent variables, which was a good idea, and which is particularly useful for the reflection machinery.
-- Unfortunately, I've developped the entire collection of provers with Fin. Instead of changing completely the provers (that would be a nightmare as Fin is present everywhere !), 
-- I'll just adapt the automatic reflection, which becomes a bit more complicated.
-- The key element of my reflection machinery is the usage of the function isElement, which returns an index AND the proof that this index effectively works. That enables
-- to simulate the behaviour of Elem that I do not have. I would say that my approach for the reflection is therefore the usual Coq approach, in the sense that I use many more external lemmas.
-- ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------


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
		

-- -----------------------
-- TEST FROM Nat TO MAGMA
-- -----------------------
	
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
    
        
    
-- Just a trivial try : Reflects only from Nat to a Magma  
-- %logging 1   
%reflection
reflectTermNat : {n:Nat} -> (g : Vect n Nat) -> (x:Nat) -> (n' ** (g':Vect n' Nat ** (ExprMa {c=Nat} {n=n+n'} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (g ++ g') x)))
reflectTermNat {n=n} g (a+b) with (reflectTermNat g a)
  reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) with (reflectTermNat (g ++ g') b) 
    reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusMa (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (weaken g'' a') b' in
	  ((n' + n'') ** ((g'++g'') ** (convertVectInExprMa (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
	  -- Fix Idris : Huge problem if convertVectInExprMa was taking proofs that (n=n') and (g=g') (instead of the other way arround) and if I give the "sym" for these proofs here.
-- %logging 0  
reflectTermNat {n=n} g t with (isElement t g)
	| Just (i ** p) = let this = VarMa {c=Nat} {n=n+Z} {g=g++Data.VectType.Vect.Nil} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (RealVariable {n=n+Z} _ _ _ (g++Data.VectType.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
							 ?MreflectTermNat_1 -- (Z ** (Data.VectType.Vect.Nil ** this))
	| Nothing = let this = VarMa {c=Nat} {n=n+S Z} {g=g++[t]} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
							 ?MreflectTermNat_2 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))  
  
 
-- ----------------------
-- TEST FROM ZZ TO RING
-- ----------------------
 
 
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
    
    
 
-- Reflects only from ZZ to Ring 
%reflection
reflectTermZForRing : {n:Nat} -> (g : Vect n ZZ) -> (x:ZZ) -> (n' ** (g':Vect n' ZZ ** (ExprR {c=ZZ} {n=n+n'} (%instance) (g ++ g') x)))
-- reflectTermZForRing g arg = ?MTRUC
reflectTermZForRing {n=n} g (a+b) with (reflectTermZForRing g a)
  reflectTermZForRing {n=n} g (a+b) | (n' ** (g' ** a')) with (reflectTermZForRing (g ++ g') b) 
    reflectTermZForRing {n=n} g (a+b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusR (weakenR g'' a') b' in
	  ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
reflectTermZForRing {n=n} g t with (isElement t g)
	| Just (i ** p) = let this = VarR {c=ZZ} {n=n+Z} {g=g++Data.VectType.Vect.Nil} (%instance) (RealVariable {n=n+Z} _ _ _ (g++Data.VectType.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
							 ?MreflectTermZForRing_1 -- (Z ** (Data.VectType.Vect.Nil ** this))
	| Nothing = let this = VarR {c=ZZ} {n=n+S Z} {g=g++[t]} (%instance) (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
							 ?MreflectTermZForRing_2 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))  
  
 
 
-- Let's try the automatic reflection
{-
expCr_automatic : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ExprR (%instance) [x,y,u,g] (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g))))
expCr_automatic x y u g = rightDep (rightDep (reflectTermZForRing [] (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) ))

exprC2r_automatic : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ExprR (%instance) [x,y,u,g] ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
exprC2r_automatic x y u g = rightDep (rightDep (reflectTermZForRing [] ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))) ))

compare_automatic : (x:ZZ) -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> Maybe ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
compare_automatic x y u g = ringDecideEq (%instance) (expCr_automatic x y u g) (expC2r_automatic x y u g) 

-- Later, we will have a real tactic "Ring" which can fail. At this point, we will
-- not have a missing case																																																																								 for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_automatic : (x:ZZ) -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
proof_automatic x y u g = let (Just ok) = compare_automatic x y u g in ok 
-} 
 
 
full_auto : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
full_auto x y u g = let (nbAddedLHS ** (gAddedLHS ** lhs)) = reflectTermZForRing [] (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) in
						 let (nbAddedRHS ** (gAddedRHS ** rhs)) = reflectTermZForRing gAddedLHS ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))) in
							let (Just ok) = ringDecideEq (%instance) (lhs x y u g) (rhs x y u g) in ok
 
 
 
-- ---------------------------------------------------
-- GENERALISED VERSION GOING FROM ANY TYPE c TO MAGMA
-- ---------------------------------------------------


%reflection
reflectTerm : {c:Type} -> {n:Nat} -> (p:Magma c) -> (g : Vect n c) -> (x:c) -> (g' ** (ExprMa p (neg (FakeSetAndNeg (%instance))) (FakeSetAndMult (%instance)) (g ++ g') x))
reflectTerm p g (Plus a b) =
--	let (g' ** a') = reflectTerm p g a in
--	let (g'' ** ys') = reflectTerm p (g ++ g') b in
		?REAL_REFLECTION_TO_DO
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

Provers.reflection.MisElement_1 = proof
  intros
  compute
  exact p'  
  
Provers.reflection.MreflectTermNat_1 = proof
  intros
  mrefine MkSigma
  exact Z
  compute
  mrefine MkSigma
  exact Nil
  compute
  rewrite p
  rewrite (index_n_plus_0 g i)
  exact this  
  
Provers.reflection.MreflectTermNat_2 = proof
  intros
  mrefine MkSigma
  exact (S Z)
  compute
  mrefine MkSigma
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this)  

Provers.reflection.MreflectTermZForRing_1 = proof
  intros
  mrefine MkSigma
  exact Z
  compute
  mrefine MkSigma
  exact Nil
  compute
  rewrite p
  rewrite (index_n_plus_0 g i)
  exact this  
  
Provers.reflection.MreflectTermZForRing_2 = proof
  intros
  mrefine MkSigma
  exact (S Z)
  compute
  mrefine MkSigma
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this)  