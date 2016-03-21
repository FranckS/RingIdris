-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reflection.idr
-- Reflect the concrete values into the abstract syntax
-------------------------------------------------------------------

module Provers.reflection


import Decidable.Equality
import Data.ZZ
import Data.Fin
import Data.Vect
import Provers.dataTypes
import Provers.tools

import Provers.ring_reduce

import Provers.ring_test
import Provers.commutativeGroup_test
import Provers.group_test
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test

%access public export

-- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Notes about the refleciton mechanism :
-- --------------------------------------
-- Edwin has switch from Fin to Elem in order to represent variables, which was a good idea, and which is particularly useful for the reflection machinery.
-- Unfortunately, I've developped the entire collection of provers with Fin. Instead of changing completely the provers (that would be a nightmare as Fin is present everywhere !), 
-- I'll just adapt the automatic reflection, which becomes a bit more complicated.
-- The key element of my reflection machinery is the usage of the function isElement, which returns an index AND the proof that this index effectively works. That enables
-- to simulate the behaviour of Elem that I do not have. I would say that my approach for the reflection is therefore the usual Coq approach, in the sense that I use more external lemmas.
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
		

-- -----------------------------------------------
-- REFLECTION FROM Nat (SEEN AS A MAGMA) TO ExprMa
-- -----------------------------------------------
	
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
    
        
    
-- Reflects only from Nat (seen as a Magma) to ExprMa
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
	| Just (i ** p) = let this = VarMa {c=Nat} {n=n+Z} {g=g++Data.Vect.Nil} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (RealVariable {n=n+Z} _ _ _ (g++Data.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
							 ?MreflectTermNat_1 -- (Z ** (Data.VectType.Vect.Nil ** this))
	| Nothing = let this = VarMa {c=Nat} {n=n+S Z} {g=g++[t]} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
							 ?MreflectTermNat_2 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))  
  
 
-- ----------------------------------------------
-- REFLECTION FROM ZZ (SEEN AS A RING) TO ExprR
-- ----------------------------------------------
 
 
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

 
-- Reflects only from ZZ (seen as a Ring) to ExprR 
%reflection
reflectTermZForRing : {n:Nat} -> (g : Vect n ZZ) -> (reflectCst:TypeReflectConstants {c=ZZ} (%instance)) -> (x:ZZ) -> (n' ** (g':Vect n' ZZ ** (ExprR {c=ZZ} {n=n+n'} (%instance) (g ++ g') x)))
-- Reflecting sums...
reflectTermZForRing {n=n} g reflectCst (a+b) with (reflectTermZForRing g reflectCst a)
  reflectTermZForRing {n=n} g reflectCst (a+b) | (n' ** (g' ** a')) with (reflectTermZForRing (g ++ g') reflectCst b) 
    reflectTermZForRing {n=n} g reflectCst (a+b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusR (weakenR g'' a') b' in
	       ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting substractions...
reflectTermZForRing {n=n} g reflectCst (a-b) with (reflectTermZForRing g reflectCst a)
  reflectTermZForRing {n=n} g reflectCst (a-b) | (n' ** (g' ** a')) with (reflectTermZForRing (g ++ g') reflectCst b) 
    reflectTermZForRing {n=n} g reflectCst (a-b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = MinusR (weakenR g'' a') b' in
	       ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting opposites
reflectTermZForRing {n=n} g reflectCst (negate a) with (reflectTermZForRing g reflectCst a)
    reflectTermZForRing {n=n} g reflectCst (negate a) | (n' ** (g' ** a')) = 
      let this = NegR a' in
        (n' ** (g' ** this))
-- Reflecting products....
reflectTermZForRing {n=n} g reflectCst (a*b) with (reflectTermZForRing g reflectCst a)
  reflectTermZForRing {n=n} g reflectCst (a*b) | (n' ** (g' ** a')) with (reflectTermZForRing (g ++ g') reflectCst b) 
    reflectTermZForRing {n=n} g reflectCst (a*b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = MultR (weakenR g'' a') b' in
	       ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Constants and variables
reflectTermZForRing {n=n} g reflectCst t =
	case reflectCst g t of
	  -- If reflectConstants has decided that this thing is a constant, then we trust it...
	  Just this => ?MreflectTermZForRing_1 -- I just return (Z ** ([] ** this)) with a few conversions for having the type aggreing (because n+0=n and g++[] = [] at the same time)
	  -- If not, then it should be considered as a variable
	  Nothing => case (isElement t g) of
					Just (i ** pr) => let this2 = VarR {n=n+Z} {g=g++Data.Vect.Nil} (%instance) (RealVariable {n=n+Z} _ _ _ (g++Data.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
											?MreflectTermZForRing_2 -- (Z ** (Data.Vect.Nil ** this))
					Nothing => let this3 = VarR {n=n+S Z} {g=g++[t]} (%instance) (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
											?MreflectTermZForRing_3 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))


reflectRingTerm : {c:Type} -> {p:Ring c} -> {n:Nat} -> (g : Vect n c) -> (reflectCst:TypeReflectConstants {c=c} p) -> (x:c) -> (n' ** (g':Vect n' c ** (ExprR {c=c} {n=n+n'} p (g ++ g') x)))

     

-- ------------------------------------------------------------------------------------------------- 
-- TEST OF THE REFLECTION MECHANISM FROM ZZ (SEEN AS A RING) TO ExprR :

-- Let's try the automatic reflection
-- With the example ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
-- that has been studied in ring_test.idr

-- -------------------------------------------------------------------------------------------------
total
%reflection
reflectConstantsForZ : TypeReflectConstants {c=ZZ} (%instance)
-- Fix Idris : I can't talk about {n=n} here (I don't need it though)
reflectConstantsForZ g (Pos number) = Just (ConstR (%instance) g (Pos number))
reflectConstantsForZ g (NegS number) = Just (ConstR (%instance) g (NegS number))
reflectConstantsForZ g _ = Nothing


-- Reflects only the LHS
exprCr_automatic : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> (newG_size ** (newG:Vect newG_size ZZ ** (ExprR (%instance) newG (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))))))
exprCr_automatic x y u g = let (nAdded ** (gAdded ** exprReflected)) = reflectTermZForRing [] reflectConstantsForZ (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) in
 								(_ ** (_ ** exprReflected))


-- ------------------------------------------------------------------------------------
-- For testing the reflection of the LHS :
-- ----------------------------------------
-- 1) Showing the context that has been built automatically for the LHS : 
--    (\x,y,u,g => leftDep (rightDep (exprCr_automatic x y u g)))
-- 2) Showing the reflected expression that has been built automatically for the LHS :
--    (\x,y,u,g => rightDep (rightDep (exprCr_automatic x y u g)))
-- ------------------------------------------------------------------------------------

-- Reflects only the RHS
exprC2r_automatic : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> (newG_size ** (newG:Vect newG_size ZZ ** (ExprR (%instance) newG ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))))))
exprC2r_automatic x y u g = let (nAdded ** (gAdded ** exprReflected)) = reflectTermZForRing [] reflectConstantsForZ ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))) in
 								(_ ** (_ ** exprReflected))

-- ------------------------------------------------------------------------------------
-- For testing the reflection of the RHS :
-- ----------------------------------------
-- 1) Showing the context that has been built automatically for the RHS : 
--    (\x,y,u,g => leftDep (rightDep (exprC2r_automatic x y u g)))
-- 2) Showing the reflected expression thaa has been built automatically for the RHS :
--    (\x,y,u,g => rightDep (rightDep (exprC2r_automatic x y u g)))
-- ------------------------------------------------------------------------------------

-- Note : the context generated automatically for the LHS is [x,y,u,g], but the one for the RHS is [x,y,g,u] because of the order of appearance of the variables
-- Update : that does not work anymore for the moment, because of the handler for constants only. I think there is a problem with Idris' %reflection machanism

-- Now, let's try to do the reflection AND the proving, all in automatic mode...

full_auto : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
full_auto x y u g = let (nbAddedLHS ** (gammaAddedLHS ** lhs)) = reflectTermZForRing [] reflectConstantsForZ (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) in
						let (nbAddedRHS ** (gammaAddedRHS ** rhs)) = reflectTermZForRing gammaAddedLHS reflectConstantsForZ ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))) in
							let (Just ok) = ringDecideEq (%instance) (weakenR gammaAddedRHS lhs) rhs in ok
 
 

-- ---------------------------------------------------------------------
-- GENERALISED VERSION GOING FROM ANY TYPE c (SEEN AS A RING) TO ExprR
-- ---------------------------------------------------------------------

%reflection
reflectTermForRing : {c:Type} -> {n:Nat} -> (p:Ring c) -> (g : Vect n c) -> (reflectCst:TypeReflectConstants p) -> (x:c) -> (n' ** (g':Vect n' c ** (ExprR p (g ++ g') x)))
reflectTermForRing {n=n} p g reflectCst (Plus a b) with (reflectTermForRing p g reflectCst a)
-- Reflecting sums...
  reflectTermForRing {n=n} p g reflectCst (Plus a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
    reflectTermForRing {n=n} p g reflectCst (Plus a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusR (weakenR g'' a') b' in
         ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting substractions...
reflectTermForRing {n=n} p g reflectCst (Minus a b) with (reflectTermForRing p g reflectCst a)
  reflectTermForRing {n=n} p g reflectCst (Minus a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
    reflectTermForRing {n=n} p g reflectCst (Minus a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = MinusR (weakenR g'' a') b' in
         ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting opposites
reflectTermForRing {n=n} p g reflectCst (Neg a) with (reflectTermForRing p g reflectCst a)
    reflectTermForRing {n=n} p g reflectCst (Neg a) | (n' ** (g' ** a')) = 
      let this = NegR a' in
        (n' ** (g' ** this))
-- Reflecting products....
reflectTermForRing {n=n} p g reflectCst (Mult a b) with (reflectTermForRing p g reflectCst a)
  reflectTermForRing {n=n} p g reflectCst (Mult a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
    reflectTermForRing {n=n} p g reflectCst (Mult a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = MultR (weakenR g'' a') b' in
         ((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Constants and variables
reflectTermForRing {n=n} p g reflectCst t =
	case reflectCst g t of
	  -- If reflectConstants has decided that this thing is a constant, then we trust it...
	  Just this => ?MreflectTermForRing_1 -- I just return (Z ** ([] ** this)) with a few conversions for having the type aggreing (because n+0=n and g++[] = [] at the same time)
	  -- If not, then it should be considered as a variable
	  Nothing => case (isElement t g) of
					Just (i ** pr) => let this2 = VarR {n=n+Z} {g=g++Data.VectType.Vect.Nil} p (RealVariable {n=n+Z} _ _ _ (g++Data.VectType.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
											?MreflectTermForRing_2 -- (Z ** (Data.VectType.Vect.Nil ** this))
					Nothing => let this3 = VarR {n=n+S Z} {g=g++[t]} p (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
											?MreflectTermForRing_3 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))

                  

-- CURRENT PROBLEMS WITH THE AUTOMATIC REFLECTION :
-- ------------------------------------------------
-- There are two problems at the moment with the general automatic reflection for Ring (which is just above) :
-- 1) It doesn't reflects the effective implementation of the abstract operations (Plus,Minus,Mult...) of the typeclass.
-- for example, if you test (\xx,yy,uu,gg:ZZ => leftDep ( rightDep( reflectTermForRing {c=ZZ} (%instance) [] (xx+yy+uu+gg)))) then it goes
-- directly in the last case, and it adds the whole formulae in the context.
-- -> Idris needs to be improved for (really) allowing reflection with abstract operation that might become concrete with an actual instance. At the moment,
-- idris allows it, but it doesn't work as expected
-- 2) Problem with Idris's %reflection when calling subfunction. See the issue open on Github here : https://github.com/idris-lang/Idris-dev/issues/2843
   
   

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
  mrefine convertVectInExprR 
  exact n
  exact g
  mrefine plusZeroRightNeutral
  mrefine vectNilRightNeutral 
  exact this  
  
Provers.reflection.MreflectTermZForRing_2 = proof
  intros
  mrefine MkSigma
  exact Z
  compute
  mrefine MkSigma
  exact Nil
  compute
  rewrite pr
  rewrite (index_n_plus_0 g i)
  exact this2  
  
Provers.reflection.MreflectTermZForRing_3 = proof
  intros
  mrefine MkSigma
  exact (S Z)
  compute
  mrefine MkSigma
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this3)  


Provers.reflection.MreflectTermForRing_1 = proof
  intros
  mrefine MkSigma
  exact Z
  compute
  mrefine MkSigma
  exact Nil
  compute
  mrefine convertVectInExprR 
  exact n
  exact g
  mrefine plusZeroRightNeutral
  mrefine vectNilRightNeutral 
  exact this  
  
Provers.reflection.MreflectTermForRing_2 = proof
  intros
  mrefine MkSigma
  exact Z
  compute
  mrefine MkSigma
  exact Nil
  compute
  rewrite pr
  rewrite (index_n_plus_0 g i)
  exact this2  
  
Provers.reflection.MreflectTermForRing_3 = proof
  intros
  mrefine MkSigma
  exact (S Z)
  compute
  mrefine MkSigma
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this3)  





