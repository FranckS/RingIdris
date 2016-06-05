-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File reflectionForSpecificDataTypes.idr
-- Reflect the concrete values into the abstract syntax for specific datatypes (for testing purpose only)
-------------------------------------------------------------------

module Provers.reflectionForSpecificDataTypes

import Decidable.Equality
import Data.ZZ
import Data.Fin
import Data.Vect
import Provers.dataTypes
import Provers.tools
import Provers.reflectionTools

import Provers.ring_reduce -- Needed for the full_auto attempt at the end of the file

import Provers.ring_test
import Provers.commutativeGroup_test
import Provers.group_test
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test

%access public export


-- -----------------------------------------------
-- REFLECTION FROM Nat (SEEN AS A MAGMA) TO ExprMa
-- -----------------------------------------------
	        
-- Reflects only from Nat (seen as a Magma) to ExprMa
-- %logging 1   
%reflection
reflectTermNat : {n:Nat} -> (g : Vect n Nat) -> (x:Nat) -> (n' ** (g':Vect n' Nat ** (ExprMa {c=Nat} {n=n+n'} (%instance) (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (g ++ g') x)))
reflectTermNat {n=n} g (a+b) with (reflectTermNat g a)
  reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) with (reflectTermNat (g ++ g') b) 
    reflectTermNat {n=n} g (a+b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
      let this = PlusMa (neg (FakeSetAndNeg (magma_to_set_class (%instance)))) (FakeSetAndMult (magma_to_set_class (%instance))) (weakenMa g'' a') b' in
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
 
 
 
 
---------- Proofs ---------- 

Provers.reflectionForSpecificDataTypes.MreflectTermNat_1 = proof
  intros
  mrefine MkDPair
  exact Z
  compute
  mrefine MkDPair
  exact Nil
  compute
  rewrite p
  rewrite (index_n_plus_0 g i)
  exact this  
  
Provers.reflectionForSpecificDataTypes.MreflectTermNat_2 = proof
  intros
  mrefine MkDPair
  exact (S Z)
  compute
  mrefine MkDPair
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this)  

Provers.reflectionForSpecificDataTypes.MreflectTermZForRing_1 = proof
  intros
  mrefine MkDPair
  exact Z
  compute
  mrefine MkDPair
  exact Nil
  compute
  mrefine convertVectInExprR 
  exact n
  exact g
  mrefine plusZeroRightNeutral
  mrefine vectNilRightNeutral 
  exact this  
  
Provers.reflectionForSpecificDataTypes.MreflectTermZForRing_2 = proof
  intros
  mrefine MkDPair
  exact Z
  compute
  mrefine MkDPair
  exact Nil
  compute
  rewrite pr
  rewrite (index_n_plus_0 g i)
  exact this2  
  
Provers.reflectionForSpecificDataTypes.MreflectTermZForRing_3 = proof
  intros
  mrefine MkDPair
  exact (S Z)
  compute
  mrefine MkDPair
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this3)   
  
  
  
  
 