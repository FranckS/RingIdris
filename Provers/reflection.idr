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
import Provers.reflectionTools


%access public export


-- ---------------------------------------------------------------------
-- GENERALISED VERSION GOING FROM ANY TYPE c (SEEN AS A RING) TO ExprR
-- ---------------------------------------------------------------------

%reflection
reflectTermForRing : {c:Type} -> {n:Nat} -> (p:Ring c) -> (g : Vect n c) -> (reflectCst:TypeReflectConstants p) -> (x:c) -> (n' ** (g':Vect n' c ** (ExprR p (g ++ g') x)))
reflectTermForRing {c=c} {n=n} p g reflectCst (Plus a b) with (reflectTermForRing p g reflectCst a)
-- Reflecting sums...
	reflectTermForRing {c=c} {n=n} p g reflectCst (Plus a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
		reflectTermForRing {c=c} {n=n} p g reflectCst (Plus a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
			let this = PlusR {c=c} (weakenR g'' a') b' in
			((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting substractions...
reflectTermForRing {c=c} {n=n} p g reflectCst (Minus a b) with (reflectTermForRing p g reflectCst a)
	reflectTermForRing {c=c} {n=n} p g reflectCst (Minus a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
		reflectTermForRing {c=c} {n=n} p g reflectCst (Minus a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
			let this = MinusR {c=c} (weakenR g'' a') b' in
			((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Reflecting opposites
reflectTermForRing {c=c} {n=n} p g reflectCst (Neg a) with (reflectTermForRing p g reflectCst a)
	reflectTermForRing {c=c} {n=n} p g reflectCst (Neg a) | (n' ** (g' ** a')) = 
		let this = NegR {c=c} a' in
        (n' ** (g' ** this))
-- Reflecting products....
reflectTermForRing {c=c} {n=n} p g reflectCst (Mult a b) with (reflectTermForRing p g reflectCst a)
	reflectTermForRing {c=c} {n=n} p g reflectCst (Mult a b) | (n' ** (g' ** a')) with (reflectTermForRing p (g ++ g') reflectCst b) 
		reflectTermForRing {c=c} {n=n} p g reflectCst (Mult a b) | (n' ** (g' ** a')) | (n'' ** (g'' ** b')) = 
			let this = MultR {c=c} (weakenR g'' a') b' in
			((n' + n'') ** ((g'++g'') ** (convertVectInExprR (plusAssociative n n' n'') (vectAppendAssociative g g' g'') this)))
-- Constants and variables
reflectTermForRing {n=n} p g reflectCst t =
	case reflectCst g t of
	  -- If reflectConstants has decided that this thing is a constant, then we trust it...
	  Just this => ?MreflectTermForRing_1 -- I just return (Z ** ([] ** this)) with a few conversions for having the type aggreing (because n+0=n and g++[] = [] at the same time)
	  -- If not, then it should be considered as a variable
	  Nothing => case (isElement t g) of
					Just (i ** pr) => let this2 = VarR {n=n+Z} {g=g++Data.Vect.Nil} p (RealVariable {n=n+Z} _ _ _ (g++Data.Vect.Nil) (replace (sym (a_plus_zero n)) i)) in
											?MreflectTermForRing_2 -- (Z ** (Data.VectType.Vect.Nil ** this))
					Nothing => let this3 = VarR {n=n+S Z} {g=g++[t]} p (RealVariable {n=n+S Z} _ _ _ (g++[t]) (lastElement' n)) in
											?MreflectTermForRing_3 -- (S Z ** ((t::Data.VectType.Vect.Nil) ** this))

                  

-- CURRENT PROBLEMS WITH THE AUTOMATIC REFLECTION :
-- ------------------------------------------------
-- There are two problems at the moment with the general automatic reflection for Ring (which is just above) :
-- 1) It doesn't reflect the effective implementation of the abstract operations (Plus,Minus,Mult...) of the typeclass.
-- for example, if you test (\xx,yy,uu,gg:ZZ => leftDep ( rightDep( reflectTermZForRing [] reflectConstantsForZ (xx+yy+uu+gg)))) then it goes
-- directly in the last case, and it adds the whole formulae in the context.
-- -> Idris needs to be improved for (really) allowing reflection with abstract operation that might become concrete with an actual instance. At the moment,
-- idris allows it, but it doesn't work as expected

-- 2) Problem with Idris's %reflection when calling subfunctions. See the issue on a smaller problem on Github here : https://github.com/idris-lang/Idris-dev/issues/2843
   
   

---------- Proofs ----------   
  
Provers.reflection.MreflectTermForRing_1 = proof
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
  
Provers.reflection.MreflectTermForRing_2 = proof
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
  
Provers.reflection.MreflectTermForRing_3 = proof
  intros
  mrefine MkDPair
  exact (S Z)
  compute
  mrefine MkDPair
  exact ([t])
  compute
  exact (replace (indexOfLastElem g t) this3)  





