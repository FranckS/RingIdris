{-
Franck Slama - University of St Andrews
file testReflection2Funs.idr
This files correspond to the problem described here : https://github.com/idris-lang/Idris-dev/issues/2843
Last version : 05 June 2016
Compiles with Idris 0.11 (version released at the end of March 2016)

This file shows two problems with Idris' reflection mechanism :
- 1) It looks like a function defined with %reflection can't call a subfunction doing a subpart of the reflection.
	-> that would be useful for having a handler for constants only for example 
	  (in my work, I need to implement an automatic reflection for any type that behaves as a Ring, 
	  but I can't know beforehand what the constants are going to be, so what I want is that the user passes a function dealing only with the reflection of constants)
- 2) Adding a "_" pattern that should not change anything did change the result
-}

-- Just a (pretty useless) syntax for reflecting natural numbers with additions, variables and constants
data MyNat : Type where
	-- Additions
	MyPlus : MyNat -> MyNat -> MyNat
	-- Constants
	MySucc : MyNat -> MyNat
	MyZero : MyNat
	-- Everything else is seen as a "variable"
	AVariable : MyNat -- We forget "which variable it was", but we don't care here for this little example
	
-- --------------------------
-- THAT WORKS :
-- --------------------------	
	
%reflection
reflectNatToMyNat : Nat -> MyNat
reflectNatToMyNat (a+b) = MyPlus (reflectNatToMyNat a) (reflectNatToMyNat b)
reflectNatToMyNat (S px) = MySucc (reflectNatToMyNat px)
reflectNatToMyNat Z = MyZero
reflectNatToMyNat _ = AVariable

-- Here, I get (MyPlus AVariable AVariable) which is what I want : OK
test1 : Nat -> Nat -> MyNat 
test1 = (\x,y => reflectNatToMyNat (x+y))



-- --------------------------
-- THE FIRST PROBLEM :
-- --------------------------

-- This is the type of a handler for constants only
TypeReflectConstants : Type
TypeReflectConstants = Nat -> Maybe(MyNat)

-- Now, we take as parameter a handler for dealing with the reflection of constants
total
%reflection
reflectNatToMyNat' : (reflectCst : TypeReflectConstants) -> Nat -> MyNat
reflectNatToMyNat' reflectCst (a+b) = MyPlus (reflectNatToMyNat' reflectCst a) (reflectNatToMyNat' reflectCst b)
reflectNatToMyNat' reflectCst t = 
	case reflectCst t of
	  -- If the function doing the reflection for constants has decided that t is a constant (and has done the reflection), then we trust it
	  Just this => this
	  -- Otherwise, we conclude that we have a variable
	  Nothing => AVariable
	  -- _ => AVariable
	  
-- We define a handler for constants...
total
%reflection
reflectNatConstants : TypeReflectConstants
reflectNatConstants Z = Just MyZero
reflectNatConstants (S px) = case reflectNatConstants px of
								Just something => Just (MySucc something) 
								Nothing => Nothing -- We lose the ability to deal with things like (S x) where x is a variable, but we decide that we don't care
-- This is just the handler for constants, so we simply return Nothing if what we had in input wasn't a constant of Nat
reflectNatConstants _ = Nothing
	  
	  
-- I DO NOT get (MyPlus AVariable AVariable) : IT FAILS WITH A "CASE BLOCK IN...". WHY ? 
test2 : Nat -> Nat -> MyNat 
test2 = (\x,y => reflectNatToMyNat' reflectNatConstants (x+y))	  
	  
-- ------------------------------------------------------------
-- SECOND PROBLEM WITH reflectNatToMyNat' :
-- ------------------------------------------------------------

-- Here I should get (MySucc MyZero), and I do get it
test3 : MyNat
test3 = reflectNatToMyNat' reflectNatConstants (S Z)
-- BUT, if I de-comment the last line "_ => AVariable" of reflectNatToMyNat' (which should be useless), I don't get the same answer (indeed, I get AVariable!) ! Why ???




