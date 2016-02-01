module Ordering



data Or : (A:Type) -> (B:Type) -> Type where
	Or_introL : {A:Type} -> {B:Type} -> (a:A) -> Or A B
	Or_introR : {A:Type} -> {B:Type} -> (b:B) -> Or A B


------------------------------------------------------
--                  SET (SETOID)                    --
------------------------------------------------------

infixl 5 ~=
interface Set c where
    -- We just require an equivalence relation over the elements of the "set"
    -- which means that two elements are EQuivalent
    -- And a way to produce a proof when it holds (it is semi-decidable, or weakly-decidable, call it as you want)
    -- I could call this structure "Setoid" instead of "Set"
    (~=) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
    eqDec : (x:c) -> (y:c) -> Maybe(x~=y) -- This relation is "weakly" decidable (weekly because eqDec only gives a proof when it holds)
    
    -- The binary relation should be an equivalence relation, ie
    -- Reflexive,
    eq_refl : (x:c) -> x~=x
    -- Symmetric,
    eq_sym : {x:c} -> {y:c} -> (x~=y) -> (y~=x)
    -- And transitive
    eq_trans : {x:c} -> {y:c} -> {z:c} -> (x~=y) -> (y~=z) -> (x~=z)
    

------------------------------------------------------
--               PARTIAL STRICT ORDER               --
------------------------------------------------------

-- Should be in fact called "PartialyStriclyOrdered c" for saying that
-- c is partially strictly ordered, but that's a bit too verbose,
-- so we just say "PartialStrictOrder c"

interface Set c => PartialStrictOrder c where
	(<<) : (x:c) -> (y:c) -> Type -- The (undecidable) relation

	-- The new (<<) operation preserves the equivalence define at the Set level
	lower_compat_equivalence_L : {x:c} -> {y:c} -> {y':c} -> (x << y) -> (x ~= x') -> (x' << y)
	lower_compat_equivalence_R : {x:c} -> {y:c} -> {y':c} -> (x << y) -> (y ~= y') -> (x << y')

	lowerDec : (x:c) -> (y:c) -> Maybe(x<<y) -- The "weak" decidable relation (week because only gives a proof when it holds)

	lower_antisym : {x:c} -> {y:c} -> (x<<y) -> (y<<x) -> (x~=y)
	lower_trans : {x:c} -> {y:c} -> {z:c} -> (x<<y) -> (y<<z) -> (x<<z)


------------------------------------------------------
--                  PARTIAL ORDER                   --
------------------------------------------------------

-- Should be in fact called "PartialyOrdered c" for saying that
-- c is partially ordered, but that's a bit too verbose,
-- so we just say "PartialOrder c"

infixl 5 <~=
interface PartialStrictOrder c => PartialOrder c where

	-- Nothing here !

	-- I can't put the operations (<~=), the functions lowerEqDec and the properties about (<~=) here
	-- because there's no way to say "final" for a definitions in Idris, that would mean that the operation can't
	-- be redefined by the user.
	-- Without being sure that the user can't redefine it, we can't unfold the definition of (<~=)
	-- Question to idris designers : Does Idris should have the keyword "final" for allowing this kind of constructions ?


-- Lower or equivalent operation	
(<~=) : {c:Type} -> {p:PartialOrder c} -> (x:c) -> (y:c) -> Type -- The (undecidable) relation
(<~=) x y = Or (x<<y) (x~=y)


-- There's only one way to define the function which decides the lower or equal operation
lowerEqDec : {c:Type} -> (p:PartialOrder c) -> (x:c) -> (y:c) -> Maybe(x <~= y)
lowerEqDec p x y with (lowerDec x y)
	lowerEqDec p x y | (Just prStrictlyLower) = Just (Or_introL prStrictlyLower)
	lowerEqDec p x y | (Nothing) with (eqDec x y)
		lowerEqDec p x y | (Nothing) | (Just prEqual) = Just (Or_introR prEqual)
		lowerEqDec p x y | (Nothing) | (Nothing) = Nothing


-- I'm forced to make the (Partialorder c) an explicit argument, otherwise we end up with a non-sense arror message
lowerEq_refl : {c:Type} -> (p:PartialOrder c) -> (x:c) -> (x <~= x)
lowerEq_refl p x = Or_introR (eq_refl x)


lowerEq_antisym : {c:Type} -> (p:PartialOrder c) -> {x:c} -> {y:c} -> (x<~=y) -> (y<~=x) -> (x ~= y)
-- FIX IDRIS : I can't do the first one, neither directly in the language nor in proof mode
lowerEq_antisym p (Or_introL x_lower_y) (Or_introL y_lower_x) = ?M_PROBLEM_WITH_IDRIS_1 -- lower_antisym x_lower_y y_lower_x
-- FIX IDRIS : I can't do the second one in the language, but I can do it in proof mode
lowerEq_antisym p (Or_introL x_lower_y) (Or_introR y_equals_x) = ?M_PROBLEM_WITH_IDRIS_2 -- eq_sym y_equals_x
-- FIX IDRIS : I can't do the third one, neither directly in the language nor in proof mode
lowerEq_antisym p (Or_introR x_equals_y) _ = ?M_PROBLEM_WITH_IDRIS_3 -- x_equals_y


lowerEq_trans : {c:Type} -> (p:PartialOrder c) -> {x:c} -> {y:c} -> {z:c} -> (x<~=y) -> (y<~=z) -> (x<~=z)
-- FIX IDRIS : I can't do the first one, neither directly in the language nor in proof mode
lowerEq_trans p (Or_introL x_lower_y) (Or_introL y_lower_z) = ?MlowerEq_trans_1 -- Or_introL (lower_trans x_lower_y y_lower_z)
-- FIX IDRIS : I can't do the second one, neither directly in the language nor in proof mode
lowerEq_trans p (Or_introL x_lower_y)  (Or_introR y_equals_z) = ?MlowerEq_trans_2 -- Or_introL (lower_compat_equivalence_R x_lower_y y_equals_z)
-- FIX IDRIS : I can't do the third one, neither directly in the language nor in proof mode
lowerEq_trans p (Or_introR x_equals_y) (Or_introL y_lower_z) = ?MlowerEq_trans_3 -- Or_introL (lower_compat_equivalence_L y_lower_z (eq_sym x_equals_y))
-- FIX IDRIS : I can't do the fourth one, neither directly in the language nor in proof mode
lowerEq_trans p (Or_introR x_equals_y) (Or_introR y_equals_z) = ?MlowerEq_trans_4 -- Or_introR (eq_trans x_equals_y y_equals_z)


------------------------------------------------------
--                   TOTAL ORDER                    --
------------------------------------------------------

-- Should be in fact called "TotalyOrdered c" for saying that
-- c is totaly ordered, but that's a bit too verbose,
-- so we just say "TotalOrder c"

interface PartialOrder c => TotalOrder c where

	-- We can now compare any two elements with (<~=)

	-- Problem with Idris : new problem with the typecheck of the property just underneath : 
	-- lowerE_undec_total : (x:c) -> (y:c) -> Or (x <~= y) (y <~= x)




---------- Proofs ----------

Ordering.M_PROBLEM_WITH_IDRIS_2 = proof
  intros
  mrefine eq_sym 
  exact y_equals_x 


