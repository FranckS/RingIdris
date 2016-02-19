-- Franck Slama
-- University of St Andrews
-- ------------------------------

module ordering


%access public export

%default total



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
    eqDec : (x:c) -> (y:c) -> Dec(x~=y)
    
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

	lowerDec : (x:c) -> (y:c) -> Dec(x<<y)

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



not_lowerEq_lemma1 : {c:Type} -> {p:PartialOrder c} -> (x:c) -> (y:c) -> (p1 : (x<<y) -> Void) -> (p2 : (x~=y) -> Void) -> (pFalse : (<~=) {p=p} x y) -> Void
not_lowerEq_lemma1 x y p1 p2 (Or_introL prStrictlyLower) = p1 prStrictlyLower
not_lowerEq_lemma1 x y p1 p2 (Or_introR prEqual) = p2 prEqual


-- There's only one way to define the function which decides the lower or equal operation
lowerEqDec : {c:Type} -> (p:PartialOrder c) -> (x:c) -> (y:c) -> Dec((<~=) {p=p} x y) -- FIX IDRIS : If I write (x <~= y) then in the file proofAndTests.idr I get a weird and broken error message which says "can't infer argument 'p''...
lowerEqDec {c} p x y with (lowerDec {c=c} x y)
	lowerEqDec {c} p x y | (Yes prStrictlyLower) = Yes (Or_introL prStrictlyLower)
	lowerEqDec {c} p x y | (No prNotStrictlyLower) with (eqDec x y)
		lowerEqDec {c} p x y | (No prNotStrictlyLower) | (Yes prEqual) = Yes (Or_introR prEqual)
		lowerEqDec {c} p x y | (No prNotStrictlyLower) | (No prNotEqual) = No ?MlowerEqDec_1


-- I'm forced to make the (Partialorder c) an explicit argument, otherwise we end up with a non-sense arror message
lowerEq_refl : {c:Type} -> (p:PartialOrder c) -> (x:c) -> ((<~=) {p=p} x x)
lowerEq_refl p x = Or_introR (eq_refl x)


-- FIX IDRIS : I can't simply state "x <~= y" because otherwise Idris introduces many instances instead of using the available 'p'
lowerEq_antisym : {c:Type} -> (p:PartialOrder c) -> {x:c} -> {y:c} -> ((<~=) {p=p} x y) -> ((<~=) {p=p} y x) -> (x ~= y)
-- FIX IDRIS : I have to do these proofs in proof mode, otherwise Idris can't find automatically the corresponding instances...
lowerEq_antisym p (Or_introL x_lower_y) (Or_introL y_lower_x) = ?MlowerEq_antisym_1 -- lower_antisym x_lower_y y_lower_x
lowerEq_antisym p (Or_introL x_lower_y) (Or_introR y_equals_x) = ?MlowerEq_antisym_2 -- eq_sym y_equals_x
lowerEq_antisym p (Or_introR x_equals_y) _ = x_equals_y


-- FIX IDRIS : I can't simply state "x <~= y" because otherwise Idris introduces many instances instead of using the available 'p'
lowerEq_trans : {c:Type} -> (p:PartialOrder c) -> {x:c} -> {y:c} -> {z:c} -> ((<~=) {p=p} x y) -> ((<~=) {p=p} y z) -> ((<~=) {p=p} x z)
-- FIX IDRIS : I need to provide {c=c} because Idris can't find automatically the right instances. And I can't give them. But just giving {c=c} helps...
lowerEq_trans p (Or_introL x_lower_y) (Or_introL y_lower_z) = Or_introL (lower_trans {c=c} x_lower_y y_lower_z)
lowerEq_trans p (Or_introL x_lower_y)  (Or_introR y_equals_z) = Or_introL (lower_compat_equivalence_R {c=c} x_lower_y y_equals_z)
lowerEq_trans p (Or_introR x_equals_y) (Or_introL y_lower_z) = ?MlowerEq_trans_1 -- Or_introL (lower_compat_equivalence_L {c=c} y_lower_z (eq_sym {c=c} x_equals_y))
lowerEq_trans p (Or_introR x_equals_y) (Or_introR y_equals_z) = Or_introR (eq_trans {c=c} x_equals_y y_equals_z)


------------------------------------------------------
--                   TOTAL ORDER                    --
------------------------------------------------------

-- Should be in fact called "TotalyOrdered c" for saying that
-- c is totaly ordered, but that's a bit too verbose,
-- so we just say "TotalOrder c"

interface PartialOrder c => TotalOrder c where

	-- We can now compare any two elements with (<~=)

	-- FIX IDRIS : I can't simply state "x <~= y" because otherwise it doesn't typecheck...
	lowerE_undec_total : (x:c) -> (y:c) -> Or ((<~=) {p=p} x y) ((<~=) {p=p} y x)




---------- Proofs ----------
ordering.MlowerEqDec_1 = proof
  intros
  exact (not_lowerEq_lemma1 x y prNotStrictlyLower prNotEqual __pi_arg)

ordering.MlowerEq_antisym_2 = proof
  intros
  mrefine eq_sym
  exact y_equals_x 

ordering.MlowerEq_antisym_1 = proof
  intros
  mrefine lower_antisym 
  exact x_lower_y 
  exact y_lower_x 

ordering.MlowerEq_trans_1 = proof
  intros
  mrefine Or_introL 
  mrefine lower_compat_equivalence_L
  exact y
  exact z
  exact y_lower_z 
  mrefine eq_sym 
  exact x_equals_y 


