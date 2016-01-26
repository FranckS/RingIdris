module Ordering



data Or : (A:Type) -> (B:Type) -> Type where
	Or_introL : {A:Type} -> (B:Type) -> (a:A) -> Or A B
	Or_introR : (A:Type) -> {B:Type} -> (b:B) -> Or A B


infixl 5 ~=
interface Set c where
    -- We just requires a (weak) decidable relation over the elements of the "set"
    -- which means that two elements are EQuivalent.
    -- (Note : that's no longer an equality, but just a relation, since that's more general)
    (~=) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
    eqDec : (x:c) -> (y:c) -> Maybe(x~=y) -- The "weak" decidable relation (week because only gives a proof when it holds)
    
    -- The binary relation should be an equivalence relation, ie
    -- Reflexive,
    eq_refl : (x:c) -> x~=x
    -- Symmetric,
    eq_sym : {x:c} -> {y:c} -> (x~=y) -> (y~=x)
    -- And transitive
    eq_trans : {x:c} -> {y:c} -> {z:c} -> (x~=y) -> (y~=z) -> (x~=z)
    


interface Set c => PartialStrictOrder c where
	(<<) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
	lowerDec : (x:c) -> (y:c) -> Maybe(x<<y) -- The "weak" decidable relation (week because only gives a proof when it holds)

	lower_antisym : {x:c} -> {y:c} -> (x<<y) -> (y<<x) -> (x~=y)
	lower_trans : {x:c} -> {y:c} -> {z:c} -> (x<<y) -> (y<<z) -> (x<<z)



-- FIX IDRIS HERE
-- it's not needed to try with an intermediate structure Pre_PartialOrder as it doesn't work either :-(
infixl 5 <~=
interface PartialStrictOrder c => PartialOrder c where
	
	(<~=) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
	(<~=) x y = Or (x<<y) (x~=y)

	-- WHY DOES IT REFUSES TO UNIFY AN OR AND A (<~=) ! IT CAN'T UNFOLD THE DEFINITION OF (<~=), AND NOT IN PROOF MODE EITHER. FIX IDRIS !
	lowerEqDec : (x:c) -> (y:c) -> Maybe(x <~= y)
	lowerEqDec x y with (lowerDec x y)
		lowerEqDec x y | (Just prStrictlyLower) = ?MlowerEqDec_1 -- Just (Or_introL _ prStrictlyLower)
		lowerEqDec x y | (Nothing) with (eqDec x y)
			lowerEqDec x y | (Nothing) | (Just prEqual) = ?MlowerEqDec_2 -- Just (Or_introR _ prEqual)
			lowerEqDec x y | (Nothing) | (Nothing) = Nothing
	
	-- SAME HERE !
	lowerEq_refl : (x:c) -> (x <~= x)
	lowerEq_refl x = ?MlowerEq_refl_1 -- Or_introR _ (eq_refl x)

{-
	lowerEq_antisym : {x:c} -> {y:c} -> (x<~=y) -> (y<~=x) -> (x ~= y)
	lowerEq_antisym (Or_introL _ x_lower_y) (Or_introL _ y_lower_x) = ?MlowerEq_antisym_1 -- Or_introL (lower_antisym x_lower_y y_lower_x)
	lowerEq_antisym (Or_introL _ x_lower_y) (Or_introR _ y_equals_x) = ?MlowerEq_antisym_2 -- Or_introR (eq_sym y_equals x)
	lowerEq_antisym (Or_introR _ x_equals_y) _ = ?MlowerEq_antisym_3 -- Or_introR x_equals_y

	lowerEq_trans : {x:c} -> {y:c} -> {z:c} -> (x<~=y) -> (y<~=z) -> (x<~=z)
	lowerEq_trans (Or_introL _ x_lower_y) (Or_introL _ y_lower_z) = ?MlowerEq_trans_1-- Or_introL (lower_trans x_lower_y y_lower_z)
	lowerEq_trans (Or_introL _ x_lower_y)  (Or_introR _ y_equals_z) = ?MlowerEq_trans_2 -- We will need the fact that <~= is "compatible" with "~=" here, which means that (a <~= b) -> (b ~= c) -> (a <~= c)
	lowerEq_trans (Or_introR _ x_equals_y) (Or_introL _ y_lower_z) = ?MlowerEq_trans_3 -- And (a <~= b) -> (a ~= c) -> (c <~= a)
	lowerEq_trans (Or_introR _ x_equals_y) (Or_introR _ y_equals_z) = ?MlowerEq_trans_4 -- Or_introR (eq_trans x_equals_y y_equals_z)
-}	

interface PartialOrder c => TotalOrder c where

	lowerE_undec_total : (x:c) -> (y:c) -> Or (Ordering.(<~=) x  y) (Ordering.(<~=) y x)



