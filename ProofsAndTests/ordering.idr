module Ordering


using (A:Type, B:Type)
    data or : A -> B -> Type where
        Or_introL : A -> or A B
        Or_introR : B -> or A B


infixl 5 ~=
class Set c where
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
    


class Set c => PartialStrictOrder c where
	(<<) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
	lowerDec : (x:c) -> (y:c) -> Maybe(x<<y) -- The "weak" decidable relation (week because only gives a proof when it holds)

	lower_antisym : {x:c} -> {y:c} -> (x<<y) -> (y<<x) -> (x~=y)
	lower_trans : {x:c} -> {y:c} -> {z:c} -> (x<<y) -> (y<<z) -> (x<<z)


infixl 5 <~=
class PartialStrictOrder c => PartialOrder c where
	
	(<~=) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
	(<~=) x y = or (x<<y) (x~=y)

	
	-- WHY DOES IT REFUSES TO UNIFY AN OR AND A FUCKING (<~=) ! THERE'S EVEN NOTHING TO UNFOLD THE DEFINITION OF (<~=) IN PROOF MODE. WHAT THE FUCK !
	lowerEqDec : (x:c) -> (y:c) -> Maybe(x <~= y)
	lowerEqDec x y with (lowerDec x y)
		lowerEqDec x y | (Just prStrictlyLower) = ?MlowerEqDec_1 -- Just (Or_introL {B=(x~=y)} prStrictlyLower)
		lowerEqDec x y | (Nothing) with (eqDec x y)
			lowerEqDec x y | (Nothing) | (Just prEqual) = ?MlowerEqDec_2 -- Just (Or_introR prEqual)
			lowerEqDec x y | (Nothing) | (Nothing) = Nothing
	
	-- SAME HERE !
	lowerEq_refl : (x:c) -> (x <~= x)
	lowerEq_refl x = ?Mlower_refl -- Or_introR (eq_refl x)

	lowerEq_antisym : {x:c} -> {y:c} -> (x<~=y) -> (y<~=x) -> (x ~= y)
	lowerEq_antisym (Or_introL x_lower_y) (Or_introL y_lower_x) = Or_introL (lower_antisym x_lower_y y_lower_x)
	lowerEq_antisym (Or_introL x_lower_y) (Or_introR y_equals_x) = Or_introR (eq_sym y_equals x)
	lowerEq_antisym (Or_introR x_equals_y) _ = Or_introR x_equals_y

	lowerEq_trans : {x:c} -> {y:c} -> {z:c} -> (x<~=y) -> (y<~=z) -> (x<~=z)
	lowerEq_trans (Or_introL x_lower_y) (Or_introL y_lower_z) = Or_introL (lower_trans x_lower_y y_lower_z)
	lowerEq_trans (Or_introL x_lower_y)  (Or_introR y_equals_z) = ?MK1 -- We will need something
	lowerEq_trans (Or_introR x_equals_y) (Or_introL y_lower_z) = ?MK2
	lowerEq_trans (Or_introR x_equals_y) (Or_introR y_equals_z) = Or_introR (eq_trans x_equals_y y_equals_z)
	

class PartialOrder c => CompleteOrder c where

	lowerE_undec_total : (x:c) -> (y:c) -> or (Ordering.(<~=) x  y) (Ordering.(<~=) y x)



