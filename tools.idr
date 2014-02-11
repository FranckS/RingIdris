-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File tools.idr
-- Various tools needed for the implementation of the ring tactic for Idris
-------------------------------------------------------------------

module tools

import Data.ZZ
import globalDef
import dataTypes

-- -------------------------------
-- A) TOOLS AND LEMMAS FOR PAIRS
-- -------------------------------

left : {A:Type} -> {B:Type} -> (A,B)  -> A
left (x,y) = x

right : {A:Type} -> {B:Type} -> (A,B) -> B
right (x,y) = y

{-
: (c1:c) -> ((Plus c1 (Neg c1) = Plus (Neg c1) c1), (Plus (Neg c1) c1 = the c Zero)) -- "the c Zero" used to make clear that we talk about Zero in c and not the one in CommutativeRing (last defined first tried ?)
-}

-- -------------------------------
-- B) TOOLS AND LEMMAS FOR GROUPS
-- -------------------------------

-- ------------------------------------------------------------------------
-- B.1/ This subpart is to obtain the lemma "group_doubleNeg" : - (-a) = a
-- ------------------------------------------------------------------------
group_unicity_symmetric : {C:Type} -> (p:dataTypes.Group C) -> (a:C) -> (b:C) -> (c:C) -> (hasSymmetric C (group_to_monoid_class p) a b) -> (hasSymmetric C (group_to_monoid_class p) a c) -> (b=c)
group_unicity_symmetric p a b c p1 p2 = let a = aux in ?MGroup_unicity_1
  where aux : Plus (Plus b a) c = Plus b (Plus a c) 
	aux = ?MGroup_unicity_2
	

hasSymmetric_sym : {C:Type} -> (p:dataTypes.Group C) -> (a:C) -> (b:C) -> (hasSymmetric C (group_to_monoid_class p) a b) -> (hasSymmetric C (group_to_monoid_class p) b a)
hasSymmetric_sym = ?MhasSymmetric_sym


plus_inverse_2 : {C:Type} -> (p:dataTypes.Group C) -> (c1:C) -> hasSymmetric C (%instance) (Neg c1) c1 -- Every element 'Neg x' has a symmetric which is x
plus_inverse_2 p c1 = ?Mplus_inverse_2	


group_doubleNeg : (C:Type) -> (p:dataTypes.Group C) -> (a:C) -> ((Neg (Neg a)) = a) 
group_doubleNeg C p a = let a = aux in let b = aux2 in ?Mgroup_doubleNeg1
  where aux : hasSymmetric C (group_to_monoid_class p) (Neg a) a
	aux = ?Mgroup_doubleNeg_2
	aux2 : hasSymmetric C (group_to_monoid_class p) (Neg a) (Neg (Neg a))
	aux2 = ?Mgroup_doubleNeg_3

-- ----------------------------------------------------------------------------
-- B.2/ This part is to obtain the lemma "push_negation" : -(a+b) = (-a) + (-b)
-- ----------------------------------------------------------------------------
{-
adding_preserves_equality_left : {C:Type} -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (z:C) -> (x=y) -> (Plus z x = Plus z y)
adding_preserves_equality_left x y z H = ?Madding_preserves_equality_left_1
-}

adding_preserves_equality : {C:Type} -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (z:C) -> (x=y) -> (Plus x z = Plus y z)
adding_preserves_equality x y z H = ?Madding_preserves_equality_1


move_other_side : {C:Type} -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (z:C) -> (Plus x y = z) -> (x = Plus z (Neg y))
move_other_side x y z H = 
	let aux : (Plus (Plus x y) (Neg y) = Plus z (Neg y)) = adding_preserves_equality _ _ (Neg y) H in
	let aux2 : (Plus (Plus x y) (Neg y) = Plus x (Plus y (Neg y))) = (Plus_assoc _ _ _) in
	let aux3 : (Plus x (Plus y (Neg y)) = Plus z (Neg y)) = ?Mmove_other_side_1 in -- Just a rewriting in an hypothesis
	let aux4 : (Plus y (Neg y) = Zero) = left (Plus_inverse _) in
	let aux5 : (Plus x (Plus y (Neg y)) = x) = ?Mmove_other_side_2 in
		?Mmove_other_side_3


push_negation : (C:Type) -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (Neg (Plus x y) = Plus (Neg y) (Neg x))
push_negation C x y = 
	let aux : (Plus (Neg (Plus x y)) (Plus x y) = Zero) = right (Plus_inverse (Plus x y)) in
	let aux2 : (Plus (Neg (Plus x y)) (Plus x y) = Plus (Plus (Neg (Plus x y)) x) y) = sym (Plus_assoc (Neg (Plus x y)) x y) in
	let aux3 : (Plus (Plus (Neg (Plus x y)) x) y = the C Zero) = ?Mpush_negation_1 in
	let aux4 : ((Plus (Neg (Plus x y)) x) = Plus Zero (Neg y)) = move_other_side _ _ _ aux3 in
	let aux5 : (Plus Zero (Neg y) = Neg y) = Plus_neutral_1 _ in
	let aux6 : ((Plus (Neg (Plus x y)) x) = Neg y) = ?Mpush_negation_2 in
	let aux7 : (Neg (Plus x y) = Plus (Neg y) (Neg x)) = move_other_side _ _ _ aux6 in
		?Mpush_negation_3


      
	      
{-
And_True_neutral : (b:Bool) -> (True && b = b)
And_True_neutral _ = refl

And_False_absorbent : (b:Bool) -> (False && b = False)
And_False_absorbent _ = refl
  
And_assoc : (a:Bool) -> (b:Bool) -> (c:Bool) -> ((a && (b && c)) = ((a && b) && c))
And_assoc True True True = refl
And_assoc True True False = refl
And_assoc True False True = refl
And_assoc True False False = refl
And_assoc False True True = refl
And_assoc False True False = refl
And_assoc False False True = refl
And_assoc False False False = refl

And_assoc2 : (a:Bool) -> (b:Bool) -> (c:Bool) -> (((a && b) && c) = (a && (b && c)))
And_assoc2 True True True = refl
And_assoc2 True True False = refl
And_assoc2 True False True = refl
And_assoc2 True False False = refl
And_assoc2 False True True = refl
And_assoc2 False True False = refl
And_assoc2 False False True = refl
And_assoc2 False False False = refl

aux1 : O = plus O O

-}

-- To add in the depository for Idris
{-
total plusAssociativeZ : (left : ZZ) -> (centre : ZZ) -> (right : ZZ) ->
  left + (centre + right) = (left + centre) + right
plusAssociativeZ (Pos u) (Pos v) (Pos w) = let P:((plus u (plus v w))=(plus (plus u v) w)) = (plusAssociative u v w) in ?MplusAssociativeZ_1
plusAssociativeZ (Pos u) (Pos v) (NegS w) = ?MplusAssociativeZ_2
plusAssociativeZ (Pos u) (NegS v) (Pos w) = ?MplusAssociativeZ_3
plusAssociativeZ (Pos u) (NegS v) (NegS w) = ?MplusAssociativeZ_4
-- 
plusAssociativeZ (NegS u) (Pos v) (Pos w) = ?MplusAssociativeZ_5
plusAssociativeZ (NegS u) (Pos v) (NegS w) = ?MplusAssociativeZ_6
plusAssociativeZ (NegS u) (NegS v) (Pos w) = ?MplusAssociativeZ_7
plusAssociativeZ (NegS u) (NegS v) (NegS w) = ?MplusAssociativeZ_8
-}


-- -----------------------------------
-- C) TOOLS AND LEMMAS FOR SEMIGROUPS
-- -----------------------------------

plusSym_4v : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus (Plus c1 c2) c3) c4 = Plus (Plus c1 c2) (Plus c3 c4))
plusSym_4v = ?MplusSym_4v

plusAux : (C : Type) -> (SemiGroup C) -> (x:C) -> (x':C) -> (y:C) -> (prEqual:x=x') -> (Plus x y = Plus x' y)

plusSym_4v' : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 = Plus (Plus (Plus c1 c2) c3) c4)
plusSym_4v' = ?MplusSym_4v'

{-
--minusNatZNeutralZ : (x:Nat) -> (minusNatZ x (S x) = Pos O)
--minusNatZNeutralZ O = ?A
-}

--class Relation s where
    --rel : s -> s -> Type

--class Relation s => Setoid s where
  --  refl : (x:s) -> rel x x
    --sym : (x:s) -> (y:s) -> (rel x y) -> (rel y x)
    --trans : (x:s) -> (y:s) -> (z:s) -> (rel x y) -> (rel y z) -> (rel x z)

---------- Proofs ----------  
{-
tools.MplusAssociativeZ_1 = proof {
  intros;
  compute;
  rewrite P;
  trivial;
}
-}

tools.MGroup_unicity_1 = proof
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  rewrite (sym (right p1))
  rewrite (sym (left p2))
  rewrite (sym (Plus_neutral_1 c))
  rewrite (sym (Plus_neutral_2 b))
  intro
  rewrite a1
  trivial

tools.MhasSymmetric_sym = proof
  intro
  intro
  intro
  intro
  intro H
  exact (right H, left H)  
  
tools.MGroup_unicity_2 = proof
  intros
  mrefine Plus_assoc

tools.Mplus_inverse_2 = proof
  intros
  mrefine hasSymmetric_sym
  mrefine Plus_inverse  

tools.Mgroup_doubleNeg1 = proof
  intros
  exact (sym (group_unicity_symmetric p (Neg a) a (Neg (Neg a)) a1 b))
  
tools.Mgroup_doubleNeg_2 = proof
  intros
  exact (right(Plus_inverse a), left(Plus_inverse a))
  
tools.Mgroup_doubleNeg_3 = proof
  intros
  exact (left (Plus_inverse (Neg a)), right(Plus_inverse (Neg a)))  
  
tools.Madding_preserves_equality_1 = proof
  intros
  rewrite H
  mrefine refl

{-  
tools.Madding_preserves_equality_left_1 = proof
  intros
  rewrite H
  mrefine refl  
-}
  
tools.Mmove_other_side_1 = proof
  intros
  rewrite aux2
  exact aux  
  
tools.Mmove_other_side_2 = proof
  intros
  rewrite (sym aux4)
  mrefine Plus_neutral_2

tools.Mmove_other_side_3 = proof
  intros
  rewrite aux5
  exact aux3 
  
tools.Mpush_negation_1 = proof
  intros
  rewrite aux2
  exact aux  
  
tools.Mpush_negation_2 = proof
  intros
  rewrite aux5
  exact aux4
     
tools.Mpush_negation_3 = proof
  intros
  rewrite aux7
  mrefine refl  
  
tools.MplusSym_4v = proof {
  intros;
  mrefine Plus_assoc;
}

tools.MplusSym_4v' = proof {
  intros;
  mrefine plusAux;
  rewrite (Plus_assoc  c1 c2 c3);
  trivial;
}

tools.plusAux = proof {
  intros;
  rewrite prEqual;
  trivial;
}

{-
tools.aux1 = proof {
  compute;
  trivial;
}
-}




