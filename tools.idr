-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File tools.idr
-- Various tools needed for the implementation of the ring tactic for Idris
-------------------------------------------------------------------

module tools

import Data.ZZ
import globalDef
import dataTypes


%default total

-- -------------------------------------------------------------
-- A) TOOLS AND LEMMAS FOR PAIRS, DEPENDENT PAIRS AND FUNCTIONS
-- -------------------------------------------------------------

left : {A:Type} -> {B:Type} -> (A,B)  -> A
left (x,y) = x

right : {A:Type} -> {B:Type} -> (A,B) -> B
right (x,y) = y

leftDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> A
leftDep (a ** b) = a

rightDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> B (leftDep x)
rightDep (a ** b) = b

{-
: (c1:c) -> ((Plus c1 (Neg c1) = Plus (Neg c1) c1), (Plus (Neg c1) c1 = the c Zero)) -- "the c Zero" used to make clear that we talk about Zero in c and not the one in CommutativeRing (last defined first tried ?)
-}


f_equal : {A:Type} -> {B:Type} -> (f:A->B) -> (x:A) -> (y:A) -> (x=y) -> (f x = f y)
f_equal f x y p = ?Mf_equal


{-
rewriteIn : {A':Type} -> {B':Type} -> {A:A'} -> {B:B'} -> (C:Type) -> (a:A) -> (p:A=B) -> (B -> C) -> C
rewriteIn C a p f = ?MrewriteIn_1
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
-- B.2/ This part is to obtain the lemma "push_negation" : -(a+b) = (-b) + (-a)
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


push_negation : (C:Type) -> (dataTypes.Group C) -> (x:C) -> (y:C) -> (Neg (Plus x y) = Plus (Neg y) (Neg x))
push_negation C p x y = 
	let aux : (Plus (Neg (Plus x y)) (Plus x y) = Zero) = right (Plus_inverse (Plus x y)) in
	let aux2 : (Plus (Neg (Plus x y)) (Plus x y) = Plus (Plus (Neg (Plus x y)) x) y) = sym (Plus_assoc (Neg (Plus x y)) x y) in
	let aux3 : (Plus (Plus (Neg (Plus x y)) x) y = the C Zero) = ?Mpush_negation_1 in
	let aux4 : ((Plus (Neg (Plus x y)) x) = Plus Zero (Neg y)) = move_other_side _ _ _ aux3 in
	let aux5 : (Plus Zero (Neg y) = Neg y) = Plus_neutral_1 _ in
	let aux6 : ((Plus (Neg (Plus x y)) x) = Neg y) = ?Mpush_negation_2 in
	let aux7 : (Neg (Plus x y) = Plus (Neg y) (Neg x)) = move_other_side (Neg (Plus x y)) x (Neg y) aux6 in
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


-- -----------------------------------
-- C) TOOLS AND LEMMAS FOR STRUCTURES
-- -----------------------------------

-- C.1) For SemiGroup

semiGroupAssoc_4terms_Aux1 : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus (Plus c1 c2) c3) c4 = Plus (Plus c1 c2) (Plus c3 c4))
semiGroupAssoc_4terms_Aux1 C p c1 c2 c3 c4 = Plus_assoc _ _ _

plusEqualLeft_SemiGroup : (C : Type) -> (SemiGroup C) -> (x:C) -> (x':C) -> (y:C) -> (prEqual:x=x') -> (Plus x y = Plus x' y)
plusEqualLeft_SemiGroup C p x x' y prEqual = ?MplusEqualLeft_SemiGroup_1

semiGroupAssoc_4terms_Aux2 : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 = Plus (Plus (Plus c1 c2) c3) c4)
semiGroupAssoc_4terms_Aux2 = ?MsemiGroupAssoc_4terms_Aux2_1

semiGroupAssoc_4terms : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4  = Plus (Plus c1 c2) (Plus c3 c4))
semiGroupAssoc_4terms C p c1 c2 c3 c4 = ?MsemiGroupAssoc_4terms_1

-- C.2) For Group

groupAssoc_4terms_Aux1 :  (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus (Plus c1 c2) c3) c4 = Plus (Plus c1 c2) (Plus c3 c4))
groupAssoc_4terms_Aux1 C p c1 c2 c3 c4 = Plus_assoc _ _ _

plusEqualLeft_Group : (C : Type) -> (dataTypes.Group C) -> (x:C) -> (x':C) -> (y:C) -> (prEqual:x=x') -> (Plus x y = Plus x' y)
plusEqualLeft_Group C p x x' y prEqual = ?MplusEqualLeft_Group_1 

groupAssoc_4terms_Aux2 : (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 = Plus (Plus (Plus c1 c2) c3) c4)
groupAssoc_4terms_Aux2 = ?MgroupAssoc_4terms_Aux2_1

groupAssoc_4terms : (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4  = Plus (Plus c1 c2) (Plus c3 c4))
groupAssoc_4terms C p c1 c2 c3 c4 = ?MgroupAssoc_4terms_1



-- -----------------------------------
-- D) ARITH TOOLS
-- -----------------------------------
-- D.1) Arith for Nat

lower_value : (x:Nat) -> (y:Nat) -> (LTE x y) -> LTE x (S y)
lower_value Z Z lteZero = lteZero
lower_value (S px) Z lteZero impossible
lower_value (S px) (S py) (lteSucc p) = lteSucc (lower_value _ _ p)
lower_value Z (S py) p = lteZero


bigger_value : (x:Nat) -> (y:Nat) -> (GTE x y) -> GTE (S x) y
bigger_value x y p = lower_value _ _ p


greater_than_succ : (x:Nat) -> (y:Nat) -> (GTE x (S y)) -> (GTE x y)
greater_than_succ (S px) Z (lteSucc p) = lteZero
greater_than_succ (S px) (S py) (lteSucc p) = lower_value (S py) px p
                                                

S_both_side : (x:Nat) -> (y:Nat) -> (x=y) -> (S x = S y)
S_both_side x y P = ?M_S_both_side_1


using (A:Type, B:Type)
    data or : A -> B -> Type where
        Left : A -> or A B
        Right : B -> or A B

        
LTE_0_one_case : (n:Nat) -> (LTE n Z) -> (n=Z)
LTE_0_one_case Z lteZero = refl
LTE_0_one_case (S pn) (lteSucc p) impossible


-- (1 >= n) -> (n=0) or (n=1)     
GTE_1_two_cases : (n:Nat) -> (GTE (S Z) n) -> or (n=Z) (n=(S Z))
-- case 1>=0 (which is 0<=1 by def of >=)
GTE_1_two_cases Z (lteZero {right=S Z}) = Left refl
GTE_1_two_cases (S pn) (lteSucc n) = let pn_is_zero : (pn=Z) = ?M_GTE_1_two_cases_1 in
                                        ?M_GTE_1_two_cases_2

                                        
GTE_S : (a:Nat) -> (b:Nat) -> (GTE a b) -> (GTE (S a) (S b))
GTE_S a b p = lteSucc p 


LTE_same : (a:Nat) -> LTE a a
LTE_same Z = lteZero
LTE_same (S pa) = lteSucc (LTE_same pa)


a_plus_zero : (a:Nat) -> (a+Z = a)
a_plus_zero Z = refl
a_plus_zero (S pa) = S_both_side _ _ (a_plus_zero pa)


plus_succ_right : (a:Nat) -> (b:Nat) -> (S(a+b) = a + (S b))
plus_succ_right Z b = refl
plus_succ_right (S pa) b = let auxP : (S(pa + b) = pa + (S b)) = plus_succ_right pa b in ?Mplus_succ_right_1


plus_succ_left : (a:Nat) -> (b:Nat) -> (S(a+b) = (S a) + b)
plus_succ_left Z b = refl
plus_succ_left (S pa) b = refl


GTE_plus : (a:Nat) -> (b:Nat) -> GTE (a+b) a
-- Proof by induction on a
GTE_plus a Z = let a_plus_zero_is_a : (a+Z = a) = a_plus_zero a in
                -- this is just (LTE_same a) but with a rewriting for the goal
                ?MGTE_plus_1
GTE_plus Z (S pb) = lteZero
GTE_plus (S pa) (S pb) = lteSucc (GTE_plus pa (S pb))


GTE_deleteSucc : (a:Nat) -> (b:Nat) -> (GTE (S a) (S b)) -> GTE a b
-- This proof is just a case analysis and not a proof by induction (there's no recursive call)
GTE_deleteSucc Z Z p = lteZero
--impossible but can't tag it as it : GTE_deleteSucc Z (S Z) lteZero = ?M1
GTE_deleteSucc Z (S (S ppb)) (lteSucc lteZero) impossible
GTE_deleteSucc Z (S (S ppb)) (lteSucc (lteSucc p)) impossible
GTE_deleteSucc Z (S pb) (lteSucc lteZero) impossible
GTE_deleteSucc (S pa) Z p = lteZero
--impossible but can't be tag as it : GTE_deleteSucc (S pa) (S pb) lteZero = ?M1
GTE_deleteSucc (S pa) (S pb) (lteSucc p) = p


plus_one_equals_succ : (n:Nat) -> (n+1 = S n)
plus_one_equals_succ Z = refl
plus_one_equals_succ (S pn) = let p_ihn : (pn + 1 = S pn) = plus_one_equals_succ pn in ?Mplus_one_equals_succ_1


moveSucc : (a:Nat) -> (b:Nat) -> (c:Nat) -> ((a+(S b))+c = ((a+b)+(S c)))
moveSucc Z Z Z = refl
moveSucc Z Z (S pc) = refl
moveSucc Z (S pb) Z = ?MmoveSucc_2
moveSucc Z (S pb) (S pc) = ?MmoveSucc_3
moveSucc (S pa) Z Z = ?MmoveSucc_4
moveSucc (S pa) Z (S pc) = ?MmoveSucc_5
moveSucc (S pa) (S pb) Z = ?MmoveSucc_6
moveSucc (S pa) (S pb) (S pc) = ?MmoveSucc_7


minusFirst : (x:Nat) -> (a:Nat) -> (b:Nat) -> (plusZ (Pos x) (minusNatZ a b) = minusNatZ (plus x a) b)
minusFirst Z Z Z = refl
minusFirst Z Z (S pb) = refl
minusFirst Z (S pa) Z = refl
minusFirst Z (S pa) (S pc) = ?MminusFirst_1
minusFirst (S px) Z Z = refl
minusFirst (S px) Z (S pb) = ?MminusFirst_2
minusFirst (S px) (S pa) Z = refl
minusFirst (S px) (S pa) (S pc) = rewrite (sym(plus_succ_right px pa)) in (minusFirst (S px) pa pc)


plus_minus_succ : (a:Nat) -> (b:Nat) -> (c:Nat) -> minusNatZ (plus a (S b)) (S c) = minusNatZ (plus a b) c
plus_minus_succ Z Z Z = refl
plus_minus_succ Z Z (S pc) = refl
plus_minus_succ Z (S pb) Z = refl
plus_minus_succ Z (S pb) (S pc) = refl
plus_minus_succ (S pa) Z Z = ?Mplus_minus_succ_1
plus_minus_succ (S pa) Z (S pc) = (plus_minus_succ pa Z pc)
plus_minus_succ (S pa) (S pb) Z = ?Mplus_minus_succ_2
plus_minus_succ (S pa) (S pb) (S pc) = (plus_minus_succ pa (S pb) pc)


minusOne : (a:Nat) -> (b:Nat) -> (minusNatZ a (S b) = plusZ (minusNatZ a b) (NegS Z))
minusOne Z Z = refl
minusOne Z (S pb) = ?MminusOne_1
minusOne (S pa) Z = refl
minusOne (S pa) (S pb) = minusOne pa pb -- Recursive call here with strictly lower first and second arguments


minusSucc : (a:Nat) -> (b:Nat) -> (c:Nat) -> (minusNatZ a (plus b (S c)) = plusZ (minusNatZ a b) (NegS c))
minusSucc Z Z Z = refl
minusSucc Z Z (S pc) = refl
minusSucc Z (S pb) Z = ?MminusSucc_1
minusSucc Z (S pb) (S pc) = ?MminusSucc_2
minusSucc (S pa) Z Z = refl
minusSucc (S pa) Z (S pc) = refl
minusSucc (S pa) (S pb) Z = minusSucc pa pb Z
minusSucc (S pa) (S pb) (S pc) = (minusSucc pa pb (S pc)) -- Recursive call here with strictly lower first and second arguments


plusPos : (a:Nat) -> (b:Nat) -> (c:Nat) -> (minusNatZ (plus a b) c = plusZ (minusNatZ a c) (Pos b))
plusPos Z Z Z = refl
plusPos Z Z (S pc) = refl
plusPos Z (S pb) Z = refl
plusPos Z (S pb) (S pc) = refl
plusPos (S pa) Z Z = refl
plusPos (S pa) Z (S pc) = (plusPos pa Z pc) -- Recursive call here with first and third arguments stricly lower
plusPos (S pa) (S pb) Z = refl
plusPos (S pa) (S pb) (S pc) = (plusPos pa (S pb) pc) -- Recursive call here with first and third arguments stricly lower


minusNegS : (a:Nat) -> (b:Nat) -> (c:Nat) -> (plusZ (minusNatZ a (S b)) (NegS c) = plusZ (minusNatZ a b) (NegS (S c)))
minusNegS Z Z Z = refl
minusNegS Z Z (S pc) = refl
minusNegS Z (S pb) Z = ?MminusNegS_1
minusNegS Z (S pb) (S pc) = ?MminusNegS_2
minusNegS (S pa) Z Z = refl
minusNegS (S pa) Z (S pc) = refl
minusNegS (S pa) (S pb) Z = (minusNegS pa pb Z) -- Recursive call here with first and second arguments stricly lower
minusNegS (S pa) (S pb) (S pc) = (minusNegS pa pb (S pc)) -- Recursive call here with first and second arguments stricly lower


switch_negS : (a:Nat) -> (b:Nat) -> (c:Nat) -> plusZ (minusNatZ a b) (NegS c) = plusZ (minusNatZ a c) (NegS b)
switch_negS Z Z Z = refl
switch_negS Z Z (S pc) = ?Mswitch_negS_1
switch_negS Z (S pb) Z = ?Mswitch_negS_2
switch_negS Z (S pb) (S pc) = ?Mswitch_negS_3
switch_negS (S pa) Z Z = refl
switch_negS (S pa) Z (S pc) = ?Mswitch_negS_4
switch_negS (S pa) (S pb) Z = ?Mswitch_negS_5
switch_negS (S pa) (S pb) (S pc) = rewrite (sym (minusNegS pa pc pb)) in (switch_negS pa pb (S pc)) 


switch_double_succ : (a:Nat) -> (b:Nat) -> plus a (S (S b)) = plus b (S (S a))
switch_double_succ Z Z = refl
switch_double_succ Z (S pb) = ?Mswitch_double_succ_1
switch_double_succ (S pa) Z = ?Mswitch_double_succ_2
switch_double_succ (S pa) (S pb) = let ih = switch_double_succ pa (S pb) in ?Mswitch_double_succ_3

-- D.2) Arith for Z

zero_plusZ_a : (a:ZZ) -> ((Pos Z) + a = a)
zero_plusZ_a (Pos x) = refl
zero_plusZ_a (NegS x) = refl

a_plusZ_zero : (a:ZZ) -> (a + (Pos Z) = a)
a_plusZ_zero (Pos x) = ?Ma_plusZ_zero_1
a_plusZ_zero (NegS x) = refl


-- To add in the depository for Idris
plusAssociativeZ : (left : ZZ) -> (centre : ZZ) -> (right : ZZ) ->
  left + (centre + right) = (left + centre) + right
-- start with POS
-- Pos - Pos - Pos
plusAssociativeZ (Pos Z) (Pos Z) (Pos Z) = refl
plusAssociativeZ (Pos Z) (Pos Z) (Pos (S pw)) = refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (Pos Z) = refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (Pos (S pw)) = refl
plusAssociativeZ (Pos (S pu)) (Pos Z) (Pos Z) = ?MplusAssociativeZ_1_2 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (Pos (S pw)) = ?MplusAssociativeZ_1_3 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (Pos Z) = ?MplusAssociativeZ_1_4 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_1_5 --done

-- Pos - Pos - Neg
plusAssociativeZ (Pos Z) (Pos Z) (NegS Z) = refl
plusAssociativeZ (Pos Z) (Pos Z) (NegS (S pw)) = refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (NegS Z) = refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_2_1 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (NegS Z) = ?MplusAssociativeZ_2_2 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (NegS (S pw)) = ?MplusAssociativeZ_2_3 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (NegS Z) = ?MplusAssociativeZ_2_4 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_2_5 --done

-- Pos - Neg - Pos
plusAssociativeZ (Pos Z) (NegS Z) (Pos Z) = refl
plusAssociativeZ (Pos Z) (NegS Z) (Pos (S pw)) = refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (Pos Z) = refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_3_1 --done
plusAssociativeZ (Pos (S pu)) (NegS Z) (Pos Z) = ?MplusAssociativeZ_3_2 --done
plusAssociativeZ (Pos (S pu)) (NegS Z) (Pos (S pw)) = ?MplusAssociativeZ_3_3 --done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (Pos Z) = ?MplusAssociativeZ_3_4 --done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_3_5 -- done

-- Pos - Neg - Neg
plusAssociativeZ (Pos Z) (NegS Z) (NegS Z) = refl
plusAssociativeZ (Pos Z) (NegS Z) (NegS (S pw)) = refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (NegS Z) = refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (NegS (S pw)) = refl
plusAssociativeZ (Pos (S pu)) (NegS Z) (NegS Z) = refl
plusAssociativeZ (Pos (S pu)) (NegS Z) (NegS (S pw)) = refl
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (NegS Z) = ?MplusAssociativeZ_4_4 -- done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_4_5 --done

-- start with NEG
-- Neg - Pos - Pos
plusAssociativeZ (NegS Z) (Pos Z) (Pos Z) = refl
plusAssociativeZ (NegS Z) (Pos Z) (Pos (S pw)) = refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (Pos Z) = refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (Pos (S pw)) = refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (Pos Z) = refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (Pos (S pw)) = refl
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (Pos Z) = ?MplusAssociativeZ_5_4 --done
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_5_5 -- done

-- Neg - Pos - Neg
plusAssociativeZ (NegS Z) (Pos Z) (NegS Z) = refl
plusAssociativeZ (NegS Z) (Pos Z) (NegS (S pw)) = refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (NegS Z) = refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_6_1 -- done
plusAssociativeZ (NegS (S pu)) (Pos Z) (NegS Z) = refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (NegS (S pw)) = refl
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (NegS Z) = ?MplusAssociativeZ_6_4 -- done
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_6_5 -- done

-- Neg - Neg - Pos
plusAssociativeZ (NegS Z) (NegS Z) (Pos Z) = refl
plusAssociativeZ (NegS Z) (NegS Z) (Pos (S pw)) = refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (Pos Z) = refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_7_1 -- done
plusAssociativeZ (NegS (S pu)) (NegS Z) (Pos Z) = refl
plusAssociativeZ (NegS (S pu)) (NegS Z) (Pos (S pw)) = ?MplusAssociativeZ_7_3 --done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (Pos Z) = refl
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_7_5 -- done

-- Neg - Neg - Neg
plusAssociativeZ (NegS Z) (NegS Z) (NegS Z) = refl
plusAssociativeZ (NegS Z) (NegS Z) (NegS (S pw)) = refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (NegS Z) = refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (NegS (S pw)) = refl
plusAssociativeZ (NegS (S pu)) (NegS Z) (NegS Z) = ?MplusAssociativeZ_8_2 -- done
plusAssociativeZ (NegS (S pu)) (NegS Z) (NegS (S pw)) = ?MplusAssociativeZ_8_3 -- done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (NegS Z) = ?MplusAssociativeZ_8_4 -- done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_8_5 --done



-- -----------------------------------
-- E) FIN TOOLS
-- -----------------------------------
minusOrEqual_Fin : {n:Nat} -> (i:Fin n) -> (j:Fin m) -> Bool
minusOrEqual_Fin fZ fZ = True
minusOrEqual_Fin fZ (fS j') = True
minusOrEqual_Fin (fS i') fZ = False
minusOrEqual_Fin (fS i') (fS j') = minusOrEqual_Fin i' j'

	
-- convert i from an element of Fin n to an element of Fin (S m), provided that (S m) is greater or equal to n
total
pre_convertFin : {n:Nat} -> (i:Fin n) -> (m:Nat) -> (p:GTE (S m) n) -> Fin (S m)
-- case  n=0, which mean 0<= Sm, but impossible because we're having an element of Fin 0
pre_convertFin {n=Z} (fZ) m (lteZero) impossible
pre_convertFin {n=Z} (fS x) m _ impossible
-- case n= Sk, which includes two cases
  -- case fZ
pre_convertFin {n=S k} (fZ {k=k}) m p = fZ {k=m}
  -- case fS x, where x is an element of Fin k
pre_convertFin {n=S k} (fS x) (S pm) p = let m_gte_k : GTE (S pm) k = GTE_deleteSucc _ _ p in
											 let x_conv : Fin (S pm) = pre_convertFin x pm m_gte_k in
												fS x_conv
-- Impossible case : transforming an element of Fin (S k) into an element of (Fin 1), which forces k to be Zero, and then
-- there is only one element to convert : fZ {k=0}. But we're having an fS, and not an fZ...
pre_convertFin {n=S k} (fS x) Z p with (decEq k Z, decEq k (S Z))
    pre_convertFin {n=S k} (fS x) Z p | (Yes refl, Yes refl) impossible
    pre_convertFin {n=S k} (fS x) Z p | (Yes refl, No p2) impossible
    pre_convertFin {n=S k} (fS x) Z p | (No p1, Yes refl) impossible
    pre_convertFin {n=S k} (fS x) Z p | (No p1, No p2) = let k_is_zero_or_one : (or (k=Z) (k=S Z)) = GTE_1_two_cases k (greater_than_succ _ _ p) in
                                                            case k_is_zero_or_one of
                                                            Left k_is_zero => ?Mpre_convertFin_1
                                                            Right k_is_one => ?Mpre_convertFin_2

-- We know that we can use pre_convertFin because (n+x) is the successor of something (ie, can't be zero), because n
-- can't be zero (otherwise we would have an inhabitant of Fin 0)
convertFin : (n:Nat) -> (i:Fin n) -> (x:Nat) -> Fin (n+x)
-- n can't be zero
convertFin Z fZ x impossible
convertFin Z (fS pi) x impossible
convertFin (S pn) i x = let proofGTE : (GTE (S(pn+x)) (S pn)) = ?MconvertFin_1 in
                        pre_convertFin i (pn+x) proofGTE



testconversion1 : Fin 6
testconversion1 = pre_convertFin {n=3} (fZ {k=2}) 5 (lteSucc (lteSucc (lteSucc lteZero)))
-- test ok

testconversion2 : Fin 6
testconversion2 = pre_convertFin {n=3} (fS (fZ {k=1})) 5 (lteSucc (lteSucc (lteSucc lteZero)))
-- test ok

-- Computes the next element of a given element in a set of n element. If the
-- current element is already the last one of the set, we return it back.
nextElement : (n:Nat) -> (i:Fin n) -> Fin n
-- n can't be zero
nextElement Z fZ impossible
nextElement Z (fS pi) impossible
-- case where this is a fZ, and we've not yet reached the final element of the set
nextElement (S (S ppn)) (fZ {k=S ppn}) = fS (fZ {k=ppn})
-- case where this is a fZ, and we've reached the final element of the set. We give back the same fZ. This enables to always loop on the last element of a set if we ask for the next element.
nextElement (S Z) (fZ {k=Z}) = fZ {k=Z}
-- case where this is a (fS pi).
nextElement (S pn) (fS {k=pn} pi) = fS (nextElement pn pi)


lastElement : (pn:Nat) -> Fin (S pn)
lastElement Z = fZ
lastElement (S ppn) = fS (lastElement ppn)

lastElement' : (pn:Nat) -> Fin(pn+1)
lastElement' pn = let pn_plus_1_equals_Spn : (pn+1 = S pn) = plus_one_equals_succ pn in
                    -- This is just a call to the other function lastElement with the argument pn, but with a rewriting of the goal
                    ?MlastElement'_1

-- -----------------------------------
-- F) VECTOR TOOLS
-- -----------------------------------

{- Not needed now
--changeIeme : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (Vect n A)

--changeIeme_correct : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (a = index_reverse i (changeIeme g i a))
-}

-- F.1) index and reverse

-- No longer needed !
{-
lastElement_of_reverse_is_first' : (g : Vect (S pn) a) -> (index (fZ {k=pn}) g = index (lastElement pn) (reverse g))
lastElement_of_reverse_is_first' (h::Nil) = refl
lastElement_of_reverse_is_first' (h::(h2::t2)) = let ih = lastElement_of_reverse_is_first' (h2::t2) in ?MA
-}

-- No longer needed !
{-
lastElement_of_reverse_is_first : (g : Vect (S pn) a) -> ((head g = index (lastElement pn) (reverse g)))
lastElement_of_reverse_is_first (h::t) = ?MB
-}

-- F.2) Append

{-
vectorAppend_assoc : {c:Type} -> {n:Nat} -> {m:Nat} -> {p:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (g3:Vect p c) -> (g1++(g2++g3) = (g1 ++ g2)++g3)
vectorAppend_assoc Nil Nil Nil = refl
vectorAppend_assoc Nil Nil (h3::t3) = refl
vectorAppend_assoc Nil (h2::t2) Nil = refl
vectorAppend_assoc Nil (h2::t2) (h3::t3) = refl
vectorAppend_assoc (h1::t1) Nil Nil = 
	let ih : (t1 ++ (Nil) = (t1 ++ Nil) ++ Nil) = vectorAppend_assoc t1 Nil Nil in 
	vectConsCong h1 (t1++[]) ((t1++[])++[]) ih 
vectorAppend_assoc (h1::t1) Nil (h3::t3) = 
	let ih = vectorAppend_assoc t1 Nil (h3::t3) in
	vectConsCong h1 (t1++(h3::t3)) ((t1++[])++(h3::t3)) ih
vectorAppend_assoc (h1::t1) (h2::t2) g3 = 
	let ih = vectorAppend_assoc t1 (h2::t2) g3 in
	vectConsCong h1 (t1++(h2::t2)++g3) ((t1++(h2::t2))++g3) ih
	-}

-- F.3) "Subsets"

using (c:Type, n:Nat, m:Nat)
    data SubSet : Vect n c -> Vect m c -> Type where
        SubSet_same : (g:Vect n c) -> SubSet g g
        SubSet_add : (c1:c) -> (g1:Vect n c) -> (g2:Vect k c) -> (SubSet g1 g2) -> SubSet g1 (c1 :: g2)


total
SubSet_wkn : (g1:Vect n c) -> (g2:Vect m c) -> (c1:c) -> (SubSet (c1::g1) g2) -> (SubSet g1 g2)
SubSet_wkn g1 _ c1 (SubSet_same _) = SubSet_add c1 g1 g1 (SubSet_same g1)
SubSet_wkn g1 (h2::t2) c1 (SubSet_add h2 g1 t2 c1_cons_g1_in_t2) = SubSet_add h2 g1 t2 (SubSet_wkn g1 t2 c1 c1_cons_g1_in_t2)


total
SubSet_trans : (g1:Vect n c) -> (g2:Vect m c) -> (g3 : Vect k c) -> (SubSet g1 g2) -> (SubSet g2 g3) -> (SubSet g1 g3)
SubSet_trans g1 _ _ (SubSet_same g1) (SubSet_same _) = SubSet_same g1
SubSet_trans g1 _ (h3::t3) (SubSet_same g1) (SubSet_add h3 g1 t3 g1_in_t3) = SubSet_add h3 g1 t3 g1_in_t3
SubSet_trans g1 (h2::t2) _ (SubSet_add h2 g1 t2 g1_in_t2) (SubSet_same _) = SubSet_add h2 g1 t2 g1_in_t2
SubSet_trans g1 (h2::t2) (h3::t3) (SubSet_add h2 g1 t2 g1_in_t2) (SubSet_add h3 _ t3 h2_cons_t2_in_t3) = 
    let t2_in_t3 : SubSet t2 t3 = SubSet_wkn t2 t3 h2 h2_cons_t2_in_t3 in 
        SubSet_add h3 g1 t3 (SubSet_trans g1 t2 t3 g1_in_t2 t2_in_t3)    
  
  
-- No longer needed !
{-
postulate    
	SubSet_size : {c:Type} -> (n:Nat) -> (m:Nat) -> (g1:Vect n c) -> (g2:Vect m c) -> (SubSet g1 g2) -> (GTE m n)
-}    

concat_SubSet : {c:Type} -> {n:Nat} -> {m:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (SubSet g1 (g2++g1))
concat_SubSet Nil Nil = SubSet_same _
concat_SubSet (h1::t1) Nil = SubSet_same _
concat_SubSet g1 (h2::t2) = let ih:SubSet g1 (t2++g1) = concat_SubSet g1 t2 in SubSet_add h2 _ _ ih

  
-- No longer needed !
{-  
-- Says that ig g2 is a "superset" of g1, then the first element are the same
postulate -- Will be proven later
	indexReverse_of_convert : {c:Type} -> {n:Nat} -> (g1:Vect n c) -> (i:Fin n) -> {m:Nat} -> (g2:Vect (S m) c) -> (p: GTE (S m) n) -> (SubSet g1 g2) -> (index_reverse i g1 = index_reverse (pre_convertFin i m p) g2)
-}	
	
-- Subset and equality
SubSet_rewriteRight : {c:Type} -> {n:Nat} -> {m:Nat} -> {p:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (g3:Vect p c) -> (SubSet g1 g2) -> (g2=g3) -> (SubSet g1 g3)
SubSet_rewriteRight g1 g2 g2 psub refl = psub -- ?MSubSet_rewriteRight_1


-- F.4) Removing elements

-- Not needed now
{-
remove_first_x_elements : {a:Type} -> {n:Nat} -> (x:Nat) -> (Vect (x+n) a) -> (Vect n a)
remove_first_x_elements Z g = g
remove_first_x_elements (S px) (h::t) = remove_first_x_elements px t
remove_first_x_elements (S px) Nil impossible


remove_first_x_subset : {a:Type} -> {n:Nat} -> (x:Nat) -> (g:Vect (x+n) a) -> (SubSet (remove_first_x_elements x g) g)
remove_first_x_subset x g = ?Mremove_first_x_subset_1

-}

-- No longer needed !
{-
-- Two remarks : 
-- 	1) The two vectors may have different size
-- 	2) The result is a Maybe, instead of Dec (a proof is only provided if they are equal)
total
vect_eq : {a:Type} -> (a_eq : (a1:a)->(a2:a)->Maybe(a1=a2)) -> (n:Nat) -> (m:Nat) -> (g1:Vect n a) -> (g2:Vect m a) -> Maybe (g1=g2)
vect_eq a_eq _ _ Nil Nil = Just refl
vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) with (decEq pn pm)
	vect_eq a_eq (S pn) (S pn) (h1::t1) (h2::t2) | (Yes refl) with (a_eq h1 h2, vect_eq a_eq pn pn t1 t2)
		vect_eq a_eq _ _ (h1::t1) (h1::t1) | (Yes refl) | (Just refl, Just refl) = Just refl
		vect_eq a_eq _ _ (h1::t1) _ | (Yes refl) | _ = Nothing
	vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) | (No _) = Nothing
vect_eq a_eq _ _ _ _ = Nothing
-}

---------- Proofs ----------  
-- Part A) : Pairs, dependent pairs, and functions

tools.Mf_equal = proof
  intros
  rewrite p
  exact refl
  
  
-- Part B) : Groups

-- B.1/ This subpart is to obtain the lemma "group_doubleNeg" : - (-a) = a


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

tools.MGroup_unicity_2 = proof
  intros
  mrefine Plus_assoc  
  
tools.MhasSymmetric_sym = proof
  intro
  intro
  intro
  intro
  intro H
  exact (right H, left H)  
  
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

-- B.2/ This part is to obtain the lemma "push_negation" : -(a+b) = (-b) + (-a)
  
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

tools.MplusEqualLeft_SemiGroup_1 = proof {
  intros;
  rewrite prEqual;
  trivial;
}

tools.MsemiGroupAssoc_4terms_Aux2_1 = proof {
  intros;
  mrefine plusEqualLeft_SemiGroup;
  rewrite (Plus_assoc c1 c2 c3);
  trivial;
}

tools.MsemiGroupAssoc_4terms_1 = proof
  intros
  rewrite (semiGroupAssoc_4terms_Aux1 C p c1 c2 c3 c4)
  rewrite (semiGroupAssoc_4terms_Aux2 C p c1 c2 c3 c4)
  exact refl

tools.MplusEqualLeft_Group_1 = proof {
  intros;
  rewrite prEqual;
  trivial;
}

tools.MgroupAssoc_4terms_Aux2_1 = proof
  intros
  mrefine plusEqualLeft_Group 
  rewrite (Plus_assoc c1 c2 c3)
  exact refl

tools.MgroupAssoc_4terms_1 = proof
  intros
  rewrite (groupAssoc_4terms_Aux1 C p c1 c2 c3 c4)
  rewrite (groupAssoc_4terms_Aux2 C p c1 c2 c3 c4)
  mrefine refl
    
{-
tools.aux1 = proof {
  compute;
  trivial;
}
-}

-- Part D : Arith tools

-- D.1) Arith for Nat

tools.M_S_both_side_1 = proof
  intros
  rewrite P
  mrefine refl
  
tools.M_GTE_1_two_cases_1 = proof
  intro pn, p
  mrefine LTE_0_one_case 
  mrefine p
  
tools.M_GTE_1_two_cases_2 = proof
  intros
  mrefine Right
  mrefine S_both_side
  mrefine pn_is_zero 

tools.Mplus_succ_right_1 = proof
  intros
  rewrite auxP
  exact refl

tools.MGTE_plus_1 = proof
  intros
  rewrite (sym a_plus_zero_is_a)
  mrefine LTE_same

tools.Mplus_one_equals_succ_1 = proof
  intros
  rewrite p_ihn 
  exact refl
  
tools.MmoveSucc_2 = proof
  intros
  rewrite (plus_succ_right pb 0)
  exact refl
  
tools.MmoveSucc_3 = proof
  intros
  rewrite (plus_succ_right pb (S pc))
  exact refl
  
tools.MmoveSucc_4 = proof
  intros
  rewrite (sym (a_plus_zero (plus pa 1)))
  rewrite (sym (a_plus_zero pa))
  exact refl

tools.MmoveSucc_5 = proof
  intros
  rewrite (plus_succ_right pa 0)
  rewrite (plus_succ_right (plus pa 0) (S pc))
  compute
  exact refl  

tools.MmoveSucc_6 = proof
  intros
  rewrite (plus_succ_right pa (S pb))
  rewrite (plus_succ_right (plus pa (S pb)) 0)
  compute
  exact refl
  
tools.MmoveSucc_7 = proof
  intros
  rewrite (plus_succ_right pa (S pb))
  rewrite (plus_succ_right (plus pa (S pb)) (S pc))
  compute
  exact refl

tools.MminusFirst_1 = proof
  intros
  rewrite (sym(plusCommutativeZ (Pos Z) (minusNatZ pa pc))) 
  exact (plusZeroRightNeutralZ (minusNatZ pa pc))

tools.MminusFirst_2 = proof
  intros
  rewrite (a_plus_zero px)
  exact refl
  
tools.Mplus_minus_succ_1 = proof
  intros
  rewrite (sym(plus_succ_right pa Z))
  exact refl

tools.Mplus_minus_succ_2 = proof
  intros
  rewrite (sym(plus_succ_right pa (S pb)))
  exact refl  

tools.MminusOne_1 = proof
  intros
  rewrite (a_plus_zero pb)
  exact refl

tools.MminusSucc_1 = proof
  intros
  rewrite (sym(plus_succ_right pb Z))
  exact refl
  
tools.MminusSucc_2 = proof
  intros
  rewrite (sym(plus_succ_right pb (S pc)))
  exact refl

tools.MminusNegS_1 = proof
  intros
  rewrite (plus_succ_right pb Z)
  exact refl
  
tools.MminusNegS_2 = proof
  intros
  rewrite (plus_succ_right pb (S pc))
  exact refl

 

tools.Mswitch_negS_1 = proof
  intros
  rewrite (a_plus_zero pc)
  exact refl

tools.Mswitch_negS_2 = proof
  intros
  rewrite (a_plus_zero pb)
  exact refl

tools.Mswitch_negS_3 = proof
  intros
  rewrite (sym(plusCommutative pb (S pc)))
  rewrite (sym( plus_succ_right pc pb))
  exact refl  

tools.Mswitch_negS_4 = proof
  intros
  rewrite (plus_one_equals_succ pc)
  rewrite (sym(minusSucc pa pc Z))
  exact refl 

tools.Mswitch_negS_5 = proof
  intros
  rewrite (minusSucc pa pb Z)
  rewrite (plus_one_equals_succ pb)
  exact refl  
  
tools.Mswitch_double_succ_1 = proof
  intros
  rewrite (plus_one_equals_succ pb)
  rewrite (plus_succ_right pb (S Z))
  exact refl
  
tools.Mswitch_double_succ_2 = proof
  intros
  rewrite (plus_one_equals_succ pa)
  rewrite (plus_succ_right pa (S Z))
  exact refl

tools.Mswitch_double_succ_3 = proof
  intros
  rewrite (plus_succ_right pb (S (S pa)))
  exact (f_equal (\x => S x) _ _ ih)  
  
-- D.2) Arith for Z

tools.Ma_plusZ_zero_1 = proof
  intros
  rewrite (a_plus_zero x)
  exact refl
  
tools.MplusAssociativeZ_1_2 = proof
  intros
  rewrite (a_plus_zero (plus pu 0))
  exact refl
  
tools.MplusAssociativeZ_1_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact refl
  
tools.MplusAssociativeZ_1_4 = proof
  intros
  rewrite (sym (a_plus_zero (pv)))
  rewrite (sym (a_plus_zero (plus pu (S pv))))
  exact refl
  
tools.MplusAssociativeZ_1_5 = proof
  intros
  rewrite (sym(plus_succ_right pv (S pw)))
  rewrite (sym (plusAssociative pu pv (S (S pw))))
  rewrite (moveSucc pu pv (S pw))
  exact refl

tools.MplusAssociativeZ_2_1 = proof
  intros
  rewrite (zero_plusZ_a (minusNatZ pv (S pw)))
  exact refl
  
tools.MplusAssociativeZ_2_2 = proof
  intros
  rewrite (a_plus_zero pu)
  exact refl
  

tools.MplusAssociativeZ_2_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact refl

tools.MplusAssociativeZ_2_4 = proof
  intros
  rewrite (plus_succ_right pu pv)
  exact refl
  
tools.MplusAssociativeZ_2_5 = proof
  intros
  rewrite (sym(minusFirst (S pu) pv (S pw)))
  rewrite (sym(plus_minus_succ pu pv pw))
  exact refl  

tools.MplusAssociativeZ_3_1 = proof
  intros
  rewrite (zero_plusZ_a (minusNatZ pw (S pv)))
  exact refl

tools.MplusAssociativeZ_3_2 = proof
  intros
  rewrite (a_plus_zero pu)
  exact refl

tools.MplusAssociativeZ_3_3 = proof
  intros
  rewrite (plus_succ_right pu pw)
  exact refl

tools.MplusAssociativeZ_3_4 = proof
  intros
  rewrite (a_plusZ_zero (minusNatZ pu (S pv)))
  exact refl
  
tools.MplusAssociativeZ_3_5 = proof
  intros
  rewrite (sym(minusFirst (S pu) pw (S pv)))
  rewrite (plus_minus_succ  pu pw pv)
  rewrite (sym(plusCommutativeZ (minusNatZ pu (S pv)) (Pos(S pw))))
  rewrite(sym(minusFirst (S pw) pu (S pv)))
  rewrite (sym(plus_minus_succ pu pw pv))
  rewrite (plusCommutative pw pu)
  exact refl
  
tools.MplusAssociativeZ_4_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (sym(minusOne pu (S pv)))
  exact refl

tools.MplusAssociativeZ_4_5 = proof
  intros
  rewrite (minusSucc pu (S pv) (S pw))
  rewrite (sym(plus_succ_right pv (S pw)))
  exact refl

tools.MplusAssociativeZ_5_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (a_plusZ_zero (minusNatZ pv (S pu)))
  exact refl

tools.MplusAssociativeZ_5_5 = proof
  intros
  rewrite (sym(plusPos pv (S pw) (S pu)))
  exact refl
  
tools.MplusAssociativeZ_6_1 = proof
  intros
  rewrite (plusCommutativeZ (NegS Z) (minusNatZ pv (S pw)))
  rewrite (sym(plusCommutativeZ (NegS Z) (minusNatZ pv (S pw))))
  rewrite (minusOne pv (S pw))
  exact refl
  
tools.MplusAssociativeZ_6_4 = proof
  intros
  rewrite (sym(minusOne pv (S pu)))
  exact refl    

tools.MplusAssociativeZ_6_5 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS (S pu)) (minusNatZ pv (S pw))))
  rewrite (sym( switch_negS pv (S pw) (S pu)))
  exact refl

tools.MplusAssociativeZ_7_1 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS Z) (minusNatZ pw (S pv))))
  rewrite (sym(switch_negS pw (S pv) Z))
  exact refl

tools.MplusAssociativeZ_7_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact refl
  
tools.MplusAssociativeZ_7_5 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS (S pu)) (minusNatZ pw (S pv))))
  rewrite (minusSucc pw (S pv) (S pu))
  rewrite (sym(plus_succ_right pu (S pv)))
  rewrite (switch_double_succ pv pu)
  exact refl  

tools.MplusAssociativeZ_8_2 = proof
  intros
  rewrite (sym (a_plus_zero pu))
  rewrite (sym(plus_succ_right pu 0))
  exact refl

tools.MplusAssociativeZ_8_3 = proof
  intros
  rewrite (sym(a_plus_zero pu))
  rewrite (sym(plus_succ_right pu (S pw)))
  exact refl

tools.MplusAssociativeZ_8_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (plus_succ_right pu (S pv))
  rewrite (sym (a_plus_zero (plus pu (S pv))))
  exact refl

tools.MplusAssociativeZ_8_5 = proof
  intros
  rewrite (plus_succ_right pu (S (S (plus pv (S pw)))))
  rewrite (sym(plus_succ_right pu (S (S (plus pv (S pw))))))
  rewrite (plus_succ_right (plus pu (S pv)) (S pw))
  rewrite (sym(plus_succ_right (plus pu (S pv)) (S pw)))
  rewrite (plus_succ_right pu (S (S (plus pv (S pw)))))
  rewrite (sym(plus_succ_right pv (S pw)))
  rewrite (sym(plus_succ_left pv (S (S pw))))
  rewrite (sym (plus_succ_left pv (S (S pw))))
  rewrite (plusAssociative pu (S pv) (S (S pw)))
  exact refl

-- Part E : Fin tools

tools.Mpre_convertFin_1 = proof
  intros
  mrefine FalseElim
  mrefine p1
  mrefine k_is_zero

tools.Mpre_convertFin_2 = proof
  intros
  mrefine FalseElim
  mrefine p2
  mrefine k_is_one

tools.MconvertFin_1 = proof
  intros
  mrefine GTE_S
  mrefine GTE_plus

tools.MlastElement'_1 = proof
  intros
  rewrite pn_plus_1_equals_Spn 
  rewrite (sym pn_plus_1_equals_Spn)
  exact (lastElement pn)
  
-- Part F : Vector tools







---------- Proofs ----------







