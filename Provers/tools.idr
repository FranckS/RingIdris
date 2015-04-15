-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File tools.idr
-- Various tools needed for the implementation of the ring tactic for Idris
-------------------------------------------------------------------

module Provers.tools

import Data.ZZ
import Data.Fin

import Provers.globalDef
import Provers.dataTypes


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
group_unicity_symmetric : {C:Type} -> (p:dataTypes.Group C) -> (a:C) -> (b:C) -> (c:C) -> (hasSymmetric C (group_to_monoid_class p) a b) -> (hasSymmetric C (group_to_monoid_class p) a c) -> (b~=c)
group_unicity_symmetric p a b c p1 p2 = let a = aux in ?MGroup_unicity_1
  where aux : Plus (Plus b a) c ~= Plus b (Plus a c) 
	aux = ?MGroup_unicity_2
	

hasSymmetric_sym : {C:Type} -> (p:dataTypes.Group C) -> (a:C) -> (b:C) -> (hasSymmetric C (group_to_monoid_class p) a b) -> (hasSymmetric C (group_to_monoid_class p) b a)
hasSymmetric_sym = ?MhasSymmetric_sym


plus_inverse_2 : {C:Type} -> (p:dataTypes.Group C) -> (c1:C) -> hasSymmetric C (%instance) (Neg c1) c1 -- Every element 'Neg x' has a symmetric which is x
plus_inverse_2 p c1 = ?Mplus_inverse_2	


group_doubleNeg : (C:Type) -> (p:dataTypes.Group C) -> (a:C) -> ((Neg (Neg a)) ~= a) 
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

--adding_preserves_equality : {C:Type} -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (z:C) -> (x~=y) -> ((Plus x z) ~= (Plus y z))
adding_preserves_equality : {C:Type} -> {p:dataTypes.Group C} -> (x:C) -> (y:C) -> (z:C) -> (x~=y) -> ((Plus x z) ~= (Plus y z))
adding_preserves_equality x y z H = ?Madding_preserves_equality_1


move_other_side : {C:Type} -> (dataTypes.Group C) -> (x:C) -> (y:C) -> (z:C) -> ((Plus x y) ~= z) -> (x ~= (Plus z (Neg y)))
move_other_side p x y z H =
    let aux : ((Plus (Plus x y) (Neg y)) ~= (Plus z (Neg y))) = adding_preserves_equality {p=p} (Plus x y) z (Neg y) H in
    let aux2 : ((Plus (Plus x y) (Neg y)) ~= (Plus x (Plus y (Neg y)))) = (Plus_assoc x y (Neg y)) in
    let aux3 : ((Plus x (Plus y (Neg y))) ~= (Plus z (Neg y))) = ?Mmove_other_side_1 in -- Just a rewriting in an hypothesis
    let aux4 : ((Plus y (Neg y)) ~= Zero) = (left (Plus_inverse y)) in
    let aux5 : ((Plus x (Plus y (Neg y))) ~= x) = ?Mmove_other_side_2 in
        ?Mmove_other_side_3


push_negation : (C:Type) -> (dataTypes.Group C) -> (x:C) -> (y:C) -> ((Neg (Plus x y)) ~= (Plus (Neg y) (Neg x)))
push_negation C p x y = 
    let aux : ((Plus (Neg (Plus x y)) (Plus x y)) ~= Zero) = right (Plus_inverse (Plus x y)) in
    let aux2 : ((Plus (Neg (Plus x y)) (Plus x y)) ~= (Plus (Plus (Neg (Plus x y)) x) y)) = set_eq_undec_sym {x=Plus (Plus (Neg (Plus x y)) x) y} {y=Plus (Neg (Plus x y)) (Plus x y)} (Plus_assoc (Neg (Plus x y)) x y) in
    let aux3 : ((Plus (Plus (Neg (Plus x y)) x) y) ~= the C Zero) = ?Mpush_negation_1 in
    let aux4 : ((Plus (Neg (Plus x y)) x) ~= (Plus Zero (Neg y))) = move_other_side p (Plus (Neg (Plus x y)) x) y Zero aux3 in
    let aux5 : ((Plus Zero (Neg y)) ~= (Neg y)) = Plus_neutral_1 (Neg y) in
    let aux6 : ((Plus (Neg (Plus x y)) x) ~= (Neg y)) = ?Mpush_negation_2 in
    let aux7 : ((Neg (Plus x y)) ~= (Plus (Neg y) (Neg x))) = move_other_side p (Neg (Plus x y)) x (Neg y) aux6 in
        ?Mpush_negation_3
	      
{-
And_True_neutral : (b:Bool) -> (True && b = b)
And_True_neutral _ = Refl

And_False_absorbent : (b:Bool) -> (False && b = False)
And_False_absorbent _ = Refl
  
And_assoc : (a:Bool) -> (b:Bool) -> (c:Bool) -> ((a && (b && c)) = ((a && b) && c))
And_assoc True True True = Refl
And_assoc True True False = Refl
And_assoc True False True = Refl
And_assoc True False False = Refl
And_assoc False True True = Refl
And_assoc False True False = Refl
And_assoc False False True = Refl
And_assoc False False False = Refl

And_assoc2 : (a:Bool) -> (b:Bool) -> (c:Bool) -> (((a && b) && c) = (a && (b && c)))
And_assoc2 True True True = Refl
And_assoc2 True True False = Refl
And_assoc2 True False True = Refl
And_assoc2 True False False = Refl
And_assoc2 False True True = Refl
And_assoc2 False True False = Refl
And_assoc2 False False True = Refl
And_assoc2 False False False = Refl

aux1 : O = plus O O

-}

-- -------------------------------
-- B') TOOLS AND LEMMAS FOR RINGS
-- -------------------------------

-- Cancelation Lemma could have been useful but we won't generalize it in fact, we just do the cancelation "by hand" when needed


-- Zero is absorbant for Mult
zeroAbsorbant : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (Mult a Zero ~= Zero)
zeroAbsorbant C p a = 
	let p1 : (Mult a Zero ~= Mult a (Plus Zero Zero)) = ?MzeroAbsorbant_1 in
	let p2 : (Mult a (Plus Zero Zero) ~= Plus (Mult a Zero) (Mult a Zero)) = ?MzeroAbsorbant_2 in
	let p3 : (Mult a Zero ~= Plus (Mult a Zero) (Mult a Zero)) = ?MzeroAbsorbant_3 in
	let p4 : (Plus (Mult a Zero) (Neg (Mult a Zero)) ~= Plus (Plus (Mult a Zero) (Mult a Zero)) (Neg (Mult a Zero))) = ?MzeroAbsorbant_4 in -- By adding (Neg (Mult a Zero)) on Right and Left of the equality p3
	let p5 : (Plus (Mult a Zero) (Neg (Mult a Zero)) ~= Plus (Mult a Zero) (Plus (Mult a Zero) (Neg (Mult a Zero)))) = ?MzeroAbsorbant_5 in -- By using assoc on the Right side of p4
	let p6 : (Plus (Mult a Zero) (Neg (Mult a Zero)) ~= Plus (Mult a Zero) Zero) = ?MzeroAbsorbant_6 in -- By simplifying opposite terms on the Right of p5
	let p7 : (Plus (Mult a Zero) (Neg (Mult a Zero)) ~= (Mult a Zero)) = ?MzeroAbsorbant_7 in -- By simplifying the add zero on the Right of p6
	let p8 : (Zero ~= Mult a Zero) = ?MzeroAbsorbant_8 in -- By simplifying oppposite terms on the left of p7
		?MzeroAbsorbant_9

zeroAbsorbant2 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (Mult Zero a ~= Zero)
zeroAbsorbant2 C p a = 
	let p1 : (Mult Zero a ~= Mult (Plus Zero Zero) a) = ?MzeroAbsorbant2_1 in
	let p2 : (Mult (Plus Zero Zero) a ~= Plus (Mult Zero a) (Mult Zero a)) = ?MzeroAbsorbant2_2 in
	let p3 : (Mult Zero a ~= Plus (Mult Zero a) (Mult Zero a)) = ?MzeroAbsorbant2_3 in
	let p4 : (Plus (Mult Zero a) (Neg (Mult Zero a)) ~= Plus (Plus (Mult Zero a) (Mult Zero a)) (Neg (Mult Zero a))) = ?MzeroAbsorbant2_4 in -- By adding (Neg (Mult Zero a)) on Right and Left of the equality p3
	let p5 : (Plus (Mult Zero a) (Neg (Mult Zero a)) ~= Plus (Mult Zero a) (Plus (Mult Zero a) (Neg (Mult Zero a)))) = ?MzeroAbsorbant2_5 in -- By using assoc on the Right side of p4
	let p6 : (Plus (Mult Zero a) (Neg (Mult Zero a)) ~= Plus (Mult Zero a) Zero) = ?MzeroAbsorbant2_6 in -- By simplifying opposite terms on the Right of p5
	let p7 : (Plus (Mult Zero a) (Neg (Mult Zero a)) ~= (Mult Zero a)) = ?MzeroAbsorbant2_7 in -- By simplifying the add zero on the Right of p6
	let p8 : (Zero ~= Mult Zero a) = ?MzeroAbsorbant2_8 in -- By simplifying oppposite terms on the left of p7
		?MzeroAbsorbant2_9
		
-- Moves the Neg in front of the product when the Neg was on the second argument
lemmaRing1 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (b:C) -> (Mult a (Neg b) ~= Neg (Mult a b))
lemmaRing1 C p a b =
	let p1 : (Plus (Mult a (Neg b)) (Mult a b) ~= Mult a (Plus (Neg b) b)) = ?MlemmaRing1_1 in
	let p2 : (Mult a (Plus (Neg b) b) ~= Mult a Zero) = ?MlemmaRing1_2 in
	let p3 : (Mult a Zero ~= Zero) = zeroAbsorbant C p a in
	let p4 : (Plus (Mult a (Neg b)) (Mult a b) ~= Zero) = ?MlemmaRing1_3 in
	let p5 : ((Mult a (Neg b)) ~= Plus Zero (Neg (Mult a b))) = move_other_side (%instance) (Mult a (Neg b)) (Mult a b) Zero p4 in
	let p6 : (Plus Zero (Neg (Mult a b)) ~= (Neg (Mult a b))) = ?MlemmaRing1_4 in
		?MlemmaRing1_5

-- Moves the Neg in front of the producti when the Neg was on the first argument
lemmaRing2 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (b:C) -> (Mult (Neg a) b ~= Neg (Mult a b))
lemmaRing2 C p a b = 
	let p1 : (Plus (Mult (Neg a) b) (Mult a b) ~= Mult (Plus (Neg a) a) b) = ?MlemmaRing2_1 in -- Use distributivity 
	let p2 : (Mult (Plus (Neg a) a) b ~= Mult Zero b) = ?MlemmaRing2_2 in -- Use symmetric elements of +
	let p3 : (Mult Zero b ~= Zero) = zeroAbsorbant2 C p b in
	let p4 : (Plus (Mult (Neg a) b) (Mult a b) ~= Zero) = ?MlemmaRing2_3 in -- Transitivity of the aboves
	let p5 : (Mult (Neg a) b ~= Plus Zero (Neg (Mult a b))) = move_other_side (%instance) (Mult (Neg a) b) (Mult a b) Zero p4 in -- Use move other side
		?MlemmaRing2_4

-- --------------------
subgoal1 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (Mult a (Neg One) ~= Neg a)
subgoal1 C p a = 
	let p1 : (Mult a One ~= a) = ?Msubgoal1_1 in
		?Msubgoal1_2

subgoal2 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (Mult (Neg One) a ~= Neg a)
subgoal2 C p a = 
	let p1 : (Mult One a ~= a) = ?Msubgoal2_1 in
		?Msubgoal2_2
-- --------------------
		
-- Moves the Neg from the second argument of the Mult to the first argument
-- A more directly would have been to directly use lemmaRing1 and lemmaRing2 since they both have the same right hand side
lemmaRing3 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (b:C) -> (Mult a (Neg b) ~= Mult (Neg a) b)
lemmaRing3 _ _ a b = 
	let p1 : (Neg b ~= Mult (Neg One) b) = ?MlemmaRing3_1 in -- Use lemma subgoal2
	let p2 : (Mult a (Mult (Neg One) b) ~= Mult (Mult a (Neg One)) b) = ?MlemmaRing3_2 in -- Use assoc of *
	let p3 : (Mult a (Neg One) ~= Neg a) = ?MlemmaRing3_3 in -- Use lemma subgoal1
		?MlemmaRing3_4


lemmaRing4 : (C:Type) -> (dataTypes.Ring C) -> (a:C) -> (b:C) -> (Mult (Neg a) (Neg b) ~= Mult a b)
lemmaRing4 C p a b = 
	let p1 : (Mult (Neg a) (Neg b) ~= Neg (Mult a (Neg b))) = lemmaRing2 C p a (Neg b) in
	let p2 : (Mult a (Neg b) ~= Neg (Mult a b)) = ?MKKK in -- Uses lemmaRing3 
	let p3 : (Mult (Neg a) (Neg b) ~= Neg (Neg (Mult a b))) = ?MLLL in --compose p1 and p2
	let p4 : (Mult (Neg a) (Neg b) ~= Mult a b) = ?MMMM in -- Uses remove double neg
		?MNNN
		
-- -----------------------------------
-- C) TOOLS AND LEMMAS FOR STRUCTURES
-- -----------------------------------

-- C.1) For SemiGroup

semiGroupAssoc_4terms_Aux1 : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus (Plus c1 c2) c3) c4 ~= Plus (Plus c1 c2) (Plus c3 c4))
semiGroupAssoc_4terms_Aux1 C p c1 c2 c3 c4 = Plus_assoc {c=C} _ _ _

plusEqualLeft_SemiGroup : (C : Type) -> (SemiGroup C) -> (x:C) -> (x':C) -> (y:C) -> (prEqual:x~=x') -> (Plus x y ~= Plus x' y)
plusEqualLeft_SemiGroup C p x x' y prEqual = ?MplusEqualLeft_SemiGroup_1

semiGroupAssoc_4terms_Aux2 : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 ~= Plus (Plus (Plus c1 c2) c3) c4)
semiGroupAssoc_4terms_Aux2 = ?MsemiGroupAssoc_4terms_Aux2_1

semiGroupAssoc_4terms : (C : Type) -> (SemiGroup C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 ~= Plus (Plus c1 c2) (Plus c3 c4))
semiGroupAssoc_4terms C p c1 c2 c3 c4 = ?MsemiGroupAssoc_4terms_1

-- C.2) For Group

groupAssoc_4terms_Aux1 :  (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus (Plus c1 c2) c3) c4 ~= Plus (Plus c1 c2) (Plus c3 c4))
groupAssoc_4terms_Aux1 C p c1 c2 c3 c4 = Plus_assoc {c=C} _ _ _

plusEqualLeft_Group : (C : Type) -> (dataTypes.Group C) -> (x:C) -> (x':C) -> (y:C) -> (prEqual:x~=x') -> (Plus x y ~= Plus x' y)
plusEqualLeft_Group C p x x' y prEqual = ?MplusEqualLeft_Group_1 

groupAssoc_4terms_Aux2 : (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 ~= Plus (Plus (Plus c1 c2) c3) c4)
groupAssoc_4terms_Aux2 = ?MgroupAssoc_4terms_Aux2_1

groupAssoc_4terms : (C : Type) -> (dataTypes.Group C) -> (c1:C) -> (c2:C) -> (c3:C) -> (c4:C) -> (Plus (Plus c1 (Plus c2 c3)) c4 ~= Plus (Plus c1 c2) (Plus c3 c4))
groupAssoc_4terms C p c1 c2 c3 c4 = ?MgroupAssoc_4terms_1



-- -----------------------------------
-- D) ARITH TOOLS
-- -----------------------------------
-- D.1) Arith for Nat

lower_value : (x:Nat) -> (y:Nat) -> (LTE x y) -> LTE x (S y)
lower_value Z Z LTEZero = LTEZero
lower_value (S px) Z LTEZero impossible
lower_value (S px) (S py) (LTESucc p) = LTESucc (lower_value _ _ p)
lower_value Z (S py) p = LTEZero


bigger_value : (x:Nat) -> (y:Nat) -> (GTE x y) -> GTE (S x) y
bigger_value x y p = lower_value _ _ p


greater_than_succ : (x:Nat) -> (y:Nat) -> (GTE x (S y)) -> (GTE x y)
greater_than_succ (S px) Z (LTESucc p) = LTEZero
greater_than_succ (S px) (S py) (LTESucc p) = lower_value (S py) px p
                                                

S_both_side : (x:Nat) -> (y:Nat) -> (x=y) -> (S x = S y)
S_both_side x y P = ?M_S_both_side_1


using (A:Type, B:Type)
    data or : A -> B -> Type where
        Left : A -> or A B
        Right : B -> or A B

        
LTE_0_one_case : (n:Nat) -> (LTE n Z) -> (n=Z)
LTE_0_one_case Z LTEZero = Refl
LTE_0_one_case (S pn) (LTESucc p) impossible


-- (1 >= n) -> (n=0) or (n=1)     
GTE_1_two_cases : (n:Nat) -> (GTE (S Z) n) -> or (n=Z) (n=(S Z))
-- case 1>=0 (which is 0<=1 by def of >=)
GTE_1_two_cases Z (LTEZero {right=S Z}) = Left Refl
GTE_1_two_cases (S pn) (LTESucc n) = let pn_is_zero : (pn=Z) = ?M_GTE_1_two_cases_1 in
                                        ?M_GTE_1_two_cases_2

                                        
GTE_S : (a:Nat) -> (b:Nat) -> (GTE a b) -> (GTE (S a) (S b))
GTE_S a b p = LTESucc p 


LTE_same : (a:Nat) -> LTE a a
LTE_same Z = LTEZero
LTE_same (S pa) = LTESucc (LTE_same pa)


a_plus_zero : (a:Nat) -> (a+Z = a)
a_plus_zero Z = Refl
a_plus_zero (S pa) = S_both_side _ _ (a_plus_zero pa)


plus_succ_right : (a:Nat) -> (b:Nat) -> (S(a+b) = a + (S b))
plus_succ_right Z b = Refl
plus_succ_right (S pa) b = let auxP : (S(pa + b) = pa + (S b)) = plus_succ_right pa b in ?Mplus_succ_right_1


plus_succ_left : (a:Nat) -> (b:Nat) -> (S(a+b) = (S a) + b)
plus_succ_left Z b = Refl
plus_succ_left (S pa) b = Refl


GTE_plus : (a:Nat) -> (b:Nat) -> GTE (a+b) a
-- Proof by induction on a
GTE_plus a Z = let a_plus_zero_is_a : (a+Z = a) = a_plus_zero a in
                -- this is just (LTE_same a) but with a rewriting for the goal
                ?MGTE_plus_1
GTE_plus Z (S pb) = LTEZero
GTE_plus (S pa) (S pb) = LTESucc (GTE_plus pa (S pb))


GTE_deleteSucc : (a:Nat) -> (b:Nat) -> (GTE (S a) (S b)) -> GTE a b
-- This proof is just a case analysis and not a proof by induction (there's no recursive call)
GTE_deleteSucc Z Z p = LTEZero
--impossible but can't tag it as it : GTE_deleteSucc Z (S Z) LTEZero = ?M1
GTE_deleteSucc Z (S (S ppb)) (LTESucc LTEZero) impossible
GTE_deleteSucc Z (S (S ppb)) (LTESucc (LTESucc p)) impossible
GTE_deleteSucc Z (S pb) (LTESucc LTEZero) impossible
GTE_deleteSucc (S pa) Z p = LTEZero
--impossible but can't be tag as it : GTE_deleteSucc (S pa) (S pb) LTEZero = ?M1
GTE_deleteSucc (S pa) (S pb) (LTESucc p) = p


plus_one_equals_succ : (n:Nat) -> (n+1 = S n)
plus_one_equals_succ Z = Refl
plus_one_equals_succ (S pn) = let p_ihn : (pn + 1 = S pn) = plus_one_equals_succ pn in ?Mplus_one_equals_succ_1


moveSucc : (a:Nat) -> (b:Nat) -> (c:Nat) -> ((a+(S b))+c = ((a+b)+(S c)))
moveSucc Z Z Z = Refl
moveSucc Z Z (S pc) = Refl
moveSucc Z (S pb) Z = ?MmoveSucc_2
moveSucc Z (S pb) (S pc) = ?MmoveSucc_3
moveSucc (S pa) Z Z = ?MmoveSucc_4
moveSucc (S pa) Z (S pc) = ?MmoveSucc_5
moveSucc (S pa) (S pb) Z = ?MmoveSucc_6
moveSucc (S pa) (S pb) (S pc) = ?MmoveSucc_7


minusFirst : (x:Nat) -> (a:Nat) -> (b:Nat) -> (plusZ (Pos x) (minusNatZ a b) = minusNatZ (plus x a) b)
minusFirst Z Z Z = Refl
minusFirst Z Z (S pb) = Refl
minusFirst Z (S pa) Z = Refl
minusFirst Z (S pa) (S pc) = ?MminusFirst_1
minusFirst (S px) Z Z = Refl
minusFirst (S px) Z (S pb) = ?MminusFirst_2
minusFirst (S px) (S pa) Z = Refl
minusFirst (S px) (S pa) (S pc) = rewrite (sym(plus_succ_right px pa)) in (minusFirst (S px) pa pc)


plus_minus_succ : (a:Nat) -> (b:Nat) -> (c:Nat) -> minusNatZ (plus a (S b)) (S c) = minusNatZ (plus a b) c
plus_minus_succ Z Z Z = Refl
plus_minus_succ Z Z (S pc) = Refl
plus_minus_succ Z (S pb) Z = Refl
plus_minus_succ Z (S pb) (S pc) = Refl
plus_minus_succ (S pa) Z Z = ?Mplus_minus_succ_1
plus_minus_succ (S pa) Z (S pc) = (plus_minus_succ pa Z pc)
plus_minus_succ (S pa) (S pb) Z = ?Mplus_minus_succ_2
plus_minus_succ (S pa) (S pb) (S pc) = (plus_minus_succ pa (S pb) pc)


minusOne : (a:Nat) -> (b:Nat) -> (minusNatZ a (S b) = plusZ (minusNatZ a b) (NegS Z))
minusOne Z Z = Refl
minusOne Z (S pb) = ?MminusOne_1
minusOne (S pa) Z = Refl
minusOne (S pa) (S pb) = minusOne pa pb -- Recursive call here with strictly lower first and second arguments


minusSucc : (a:Nat) -> (b:Nat) -> (c:Nat) -> (minusNatZ a (plus b (S c)) = plusZ (minusNatZ a b) (NegS c))
minusSucc Z Z Z = Refl
minusSucc Z Z (S pc) = Refl
minusSucc Z (S pb) Z = ?MminusSucc_1
minusSucc Z (S pb) (S pc) = ?MminusSucc_2
minusSucc (S pa) Z Z = Refl
minusSucc (S pa) Z (S pc) = Refl
minusSucc (S pa) (S pb) Z = minusSucc pa pb Z
minusSucc (S pa) (S pb) (S pc) = (minusSucc pa pb (S pc)) -- Recursive call here with strictly lower first and second arguments


plusPos : (a:Nat) -> (b:Nat) -> (c:Nat) -> (minusNatZ (plus a b) c = plusZ (minusNatZ a c) (Pos b))
plusPos Z Z Z = Refl
plusPos Z Z (S pc) = Refl
plusPos Z (S pb) Z = Refl
plusPos Z (S pb) (S pc) = Refl
plusPos (S pa) Z Z = Refl
plusPos (S pa) Z (S pc) = (plusPos pa Z pc) -- Recursive call here with first and third arguments stricly lower
plusPos (S pa) (S pb) Z = Refl
plusPos (S pa) (S pb) (S pc) = (plusPos pa (S pb) pc) -- Recursive call here with first and third arguments stricly lower


minusNegS : (a:Nat) -> (b:Nat) -> (c:Nat) -> (plusZ (minusNatZ a (S b)) (NegS c) = plusZ (minusNatZ a b) (NegS (S c)))
minusNegS Z Z Z = Refl
minusNegS Z Z (S pc) = Refl
minusNegS Z (S pb) Z = ?MminusNegS_1
minusNegS Z (S pb) (S pc) = ?MminusNegS_2
minusNegS (S pa) Z Z = Refl
minusNegS (S pa) Z (S pc) = Refl
minusNegS (S pa) (S pb) Z = (minusNegS pa pb Z) -- Recursive call here with first and second arguments stricly lower
minusNegS (S pa) (S pb) (S pc) = (minusNegS pa pb (S pc)) -- Recursive call here with first and second arguments stricly lower


switch_negS : (a:Nat) -> (b:Nat) -> (c:Nat) -> plusZ (minusNatZ a b) (NegS c) = plusZ (minusNatZ a c) (NegS b)
switch_negS Z Z Z = Refl
switch_negS Z Z (S pc) = ?Mswitch_negS_1
switch_negS Z (S pb) Z = ?Mswitch_negS_2
switch_negS Z (S pb) (S pc) = ?Mswitch_negS_3
switch_negS (S pa) Z Z = Refl
switch_negS (S pa) Z (S pc) = ?Mswitch_negS_4
switch_negS (S pa) (S pb) Z = ?Mswitch_negS_5
switch_negS (S pa) (S pb) (S pc) = rewrite (sym (minusNegS pa pc pb)) in (switch_negS pa pb (S pc)) 


switch_double_succ : (a:Nat) -> (b:Nat) -> plus a (S (S b)) = plus b (S (S a))
switch_double_succ Z Z = Refl
switch_double_succ Z (S pb) = ?Mswitch_double_succ_1
switch_double_succ (S pa) Z = ?Mswitch_double_succ_2
switch_double_succ (S pa) (S pb) = let ih = switch_double_succ pa (S pb) in ?Mswitch_double_succ_3

-- D.2) Arith for Z

zero_plusZ_a : (a:ZZ) -> ((Pos Z) + a = a)
zero_plusZ_a (Pos x) = Refl
zero_plusZ_a (NegS x) = Refl

a_plusZ_zero : (a:ZZ) -> (a + (Pos Z) = a)
a_plusZ_zero (Pos x) = ?Ma_plusZ_zero_1
a_plusZ_zero (NegS x) = Refl


-- To add in the depository for Idris
plusAssociativeZ : (left : ZZ) -> (centre : ZZ) -> (right : ZZ) ->
  left + (centre + right) = (left + centre) + right
-- start with POS
-- Pos - Pos - Pos
plusAssociativeZ (Pos Z) (Pos Z) (Pos Z) = Refl
plusAssociativeZ (Pos Z) (Pos Z) (Pos (S pw)) = Refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (Pos Z) = Refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (Pos (S pw)) = Refl
plusAssociativeZ (Pos (S pu)) (Pos Z) (Pos Z) = ?MplusAssociativeZ_1_2 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (Pos (S pw)) = ?MplusAssociativeZ_1_3 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (Pos Z) = ?MplusAssociativeZ_1_4 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_1_5 --done

-- Pos - Pos - Neg
plusAssociativeZ (Pos Z) (Pos Z) (NegS Z) = Refl
plusAssociativeZ (Pos Z) (Pos Z) (NegS (S pw)) = Refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (NegS Z) = Refl
plusAssociativeZ (Pos Z) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_2_1 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (NegS Z) = ?MplusAssociativeZ_2_2 --done
plusAssociativeZ (Pos (S pu)) (Pos Z) (NegS (S pw)) = ?MplusAssociativeZ_2_3 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (NegS Z) = ?MplusAssociativeZ_2_4 --done
plusAssociativeZ (Pos (S pu)) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_2_5 --done

-- Pos - Neg - Pos
plusAssociativeZ (Pos Z) (NegS Z) (Pos Z) = Refl
plusAssociativeZ (Pos Z) (NegS Z) (Pos (S pw)) = Refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (Pos Z) = Refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_3_1 --done
plusAssociativeZ (Pos (S pu)) (NegS Z) (Pos Z) = ?MplusAssociativeZ_3_2 --done
plusAssociativeZ (Pos (S pu)) (NegS Z) (Pos (S pw)) = ?MplusAssociativeZ_3_3 --done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (Pos Z) = ?MplusAssociativeZ_3_4 --done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_3_5 -- done

-- Pos - Neg - Neg
plusAssociativeZ (Pos Z) (NegS Z) (NegS Z) = Refl
plusAssociativeZ (Pos Z) (NegS Z) (NegS (S pw)) = Refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (NegS Z) = Refl
plusAssociativeZ (Pos Z) (NegS (S pv)) (NegS (S pw)) = Refl
plusAssociativeZ (Pos (S pu)) (NegS Z) (NegS Z) = Refl
plusAssociativeZ (Pos (S pu)) (NegS Z) (NegS (S pw)) = Refl
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (NegS Z) = ?MplusAssociativeZ_4_4 -- done
plusAssociativeZ (Pos (S pu)) (NegS (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_4_5 --done

-- start with NEG
-- Neg - Pos - Pos
plusAssociativeZ (NegS Z) (Pos Z) (Pos Z) = Refl
plusAssociativeZ (NegS Z) (Pos Z) (Pos (S pw)) = Refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (Pos Z) = Refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (Pos (S pw)) = Refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (Pos Z) = Refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (Pos (S pw)) = Refl
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (Pos Z) = ?MplusAssociativeZ_5_4 --done
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_5_5 -- done

-- Neg - Pos - Neg
plusAssociativeZ (NegS Z) (Pos Z) (NegS Z) = Refl
plusAssociativeZ (NegS Z) (Pos Z) (NegS (S pw)) = Refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (NegS Z) = Refl
plusAssociativeZ (NegS Z) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_6_1 -- done
plusAssociativeZ (NegS (S pu)) (Pos Z) (NegS Z) = Refl
plusAssociativeZ (NegS (S pu)) (Pos Z) (NegS (S pw)) = Refl
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (NegS Z) = ?MplusAssociativeZ_6_4 -- done
plusAssociativeZ (NegS (S pu)) (Pos (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_6_5 -- done

-- Neg - Neg - Pos
plusAssociativeZ (NegS Z) (NegS Z) (Pos Z) = Refl
plusAssociativeZ (NegS Z) (NegS Z) (Pos (S pw)) = Refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (Pos Z) = Refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_7_1 -- done
plusAssociativeZ (NegS (S pu)) (NegS Z) (Pos Z) = Refl
plusAssociativeZ (NegS (S pu)) (NegS Z) (Pos (S pw)) = ?MplusAssociativeZ_7_3 --done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (Pos Z) = Refl
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (Pos (S pw)) = ?MplusAssociativeZ_7_5 -- done

-- Neg - Neg - Neg
plusAssociativeZ (NegS Z) (NegS Z) (NegS Z) = Refl
plusAssociativeZ (NegS Z) (NegS Z) (NegS (S pw)) = Refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (NegS Z) = Refl
plusAssociativeZ (NegS Z) (NegS (S pv)) (NegS (S pw)) = Refl
plusAssociativeZ (NegS (S pu)) (NegS Z) (NegS Z) = ?MplusAssociativeZ_8_2 -- done
plusAssociativeZ (NegS (S pu)) (NegS Z) (NegS (S pw)) = ?MplusAssociativeZ_8_3 -- done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (NegS Z) = ?MplusAssociativeZ_8_4 -- done
plusAssociativeZ (NegS (S pu)) (NegS (S pv)) (NegS (S pw)) = ?MplusAssociativeZ_8_5 --done



-- -----------------------------------
-- E) FIN TOOLS
-- -----------------------------------
minusOrEqual_Fin : {n:Nat} -> (i:Fin n) -> (j:Fin m) -> Bool
minusOrEqual_Fin FZ FZ = True
minusOrEqual_Fin FZ (FS j') = True
minusOrEqual_Fin (FS i') FZ = False
minusOrEqual_Fin (FS i') (FS j') = minusOrEqual_Fin i' j'

	
-- convert i from an element of Fin n to an element of Fin (S m), provided that (S m) is greater or equal to n
total
pre_convertFin : {n:Nat} -> (i:Fin n) -> (m:Nat) -> (p:GTE (S m) n) -> Fin (S m)
-- case  n=0, which mean 0<= Sm, but impossible because we're having an element of Fin 0
pre_convertFin {n=Z} (FZ) m (LTEZero) impossible
pre_convertFin {n=Z} (FS x) m _ impossible
-- case n= Sk, which includes two cases
  -- case FZ
pre_convertFin {n=S k} (FZ {k=k}) m p = FZ {k=m}
  -- case FS x, where x is an element of Fin k
pre_convertFin {n=S k} (FS x) (S pm) p = let m_gte_k : GTE (S pm) k = GTE_deleteSucc _ _ p in
											 let x_conv : Fin (S pm) = pre_convertFin x pm m_gte_k in
												FS x_conv
-- Impossible case : transforming an element of Fin (S k) into an element of (Fin 1), which forces k to be Zero, and then
-- there is only one element to convert : FZ {k=0}. But we're having an FS, and not an FZ...
pre_convertFin {n=S k} (FS x) Z p with (decEq k Z, decEq k (S Z))
    pre_convertFin {n=S k} (FS x) Z p | (Yes Refl, Yes Refl) impossible
    pre_convertFin {n=S k} (FS x) Z p | (Yes Refl, No p2) impossible
    pre_convertFin {n=S k} (FS x) Z p | (No p1, Yes Refl) impossible
    pre_convertFin {n=S k} (FS x) Z p | (No p1, No p2) = let k_is_zero_or_one : (or (k=Z) (k=S Z)) = GTE_1_two_cases k (greater_than_succ _ _ p) in
                                                            case k_is_zero_or_one of
                                                            Left k_is_zero => ?Mpre_convertFin_1
                                                            Right k_is_one => ?Mpre_convertFin_2

-- We know that we can use pre_convertFin because (n+x) is the successor of something (ie, can't be zero), because n
-- can't be zero (otherwise we would have an inhabitant of Fin 0)
convertFin : (n:Nat) -> (i:Fin n) -> (x:Nat) -> Fin (n+x)
-- n can't be zero
convertFin Z FZ x impossible
convertFin Z (FS pi) x impossible
convertFin (S pn) i x = let proofGTE : (GTE (S(pn+x)) (S pn)) = ?MconvertFin_1 in
                        pre_convertFin i (pn+x) proofGTE



testconversion1 : Fin 6
testconversion1 = pre_convertFin {n=3} (FZ {k=2}) 5 (LTESucc (LTESucc (LTESucc LTEZero)))
-- test ok

testconversion2 : Fin 6
testconversion2 = pre_convertFin {n=3} (FS (FZ {k=1})) 5 (LTESucc (LTESucc (LTESucc LTEZero)))
-- test ok

-- Computes the next element of a given element in a set of n element. If the
-- current element is already the last one of the set, we return it back.
nextElement : (n:Nat) -> (i:Fin n) -> Fin n
-- n can't be zero
nextElement Z FZ impossible
nextElement Z (FS pi) impossible
-- case where this is a FZ, and we've not yet reached the final element of the set
nextElement (S (S ppn)) (FZ {k=S ppn}) = FS (FZ {k=ppn})
-- case where this is a FZ, and we've reached the final element of the set. We give back the same FZ. This enables to always loop on the last element of a set if we ask for the next element.
nextElement (S Z) (FZ {k=Z}) = FZ {k=Z}
-- case where this is a (FS pi).
nextElement (S pn) (FS {k=pn} pi) = FS (nextElement pn pi)


lastElement : (pn:Nat) -> Fin (S pn)
lastElement Z = FZ
lastElement (S ppn) = FS (lastElement ppn)

lastElement' : (pn:Nat) -> Fin(pn+1)
lastElement' pn = let pn_plus_1_equals_Spn : (pn+1 = S pn) = plus_one_equals_succ pn in
                    -- This is just a call to the other function lastElement with the argument pn, but with a rewriting of the goal
                    ?MlastElement'_1

-- -----------------------------------
-- F) VECTOR TOOLS
-- -----------------------------------

{- Not needed now
--changeIeme : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (Vect n A)

--changeIeme_correct : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (a = index i (changeIeme g i a))
-}

-- F.1) index and reverse

-- No longer needed !
{-
lastElement_of_reverse_is_first' : (g : Vect (S pn) a) -> (index (FZ {k=pn}) g = index (lastElement pn) (reverse g))
lastElement_of_reverse_is_first' (h::Nil) = Refl
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
vectorAppend_assoc Nil Nil Nil = Refl
vectorAppend_assoc Nil Nil (h3::t3) = Refl
vectorAppend_assoc Nil (h2::t2) Nil = Refl
vectorAppend_assoc Nil (h2::t2) (h3::t3) = Refl
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

-- No longer needed !
{-
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




concat_SubSet : {c:Type} -> {n:Nat} -> {m:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (SubSet g1 (g2++g1))
concat_SubSet Nil Nil = SubSet_same _
concat_SubSet (h1::t1) Nil = SubSet_same _
concat_SubSet g1 (h2::t2) = let ih:SubSet g1 (t2++g1) = concat_SubSet g1 t2 in SubSet_add h2 _ _ ih

  
-- No longer needed !
-- Says that if g2 is a "superset" of g1, then the first element are the same
postulate -- Will be proven later
	indexReverse_of_convert : {c:Type} -> {n:Nat} -> (g1:Vect n c) -> (i:Fin n) -> {m:Nat} -> (g2:Vect (S m) c) -> (p: GTE (S m) n) -> (SubSet g1 g2) -> (index i g1 = index (pre_convertFin i m p) g2)
	
	
-- Subset and equality
SubSet_rewriteRight : {c:Type} -> {n:Nat} -> {m:Nat} -> {p:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (g3:Vect p c) -> (SubSet g1 g2) -> (g2=g3) -> (SubSet g1 g3)
SubSet_rewriteRight g1 g2 g2 psub Refl = psub -- ?MSubSet_rewriteRight_1
-}


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
vect_eq a_eq _ _ Nil Nil = Just Refl
vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) with (decEq pn pm)
	vect_eq a_eq (S pn) (S pn) (h1::t1) (h2::t2) | (Yes Refl) with (a_eq h1 h2, vect_eq a_eq pn pn t1 t2)
		vect_eq a_eq _ _ (h1::t1) (h1::t1) | (Yes Refl) | (Just Refl, Just Refl) = Just Refl
		vect_eq a_eq _ _ (h1::t1) _ | (Yes Refl) | _ = Nothing
	vect_eq a_eq (S pn) (S pm) (h1::t1) (h2::t2) | (No _) = Nothing
vect_eq a_eq _ _ _ _ = Nothing
-}

---------- Proofs ----------  
-- Part A) : Pairs, dependent pairs, and functions

Provers.tools.Mf_equal = proof
  intros
  rewrite p
  exact Refl
  
  
-- Part B) : Groups

-- B.1/ This subpart is to obtain the lemma "group_doubleNeg" : - (-a) = a


Provers.tools.MGroup_unicity_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus b (Plus a c))
  exact (Plus (Plus b a) c)
  exact (set_eq_undec_sym {c=C} (add_zero_right _ (Plus a c) b (left p2)))
  exact (set_eq_undec_sym {c=C} (add_zero_left _ (Plus b a) c (right p1)))
  exact (set_eq_undec_sym {c=C} a1)

Provers.tools.MGroup_unicity_2 = proof
  intros
  mrefine Plus_assoc  
  
Provers.tools.MhasSymmetric_sym = proof
  intro
  intro
  intro
  intro
  intro H
  exact (right H, left H)  
  
Provers.tools.Mplus_inverse_2 = proof
  intros
  mrefine hasSymmetric_sym
  mrefine Plus_inverse  

Provers.tools.Mgroup_doubleNeg1 = proof
  intros
  exact (set_eq_undec_sym {c=C} (group_unicity_symmetric p (Neg a) a (Neg (Neg a)) a1 b))
  
Provers.tools.Mgroup_doubleNeg_2 = proof
  intros
  exact (right(Plus_inverse a), left(Plus_inverse a))
  
Provers.tools.Mgroup_doubleNeg_3 = proof
  intros
  exact (left (Plus_inverse (Neg a)), right(Plus_inverse (Neg a)))  

-- B.2/ This part is to obtain the lemma "push_negation" : -(a+b) = (-b) + (-a)
  
Provers.tools.Madding_preserves_equality_1 = proof
  intros
  exact (Plus_preserves_equiv {c=C} H (set_eq_undec_refl z))

{-  
Provers.tools.Madding_preserves_equality_left_1 = proof
  intros
  rewrite H
  mrefine Refl  
-}
  
Provers.tools.Mmove_other_side_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus x y) (Neg y))
  exact (Plus z (Neg y))
  exact (set_eq_undec_sym {c=C} aux2)
  exact (set_eq_undec_refl {c=C} (Plus z (Neg y)))
  exact aux
  
Provers.tools.Mmove_other_side_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus x Zero)
  exact x
  mrefine Plus_preserves_equiv 
  exact (set_eq_undec_refl x)
  exact (Plus_neutral_2 x)
  exact (set_eq_undec_refl x)
  exact (left (Plus_inverse y))

Provers.tools.Mmove_other_side_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact x
  exact (Plus x (Plus y (Neg y)))
  exact (set_eq_undec_refl {c=C} x)
  exact (set_eq_undec_sym {c=C} aux3)
  exact (set_eq_undec_sym {c=C} aux5)
  
Provers.tools.Mpush_negation_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg (Plus x y)) (Plus x y))
  exact (the C Zero)
  exact (set_eq_undec_sym {c=C} aux2)
  exact (set_eq_undec_refl {c=C} Zero)
  exact aux  
  
Provers.tools.Mpush_negation_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus Zero (Neg y))
  exact (Neg y)
  exact aux4
  exact (set_eq_undec_refl (Neg y))
  exact aux5
  
Provers.tools.Mpush_negation_3 = proof
  intros
  exact aux7  
     
Provers.tools.MplusEqualLeft_SemiGroup_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact prEqual 
  exact (set_eq_undec_refl {c=C} y) 

Provers.tools.MsemiGroupAssoc_4terms_Aux2_1 = proof
  intros
  mrefine plusEqualLeft_SemiGroup 
  exact (set_eq_undec_sym {c=C} (Plus_assoc c1 c2 c3))

Provers.tools.MsemiGroupAssoc_4terms_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus (Plus c1 c2) c3) c4)
  exact (Plus (Plus (Plus c1 c2) c3) c4)
  exact (semiGroupAssoc_4terms_Aux2 C p c1 c2 c3 c4)
  exact (set_eq_undec_sym {c=C} (semiGroupAssoc_4terms_Aux1 C p c1 c2 c3 c4))
  exact (set_eq_undec_refl {c=C} (Plus (Plus (Plus c1 c2) c3) c4))

Provers.tools.MplusEqualLeft_Group_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  exact prEqual 
  exact (set_eq_undec_refl y)

Provers.tools.MgroupAssoc_4terms_Aux2_1 = proof
  intros
  mrefine plusEqualLeft_Group 
  exact (set_eq_undec_sym {c=C} (Plus_assoc c1 c2 c3))

Provers.tools.MgroupAssoc_4terms_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Plus (Plus c1 c2) c3) c4)
  exact (Plus (Plus (Plus c1 c2) c3) c4)
  exact (groupAssoc_4terms_Aux2 C p c1 c2 c3 c4)
  exact (set_eq_undec_sym {c=C} (groupAssoc_4terms_Aux1 C p c1 c2 c3 c4))
  exact (set_eq_undec_refl {c=C} (Plus (Plus (Plus c1 c2) c3) c4))
  
{-
Provers.tools.aux1 = proof {
  compute;
  trivial;
}
-}

-- Part D : Arith tools

-- D.1) Arith for Nat

Provers.tools.M_S_both_side_1 = proof
  intros
  rewrite P
  mrefine Refl
  
Provers.tools.M_GTE_1_two_cases_1 = proof
  intro pn, p
  mrefine LTE_0_one_case 
  mrefine p
  
Provers.tools.M_GTE_1_two_cases_2 = proof
  intros
  mrefine Right
  mrefine S_both_side
  mrefine pn_is_zero 

Provers.tools.Mplus_succ_right_1 = proof
  intros
  rewrite auxP
  exact Refl

Provers.tools.MGTE_plus_1 = proof
  intros
  rewrite (sym a_plus_zero_is_a)
  mrefine LTE_same

Provers.tools.Mplus_one_equals_succ_1 = proof
  intros
  rewrite p_ihn 
  exact Refl
  
Provers.tools.MmoveSucc_2 = proof
  intros
  rewrite (plus_succ_right pb 0)
  exact Refl
  
Provers.tools.MmoveSucc_3 = proof
  intros
  rewrite (plus_succ_right pb (S pc))
  exact Refl
  
Provers.tools.MmoveSucc_4 = proof
  intros
  rewrite (sym (a_plus_zero (plus pa 1)))
  rewrite (sym (a_plus_zero pa))
  exact Refl

Provers.tools.MmoveSucc_5 = proof
  intros
  rewrite (plus_succ_right pa 0)
  rewrite (plus_succ_right (plus pa 0) (S pc))
  compute
  exact Refl  

Provers.tools.MmoveSucc_6 = proof
  intros
  rewrite (plus_succ_right pa (S pb))
  rewrite (plus_succ_right (plus pa (S pb)) 0)
  compute
  exact Refl
  
Provers.tools.MmoveSucc_7 = proof
  intros
  rewrite (plus_succ_right pa (S pb))
  rewrite (plus_succ_right (plus pa (S pb)) (S pc))
  compute
  exact Refl

Provers.tools.MminusFirst_1 = proof
  intros
  rewrite (sym(plusCommutativeZ (Pos Z) (minusNatZ pa pc))) 
  exact (plusZeroRightNeutralZ (minusNatZ pa pc))

Provers.tools.MminusFirst_2 = proof
  intros
  rewrite (a_plus_zero px)
  exact Refl
  
Provers.tools.Mplus_minus_succ_1 = proof
  intros
  rewrite (sym(plus_succ_right pa Z))
  exact Refl

Provers.tools.Mplus_minus_succ_2 = proof
  intros
  rewrite (sym(plus_succ_right pa (S pb)))
  exact Refl  

Provers.tools.MminusOne_1 = proof
  intros
  rewrite (a_plus_zero pb)
  exact Refl

Provers.tools.MminusSucc_1 = proof
  intros
  rewrite (sym(plus_succ_right pb Z))
  exact Refl
  
Provers.tools.MminusSucc_2 = proof
  intros
  rewrite (sym(plus_succ_right pb (S pc)))
  exact Refl

Provers.tools.MminusNegS_1 = proof
  intros
  rewrite (plus_succ_right pb Z)
  exact Refl
  
Provers.tools.MminusNegS_2 = proof
  intros
  rewrite (plus_succ_right pb (S pc))
  exact Refl

 

Provers.tools.Mswitch_negS_1 = proof
  intros
  rewrite (a_plus_zero pc)
  exact Refl

Provers.tools.Mswitch_negS_2 = proof
  intros
  rewrite (a_plus_zero pb)
  exact Refl

Provers.tools.Mswitch_negS_3 = proof
  intros
  rewrite (sym(plusCommutative pb (S pc)))
  rewrite (sym( plus_succ_right pc pb))
  exact Refl  

Provers.tools.Mswitch_negS_4 = proof
  intros
  rewrite (plus_one_equals_succ pc)
  rewrite (sym(minusSucc pa pc Z))
  exact Refl 

Provers.tools.Mswitch_negS_5 = proof
  intros
  rewrite (minusSucc pa pb Z)
  rewrite (plus_one_equals_succ pb)
  exact Refl  
  
Provers.tools.Mswitch_double_succ_1 = proof
  intros
  rewrite (plus_one_equals_succ pb)
  rewrite (plus_succ_right pb (S Z))
  exact Refl
  
Provers.tools.Mswitch_double_succ_2 = proof
  intros
  rewrite (plus_one_equals_succ pa)
  rewrite (plus_succ_right pa (S Z))
  exact Refl

Provers.tools.Mswitch_double_succ_3 = proof
  intros
  rewrite (plus_succ_right pb (S (S pa)))
  exact (f_equal (\x => S x) _ _ ih)  
  
-- D.2) Arith for Z

Provers.tools.Ma_plusZ_zero_1 = proof
  intros
  rewrite (a_plus_zero x)
  exact Refl
  
Provers.tools.MplusAssociativeZ_1_2 = proof
  intros
  rewrite (a_plus_zero (plus pu 0))
  exact Refl
  
Provers.tools.MplusAssociativeZ_1_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact Refl
  
Provers.tools.MplusAssociativeZ_1_4 = proof
  intros
  rewrite (sym (a_plus_zero (pv)))
  rewrite (sym (a_plus_zero (plus pu (S pv))))
  exact Refl
  
Provers.tools.MplusAssociativeZ_1_5 = proof
  intros
  rewrite (sym(plus_succ_right pv (S pw)))
  rewrite (sym (plusAssociative pu pv (S (S pw))))
  rewrite (moveSucc pu pv (S pw))
  exact Refl

Provers.tools.MplusAssociativeZ_2_1 = proof
  intros
  rewrite (zero_plusZ_a (minusNatZ pv (S pw)))
  exact Refl
  
Provers.tools.MplusAssociativeZ_2_2 = proof
  intros
  rewrite (a_plus_zero pu)
  exact Refl
  

Provers.tools.MplusAssociativeZ_2_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact Refl

Provers.tools.MplusAssociativeZ_2_4 = proof
  intros
  rewrite (plus_succ_right pu pv)
  exact Refl
  
Provers.tools.MplusAssociativeZ_2_5 = proof
  intros
  rewrite (sym(minusFirst (S pu) pv (S pw)))
  rewrite (sym(plus_minus_succ pu pv pw))
  exact Refl  

Provers.tools.MplusAssociativeZ_3_1 = proof
  intros
  rewrite (zero_plusZ_a (minusNatZ pw (S pv)))
  exact Refl

Provers.tools.MplusAssociativeZ_3_2 = proof
  intros
  rewrite (a_plus_zero pu)
  exact Refl

Provers.tools.MplusAssociativeZ_3_3 = proof
  intros
  rewrite (plus_succ_right pu pw)
  exact Refl

Provers.tools.MplusAssociativeZ_3_4 = proof
  intros
  rewrite (a_plusZ_zero (minusNatZ pu (S pv)))
  exact Refl
  
Provers.tools.MplusAssociativeZ_3_5 = proof
  intros
  rewrite (sym(minusFirst (S pu) pw (S pv)))
  rewrite (plus_minus_succ  pu pw pv)
  rewrite (sym(plusCommutativeZ (minusNatZ pu (S pv)) (Pos(S pw))))
  rewrite(sym(minusFirst (S pw) pu (S pv)))
  rewrite (sym(plus_minus_succ pu pw pv))
  rewrite (plusCommutative pw pu)
  exact Refl
  
Provers.tools.MplusAssociativeZ_4_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (sym(minusOne pu (S pv)))
  exact Refl

Provers.tools.MplusAssociativeZ_4_5 = proof
  intros
  rewrite (minusSucc pu (S pv) (S pw))
  rewrite (sym(plus_succ_right pv (S pw)))
  exact Refl

Provers.tools.MplusAssociativeZ_5_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (a_plusZ_zero (minusNatZ pv (S pu)))
  exact Refl

Provers.tools.MplusAssociativeZ_5_5 = proof
  intros
  rewrite (sym(plusPos pv (S pw) (S pu)))
  exact Refl
  
Provers.tools.MplusAssociativeZ_6_1 = proof
  intros
  rewrite (plusCommutativeZ (NegS Z) (minusNatZ pv (S pw)))
  rewrite (sym(plusCommutativeZ (NegS Z) (minusNatZ pv (S pw))))
  rewrite (minusOne pv (S pw))
  exact Refl
  
Provers.tools.MplusAssociativeZ_6_4 = proof
  intros
  rewrite (sym(minusOne pv (S pu)))
  exact Refl    

Provers.tools.MplusAssociativeZ_6_5 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS (S pu)) (minusNatZ pv (S pw))))
  rewrite (sym( switch_negS pv (S pw) (S pu)))
  exact Refl

Provers.tools.MplusAssociativeZ_7_1 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS Z) (minusNatZ pw (S pv))))
  rewrite (sym(switch_negS pw (S pv) Z))
  exact Refl

Provers.tools.MplusAssociativeZ_7_3 = proof
  intros
  rewrite (a_plus_zero pu)
  exact Refl
  
Provers.tools.MplusAssociativeZ_7_5 = proof
  intros
  rewrite (sym(plusCommutativeZ (NegS (S pu)) (minusNatZ pw (S pv))))
  rewrite (minusSucc pw (S pv) (S pu))
  rewrite (sym(plus_succ_right pu (S pv)))
  rewrite (switch_double_succ pv pu)
  exact Refl  

Provers.tools.MplusAssociativeZ_8_2 = proof
  intros
  rewrite (sym (a_plus_zero pu))
  rewrite (sym(plus_succ_right pu 0))
  exact Refl

Provers.tools.MplusAssociativeZ_8_3 = proof
  intros
  rewrite (sym(a_plus_zero pu))
  rewrite (sym(plus_succ_right pu (S pw)))
  exact Refl

Provers.tools.MplusAssociativeZ_8_4 = proof
  intros
  rewrite (sym(a_plus_zero pv))
  rewrite (plus_succ_right pu (S pv))
  rewrite (sym (a_plus_zero (plus pu (S pv))))
  exact Refl

Provers.tools.MplusAssociativeZ_8_5 = proof
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
  exact Refl

-- Part E : Fin tools

Provers.tools.Mpre_convertFin_1 = proof
  intros
  mrefine void -- is the eliminator of false, previously called FalseElim (which was a better name for the logical side :-( )
  mrefine p1
  mrefine k_is_zero

Provers.tools.Mpre_convertFin_2 = proof
  intros
  mrefine void
  mrefine p2
  mrefine k_is_one

Provers.tools.MconvertFin_1 = proof
  intros
  mrefine GTE_S
  mrefine GTE_plus

Provers.tools.MlastElement'_1 = proof
  intros
  rewrite pn_plus_1_equals_Spn 
  rewrite (sym pn_plus_1_equals_Spn)
  exact (lastElement pn)
  
-- Part F : Vector tools



-- -------- Part for Rings -------------
Provers.tools.MzeroAbsorbant_1 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine Plus_neutral_1

Provers.tools.MzeroAbsorbant_2 = proof
  intros
  mrefine Mult_dist

Provers.tools.MzeroAbsorbant_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult a Zero)
  exact (Mult a (Plus Zero Zero))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p1
  exact p2

Provers.tools.MzeroAbsorbant_4 = proof
  intros
  mrefine adding_preserves_equality 
  exact p3

Provers.tools.MzeroAbsorbant_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult a Zero) (Neg (Mult a Zero)))
  exact (Plus (Plus (Mult a Zero) (Mult a Zero)) (Neg (Mult a Zero)))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p4
  mrefine Plus_assoc 

Provers.tools.MzeroAbsorbant_6 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult a Zero) (Neg (Mult a Zero)))
  exact (Plus (Mult a Zero) (Plus (Mult a Zero) (Neg (Mult a Zero))))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact p5
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine left
  exact (Plus (Neg (Mult a Zero)) (Mult a Zero) ~= Zero)
  mrefine Plus_inverse 

Provers.tools.MzeroAbsorbant_7 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult a Zero) (Neg (Mult a Zero)))
  exact (Plus (Mult a Zero) Zero)
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p6
  mrefine Plus_neutral_2

Provers.tools.MzeroAbsorbant_8 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult a Zero) (Neg (Mult a Zero)))
  exact (Mult a Zero)
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p7
  mrefine left
  exact (Plus (Neg (Mult a Zero)) (Mult a Zero) ~= Zero)
  mrefine Plus_inverse 

Provers.tools.MzeroAbsorbant_9 = proof
  intros
  mrefine set_eq_undec_sym 
  exact p8
  
-- ----------------------------- 
Provers.tools.MzeroAbsorbant2_1 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  mrefine Plus_neutral_1
  
Provers.tools.MzeroAbsorbant2_2 = proof
  intros
  mrefine Mult_dist_2  

Provers.tools.MzeroAbsorbant2_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Plus Zero Zero) a)
  exact (Mult (Plus Zero Zero) a)
  exact p1
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact p2  
  
Provers.tools.MzeroAbsorbant2_4 = proof
  intros
  mrefine adding_preserves_equality 
  exact p3  
  
Provers.tools.MzeroAbsorbant2_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult Zero a) (Neg(Mult Zero a)))
  exact (Plus (Plus (Mult Zero a) (Mult Zero a)) (Neg (Mult Zero a)))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p4
  mrefine Plus_assoc  
  
Provers.tools.MzeroAbsorbant2_6 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult Zero a) (Neg (Mult Zero a)))
  exact (Plus (Mult Zero a) (Plus (Mult Zero a) (Neg (Mult Zero a))))
  mrefine set_eq_undec_refl 
  mrefine Plus_preserves_equiv 
  exact p5
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine left
  exact (Plus (Neg (Mult Zero a)) (Mult Zero a) ~= Zero)
  mrefine Plus_inverse
  
Provers.tools.MzeroAbsorbant2_7 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult Zero a) (Neg (Mult Zero a)))
  exact (Plus (Mult Zero a) Zero)
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  exact p6
  mrefine Plus_neutral_2
  
Provers.tools.MzeroAbsorbant2_8 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult Zero a) (Neg (Mult Zero a)))
  exact (Mult Zero a)
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl 
  exact p7
  mrefine left
  exact (Plus (Neg (Mult Zero a)) (Mult Zero a) ~= Zero)
  mrefine Plus_inverse 
  
Provers.tools.MzeroAbsorbant2_9 = proof
  intros
  mrefine set_eq_undec_sym 
  exact p8

-- -----------------------------  
Provers.tools.MlemmaRing1_1 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_dist

Provers.tools.MlemmaRing1_2 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  mrefine right
  exact (Plus b (Neg b) ~= Zero)
  mrefine Plus_inverse
  
Provers.tools.MlemmaRing1_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Mult a (Neg b)) (Mult a b))
  exact (Mult a Zero)
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  mrefine eq_preserves_eq 
  exact p3
  exact (Plus (Mult a (Neg b)) (Mult a b))
  exact (Mult a (Plus (Neg b) b))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p1
  exact p2  

Provers.tools.MlemmaRing1_4 = proof
  intros
  mrefine Plus_neutral_1

Provers.tools.MlemmaRing1_5 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult a (Neg b))
  exact (Plus Zero (Neg (Mult a b)))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p5
  exact p6

-- ----------------------------- 
Provers.tools.MlemmaRing2_1 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_dist_2
 
Provers.tools.MlemmaRing2_2 = proof
  intros
  mrefine Mult_preserves_equiv 
  mrefine right
  mrefine set_eq_undec_refl 
  exact (Plus a (Neg a) ~= Zero)
  mrefine Plus_inverse  
  
Provers.tools.MlemmaRing2_3 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Plus (Neg a) a) b)
  exact (Mult (Plus (Neg a) a) b)
  exact p1
  mrefine eq_preserves_eq
  mrefine set_eq_undec_refl 
  exact (Mult Zero b)
  exact (Mult Zero b)
  mrefine set_eq_undec_sym 
  exact p2
  mrefine set_eq_undec_refl 
  exact p3  
  
Provers.tools.MlemmaRing2_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Neg a) b)
  exact (Plus Zero (Neg (Mult a b)))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact p5
  mrefine Plus_neutral_1
  
-- -----------------------------  
Provers.tools.Msubgoal1_1 = proof
  intros
  mrefine left
  exact (Mult One a ~= a)
  mrefine Mult_neutral 

Provers.tools.Msubgoal1_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult a (Neg One))
  exact (Neg (Mult a One))
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  mrefine lemmaRing1 
  mrefine set_eq_undec_sym 
  exact p1  

Provers.tools.Msubgoal2_1 = proof
  intros
  mrefine right
  exact (Mult a One ~= a)
  mrefine Mult_neutral   
  
Provers.tools.Msubgoal2_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult (Neg One) a)
  exact (Neg (Mult One a))
  mrefine set_eq_undec_refl 
  mrefine Neg_preserves_equiv 
  mrefine lemmaRing2
  mrefine set_eq_undec_sym 
  exact p1  
  
-- -----------------------------
Provers.tools.MlemmaRing3_1 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine subgoal2

Provers.tools.MlemmaRing3_2 = proof
  intros
  mrefine set_eq_undec_sym 
  mrefine Mult_assoc 

Provers.tools.MlemmaRing3_3 = proof
  intros
  mrefine subgoal1 

Provers.tools.MlemmaRing3_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Mult a (Mult (Neg One) b))
  exact (Mult (Mult a (Neg One)) b)
  mrefine Mult_preserves_equiv 
  mrefine Mult_preserves_equiv 
  exact p2
  mrefine set_eq_undec_refl 
  exact p1
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_refl
  exact p3


