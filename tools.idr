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

leftDep : {A:Type} -> {B:A->Type} -> (x : Exists A B) -> A
leftDep (a ** b) = a

rightDep : {A:Type} -> {B:A->Type} -> (x:Exists A B) -> B (leftDep x)
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

-- To add in the depository for Idris
postulate
plusAssociativeZ : (left : ZZ) -> (centre : ZZ) -> (right : ZZ) ->
  left + (centre + right) = (left + centre) + right
{-
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
    

-- -----------------------------------
-- C) ARITH TOOLS
-- -----------------------------------
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

-- -----------------------------------
-- D) FIN TOOLS
-- -----------------------------------

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
-- E) VECTOR TOOLS
-- -----------------------------------

{- Not needed now
--changeIeme : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (Vect n A)

--changeIeme_correct : {A:Type} -> {n:Nat} -> (g:Vect n A) -> (i:Fin n) -> (a:A) -> (a = index_reverse i (changeIeme g i a))
-}

-- E.1) index and reverse

postulate -- Will be proven later
    lastElement_of_reverse_is_first : (g : Vect (S pn) a) -> ((head g = index (lastElement pn) (reverse g)))

-- E.2) Append

vectorAppendNil : (c:Type) -> (n:Nat) -> (g1:Vect n c) -> (g1 ++ Nil = g1)
vectorAppendNil c Z Nil = refl
vectorAppendNil c (S pn) (h::t) = 
	let paux : (pn + Z = pn) = a_plus_zero pn in -- Note : There is probably a bug in rewrite, since we can't rewrite (sym paux) to immediately prove the metavariable ?MvectorAppendNil_1. Why ?
	let paux2 : (Vect (pn+Z) c = Vect pn c) = ?MvectorAppendNil_1 in 
	let ih : (t++Nil = t) = vectorAppendNil c pn t in -- Induction hypothesis
		?MvectorAppendNil_2 -- Here I just want to rewrite (sym ih) in the current goal and then it's simply refl, and this rewriting should be doable since paux2 attests that the two types are convertible
    

vectorAppend_assoc : {c:Type} -> {n:Nat} -> {m:Nat} -> {p:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (g3:Vect p c) -> (g1++(g2++g3) = (g1 ++ g2)++g3)
vectorAppend_assoc Nil Nil Nil = refl
vectorAppend_assoc Nil Nil (h3::t3) = refl
vectorAppend_assoc Nil (h2::t2) Nil = refl
vectorAppend_assoc Nil (h2::t2) (h3::t3) = refl
vectorAppend_assoc (h1::t1) Nil Nil = let ih : (t1 ++ (Nil ++ Nil) = (t1 ++ Nil) ++ Nil) = vectorAppend_assoc t1 Nil Nil in ?MvectorAppend_assoc_1
vectorAppend_assoc (h1::t1) Nil (h3::t3) = ?MvectorAppend_assoc_2
vectorAppend_assoc (h1::t1) (h2::t2) Nil = ?MvectorAppend_assoc_3
vectorAppend_assoc (h1::t1) (h2::t2) (h3::t3) = ?MvectorAppend_assoc_4  


-- E.3) "Subsets"

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
    

postulate    
	SubSet_size : {c:Type} -> (n:Nat) -> (m:Nat) -> (g1:Vect n c) -> (g2:Vect m c) -> (SubSet g1 g2) -> (GTE m n)
    

concat_SubSet : {c:Type} -> {n:Nat} -> {m:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (SubSet g1 (g2++g1))
concat_SubSet Nil Nil = SubSet_same _
concat_SubSet (h1::t1) Nil = SubSet_same _
concat_SubSet g1 (h2::t2) = let ih:SubSet g1 (t2++g1) = concat_SubSet g1 t2 in SubSet_add h2 _ _ ih

    
-- Says that ig g2 is a "superset" of g1, then the first element are the same
postulate -- Will be proven later
	indexReverse_of_convert : {c:Type} -> {n:Nat} -> (g1:Vect n c) -> (i:Fin n) -> {m:Nat} -> (g2:Vect (S m) c) -> (p: GTE (S m) n) -> (SubSet g1 g2) -> (index_reverse i g1 = index_reverse (pre_convertFin i m p) g2)
	
	
-- Subset and equality
SubSet_rewriteRight : {c:Type} -> {n:Nat} -> {m:Nat} -> {p:Nat} -> (g1:Vect n c) -> (g2:Vect m c) -> (g3:Vect p c) -> (SubSet g1 g2) -> (g2=g3) -> (SubSet g1 g3)
SubSet_rewriteRight g1 g2 g3 psub peq = ?MSubSet_rewriteRight_1


-- E.4) Removing elements

-- Not needed now
{-
remove_first_x_elements : {a:Type} -> {n:Nat} -> (x:Nat) -> (Vect (x+n) a) -> (Vect n a)
remove_first_x_elements Z g = g
remove_first_x_elements (S px) (h::t) = remove_first_x_elements px t
remove_first_x_elements (S px) Nil impossible


remove_first_x_subset : {a:Type} -> {n:Nat} -> (x:Nat) -> (g:Vect (x+n) a) -> (SubSet (remove_first_x_elements x g) g)
remove_first_x_subset x g = ?Mremove_first_x_subset_1

-}

---------- Proofs ----------  
-- Part A) : Pairs, dependent pairs, and functions

tools.Mf_equal = proof
  intros
  rewrite p
  exact refl
  
  
-- Part B) : Groups

-- B.1/ This subpart is to obtain the lemma "group_doubleNeg" : - (-a) = a

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

-- Part C : Arith tools

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

-- Part D : Fin tools

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
  
-- Part E : Vector tools


