module NewAutoAssoc_tools

import Decidable.Equality
import Data.Fin
import Data.Vect

%default total


leftDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> A
leftDep (a ** b) = a

rightDep : {A:Type} -> {B:A->Type} -> (x : Sigma A B) -> B (leftDep x)
rightDep (a ** b) = b


lower_value : (x:Nat) -> (y:Nat) -> (LTE x y) -> LTE x (S y)
lower_value Z Z LTEZero = LTEZero
lower_value (S px) Z LTEZero impossible
lower_value (S px) (S py) (LTESucc p) = LTESucc (lower_value _ _ p)
lower_value Z (S py) p = LTEZero

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

a_plus_zero : (a:Nat) -> (a+Z = a)
a_plus_zero Z = Refl
a_plus_zero (S pa) = S_both_side _ _ (a_plus_zero pa)
                                        
                                        
GTE_S : (a:Nat) -> (b:Nat) -> (GTE a b) -> (GTE (S a) (S b))
GTE_S a b p = LTESucc p                                         
        
        
LTE_same : (a:Nat) -> LTE a a
LTE_same Z = LTEZero
LTE_same (S pa) = LTESucc (LTE_same pa)        
        
        
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



pre_convertFin_proofIrr : {n:Nat} -> (i:Fin n) -> (m:Nat) -> (p1:GTE (S m) n) -> (p2:GTE (S m) n) -> (pre_convertFin i m p1 = pre_convertFin i m p2)
pre_convertFin_proofIrr FZ m p1 p2 = Refl
pre_convertFin_proofIrr (FS pi) m p1 p2 = 
	-- Huuum... Recursive call ? How ?
	 ?Mpre_convertFin_proofIrr_1
	 
	 
elimFinZero : (x:Fin Z) -> Void
elimFinZero FZ impossible
elimFinZero (FS y) impossible 
	 
	 
-- for all vector v, if the ith element of v is elem, then the (i+1)th element of any vector with one more element on the left is still elem	 
elemInBigerVect : {T:Type} -> {v : Vect n T} -> (i:Fin n) -> (elem:T) -> (proofInside : index i v = elem) -> (head:T) -> (index (FS i) (head::v) = elem) 
elemInBigerVect fZ elem proofInside = ?MelemInBigerVect_1 -- why I can't just give proofInside here and need to do it in proof mode ?
elemInBigerVect (FS i') elem proofInside = ?MelemInBigerVect_2
	 

lastElement : (pn:Nat) -> Fin (S pn)
lastElement Z = FZ
lastElement (S ppn) = FS (lastElement ppn)

lastElement' : (pn:Nat) -> Fin(pn+1)
lastElement' pn = let pn_plus_1_equals_Spn : (pn+1 = S pn) = plus_one_equals_succ pn in
                    -- This is just a call to the other function lastElement with the argument pn, but with a rewriting of the goal
                    rewrite pn_plus_1_equals_Spn in lastElement pn -- Fix Idris here : if I do EXACTLY the same in proof mode, then when proving the 
								   -- matavariable MlastElement_defEquiv_1 from the next definition, the definition of lastElement' doesn't unfold well
								   -- (see previous def of lastElement' in proof mode on the github history)
     
lastElement_defEquiv : (pn:Nat) -> (lastElement pn = lastElement' pn)     
lastElement_defEquiv Z = Refl
lastElement_defEquiv (S pn) = ?MlastElement_defEquiv_2
     
indexOfLastElem : {T:Type} -> {n:Nat} -> (v:Vect n T) -> (x:T) -> index (lastElement' n) (v++[x]) = x 	 
indexOfLastElem [] x = ?MindexOfLastElem_1 -- What the hell, I can't give Refl directly here, I need to do it in proof mode...
indexOfLastElem (vh::vt) x = let paux = indexOfLastElem vt x in ?MindexOfLastElem_2 -- Will use elemInBigerVect and the induction hypothesis paux

	 
f_equal : {A:Type} -> {B:Type} -> (f:A->B) -> (x:A) -> (y:A) -> (x=y) -> (f x = f y)
f_equal f x y p = ?Mf_equal	 

f_equal_threeArgs : {A:Type} -> {B:Type} -> {C:Type} -> {D:Type} -> (f:A -> B -> C -> D) -> 
		    (x1:A) -> (y1:A) -> (x2:B) -> (y2:B) -> (x3:C) -> (y3:C) ->
		    (x1=y1) -> (x2=y2) -> (x3=y3) -> 
		    (f x1 x2 x3 = f y1 y2 y3)
f_equal_threeArgs f x1 y1 x2 y2 x3 y3 p1 p2 p3 = ?Mf_equal_threeArgs_1 

	 
appendSingleton : {T:Type} -> (x:T) -> (xs:List T) -> ([x]++xs = x::xs)
appendSingleton x [] = Refl
appendSingleton x (xsh::xst) = Refl
	 	 
	 
	 
-- Proofs	 
	 
-- new bits
NewAutoAssoc_tools.M_S_both_side_1 = proof
  intros
  rewrite P
  mrefine Refl

NewAutoAssoc_tools.M_GTE_1_two_cases_1 = proof
  intro pn, p
  mrefine LTE_0_one_case 
  mrefine p
  
NewAutoAssoc_tools.M_GTE_1_two_cases_2 = proof
  intros
  mrefine Right
  mrefine S_both_side
  mrefine pn_is_zero 
  
NewAutoAssoc_tools.MGTE_plus_1 = proof
  intros
  rewrite (sym a_plus_zero_is_a)
  mrefine LTE_same
  
NewAutoAssoc_tools.Mplus_one_equals_succ_1 = proof
  intros
  rewrite p_ihn 
  exact Refl  
  
NewAutoAssoc_tools.Mpre_convertFin_1 = proof
  intros
  mrefine void -- is the eliminator of false, previously called FalseElim (which was a better name for the logical side :-( )
  mrefine p1
  mrefine k_is_zero

NewAutoAssoc_tools.Mpre_convertFin_2 = proof
  intros
  mrefine void
  mrefine p2
  mrefine k_is_one

NewAutoAssoc_tools.MconvertFin_1 = proof
  intros
  mrefine GTE_S
  mrefine GTE_plus
  
NewAutoAssoc_tools.MindexOfLastElem_1 = proof
  intros
  exact Refl  
  
NewAutoAssoc_tools.MelemInBigerVect_1 = proof
  intros
  exact proofInside 
  
NewAutoAssoc_tools.MelemInBigerVect_2 = proof
  intros
  exact proofInside 

NewAutoAssoc_tools.Mf_equal = proof
  intros
  rewrite p
  exact Refl
  
NewAutoAssoc_tools.Mf_equal_threeArgs_1 = proof
  intros
  rewrite p1
  rewrite p2 
  rewrite p3
  exact Refl
  
  
  
  