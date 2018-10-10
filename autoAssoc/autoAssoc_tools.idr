module autoAssoc_tools

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


LTE_deleteSucc : (a:Nat) -> (b:Nat) -> (LTE (S a) (S b)) -> LTE a b
-- This proof is just a case analysis and not a proof by induction (there's no recursive call)
LTE_deleteSucc Z Z p = LTEZero
LTE_deleteSucc Z (S pb) p = LTEZero
-- first argument is a Succ
LTE_deleteSucc (S pa) Z (LTESucc LTEZero) impossible
LTE_deleteSucc (S (S ppa)) Z (LTESucc LTEZero) impossible
LTE_deleteSucc (S (S ppa)) Z (LTESucc (LTESucc p)) impossible
LTE_deleteSucc (S pa) (S pb) (LTESucc p) = p


LTE_lower_than_zero : {x:Nat} -> (LTE x 0) -> (x=0)
LTE_lower_than_zero LTEZero = Refl
LTE_lower_than_zero (LTESucc n) impossible


Succ_LTE_1_one_case : (n:Nat) -> (LTE (S n) 1) -> (n=Z)
Succ_LTE_1_one_case Z pr = Refl
Succ_LTE_1_one_case (S pn) pr = 
      -- The absurd thing that we have in the context implies the absurd thing that we have to prove by using LTE (S a) (S b) -> LTE a b (to write)
     ?MSucc_LTE_1_one_case_1

     
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
GTE_deleteSucc a b p = LTE_deleteSucc b a p


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


elimFinZero : (x:Fin Z) -> Void
elimFinZero FZ impossible
elimFinZero (FS y) impossible 
	 

elimFinZero' : (n:Nat) -> (Fin n) -> (p:n=Z) -> Void
elimFinZero' n i p = ?MelimFinZero'_1


pre_convertFin_proofIrr : {n:Nat} -> (i:Fin n) -> (m:Nat) -> (p1:GTE (S m) n) -> (p2:GTE (S m) n) -> (pre_convertFin i m p1 = pre_convertFin i m p2)
pre_convertFin_proofIrr FZ m p1 p2 = Refl
pre_convertFin_proofIrr (FS pi) (S pm) p1 p2 = 
	 let ihn = pre_convertFin_proofIrr pi pm (GTE_deleteSucc (S pm) _ p1) (GTE_deleteSucc (S pm) _ p2) in
	 -- Fix Idris : in proof mode, I can't do a "mrefine f_equal". Instead, I have to do the "rewrite..." with everything. Why ? See the proof of Mpre_convertFin_proofIrr_1.
	 ?Mpre_convertFin_proofIrr_1    
pre_convertFin_proofIrr (FS pi) Z p1 p2 =
	 ?Mpre_convertFin_proofIrr_2	 
	 
	 
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
  
{-  
lastElement_defEquiv : (pn:Nat) -> (lastElement pn = lastElement' pn)     
lastElement_defEquiv Z = Refl
lastElement_defEquiv (S pn) = ?MlastElement_defEquiv_2
-}  
  
     


-- Hourray ! I can do it because I can pattern match p with (only) Refl
fin_replace : {n:Nat} -> {n':Nat} -> (i:Fin n) -> (eq:n=n') -> (replace eq i = i)
fin_replace i Refl = Refl

-- My trick : in order to be able to write the type (index (replace eq i) vect = index i vect), we already need to do a dependent pattern maching...
index_replace_type : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vect:Vect n T) -> (eq:n=n') -> Type
index_replace_type i vect eq with (eq)
  index_replace_type i vect eq | (Refl) = (index (replace eq i) vect = index i vect)

-- ... and thanks to this little trick, we can write the auxiliary lemma we need...
index_replace : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vect:Vect n T) -> (eq:n=n') -> (index_replace_type i vect eq)
index_replace i vect eq with (eq)
  index_replace i vect eq | (Refl) = Refl

  
trick_vect_size : {T:Type} -> {n:Nat} -> (vh:T) -> (vt:Vect n T) -> (x:T) -> (Vect (S (S n)) T) 
trick_vect_size vh vt x ?= vh::vt++[x]  
  
-- ... and this auxiliary lemma is going to be useful for proving the metavariable MindexOfLastElem_4 of this lemma
indexOfLastElem : {T:Type} -> {n:Nat} -> (v:Vect n T) -> (x:T) -> index (lastElement' n) (v++[x]) = x 	 
indexOfLastElem [] x = ?MindexOfLastElem_1 -- What the hell, I can't give Refl directly here, I need to do it in proof mode...
indexOfLastElem {n=S pn} (vh::vt) x = 
			     let paux = indexOfLastElem vt x in 
			     let paux2 : ((=) {A=Fin (S (pn+1))} {B=Fin (S (S pn))} (replace (sym (Mplus_one_equals_succ_1 pn (plus_one_equals_succ pn))) (FS (lastElement pn))) (FS (lastElement pn)) ) = ?MindexOfLastElem_2 in
			     let paux3 = index_replace (FS (lastElement pn)) (trick_vect_size vh vt x) (sym (Mplus_one_equals_succ_1 pn (plus_one_equals_succ pn))) in
			     ?MindexOfLastElem_4 -- Will use elemInBigerVect and the induction hypothesis called paux and paux2 or paux3
			     -- Damn, I can't do rewrite (index_replace (FS (lastElement pn)) (vh::vt++[x]) (sym (replace (plus_one_equals_succ pn) Refl)))
			     -- in order to start the proof of this metavariable. There's a problem with the type of index_replace which is not unfolded as it should be. Why ?
		
{-		     
indexOfLastElem : {T:Type} -> {n:Nat} -> (v:Vect n T) -> (x:T) -> index (lastElement' n) (v++[x]) = x 	 
indexOfLastElem [] x = ?MindexOfLastElem_1 -- What the hell, I can't give Refl directly here, I need to do it in proof mode...
indexOfLastElem {n=S pn} (vh::vt) x with (fin_replace (FS (lastElement pn)) (sym (replace (plus_one_equals_succ pn) Refl)))
  indexOfLastElem {n=S pn} (vh::vt) x | (Refl) = ?MXXY
  -} 
  
{-
  = let paux = indexOfLastElem vt x in 
			     -- let paux2 : (index (replace (sym (Mplus_one_equals_succ_1 n (plus_one_equals_succ n))) (FS (lastElement n))) = (FS (lastElement n))) = ?MindexOfLastElem_2 in
			     let paux2 : ((=) {A=Fin (S (pn+1))} {B=Fin (S (S pn))} (replace (sym (Mplus_one_equals_succ_1 pn (plus_one_equals_succ pn))) (FS (lastElement pn))) (FS (lastElement pn)) ) = ?MindexOfLastElem_2 in
			     -- let paux3 : (index (replace (sym (Mplus_one_equals_succ_1 pn (plus_one_equals_succ pn))) (FS (lastElement pn))) (vh::vt++[x]) = index (FS (lastElement pn)) (vh::vt++[x])) = ?MindexOfLastElem_3 in 
			     ?MindexOfLastElem_4 -- Will use elemInBigerVect and the induction hypothesis paux and rewrite_fin_element
			     -- rewrite (rewrite_fin_element (FS (lastElement _)) _ (sym (Mplus_one_equals_succ_1 _ (plus_one_equals_succ _)))) in Refl
			     -}			     
			     
			     

indexOfFS : {T:Type} -> {n:Nat} -> (i:Fin n) -> (vh:T) -> (vt:Vect n T) -> index (FS i) (vh::vt) = index i vt
indexOfFS FZ vh (vth::vtt) = Refl
indexOfFS (FS pi) vh (vth::vtt) = Refl


f_equal : {A:Type} -> {B:Type} -> (f:A->B) -> (x:A) -> (y:A) -> (x=y) -> (f x = f y)
f_equal f x y p = ?Mf_equal	 

f_equal_twoArgs : {A:Type} -> {B:Type} -> {C:Type} -> (f:A -> B -> C) -> 
		    (x1:A) -> (y1:A) -> (x2:B) -> (y2:B) ->
		    (x1=y1) -> (x2=y2) -> 
		    (f x1 x2 = f y1 y2)
f_equal_twoArgs f x1 y1 x2 y2 p1 p2 = ?Mf_equal_twoArgs_1 


f_equal_threeArgs : {A:Type} -> {B:Type} -> {C:Type} -> {D:Type} -> (f:A -> B -> C -> D) -> 
		    (x1:A) -> (y1:A) -> (x2:B) -> (y2:B) -> (x3:C) -> (y3:C) ->
		    (x1=y1) -> (x2=y2) -> (x3=y3) -> 
		    (f x1 x2 x3 = f y1 y2 y3)
f_equal_threeArgs f x1 y1 x2 y2 x3 y3 p1 p2 p3 = ?Mf_equal_threeArgs_1 


f_equal_typeConstructor_threeArgs : {A:Type} -> {B:Type} -> {C:Type} -> (f:A -> B -> C -> Type) ->
		    (x1:A) -> (y1:A) -> (x2:B) -> (y2:B) -> (x3:C) -> (y3:C) ->
		    (x1=y1) -> (x2=y2) -> (x3=y3) -> 
		    (f x1 x2 x3 = f y1 y2 y3)
f_equal_typeConstructor_threeArgs f x1 y1 x2 y2 x3 y3 p1 p2 p3 = ?Mf_equal_typeConstructor_threeArgs_1


	    
appendSingleton : {T:Type} -> (x:T) -> (xs:List T) -> ([x]++xs = x::xs)
appendSingleton x [] = Refl
appendSingleton x (xsh::xst) = Refl
	 	 

{-
-- Fix Idris : if I only give the first line of the definition by induction on the vect, Idris doesn't complain about the fact that this function isn't total (even If tagged as total) 
index_simpl1 : {T:Type} -> {n:Nat} -> (vect:Vect (S (S n)) T) -> 
		 (index (replace (sym (replace (plus_one_equals_succ n) Refl)) (FS (lastElement n))) vect =  index (FS (lastElement n)) vect)
index_simpl1 {n=Z} (h::t) = Refl
index_simpl1 {n=S Z} (h::t) = ?Mindex_simpl1_1
index_simpl1 {n=S (S Z)} (h::t) = ?Mindex_simpl1_2
index_simpl1 {n=S (S (S n'))} (h::t) = 
  -- let ihn = index_simpl1 {n=S (S n')} t in 
	 ?Mindex_simpl1_3
-}


-- index_replace_mkType : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vect:Vect n T) -> (eq:n=n') -> Type
-- index_replace_mkType i vect eq ?= (index (replace eq i) vect = index i vect)


-- index_replace : {T:Type} -> {n:Nat} -> {n':Nat} -> (i:Fin n) -> (vect:Vect n T) -> (eq:n=n') -> (index (replace eq i) vect = index i vect)
	 
	 

	 
	 
-- Proofs	 
	 
-- new bits
NewAutoAssoc_tools.M_S_both_side_1 = proof
  intros
  rewrite P
  mrefine Refl

NewAutoAssoc_tools.MSucc_LTE_1_one_case_1 = proof
  intros
  let prAux = LTE_deleteSucc _ _ pr
  exact (LTE_lower_than_zero prAux)  
  
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

NewAutoAssoc_tools.Mpre_convertFin_proofIrr_1 = proof
  intros
  exact (f_equal (\i => FS i) (pre_convertFin pi pm (GTE_deleteSucc (S pm) k p1)) (pre_convertFin pi pm (GTE_deleteSucc (S pm) k p2)) ihn)  
  
NewAutoAssoc_tools.Mpre_convertFin_proofIrr_2 = proof
  intros
  mrefine void
  mrefine elimFinZero'
  exact k
  exact pi
  exact (Succ_LTE_1_one_case k p1)
    
NewAutoAssoc_tools.MelimFinZero'_1 = proof
  intros
  exact (elimFinZero (rewrite (sym p) in i))  
  
NewAutoAssoc_tools.trick_vect_size_lemma_1 = proof
  intros
  rewrite (plus_one_equals_succ n)
  exact value  
  
NewAutoAssoc_tools.MindexOfLastElem_1 = proof
  intros
  exact Refl  
  
NewAutoAssoc_tools.MindexOfLastElem_2 = proof
  intros
  mrefine fin_replace 
  
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
  
NewAutoAssoc_tools.Mf_equal_twoArgs_1 = proof
  intros
  rewrite p1
  rewrite p2
  exact Refl  
  
NewAutoAssoc_tools.Mf_equal_threeArgs_1 = proof
  intros
  rewrite p1
  rewrite p2 
  rewrite p3
  exact Refl
  
NewAutoAssoc_tools.Mf_equal_typeConstructor_threeArgs_1 = proof
  intros
  rewrite p1
  rewrite p2
  rewrite p3
  exact Refl  
  
  
  
  
{-  
NewAutoAssoc_tools.Mindex_simpl1_1 = proof
  intros
  compute
  exact Refl
  
NewAutoAssoc_tools.Mindex_simpl1_2 = proof
  intros
  compute
  exact Refl  
  -}

  
  
