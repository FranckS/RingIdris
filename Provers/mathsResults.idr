-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File mathsResults.idr
-- Various lemmas and theorems about algebraic structures, *not* strictly needed fot implementation of the ring tactic for Idris,
-- but nice enough for being formulated here
----------------------------------------------------------------------------------------------------------------------------------

module Provers.mathsResults

import Data.ZZ
import Provers.globalDef
import Provers.dataTypes
import Provers.tools


%default total

-- ---------------------------------
-- Mathematical results for a Group
------------------------------------

-- This is a (logical) DEFINITION, not a LEMMA (lies in TYPE)
bad_push_negation : (C:Type) -> (p:dataTypes.Group C) -> (x:C) -> (y:C) -> Type
bad_push_negation C p x y = (Neg (Plus x y) ~= Plus (Neg x) (Neg y))

bad_swap : (C:Type) -> (p:dataTypes.Group C) -> ((x:C) -> (y:C) -> (bad_push_negation C p x y)) -> ((x:C) -> (y:C) -> (Plus (Neg x) (Neg y) ~= Plus (Neg y) (Neg x)))
bad_swap C p Hbad x y = 
	let aux : (Neg (Plus x y) ~= Plus (Neg x) (Neg y)) = Hbad x y in
	let aux2 : (Neg (Plus x y) ~= Plus (Neg y) (Neg x)) = ?Mbad_swap_1 in
		?Mbad_swap_2

-- Proof that (forall x y, bad_push_negation x y) -> (forall x y, Plus x y ~= Plus y x)
-- That is too say, if we could develop the negation in the left-right order, then any group would be a commutative group
-- The conclusion is to *never* develop Neg (Plus x y) as Plus (Neg x) (Neg y) in our normalization procedure
bad_commutativity : (C:Type) -> (p:dataTypes.Group C) -> ((x:C) -> (y:C) -> (bad_push_negation C p x y)) -> ((x:C) -> (y:C) -> Plus x y ~= Plus y x)
bad_commutativity C p Hbad x y = 
	let aux : (Neg (Neg x) ~= x) = group_doubleNeg C p x in
	let aux2 : (Neg (Neg y) ~= y) = group_doubleNeg C p y in
	let aux3 : (Plus x y ~= Plus (Neg (Neg x)) (Neg (Neg y))) = ?Mbad_commutativity_1 in
	let aux4 : (Plus (Neg (Neg x)) (Neg (Neg y)) ~= Plus (Neg (Neg y)) (Neg (Neg x))) = bad_swap C p Hbad (Neg x) (Neg y) in
	let aux5 : (Plus x y ~= Plus (Neg (Neg y)) (Neg (Neg x))) = ?Mbad_commutativity_2 in
	let aux6 : (Plus y x ~= Plus (Neg (Neg y)) (Neg (Neg x))) = ?Mbad_commutativity_3 in
		?Mbad_commutativity_4

{-		
-- Question : HOW CAN I DEFINE AN INSTANCE "ON THE FLY" ?
bad_push_negation_IMPLIES_commutativeGroup : (C:Type) -> (p:dataTypes.Group C) -> ((x:C) -> (y:C) -> (bad_push_negation C p x y)) -> (dataTypes.CommutativeGroup C)
bad_push_negation_IMPLIES_commutativeGroup C p Hbad = 
	let comm : ((x:C) -> (y:C) -> (Plus x y ~= Plus y x)) = bad_commutativity C p Hbad in
	 (instance CommutativeGroup C where
		Plus_comm c1 c2 = comm c1 c2)
		--?Mbad_push_negation_IMPLIES_commutativeGroup_1
-}



---------- Proofs ---------- 
Provers.mathsResults.Mbad_swap_1 = proof
  intros
  exact (push_negation C p x y)
  
Provers.mathsResults.Mbad_swap_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg x) (Neg y))
  exact (Neg (Plus x y))
  mrefine set_eq_undec_refl
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_sym 
  exact aux2
  exact aux

Provers.mathsResults.Mbad_commutativity_1 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_sym 
  exact aux
  exact aux2

Provers.mathsResults.Mbad_commutativity_2 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus x y)
  exact (Plus (Neg (Neg x)) (Neg (Neg y)))
  mrefine set_eq_undec_refl 
  mrefine set_eq_undec_sym 
  exact aux3
  exact aux4  
  
Provers.mathsResults.Mbad_commutativity_3 = proof
  intros
  mrefine Plus_preserves_equiv 
  mrefine set_eq_undec_sym 
  mrefine set_eq_undec_sym 
  exact aux2
  exact aux 
  
Provers.mathsResults.Mbad_commutativity_4 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus (Neg (Neg y)) (Neg (Neg x)))
  exact (Plus (Neg (Neg y)) (Neg (Neg x)))
  exact aux5
  exact aux6
  mrefine set_eq_undec_refl 

  
  














  
