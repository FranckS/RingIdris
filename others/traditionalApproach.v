(* Franck Slama
   University of St Andrews
   traditionalApproach.v

   This file is an axiomatic formalisation of how
   our tactic could be developped in a "traditional approach",
   ie without our type-safe reflection mechanism.
   This code and these proofs conform to my PhD thesis, section 4.8.1
*)

(* Our universe *)

Axiom Expr : Type.
Axiom c : Type.
Axiom equiv : c -> c -> Prop.
Notation "x ~= y" := (equiv x y) (at level 75).
Axiom eq_refl : forall x, x ~= x.
Axiom eq_sym : forall x y, x ~= y -> y ~= x.
Axiom eq_trans : forall x y z, (x ~= y) -> (y ~= z) -> (x ~= z).

Lemma eq_preserves_eq : forall x y c1 c2, (x ~= c1) -> (y ~= c2) -> (c1 ~= c2) -> (x ~= y).
intros.
assert (x ~= c2).
apply eq_trans with (y:=c1).
assumption.
assumption.
assert (c2~=y).
apply eq_sym.
assumption.
apply eq_trans with (y:=c2).
assumption.
assumption.
Qed.

(* reify, reflect, and their correctness lemma *)

Axiom reify : Expr -> c.
Axiom reflect : c -> Expr.

Axiom reflect_and_reify_correct : forall x:c, reify (reflect x) ~= x.

(* Normalisation function and correctness lemma *)

Axiom normalise : Expr -> Expr.

Axiom normalise_correct : forall e:Expr, reify (normalise e) ~= reify e.

(* Syntactic equality test and correctness lemma *)

Axiom beq_Expr : Expr -> Expr -> bool.

Axiom beq_Expr_correct : forall (e1 e2:Expr), beq_Expr e1 e2 = true -> reify e1 ~= reify e2.

(* Kernel of the tactic and its correctness lemma *)

Definition decideEq (x:c) (y:c) : bool :=
  let ex := reflect x in
  let ey := reflect y in
  beq_Expr (normalise ex) (normalise ey).


Theorem decideEq_correct : forall (x y:c), decideEq x y = true -> x ~= y.
Proof.
intros.

(* 1) "We first need to obtain a proof H0 of (reify (reflect x) ~= reify (reflect y))..." *)
(* -------------------------------------------------------------------------------------- *)
assert (reify (reflect x) ~= reify (reflect y)).
apply eq_preserves_eq with (c1:=reify (normalise (reflect x))) (c2:=reify (normalise (reflect y))).

(* "... which mostly involves using two times the lemma normalise_correct..." *)
apply eq_sym.
apply normalise_correct.
apply eq_sym.
apply normalise_correct.

(* "...and to use one time beq_Expr_correct in the (unfolded) hypothesis" *)
unfold decideEq in H.
apply beq_Expr_correct in H.
assumption.

(* 2) "Then, we can build the desired proof of x ~= y" *)
(* --------------------------------------------------- *)
apply eq_preserves_eq with (c1:=reify (reflect x)) (c2:=reify (reflect y)).
(* "...by using two calls to the reflect_and_reify_correct lemma..." *)
apply eq_sym.
apply reflect_and_reify_correct.
apply eq_sym.
apply reflect_and_reify_correct.
(* ...and the freshly obtained proof $H0$ *)
apply H0.

Qed.


