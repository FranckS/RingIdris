Require Import Bool.

Inductive Expr :=
   | Const1 : Expr
   | Const2 : Expr
   | Plus : Expr -> Expr -> Expr.

Fixpoint Expr_eq (e1:Expr) (e2:Expr) : bool :=
  match (e1,e2) with
   | (Const1, Const1) => true
   | (Const2, Const2) => true
   | (Plus a1 b1, Plus a2 b2) => (Expr_eq a1 a2) && (Expr_eq b1 b2)
   | _ => false
   end.

Fixpoint reify (e:Expr) : nat :=
  match e with
   | Const1 => O
   | Const2 => (S O)
   | (Plus a b) => (reify a) + (reify b)
   end.


Lemma Expr_eq_correct : forall (e1 e2:Expr), Expr_eq e1 e2 = true -> reify e1 = reify e2.
Proof.
intros e1 e2 H.
induction e1.
destruct e2.
reflexivity.
inversion H.
inversion H.
destruct e2.
inversion H.
reflexivity.
inversion H.
induction e2.
inversion H.
inversion H.
inversion H.
simpl.
assert (reify e1_1 = reify e2_1).
apply Expr_eq_correct.

apply IHe2_1.





