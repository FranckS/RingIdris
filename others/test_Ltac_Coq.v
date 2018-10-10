Ltac test n :=
  match n with
  | O => true
  | S _ => O
  end.

(* This is not accepted *)
(*
Definition myfun (n:nat) : nat :=
  match n with
  | O => O
  | S pn => test pn
  end.
*)

Ltac test2 n :=
  apply n.

(* But this is accepted *)
Definition myfun (n:nat) : nat.
case n.
(try (test2 5)).
(* ok *) 

