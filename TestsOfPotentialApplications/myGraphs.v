Require Import Decidable.
Local Open Scope nat_scope.
Require Import Arith.

Inductive Fin : nat -> Type :=
  | fZ : forall n, Fin (S n)
  | fS : forall n, Fin n -> Fin (S n).

Fixpoint fin_dec {n:nat} (i:Fin n) (j:Fin n) {struct n} : bool :=
  match n with
  |O => true
  |S pn => match (i,j) with
           |(fZ k, fZ k') => beq_nat k k'
           |(fS _ i', fS _ j') => fin_dec i' j'
           | _ => false
           end
  end.
 

Inductive Graph : nat -> nat -> Type :=
  (* Add n nodes at once *)
  | addNodes : forall (nbNodes:nat), Graph nbNodes O
  (* Add an edge between two already existing nodes *)
  (* The new edge connects the nodes i and j *) 
  | addEdge : forall {nbNodes:nat} {nbEdges} (i j : Fin nbNodes),
                (Graph nbNodes nbEdges) -> Graph nbNodes (S nbEdges).


(* Utility functions *)

(* Without using the index (recomputes n using the structure of the graph) *)
Fixpoint getNbNodes {n e : nat} (g : Graph n e) : nat := 
  match g with
  |addNodes nbNodes => nbNodes
  |addEdge _ _ _ _ g' => getNbNodes g' (*continue *)
  end.

(* Without using the index (recomputes e using the structure of the graph) *)
Fixpoint getNbEdges {n e : nat} (g : Graph n e) : nat :=
  match g with
  |addNodes n => O
  |addEdge _ _ _ _ g' => S (getNbEdges g')
  end.



(* First equivalence relation *)

Inductive edgeExists : forall {n e : nat}, (Graph n e) ->  (Fin n) -> (Fin n) -> Prop :=
  |isLastAdded : forall {n e : nat} (g : Graph n e) (i j : Fin n), edgeExists (addEdge i j g) i j
  (* the edge [i,j] was already contained in g, so it is still after having added [i',j'] *)
  |wasAddedBefore : forall {n e : nat} (g:Graph n e) (i j i' j' : Fin n), edgeExists g i j -> edgeExists (addEdge i' j' g) i j.


Definition edgeExists_dec {n e : nat} (g : Graph n e) (i j : Fin n) : bool :=
  match g with
  |addNodes _ => false
  |addEdge _ _ i' j' g' =>  
  end.



(* First, naive, equivalence relation *)
(* Note : good thing : thanks to dependent types, we don't have to state that they should have the same number of nodes and edges *)
Definition graphEq_1 {n e : nat} (g1 g2 : Graph n e) : Prop :=
  forall (i j : Fin n), edgeExists g1 i j <-> edgeExists g2 i j.






