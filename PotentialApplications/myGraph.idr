-- myGraph.idr
-- Author : Franck Slama


import Data.Fin


data Graph : Nat -> Nat -> Type where
  -- Add n nodes at once
  addNodes : (nbNodes : Nat) -> Graph nbNodes Z
  -- Add an edge between two already existing nodes
  -- The new edge connects the nodes i and j
  addEdge : {nbNodes : Nat} -> {nbEdges : Nat} -> (i,j : Fin nbNodes) -> (Graph nbNodes nbEdges) -> Graph nbNodes (S nbEdges)
                

-- ---------------------             
-- Utility functions ---
-- ---------------------

-- Without using the index (recomputes n using the structure of the graph)
getNbNodes : {n, e : Nat} -> (g : Graph n e) -> Nat 
getNbNodes (addNodes n) = n
getNbNodes (addEdge _ _ g') = getNbNodes g' --continue


-- Without using the index (recomputes e using the structure of the graph)
getNbEdges : {n, e : Nat} -> (g : Graph n e) -> Nat
getNbEdges (addNodes n) = Z
getNbEdges (addEdge _ _ g') = S (getNbEdges g')



data edgeExists : {n, e : Nat} -> (Graph n e) -> (Fin n) -> (Fin n) -> Type where
  isLastAdded : {n, e : Nat} -> (g : Graph n e) -> (i, j : Fin n) -> edgeExists (addEdge i j g) i j
  -- the edge [i,j] was already contained in g, so it is still after having added [i',j']
  wasAddedBefore : {n, e : Nat} -> (g:Graph n e) -> (i, j, i', j' : Fin n) -> edgeExists g i j -> edgeExists (addEdge i' j' g) i j


-- Boolean equality on Fin
Fin_beq : {n:Nat} -> Fin n -> Fin n -> Bool
Fin_beq i j with (decEq i j)
  | (Yes pyes) = True
  | (No pno) = False


edgeExists_dec : {n, e : Nat} -> (Graph n e) -> (i, j : Fin n) -> Bool
-- There is no edges, so the answer is no...
edgeExists_dec (addNodes _) _ _ = False
-- Here we have to check
edgeExists_dec (addEdge i' j' g') i j = ((Fin_beq i i') && (Fin_beq j j')
                                        ||
					(Fin_beq i j') && (Fin_beq j i'))
                                        ||
					(edgeExists_dec g' i j)
	

-- To do : proof that edgeExists_dec effectively decides the predicate edgeExists	
	

-- First, naive, equivalence relation
-- Note : good thing : thanks to dependent types, we don't have to state that they should have the same number of nodes and edges
graphEq_1 : {n, e : Nat} -> (g1, g2 : Graph n e) -> Type
-- Note : uggly because Idris is not intended to write logical statments (we don't have the equivalence symbol <->, and other useful things)
graphEq_1 g1 g2 = ((i, j : Fin n) -> (edgeExists g1 i j) -> (edgeExists g2 i j)
		  ,
		   (i, j : Fin n) -> (edgeExists g2 i j) -> (edgeExists g1 i j))

	

-- To do : writing a decision procedure for graphEq_1 and proving that it effectively decides this predicate






