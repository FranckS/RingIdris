data T : Type where
	T1 : T
	T2 : T -> T
	
{- Induction principle for T -}
total
ind_T : (P:T->Type) ->	(P T1) -> ((t:T) -> P t -> P (T2 t))
		-> ((t:T) -> P t)
ind_T P H1 H2 T1 = H1
ind_T P H1 H2 (T2 t) = let ihn = ind_T P H1 H2 t in
						   H2 t ihn
						   
						   
{- So, clearly, we can prove the induction principle for any inductive type,
simple because we can define recursive functions on smaller terms. So either we
consider that recursive definitions is a primitive thing, and thus ind_T can be proven
as we just did, or we take a purely logical point of view (forgetting recursive definitions), 
and we consider ind_T to be an axiom -}


{- I think in Coq, the induction principle is more primitive, and recursive definitions
are translated automatically by the use of "T_ind" principles that are axioms automatically
added to the theory when we define a new indutive type T. Let's check in axiomInduction_byRecursivity_Coq.v
with the use of "print" for printing the proof term -}

