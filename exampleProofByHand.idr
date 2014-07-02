-- Proof of (l1 ++ l2) ++ (l3 ++l4) = (l1 ++ (l2 ++l3) ++l4)
-- Without automation

goal : {A:Type} -> (l1:List A) -> (l2:List A) -> (l3:List A) -> (l4:List A)
        -> (l1++l2) ++ (l3++l4) = (l1 ++ (l2++l3) ++ l4)
goal l1 l2 l3 l4 = ?MX



---------- Proofs ----------
Main.MX = proof
  intros
  rewrite (appendAssociative l2 l3 l4) -- (l2 + l3) + l4 = (l2 + (l3 + l4))
  rewrite (appendAssociative l1 l2 (l3 ++ l4)) -- (l1 + l2) + (l3 + l4) = l1 + (l2 + (l3 + l4))
  exact refl

