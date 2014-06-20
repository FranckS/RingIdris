module AutoAssoc

import Decidable.Equality

-- Expr is a reflection of a list, indexed over the concrete list,
-- and over a set of list variables.

using (x : List a, y : List a, G : Vect n (List a))
  data Expr : (G : Vect n (List a)) -> List a -> Type where
       App  : Expr G x -> Expr G y -> Expr G (x ++ y)
       Var  : (i : Fin n) -> Expr G (index i G)
       ENil : Expr G []

-- Fully right associative list expressions

  data RExpr : (G : Vect n (List a)) -> List a -> Type where
       RApp : RExpr G x -> (i : Fin n) -> RExpr G (x ++ index i G)
       RNil : RExpr G []

-- Convert an expression to a right associative expression, and return
-- a proof that the rewriting has an equal interpretation to the original
-- expression.

-- The idea is that we use this proof to build a proof of equality of
-- list appends

  expr_r : Expr G x -> (x' ** (RExpr G x', x = x'))
  expr_r ENil = (_ ** (RNil, refl))
  expr_r (Var i) = (_ ** (RApp RNil i, refl))
  expr_r (App ex ey) = let (xl ** (xr, xprf)) = expr_r ex in
                       let (yl ** (yr, yprf)) = expr_r ey in
                           appRExpr _ _ xr yr xprf yprf
    where 
      appRExpr : (x', y' : List a) ->
                 RExpr G x -> RExpr G y -> (x' = x) -> (y' = y) ->
                 (w' ** (RExpr G w', x' ++ y' = w'))
      appRExpr x' y' rxs (RApp e i) xprf yprf
         = let (xs ** (rec, prf)) = appRExpr _ _ rxs e refl refl in
               (_ ** (RApp rec i, ?appRExpr1))
      appRExpr x' y' rxs RNil xprf yprf = (_ ** (rxs, ?appRExpr2))

-- ...and back again

  r_expr : RExpr G x -> Expr G x
  r_expr RNil = ENil
  r_expr (RApp xs i) = App (r_expr xs) (Var i)

-- Convert an expression to some other equivalent expression (which
-- just happens to be normalised to right associative form)

  reduce : Expr G x -> (x' ** (Expr G x', x = x'))
  reduce e = let (x' ** (e', prf)) = expr_r e in
                 (x' ** (r_expr e', prf))

-- Build a proof that two expressions are equal. If they are, we'll know
-- that the indices are equal.

  eqExpr : (e : Expr G x) -> (e' : Expr G y) ->
           Maybe (e = e')
  eqExpr (App x y) (App x' y') with (eqExpr x x', eqExpr y y')
    eqExpr (App x y) (App x y)   | (Just refl, Just refl) = Just refl
    eqExpr (App x y) (App x' y') | _ = Nothing
  eqExpr (Var i) (Var j) with (decEq i j)
    eqExpr (Var i) (Var i) | (Yes refl) = Just refl
    eqExpr (Var i) (Var j) | _ = Nothing
  eqExpr ENil ENil = Just refl
  eqExpr _ _ = Nothing

  buildProof : {x : List a} -> {y : List a} ->
               Expr G ln -> Expr G rn ->
               (x = ln) -> (y = rn) -> Maybe (x = y) 
  buildProof e e' lp rp with (eqExpr e e')
    buildProof e e lp rp  | Just refl = ?bp1
    buildProof e e' lp rp | Nothing = Nothing

  testEq : Expr G x -> Expr G y -> Maybe (x = y)
  testEq l r = let (ln ** (l', lPrf)) = reduce l in 
               let (rn ** (r', rPrf)) = reduce r in
                   buildProof l' r' lPrf rPrf

  -- a couple of test expressions

  e1 : (xs, ys, zs : List a) -> 
           Expr [xs, ys, zs] ((xs ++ ys) ++ (xs ++ zs))
  e1 xs ys zs = App (App (Var fZ) (Var (fS fZ))) 
                        (App (Var fZ) (Var (fS (fS fZ))))

  e2 : (xs, ys, zs : List a) -> 
           Expr [xs, ys, zs] (xs ++ ((ys ++ xs) ++ zs))
  e2 xs ys zs = App (Var fZ) 
         (App (App (Var (fS fZ)) (Var fZ)) (Var (fS (fS fZ))))

  -- TODO: need a tactic to run testEq rather than matching on Just ok, 
  -- since obviously that might fail...
  -- At the REPL, try 'magic {a=Int}' to see the generated proof.


  e1_e2_testEq : (xs, ys, zs : List a) ->
          Maybe (((xs ++ ys) ++ (xs ++ zs)) = (xs ++ ((ys ++ xs) ++ zs)))
  e1_e2_testEq xs ys zs = testEq (e1 xs ys zs) (e2 xs ys zs)


  magic : (xs, ys, zs : List a) ->
          (((xs ++ ys) ++ (xs ++ zs)) = (xs ++ ((ys ++ xs) ++ zs)))
  magic = \xs, ys,zs => 
     let (Just ok) = e1_e2_testEq xs ys zs in ok

---------- Proofs ----------
{-
AutoAssoc.appRExpr1 = proof {
  intros;
  rewrite sym xprf;
  rewrite sym yprf;
  rewrite prf;
  rewrite sym (appendAssociative x x2 (index i G));
  exact refl
}
-}

appRExpr2 = proof {
  intros;
  rewrite xprf;
  rewrite sym yprf;
  rewrite appendNilRightNeutral x';
  exact refl
}

bp1 = proof {
  intros;
  refine Just;
  rewrite sym lp;
  rewrite sym rp;
  exact refl
}
