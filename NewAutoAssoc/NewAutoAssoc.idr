module NewAutoAssoc


import Decidable.Equality
import Data.Fin
import Data.Vect
import NewAutoAssoc_tools

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
  expr_r ENil = (_ ** (RNil, Refl))
  expr_r (Var i) = (_ ** (RApp RNil i, Refl))
  expr_r (App ex ey) = let (xl ** (xr, xprf)) = expr_r ex in
                       let (yl ** (yr, yprf)) = expr_r ey in
                           appRExpr _ _ xr yr xprf yprf
    where 
      appRExpr : (x', y' : List a) ->
                 RExpr G x -> RExpr G y -> (x' = x) -> (y' = y) ->
                 (w' ** (RExpr G w', x' ++ y' = w'))
      appRExpr x' y' rxs (RApp e i) xprf yprf
         = let (xs ** (rec, prf)) = appRExpr _ _ rxs e Refl Refl in
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
    eqExpr (App x y) (App x y)   | (Just Refl, Just Refl) = Just Refl
    eqExpr (App x y) (App x' y') | _ = Nothing
  eqExpr (Var i) (Var j) with (decEq i j)
    eqExpr (Var i) (Var i) | (Yes Refl) = Just Refl
    eqExpr (Var i) (Var j) | _ = Nothing
  eqExpr ENil ENil = Just Refl
  eqExpr _ _ = Nothing

  buildProof : {x : List a} -> {y : List a} ->
               Expr G ln -> Expr G rn ->
               (x = ln) -> (y = rn) -> Maybe (x = y) 
  buildProof e e' lp rp with (eqExpr e e')
    buildProof e e lp rp  | Just Refl = ?bp1
    buildProof e e' lp rp | Nothing = Nothing

  testEq : Expr G x -> Expr G y -> Maybe (x = y)
  testEq l r = let (ln ** (l', lPrf)) = reduce l in 
               let (rn ** (r', rPrf)) = reduce r in
                   buildProof l' r' lPrf rPrf
                   

  -- a couple of test expressions

  e1 : (xs, ys, zs : List a) -> 
           Expr [xs, ys, zs] ((xs ++ ys) ++ (xs ++ zs))
  e1 xs ys zs = App (App (Var FZ) (Var (FS FZ))) 
                        (App (Var FZ) (Var (FS (FS FZ))))

  e2 : (xs, ys, zs : List a) -> 
           Expr [xs, ys, zs] (xs ++ ((ys ++ xs) ++ zs))
  e2 xs ys zs = App (Var FZ) 
         (App (App (Var (FS FZ)) (Var FZ)) (Var (FS (FS FZ))))

         
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
		 


-- new test		 
		 
  e3 : (xs, ys : List a) -> 
           Expr [xs, ys] (([] ++ xs) ++ys)
  e3 xs ys = App (App ENil (Var FZ)) (Var (FS FZ)) 
                        

  e4 : (xs, ys : List a) -> 
           Expr [xs, ys] (xs ++ ys)
  e4 xs ys = App (Var FZ) (Var (FS FZ))		 
		 
		 
  e3_e4_testEq : (xs, ys : List a) ->
          Maybe ((([] ++ xs) ++ys) = (xs ++ ys))
  e3_e4_testEq xs ys = testEq (e3 xs ys) (e4 xs ys)	 
		 

  magic2 : (xs, ys : List a) ->
          (([] ++ (xs++ys)) = (xs ++ ys))
  magic2 = \xs, ys => 
     let (Just ok) = e3_e4_testEq xs ys in ok	 

     
-- new test	2	 
		 
  e5 : (xs, ys : List a) -> 
           Expr [xs, ys] ((xs ++ []) ++ys)
  e5 xs ys = App (App (Var FZ) ENil) (Var (FS FZ)) 
                        

  e6 : (xs, ys : List a) -> 
           Expr [xs, ys] (xs ++ ys)
  e6 xs ys = App (Var FZ) (Var (FS FZ))		 
		 
		 
  e5_e6_testEq : (xs, ys : List a) ->
          Maybe (((xs ++ []) ++ys) = (xs ++ ys))
  e5_e6_testEq xs ys = testEq (e5 xs ys) (e6 xs ys)	 
		 

  magic3 : (xs, ys : List a) ->
          (((xs ++ []) ++ys) = (xs ++ ys))
  magic3 = \xs, ys => 
     let (Just ok) = e5_e6_testEq xs ys in ok	     
 
 
-- ---------------------
-- Automatic reflection 
-- ---------------------

	
total	
lemmaExtension : {c:Type} -> {n:Nat} ->	{m:Nat} -> (g:Vect n c) -> (g':Vect m c) -> (i:Fin n) -> (index i g = index (convertFin _ i m) (g++g'))
lemmaExtension Nil g' (FZ {k=k}) impossible
lemmaExtension (gh::gt) g' (FZ {k=k}) = Refl
lemmaExtension (gh::gt) g' (FS {k=Z} pi) = let proofOfFalse : Void = elimFinZero pi in -- Just elim the element of (Fin 0) that we have in the context to build an inhabitant of False (Void)
												?MlemmaExtension_1 -- Just elim the inhabitant of False that we have constructed in the context
lemmaExtension (gh::gt) g' (FS {k=S pk} pi) = let ih = lemmaExtension gt g' pi in ?MlemmaExtension_2

	
total
weaken : {n:Nat} -> {m:Nat} -> {G:Vect n (List a)} -> {x:List a} -> (G':Vect m (List a)) -> (Expr G x) -> (Expr (G ++ G') x)
weaken G' ENil = ENil
weaken G' (App e1 e2) = App (weaken G' e1) (weaken G' e2)
weaken {n=n} {m=m} {G=G} G' (Var i) =
	let pExt = lemmaExtension G G' i in
		rewrite pExt in (Var (convertFin _ i m)) 

     
total
isElement : {n:Nat} -> (x : a) -> (G : Vect n a) -> Maybe (i:Fin n ** (index i G = x))
isElement x [] = Nothing
isElement x (y :: ys) with (prim__syntactic_eq _ _ x y)
	isElement x (x :: ys) | Just Refl = Just (FZ ** Refl) -- [| Stop |]
	isElement x (y :: ys) | Nothing = let recCall = isElement x ys in -- [| Pop (isElem x ys) |]  
										case recCall of
										Nothing => Nothing
										Just (i' ** p') => Just ((FS i') ** ?MLA) 
  
 
{-
-- Reflects lists to Expr  
%reflection
reflectList : {n:Nat} -> (G : Vect n (List a)) -> (x:List a) -> (m ** (G' : Vect m (List a) ** (Expr (G ++ G') x)))
reflectList {n=n} G Nil = (Z ** ([] ** (ENil {n=n+0} {G=G++[]}))) -- What the hell. Why do I have to give precisely the Z for m ?
reflectList {n=n} G (x :: xs) with (reflectList G xs)
     | (m ** (G' ** xs')) with (isElement (List.(::) x []) (G ++ G'))
        | Just i = (_ ** (G' ** (App (Var i) xs')))
        | Nothing = ?MTOSEE -- ([x] :: G' ** App (Var Stop) (weaken [[x]] xs'))

-}
   
   
        
{-
 
%reflection
reflectList : (G : List (List a)) ->
          (xs : List a) -> (G' ** Expr (G' ++ G) xs)
reflectList G [] = ([] ** ENil)

reflectList G (x :: xs) with (reflectList G xs)
     | (G' ** xs') with (isElem (List.(::) x []) (G' ++ G))
        | Just p = (G' ** App (Var p) xs')
        | Nothing = ([x] :: G' ** App (Var Stop) (weaken [[x]] xs'))

reflectList G (xs ++ ys) with (reflectList G xs)
     | (G' ** xs') with (reflectList (G' ++ G) ys)
         | (G'' ** ys') = ((G'' ++ G') **
                              rewrite (sym (appendAssociative G'' G' G)) in
                                 App (weaken G'' xs') ys')
reflectList G t with (isElem t G)
            | Just p = ([] ** Var p)
            | Nothing = ([t] ** Var Stop) 
 
 
-} 
 
     
-- ----------------------------------------------------     
-- Theoretical bit, not relevant for the implementation 
-- ----------------------------------------------------
                   
decode : {G:Vect n (List a)} -> (Expr G x) -> List a
decode ENil = []
decode {G=G} (Var i) = index i G
decode (App e1 e2) = (decode e1) ++ (decode e2)     
     

-- lemma
total
decode_correct : {G:Vect n (List a)} -> {x:List a} -> (e : Expr G x) -> (decode e = x)
decode_correct ENil = Refl
decode_correct (Var i) = Refl
decode_correct (App e1 e2) = 
	let e1_decode_ok = decode_correct e1 in
	let e2_decode_ok = decode_correct e2 in
		rewrite e1_decode_ok in (rewrite e2_decode_ok in Refl)
 
 
 
-- Main theorem
-- theoremIdentity : {G:Vect n (List a)} -> (x:List a) -> decode ( -- I need to have the encode function (reflection) defined here, in order to be able to talk about it. To be added.
 
     
---------- Proofs ----------

NewAutoAssoc.appRExpr1 = proof {
  intros;
  rewrite sym xprf;
  rewrite sym yprf;
  rewrite prf;
  mrefine appendAssociative
}


NewAutoAssoc.appRExpr2 = proof {
  intros;
  rewrite xprf;
  rewrite sym yprf;
  rewrite appendNilRightNeutral x';
  exact Refl
}

NewAutoAssoc.bp1 = proof {
  intros;
  refine Just;
  rewrite sym lp;
  rewrite sym rp;
  exact Refl
}



-- ---------------------
-- Automatic reflection 
-- ---------------------
-- Just uses the proof of Void that we have constructed in the context
NewAutoAssoc.MlemmaExtension_1 = proof
  intros
  exact (void proofOfFalse)

NewAutoAssoc.MlemmaExtension_2 = proof
  intros
  rewrite (sym ih)
  rewrite (pre_convertFin_proofIrr pi _ (LTESucc (GTE_plus pk m)) (GTE_plus (S pk) m))
  mrefine Refl







