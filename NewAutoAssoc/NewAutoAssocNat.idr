module NewAutoAssocNat


import Decidable.Equality
import Data.Fin
import Data.Vect
import NewAutoAssoc_tools

-- Expr is a reflection of a Nat, indexed over the concrete Nat,
-- and over a set of Nat variables.


-- First attempt presented in the paper, without the index
using (x : Nat, y : Nat, G : Vect n Nat)
  data XExpr : (G : Vect n Nat) -> Type where
      XPlus : XExpr G -> XExpr G -> XExpr G
      XVar : (i:Fin n) -> XExpr G
      XZero : XExpr G

-- Second attempt, also presented in the paper
  data Expr : (G : Vect n Nat) -> Nat -> Type where
       Plus  : Expr G x -> Expr G y -> Expr G (x + y)
       Var  : (i : Fin n) -> Expr G (index i G)
       Zero : Expr G Z


-- Fully left associative nat expressions

  data LExpr : (G : Vect n Nat) -> Nat -> Type where
       LPlus : LExpr G x -> (i : Fin n) -> LExpr G (x + index i G)
       LZero : LExpr G Z

-- Convert an expression to a left associative expression, and return
-- a proof that the rewriting has an equal interpretation to the original
-- expression.

-- The idea is that we use this proof to build a proof of equality of
-- list Plusends

  expr_l : Expr gam x -> (x' ** (LExpr gam x', x = x'))
  expr_l Zero = (_ ** (LZero, Refl))
  expr_l (Var i) = (_ ** (LPlus LZero i, Refl))
  expr_l (Plus ex ey) = 
    let (x' ** (ex', px)) = expr_l ex in
    let (y' ** (ey', py)) = expr_l ey in
    let (res ** (normRes, Pres)) = plusLExpr ex' ey' in
      (res ** (normRes, rewrite px in (rewrite py in Pres)))
        where 
        plusLExpr : {gam : Vect n Nat} -> {x, y : Nat} 
              -> LExpr gam x -> LExpr gam y  
              -> (z ** (LExpr gam z, x+y=z))
        plusLExpr {x=x} ex LZero = 
          (_ ** (ex, rewrite (plusZeroRightNeutral x) in Refl))          
        plusLExpr ex (LPlus e i) =
          let (xRec ** (rec, prfRec)) = plusLExpr ex e in
              (_ ** (LPlus rec i, ?MplusLExpr))

-- ...and back again

  total
  l_expr : LExpr G x -> Expr G x
  l_expr LZero = Zero
  l_expr (LPlus xs i) = Plus (l_expr xs) (Var i)

-- Convert an expression to some other equivalent expression (which
-- just happens to be normalised to left associative form)

  total
  reduce : Expr G x -> (x' ** (Expr G x', x = x'))
  reduce e = let (x' ** (e', prf)) = expr_l e in
                 (x' ** (l_expr e', prf))


 -- Build a proof that two expressions are equal. If they are, we'll know
 -- that the indices are equal.

  total
  eqExpr : (e : Expr G x) -> (e' : Expr G y) ->
           Maybe (e = e')
  eqExpr (Plus x y) (Plus x' y') with (eqExpr x x', eqExpr y y')
    eqExpr (Plus x y) (Plus x y)   | (Just Refl, Just Refl) = Just Refl
    eqExpr (Plus x y) (Plus x' y') | _ = Nothing
  eqExpr (Var i) (Var j) with (decEq i j)
    eqExpr (Var i) (Var i) | (Yes Refl) = Just Refl
    eqExpr (Var i) (Var j) | _ = Nothing
  eqExpr Zero Zero = Just Refl
  eqExpr _ _ = Nothing

  total
  buildProof : {x : Nat} -> {y : Nat} ->
               Expr G ln -> Expr G rn ->
               (x = ln) -> (y = rn) -> Maybe (x = y) 
  buildProof e e' lp rp with (eqExpr e e')
    buildProof e e lp rp  | Just Refl = ?bp1
    buildProof e e' lp rp | Nothing = Nothing

  total
  testEq : Expr G x -> Expr G y -> Maybe (x = y)
  testEq l r = let (ln ** (l', lPrf)) = reduce l in 
               let (rn ** (r', rPrf)) = reduce r in
                   buildProof l' r' lPrf rPrf           



 -- a couple of test expressions
  -- LSH reflected with the first version of the reflected terms
  Xe1 : (x, y, z : Nat) -> 
           XExpr [x, y, z]
  Xe1 x y z = XPlus (XPlus (XVar FZ) (XVar (FS FZ))) 
                    (XPlus (XVar FZ) (XVar (FS (FS FZ))))


  e1 : (x, y, z : Nat) -> 
           Expr [x, y, z] ((x + y) + (x + z))
  e1 x y z = Plus (Plus (Var FZ) (Var (FS FZ))) 
                        (Plus (Var FZ) (Var (FS (FS FZ))))

  e2 : (x, y, z : Nat) -> 
           Expr [x, y, z] (x + ((y + x) + z))
  e2 xs ys zs = Plus (Var FZ) 
         (Plus (Plus (Var (FS FZ)) (Var FZ)) (Var (FS (FS FZ))))

         
  -- TODO: need a tactic to run testEq rather than matching on Just ok, 
  -- since obviously that might fail...
  -- At the REPL, try 'magic' to see the generated proof.


  e1_e2_testEq : (x, y, z : Nat) ->
          Maybe (((x + y) + (x + z)) = (x + ((y + x) + z)))
  e1_e2_testEq x y z = testEq (e1 x y z) (e2 x y z)


  magic : (x, y, z : Nat) ->
          (((x + y) + (x + z)) = (x + ((y + x) + z)))
  magic = \x, y,z => 
     let (Just ok) = e1_e2_testEq x y z in ok                        



-- ---------------------
-- Automatic reflection 
-- ---------------------

total 
lemmaExtension : {c:Type} -> {n:Nat} -> {m:Nat} -> (g:Vect n c) -> (g':Vect m c) -> (i:Fin n) -> (index i g = index (convertFin _ i m) (g++g'))
lemmaExtension Nil g' (FZ {k=k}) impossible
lemmaExtension (gh::gt) g' (FZ {k=k}) = Refl
lemmaExtension (gh::gt) g' (FS {k=Z} pi) = let proofOfFalse : Void = elimFinZero pi in -- Just elim the element of (Fin 0) that we have in the context to build an inhabitant of False (Void)
                        ?MlemmaExtension_1 -- Just elim the inhabitant of False that we have constructed in the context
lemmaExtension (gh::gt) g' (FS {k=S pk} pi) = let ih = lemmaExtension gt g' pi in ?MlemmaExtension_2

  
total
weaken : {n:Nat} -> {m:Nat} -> {G:Vect n Nat} -> {x:Nat} -> (G':Vect m Nat) -> (Expr G x) -> (Expr (G ++ G') x)
weaken G' Zero = Zero
weaken G' (Plus e1 e2) = Plus (weaken G' e1) (weaken G' e2)
weaken {n=n} {m=m} {G=G} G' (Var i) =
  let pExt = lemmaExtension G G' i in
    rewrite pExt in (Var (convertFin _ i m)) 

     
total
isElement : {n:Nat} -> (x : a) -> (G : Vect n a) -> Maybe (i:Fin n ** (index i G = x))
isElement x [] = Nothing
isElement x (y :: ys) with (prim__syntactic_eq _ _ x y)
  isElement x (x :: ys) | Just Refl = Just (FZ ** Refl) -- [| Stop |]
  isElement x (y :: ys) | Nothing = let recCall = isElement x ys in 
               -- [| Pop (isElem x ys) |]  
          case recCall of
            Nothing => Nothing
            Just (i' ** p') => Just ((FS i') ** ?MisElement_1) 

-- Reflects Nat to Expr  
%reflection
total
reflectNat : {n:Nat} -> (G : Vect n Nat) -> (x:Nat) -> (m ** (G' : Vect m Nat ** (Expr (G ++ G') x)))
reflectNat {n=n} G Z = (Z ** ([] ** (Zero {n=n+0} {G=G++[]}))) -- What the hell. Why do I have to give precisely the Z for m ?
reflectNat G (x + y) =
     let (_ ** (G' ** x')) = (reflectNat G x) in
     let (_ ** (G'' ** y')) = (reflectNat (G ++ G') y) in
     let result = Plus (weaken G'' x') y' in 
        (_ ** ((G' ++ G'') ** ?MreflectNat_1)) -- The proof MreflectNat_1 will use (sym (vectAppendAssociative G G' G''))
reflectNat {n=n} G t with (isElement t G)
            | Just (i ** p) = let result = Var {G=G++[]} (convertFin n i Z) in
                                  (Z ** ([] ** ?MreflectNat_2)) -- We don't add anything
            | Nothing ?= (((S Z) ** ((t :: Vect.Nil) ** Var {G=G++[t]} (lastElement' n))))  -- We add the variable 't' to the context, and we can now reference it with (lastElement' n)
            -- The proof will use the fact that (index (lastElement' n) (G ++ [t])) = t
            -- By using the lemma elemInBigerVect that we've proved in NewAutoAssoc_tools.idr
{- 
-- We don't care of Succ here in fact
reflectNat {n=n} G (S x) with (reflectNat G x)
     | (m ** (G' ** x')) with (isElement x (G ++ G'))
        | Just (i ** proofIndex) = --let prEqual:(Expr (G++G') (S x) = Expr (G++G') (index i (G++G') + 1)) = ?MreflectNat_1 in
           let this = Plus (Var i) x' in 
              (m ** (G' ** ?MreflectNat_2))  -- (G' ** (App (Var i) x')))
-}


---------- Proofs ----------
-- This proof is directly done in the definition now
{-
NewAutoAssoc.Mexpr_l1 = proof
  intros
  rewrite (sym px)
  rewrite (sym py)
  exact Pres
-}

-- FIX IDRIS HERE : Why do we have a "gam" and "gam1" in the context ? We should only have ONE contaxt. It's certainly just some elaboration crap...
NewAutoAssocNat.MplusLExpr = proof
  intros
  rewrite (sym (plusAssociative x1 x2 (index i gam1)))
  rewrite prfRec
  exact Refl

NewAutoAssocNat.bp1 = proof {
  intros;
  refine Just;
  rewrite sym lp;
  rewrite sym rp;
  exact Refl
}

-- -----------------------------------
-- Proofs for the automatic reflection 
-- ------------------------------------
-- Just uses the proof of Void that we have constructed in the context
NewAutoAssocNat.MlemmaExtension_1 = proof
  intros
  exact (void proofOfFalse)

NewAutoAssocNat.MlemmaExtension_2 = proof
  intros
  rewrite (sym ih)
  rewrite (pre_convertFin_proofIrr pi _ (LTESucc (GTE_plus pk m)) (GTE_plus (S pk) m))
  mrefine Refl

NewAutoAssocNat.MisElement_1 = proof
  intros
  exact (elemInBigerVect _ x p' y)




