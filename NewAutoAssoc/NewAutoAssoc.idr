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

-- Fully left associative list expressions

  data RExpr : (G : Vect n (List a)) -> List a -> Type where
       RApp : RExpr G x -> (i : Fin n) -> RExpr G (x ++ index i G)
       RNil : RExpr G []

-- Convert an expression to a right associative expression, and return
-- a proof that the rewriting has an equal interpretation to the original
-- expression.

-- The idea is that we use this proof to build a proof of equality of
-- list appends

  total
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

  total
  r_expr : RExpr G x -> Expr G x
  r_expr RNil = ENil
  r_expr (RApp xs i) = App (r_expr xs) (Var i)

-- Convert an expression to some other equivalent expression (which
-- just happens to be normalised to right associative form)

  total
  reduce : Expr G x -> (x' ** (Expr G x', x = x'))
  reduce e = let (x' ** (e', prf)) = expr_r e in
                 (x' ** (r_expr e', prf))

-- Build a proof that two expressions are equal. If they are, we'll know
-- that the indices are equal.

  total
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

  total
  buildProof : {x : List a} -> {y : List a} ->
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
	isElement x (y :: ys) | Nothing = let recCall = isElement x ys in 
				       -- [| Pop (isElem x ys) |]  
					case recCall of
						Nothing => Nothing
						Just (i' ** p') => Just ((FS i') ** ?MisElement_1) 
  
  
total
Expr_eq_components : {a:Type} -> {x:Nat} -> {y:Nat} -> {vect1:Vect x (List a)} -> {vect2:Vect y (List a)} -> {v1:List a} -> {v2:List a} -> 
		      (x=y) -> (vect1=vect2) -> (v1=v2) ->
		      (Expr {n=x} vect1 v1 = Expr {n=y} vect2 v2)
-- I can't simply do (f_equal_typeConstructor_threeArgs (\u:Nat => \v:Vect u (List a) => \w:List a => Expr {a=a} {n=u} v w) x y vect1 vect2 v1 v2 p1 p2 p3)
-- Instead, I would need a dependent rewrite, which doesn't exists in Idris, so I do it "in the language", with the dependent pattern matching
Expr_eq_components {a=a} {x=x} {y=y} {vect1=vect1} {vect2=vect2} {v1=v1} {v2=v2} p1 p2 p3 with (p1) 
  Expr_eq_components {a=a} {x=x} {y=x} {vect1=vect1} {vect2=vect2} {v1=v1} {v2=v2} p1 p2 p3 | (Refl) with (p2)
    Expr_eq_components {a=a} {x=x} {y=x} {vect1=vect1} {vect2=vect1} {v1=v1} {v2=v2} p1 p2 p3 | (Refl) | (Refl) with (p3)
      Expr_eq_components {a=a} {x=x} {y=x} {vect1=vect1} {vect2=vect1} {v1=v1} {v2=v1} p1 p2 p3 | (Refl) | (Refl) | (Refl) = Refl

 

-- Reflects lists to Expr  
%reflection
total
reflectList : {n:Nat} -> (G : Vect n (List a)) -> (x:List a) -> (m ** (G' : Vect m (List a) ** (Expr (G ++ G') x)))
reflectList {n=n} G Nil = (Z ** ([] ** (ENil {n=n+0} {G=G++[]}))) -- What the hell. Why do I have to give precisely the Z for m ?
reflectList {n=n} G (x :: xs) with (reflectList G xs)
     | (m ** (G' ** xs')) with (isElement (List.(::) x []) (G ++ G'))
        | Just (i ** proofIndex) = let prEqual:(Expr (G++G') (x::xs) = Expr (G++G') (index i (G++G') ++ xs)) = ?MreflectList_1 in
				   let this = App (Var i) xs' in 
				      (m ** (G' ** ?MreflectList_2)) 	-- (G' ** (App (Var i) xs')))
	| Nothing = -- (rewrite (indexOfLastElem (G++G') x) in 
		    let this = App (Var (lastElement' (n+m))) (weaken [[x]] xs') in -- (rewrite (plusAssoc n m 1) in (rewrite (sym (vectAppendAssociative G G' [[x]])) in (App (Var FZ) (weaken [[x]] xs')))) in
		    let paux0:(Expr ((G++G')++[[x]]) (x::xs) = Expr ((G++G')++[[x]]) ([x]++xs)) = ?MreflectList_3 in
		    let paux:(index (lastElement' (n+m)) ((G++G')++[[x]]) = [x]) = ?MreflectList_4 in
		    let paux2:([x]++xs = (index (lastElement' (n+m)) ((G++G') ++ [[x]])) ++ xs) = ?MreflectList_5 in
		    let this' : (Expr ((G++G') ++ [[x]]) ([x]++xs)) = ?MreflectList_6 in
		    let paux3 : ((Expr (G++(G'++[[x]])) ([x]++xs)) = (Expr ((G++G')++[[x]]) ([x]++xs))) = ?MreflectList_7 in
			?MreflectList_8 -- ((m+1) ** ((G'++[[x]]) ** this)) -- ([x] :: G' ** App (Var Stop) (weaken [[x]] xs'))


-- Inspiration from what Edwin is doing :
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
        
        
-- ---------------------------------------------------------------------------------------------------------------------------------------------
-- What is under shows that %reflection is not dangerous for what we are doing : we produce something which is forced to have the right index !
-- ---------------------------------------------------------------------------------------------------------------------------------------------

data StupidNat : Nat -> Type where
	Zero : StupidNat Z
	One : StupidNat (S Z)
	Succ : (StupidNat n) -> StupidNat (S n)
   
%reflection
total
encode : (x:Nat) -> StupidNat x
-- Good thing, the (stupid!) line just under is rejected : the %reflection notation still procudes something TYPED !
-- That means that in my real function reflectList, I can't return something which doesn't have the right index
--encode Z = One
encode Z = Zero
encode (S px) = Succ (encode px)
   

-- ----------------------------------------------------     
-- Theoretical bit, not relevant for the implementation 
-- ----------------------------------------------------
total           
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
 
 
-- -----------------------------------------------------------------------------
-- Just three getters for (m ** (G ** e)) needed for expressing our main theorem
-- -----------------------------------------------------------------------------
total
getSizeVector : {x:List a} -> (G:Vect n (List a)) -> (arg:(m:Nat ** (G':Vect m (List a) ** Expr (G++G') x))) -> Nat
getSizeVector G (m ** (G' ** e)) = m

total
getContext : {x:List a} -> (G:Vect n (List a)) -> (arg:(m:Nat ** (G':Vect m (List a) ** Expr (G++G') x))) -> Vect (getSizeVector G arg) (List a)
getContext G (m ** (G' ** e)) = G'

total
getExp : {x:List a} -> (G:Vect n (List a)) -> (arg:(m:Nat ** (G':Vect m (List a) ** Expr (G++G') x))) -> Expr (G++(getContext G arg)) x
getExp G (m ** (G' ** e)) = e
 
-- Main theorem : for all x, the decode of the encode of x gives x
--theoremIdentity : (G:Vect n (List a)) -> (x:List a) -> (let (m ** (G' ** e)) = reflectList G x in decode e = x os
total
theoremIdentity : {a:Type} -> {n:Nat} -> (G:Vect n (List a)) -> (x:List a) -> (decode (getExp G (reflectList G x)) = x) 
theoremIdentity G [] = Refl
theoremIdentity G (h::t) = ?MtheoremIdentity_1 -- Should be easy once reflect is defined for (h::t) !

    
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



-- -----------------------------------
-- Proofs for the automatic reflection 
-- ------------------------------------
-- Just uses the proof of Void that we have constructed in the context
NewAutoAssoc.MlemmaExtension_1 = proof
  intros
  exact (void proofOfFalse)

NewAutoAssoc.MlemmaExtension_2 = proof
  intros
  rewrite (sym ih)
  rewrite (pre_convertFin_proofIrr pi _ (LTESucc (GTE_plus pk m)) (GTE_plus (S pk) m))
  mrefine Refl

NewAutoAssoc.MisElement_1 = proof
  intros
  exact (elemInBigerVect _ x p' y)

NewAutoAssoc.MreflectList_1 = proof
  intros
  rewrite (sym proofIndex)
  exact Refl

NewAutoAssoc.MreflectList_2 = proof
  intros
  exact (rewrite prEqual in this)

NewAutoAssoc.MreflectList_3 = proof
  intros
  exact Refl  

NewAutoAssoc.MreflectList_4 = proof
  intros
  mrefine indexOfLastElem     
  
NewAutoAssoc.MreflectList_5 = proof
  intros
  exact (rewrite paux in Refl) -- Fix Idris : I can just do (rewrite paux)

NewAutoAssoc.MreflectList_6 = proof
  intros
  exact (rewrite paux2 in this)  

NewAutoAssoc.MreflectList_7 = proof
  intros
  mrefine Expr_eq_components 
  mrefine plusAssociative
  mrefine vectAppendAssociative 
  exact Refl  
  
NewAutoAssoc.MreflectList_8 = proof
  intros
  mrefine MkSigma 
  exact (m+1)
  mrefine MkSigma 
  exact (G'++[[x]])
  exact (rewrite paux3 in this')





