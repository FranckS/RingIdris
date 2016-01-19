-- myBinary_new.idr
-- This one uses the adapted solver (commutative monoid, for Nat)

module Main

import Data.Fin
import Provers.dataTypes
import Provers.commutativeMonoid_reduce -- For the appropriate reduction procedure
import Provers.commutativeMonoid_test -- For the instance (CommutativeMonoid Nat)
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test


data Bit : Nat -> Type where
     b0 : Bit Z
     b1 : Bit (S Z)

     
infixl 5 #     
     
     
data Binary : (width : Nat) -> (value : Nat) -> Type where
     zero : Binary Z Z
     (#) : Binary w v -> Bit bit -> Binary (S w) (bit + 2 * v)


pad : Binary w n -> Binary (S w) n
pad zero = zero # b0
pad (num # x) = pad num # x



pattern syntax bitpair [x] [y] = (_ ** (_ ** (x, y, _)))
term syntax bitpair [x] [y] = (_ ** (_ ** (x, y, Refl)))

addBit : Bit x -> Bit y -> Bit c ->
          (bX ** (bY ** (Bit bX, Bit bY, c + x + y = bY + 2 * bX)))
addBit b0 b0 b0 = bitpair b0 b0
addBit b0 b0 b1 = bitpair b0 b1
addBit b0 b1 b0 = bitpair b0 b1
addBit b0 b1 b1 = bitpair b1 b0
addBit b1 b0 b0 = bitpair b0 b1
addBit b1 b0 b1 = bitpair b1 b0
addBit b1 b1 b0 = bitpair b1 b0
addBit b1 b1 b1 = bitpair b1 b1


-- Used for the paper for telling the reader the expected and given indices

-- adc rejected because the indices don't match
adcRej : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adcRej zero zero carry ?= zero # carry
adcRej (numx # bX) (numy # bY) carry
   ?= let (vCarry0 ** (vLsb ** (carry0, lsb, _))) = addBit bX bY carry in
          adcRej numx numy carry0 # lsb


adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc zero zero carry ?= zero # carry
adc (numx # bX) (numy # bY) carry
   ?= let (vCarry0 ** (vLsb ** (carry0, lsb, _))) = addBit bX bY carry in
          adc numx numy carry0 # lsb
      
      
      
-- LHS
LHSreflected : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] 
                         (plus x1 
                                (plus 
                                    (plus 
                                        (plus x v) 
                                        v1)
                                    (plus 
                                        (plus 
                                            (plus x v) 
                                            v1) 
                                        Z)
                                )
                        )
LHSreflected c bit0 bit1 x x1 v v1 = 
        PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS( (FS (FS FZ)))))))
               (PlusCM _
                        (PlusCM _
                            (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))))
                            (VarCM _ _ (RealVariable _ _ _ _ (FS(FS(FS(FS(FS(FS FZ)))))))))
                        (PlusCM _
                            (PlusCM _
                                (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))))
                                (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))))
                            (ConstCM _ _ _ Z))
                )
        


-- LHS normalized
-- We nned to do it by hand
{-
LHSreflected': (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) [c, bit0, bit1, x, x1, v, v1] (leftDep (commutativeMonoidReduce _ (LHSreflected c bit0 bit1 x x1 v v1)))
LHSreflected' c bit0 bit1 x x1 v v1 = left (rightDep (commutativeMonoidReduce _ (LHSreflected c bit0 bit1 x x1 v v1)))
-}

-- Just the same as above, but by hand
LHSreflected'_bis : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] (v1+(v1+(v+(v+(x1+(x+x))))))
LHSreflected'_bis c bit0 bit1 x x1 v v1 = PlusCM _ (VarCM _ _ (RealVariable _ _ _ _  (FS (FS (FS (FS (FS (FS FZ)))))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))) 
					  (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))) 
					    (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS FZ)))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) 
                                                        (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))))))))
         
        
        
        
-- RHS
RHSreflected : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] 
                         (plus 
                            (plus c 
                                   (plus bit0 
                                          (plus v 
                                                (plus v Z)
                                           )
                                    )
                             )
                             (plus bit1 
                                    (plus v1 (plus v1 Z))
                             )
                         )
RHSreflected c bit0 bit1 x x1 v v1 = 
                PlusCM _
                    (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ FZ))
                            (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS FZ)))
                                   (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ)))))))
                                          (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))) (ConstCM _ _ _ Z))
                                   )
                            )
                    )
                    (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS  (FS FZ))))
                            (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))) (ConstCM _ _ _ Z)))
                    )
            
            
            
            
RHSreflected'_bis : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] (plus v1 (plus v1 (plus v (plus v (plus bit1 (plus bit0 c))))))
RHSreflected'_bis c bit0 bit1 x x1 v v1 = PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS (FS FZ)))))))) 
					  (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS (FS FZ))))))) 
					    (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS FZ)))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS FZ))) 
                                                                                                (VarCM _ _ (RealVariable _ _ _ _ FZ)))))))
														  
  
            
            
--LHS of the known equality
leftKnown : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1]
                    (plus (plus c bit0) bit1)
leftKnown c bit0 bit1 x x1 v v1 = PlusCM _
                                    (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ FZ)) (VarCM _ _ (RealVariable _ _ _ _ (FS FZ))))
                                    (VarCM _ _ (RealVariable _ _ _ _ (FS (FS FZ))))
                    
                    
                    
                    
-- Normalized LHS of the known equality
leftKnown'_bis : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] (plus bit1 (plus bit0 c))
leftKnown'_bis c bit0 bit1 x x1 v v1 = PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS FZ)))) 
					  (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS FZ))) (VarCM _ _ (RealVariable _ _ _ _ FZ)))


                    
-- RHS of the known equality                    
rightKnown : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1]
                    (plus x1
                          (plus x (plus x Z)))
rightKnown c bit0 bit1 x x1 v v1 = PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS FZ))))))
                                          (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) (ConstCM _ _ _ Z))) 
      
      
      
-- Normalized RHS of the known equality
rightKnown'_bis : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) (FakeSetAndMult (commutativeMonoid_to_set (%instance))) [c, bit0, bit1, x, x1, v, v1] (plus x1 (plus x x))
rightKnown'_bis c bit0 bit1 x x1 v v1 = PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS (FS FZ))))))
                                          (PlusCM _ (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))) (VarCM _ _ (RealVariable _ _ _ _ (FS (FS (FS FZ))))))
           
      
      
      
-- We're going to use this fact to prove the second lemma of adc.
-- The idea is that we don't make this proof by hand, but we call our tactic fot commutative Monoid (4 times here)
goal : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat)
               -> (known : (plus (plus c bit0) bit1 = plus x1 (plus x (plus x Z)))) ->
                 Maybe (
                        (plus x1 
                                (plus 
                                    (plus 
                                        (plus x v) 
                                        v1)
                                    (plus 
                                        (plus 
                                            (plus x v) 
                                            v1) 
                                        Z)
                                )
                        )
                =
                    (plus 
                            (plus c 
                                   (plus bit0 
                                          (plus v 
                                                (plus v Z)
                                           )
                                    )
                             )
                             (plus bit1 
                                    (plus v1 (plus v1 Z))
                             )
                         )
                    )
goal c bit0 bit1 x x1 v v1 known = 
  let maybe_LHS_equals_LHS'bis = (commutativeMonoidDecideEq _ (LHSreflected c bit0 bit1 x x1 v v1) (LHSreflected'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_RHS_equals_RHS'bis = (commutativeMonoidDecideEq _ (RHSreflected c bit0 bit1 x x1 v v1) (RHSreflected'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_leftKnown_equals_leftKnown'bis = (commutativeMonoidDecideEq _ (leftKnown c bit0 bit1 x x1 v v1) (leftKnown'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_rightKnown_equals_rightKnown'bis = (commutativeMonoidDecideEq _ (rightKnown c bit0 bit1 x x1 v v1) (rightKnown'_bis c bit0 bit1 x x1 v v1)) in
				      
  case (maybe_LHS_equals_LHS'bis, maybe_RHS_equals_RHS'bis, maybe_leftKnown_equals_leftKnown'bis, maybe_rightKnown_equals_rightKnown'bis) of
    (Just p1, Just p2, Just p3, Just p4) => let LHS_equals_LHS'bis : (plus x1 (plus (plus (plus x v) v1)(plus (plus (plus x v) v1) Z)) = v1+(v1+(v+(v+(x1+(x+x)))))) = p1 in
						let RHS_equals_RHS'bis : (plus (plus c (plus bit0 (plus v (plus v Z)))) (plus bit1 (plus v1 (plus v1 Z))) = (plus v1 (plus v1 (plus v (plus v (plus bit1 (plus bit0 c))))))) = p2 in
						  let leftKnown_equals_leftKnown'bis : ((plus (plus c bit0) bit1) = (plus bit1 (plus bit0 c))) = p3 in
						    let rightKnown_equals_rightKnown'bis : ((plus x1 (plus x (plus x Z))) = (plus x1 (plus x x))) = p4 in
						      -- uses the known equality "known" and "leftKnown_equals_leftKnown'bis"
						      let newKnownEquality : ((plus bit1 (plus bit0 c)) = (plus x1 (plus x x))) = ?Mgoal_1 in
							?Mgoal_2
    _ => Nothing
-- Works for all variables ! Great !  
      
      



-- Uses the result above to transfom a Binary encoding a natural into a binary encoding another natural, because these two naturals are equal, thanks to the property of the commutative monoid Nat.
-- l is the length of the Binary   
goal_aux : (l:Nat) -> (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat)
               -> (known : (plus (plus c bit0) bit1 = plus x1 (plus x (plus x Z)))) ->
           (Maybe (Binary l (plus x1 
                                (plus 
                                    (plus 
                                        (plus x v) 
                                        v1)
                                    (plus 
                                        (plus 
                                            (plus x v) 
                                            v1) 
                                        Z)
                                )
                        )
		  -> Binary l (plus 
                            (plus c 
                                   (plus bit0 
                                          (plus v 
                                                (plus v Z)
                                           )
                                    )
                             )
                             (plus bit1 
                                    (plus v1 (plus v1 Z))
                             )
                         )
		    ))
goal_aux l c bit0 bit1 x x1 v v1 known = 
  case goal c bit0 bit1 x x1 v v1 known of
    Just p => ?Mgoal_aux_1
    Nothing => Nothing
   
    
-- ----------------------------------------
-- Part added for performances tests
-- ----------------------------------------

thisIsAJust : {T:Type} -> (Lazy(Maybe T)) -> Bool
thisIsAJust (Just something) = True
thisIsAJust Nothing = False


resultOfProof : (l:Nat) -> (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat)
               -> (known : (plus (plus c bit0) bit1 = plus x1 (plus x (plus x Z)))) 
               -> Bool
resultOfProof = \l, c, bit0, bit1, x, x1, v, v1, known => thisIsAJust (goal_aux l c bit0 bit1 x x1 v v1 known)



eqb : Bool -> Bool -> Bool
eqb True True = True
eqb False False = True
eqb _ _ = False




goalProven : (l:Nat) -> (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat)
               -> (known : (plus (plus c bit0) bit1 = plus x1 (plus x (plus x Z)))) 
               -> Bool
goalProven l c bit0 bit1 x x1 v v1 known = eqb
                                           (resultOfProof l c bit0 bit1 x x1 v v1 known)
                                            True


-- I want to do the test of perf by evaluating the execution time of (\l, c, bit0, bit1, x, x1, v, v1, known => goalProven l c bit0 bit1 x x1 v v1 known)
-- But I don't get a simple boolean as anwser. Why ?

-- ----------------------------------------
-- End of part added for performances tests
-- ----------------------------------------




-- This is NOT total   
getJust : {a:Type} -> (Maybe a) -> a
getJust (Just x) = x

    
-- Same as above, except that we forget that the result could be a "Nothing"             
goal_final : (l:Nat) -> (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat)
               -> (known : (plus (plus c bit0) bit1 = plus x1 (plus x (plus x Z)))) ->
           (Binary l (plus x1 
                                (plus 
                                    (plus 
                                        (plus x v) 
                                        v1)
                                    (plus 
                                        (plus 
                                            (plus x v) 
                                            v1) 
                                        Z)
                                )
                        )
		  -> Binary l (plus 
                            (plus c 
                                   (plus bit0 
                                          (plus v 
                                                (plus v Z)
                                           )
                                    )
                             )
                             (plus bit1 
                                    (plus v1 (plus v1 Z))
                             )
                         )
		    )
goal_final l c bit0 bit1 x x1 v v1 known = getJust (goal_aux l c bit0 bit1 x x1 v v1 known)

--  To print the generated proof do :
-- (\l, c, bit0, bit1, x, x1, v, v1, known => goal_final l c bit0 bit1 x x1 v v1 known)





---------- Proofs ----------
-- Old proof, done by hand
{-
Main.adc_lemma_2 = proof {
    intro c,w,v,bit0,num0;
    intro b0,v1,bit1,num1,b1;
    intro bc,x,x1,bX,bX1;
    rewrite sym (plusZeroRightNeutral x);
    rewrite sym (plusZeroRightNeutral v1);
    rewrite sym (plusZeroRightNeutral (plus (plus x v) v1));
    rewrite sym (plusZeroRightNeutral v);
    intro thing1,thing2;
    rewrite sym (plusAssociative (plus c (plus bit0 (plus v v))) bit1 (plus v1 v1));
    rewrite (plusAssociative c (plus bit0 (plus v v)) bit1);
    rewrite (plusAssociative bit0 (plus v v) bit1);
    rewrite plusCommutative bit1 (plus v v);
    rewrite sym (plusAssociative c bit0 (plus bit1 (plus v v)));
    rewrite sym (plusAssociative (plus c bit0) bit1 (plus v v));
    rewrite sym thing1;
    rewrite plusAssociative x1 (plus x x) (plus v v);
    rewrite plusAssociative x x (plus v v);
    rewrite sym (plusAssociative x v v);
    rewrite plusCommutative v (plus x v);
    rewrite sym (plusAssociative x v (plus x v));
    rewrite (plusAssociative x1 (plus (plus x v) (plus x v)) (plus v1 v1));
    rewrite sym (plusAssociative (plus (plus x v) (plus x v)) v1 v1);
    rewrite (plusAssociative (plus x v) (plus x v) v1);
    rewrite (plusCommutative v1 (plus x v));
    rewrite sym (plusAssociative (plus x v) v1 (plus x v));
    rewrite (plusAssociative (plus (plus x v) v1) (plus x v) v1);
    trivial;
}
-}
Main.Mgoal_1 = proof
  intros
  rewrite leftKnown_equals_leftKnown'bis
  rewrite rightKnown_equals_rightKnown'bis
  rewrite known
  exact Refl

Main.Mgoal_2 = proof
  intros
  mrefine Just
  rewrite (sym LHS_equals_LHS'bis) 
  rewrite (sym RHS_equals_RHS'bis) 
  rewrite newKnownEquality 
  exact Refl

Main.Mgoal_aux_1 = proof
  intros
  rewrite p
  exact (Just (\x => x))



-- New proof, with our new bit of automation !!!
Main.adc_lemma_2 = proof
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro equalityKnown
  exact (goal_final (S (S w)) c bit bit1 vCarry0 vLsb v v1 equalityKnown)

Main.adc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral c) ;
    trivial;
}






