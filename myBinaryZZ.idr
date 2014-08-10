-- myBinaryZZ.idr

module Main


import Data.ZZ
import tools -- For PlusAssociativeZ that I've proved (to be added soon to the repository of Idris)
import commutativeGroup_reduce -- For the normalization procedure
import commutativeGroup_test -- For the instance CommutativeGroup ZZ

data Bit : ZZ -> Type where
     b0 : Bit (Pos Z)
     b1 : Bit (Pos (S Z))
     

     
     
infixl 5 #     
     
     
data Binary : (width : Nat) -> (value : ZZ) -> Type where
     zero : Binary Z (Pos Z)
     (#) : Binary w v -> Bit bit -> Binary (S w) (bit + (v + (v+0))) -- bit + 2*v


pad : Binary w n -> Binary (S w) n
pad zero = zero # b0
pad (num # x) = pad num # x



pattern syntax bitpair [x] [y] = (_ ** (_ ** (x, y, _)))
term syntax bitpair [x] [y] = (_ ** (_ ** (x, y, refl)))

addBit : Bit x -> Bit y -> Bit c ->
          (bX ** (bY ** (Bit bX, Bit bY, c + x + y = bY + (bX + (bX + 0))))) -- 
addBit b0 b0 b0 = bitpair b0 b0
addBit b0 b0 b1 = bitpair b0 b1
addBit b0 b1 b0 = bitpair b0 b1
addBit b0 b1 b1 = bitpair b1 b0
addBit b1 b0 b0 = bitpair b0 b1
addBit b1 b0 b1 = bitpair b1 b0
addBit b1 b1 b0 = bitpair b1 b0
addBit b1 b1 b1 = bitpair b1 b1

adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc zero zero carry ?= zero # carry
adc (numx # bX) (numy # bY) carry
   ?= let (vCarry0 ** (vLsb ** (carry0, lsb, _))) = addBit bX bY carry in
          adc numx numy carry0 # lsb
          
-------------------------------------
-- TEST WHAT WE CAN DO AT THE MOMENT
-- ----------------------------------
          
-- The context is : c, bit0, bit1, x, x1, v, v1


-- The known equality is :
--(plusZ (plusZ c bit0) bit1 = plusZ x1 (plusZ x x))


--LHS of the known equality
leftKnown : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1]
                    (plusZ (plusZ c bit0) bit1)
leftKnown c bit0 bit1 x x1 v v1 = PlusCG
                                    (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS (fS fZ)))))))) (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS fZ))))))))
                                    (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS fZ))))))

-- Normalized LHS of the known equality
leftKnown': (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (leftDep (commutativeGroupReduce _ (leftKnown c bit0 bit1 x x1 v v1)))
leftKnown' c bit0 bit1 x x1 v v1 = left (rightDep (commutativeGroupReduce _ (leftKnown c bit0 bit1 x x1 v v1)))




leftKnown'_bis : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (plusZ bit1 (plusZ bit0 c))
leftKnown'_bis c bit0 bit1 x x1 v v1 = PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS fZ)))))) 
					  (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS fZ))))))) (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS (fS fZ)))))))))




rightKnown : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1]
                    (plusZ x1
                          (plusZ x x))
rightKnown c bit0 bit1 x x1 v v1 = PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS fZ))))
                                          (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ)))))) 


-- Normalized RHS of the known equality
rightKnown': (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (leftDep (commutativeGroupReduce _ (rightKnown c bit0 bit1 x x1 v v1)))
rightKnown' c bit0 bit1 x x1 v v1 = left (rightDep (commutativeGroupReduce _ (rightKnown c bit0 bit1 x x1 v v1)))



rightKnown'_bis : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (plusZ x1 (plusZ x x))
rightKnown'_bis c bit0 bit1 x x1 v v1 = PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS fZ))))
                                          (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))))
                                          
                                          
-- Use this to see the two results of the normalizations for the known equality : 
-- \c => \bit0 => \bit1 => \x => \x1 => \v => \v1 => print_ExprCG show (leftKnown' c bit0 bit1 x x1 v v1)
-- \c => \bit0 => \bit1 => \x => \x1 => \v => \v1 => print_ExprCG show (rightKnown' c bit0 bit1 x x1 v v1)

-- ---------------
-- Normalization of the LHS and RHS of the equality that we want to prove

-- LHS
LHSreflected : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] 
                         (plusZ x1 
                                (plusZ 
                                    (plusZ 
                                        (plusZ x v) 
                                        v1)
                                    (plusZ 
                                        (plusZ 
                                            (plusZ x v) 
                                            v1) 
                                        (Pos 0))
                                )
                        )
LHSreflected c bit0 bit1 x x1 v v1 = 
        PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS fZ))))
               (PlusCG
                        (PlusCG
                            (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) (VarCG _ (RealVariable _ _ _ (fS fZ))))
                            (VarCG _ (RealVariable _ _ _ fZ)))
                        (PlusCG
                            (PlusCG
                                (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) (VarCG _ (RealVariable _ _ _ (fS fZ))))
                                (VarCG _ (RealVariable _ _ _ fZ)))
                            (ConstCG _ _ (Pos 0)))
                )

-- LHS normalized
LHSreflected': (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (leftDep (commutativeGroupReduce _ (LHSreflected c bit0 bit1 x x1 v v1)))
LHSreflected' c bit0 bit1 x x1 v v1 = left (rightDep (commutativeGroupReduce _ (LHSreflected c bit0 bit1 x x1 v v1)))


-- Just the same as above, but by hand
LHSreflected'_bis : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (v1+(v1+(v+(v+(x1+(x+x))))))
LHSreflected'_bis c bit0 bit1 x x1 v v1 = PlusCG (VarCG _ (RealVariable _ _ _ fZ)) (PlusCG (VarCG _ (RealVariable _ _ _ fZ)) 
					  (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ))) (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ))) 
					    (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS fZ)))) (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))) 
													(VarCG _ (RealVariable _ _ _ (fS (fS (fS fZ))))))))))
             
             
-- RHS
RHSreflected : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] 
                         (plusZ 
                            (plusZ c 
                                   (plusZ bit0 
                                          (plusZ v 
                                                (plusZ v (Pos 0))
                                           )
                                    )
                             )
                             (plusZ bit1 
                                    (plusZ v1 v1)
                             )
                         )
RHSreflected c bit0 bit1 x x1 v v1 = 
                PlusCG
                    (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS (fS fZ))))))))
                            (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS fZ)))))))
                                   (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ)))
                                          (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ))) (ConstCG _ _ (Pos 0)))
                                   )
                            )
                    )
                    (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS  (fS fZ))))))
                            (PlusCG (VarCG _ (RealVariable _ _ _ fZ)) (VarCG _ (RealVariable _ _ _ fZ)))
                    )
                


                               
                
-- RHS reflected
RHSreflected': (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (leftDep (commutativeGroupReduce _ (RHSreflected c bit0 bit1 x x1 v v1)))
RHSreflected' c bit0 bit1 x x1 v v1 = left (rightDep (commutativeGroupReduce _ (RHSreflected c bit0 bit1 x x1 v v1)))



RHSreflected'_bis : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ) 
               -> ExprCG (%instance) [c, bit0, bit1, x, x1, v, v1] (plusZ v1 (plusZ v1 (plusZ v (plusZ v (plusZ bit1 (plusZ bit0 c))))))
RHSreflected'_bis c bit0 bit1 x x1 v v1 = PlusCG (VarCG _ (RealVariable _ _ _ fZ)) (PlusCG (VarCG _ (RealVariable _ _ _ fZ)) 
					  (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ))) (PlusCG (VarCG _ (RealVariable _ _ _ (fS fZ))) 
					    (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS fZ)))))) (PlusCG (VarCG _ (RealVariable _ _ _ (fS (fS (fS (fS (fS fZ))))))) 
														  (VarCG _ (RealVariable _ _ _ (fS (fS (fS( fS( fS (fS fZ)))))))))))))
														  
               

-- Use this to see the two results of the normalizations : 
-- \c => \bit0 => \bit1 => \x => \x1 => \v => \v1 => print_ExprCG show (LHSreflected' c bit0 bit1 x x1 v v1)
-- \c => \bit0 => \bit1 => \x => \x1 => \v => \v1 => print_ExprCG show (RHSreflected' c bit0 bit1 x x1 v v1)
   
   
-- This is NOT total   
getJust : {a:Type} -> (Maybe a) -> a
getJust (Just x) = x




goal : (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ)
               -> (known : (plusZ (plusZ c bit0) bit1 = plusZ x1 (plusZ x x))) ->
                 Maybe (
                        (plusZ x1 
                                (plusZ 
                                    (plusZ 
                                        (plusZ x v) 
                                        v1)
                                    (plusZ 
                                        (plusZ 
                                            (plusZ x v) 
                                            v1) 
                                        (Pos 0))
                                )
                        )
                =
                    (plusZ 
                            (plusZ c 
                                   (plusZ bit0 
                                          (plusZ v 
                                                (plusZ v (Pos 0))
                                           )
                                    )
                             )
                             (plusZ bit1 
                                    (plusZ v1 v1)
                             )
                         )
                    )
goal c bit0 bit1 x x1 v v1 known = 
  let maybe_LHS_equals_LHS'bis = (commutativeGroupDecideEq _ (LHSreflected c bit0 bit1 x x1 v v1) (LHSreflected'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_RHS_equals_RHS'bis = (commutativeGroupDecideEq _ (RHSreflected c bit0 bit1 x x1 v v1) (RHSreflected'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_leftKnown_equals_leftKnown'bis = (commutativeGroupDecideEq _ (leftKnown c bit0 bit1 x x1 v v1) (leftKnown'_bis c bit0 bit1 x x1 v v1)) in
  let maybe_rightKnown_equals_rightKnown'bis = (commutativeGroupDecideEq _ (rightKnown c bit0 bit1 x x1 v v1) (rightKnown'_bis c bit0 bit1 x x1 v v1)) in
				      
  case (maybe_LHS_equals_LHS'bis, maybe_RHS_equals_RHS'bis, maybe_leftKnown_equals_leftKnown'bis, maybe_rightKnown_equals_rightKnown'bis) of
    (Just p1, Just p2, Just p3, Just p4) => let LHS_equals_LHS'bis : (plusZ x1 (plusZ (plusZ (plusZ x v) v1)(plusZ (plusZ (plusZ x v) v1) (Pos 0))) = v1+(v1+(v+(v+(x1+(x+x)))))) = p1 in
						let RHS_equals_RHS'bis : (plusZ (plusZ c (plusZ bit0 (plusZ v (plusZ v (Pos 0))))) (plusZ bit1 (plusZ v1 v1)) = (plusZ v1 (plusZ v1 (plusZ v (plusZ v (plusZ bit1 (plusZ bit0 c))))))) = p2 in
						  let leftKnown_equals_leftKnown'bis : ((plusZ (plusZ c bit0) bit1) = (plusZ bit1 (plusZ bit0 c))) = p3 in
						    let rightKnown_equals_rightKnown'bis : ((plusZ x1 (plusZ x x)) = (plusZ x1 (plusZ x x))) = p4 in -- useless
						      -- uses the known equality "known" and "leftKnown_equals_leftKnown'bis"
						      let newKnownEquality : ((plusZ bit1 (plusZ bit0 c)) = (plusZ x1 (plusZ x x))) = ?Mgoal_1 in
							?Mgoal_2
    _ => Nothing
-- Works for all variables ! Great !     
                                               
   

-- l is the length of the Binary   
goal_aux : (l:Nat) -> (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ)
               -> (known : (plusZ (plusZ c bit0) bit1 = plusZ x1 (plusZ x x))) ->
           (Maybe (Binary l (plusZ x1 
                                (plusZ 
                                    (plusZ 
                                        (plusZ x v) 
                                        v1)
                                    (plusZ 
                                        (plusZ 
                                            (plusZ x v) 
                                            v1) 
                                        (Pos 0))
                                )
                        )
		  -> Binary l (plusZ 
                            (plusZ c 
                                   (plusZ bit0 
                                          (plusZ v 
                                                (plusZ v (Pos 0))
                                           )
                                    )
                             )
                             (plusZ bit1 
                                    (plusZ v1 v1)
                             )
                         )
		    ))
goal_aux l c bit0 bit1 x x1 v v1 known = 
  case goal c bit0 bit1 x x1 v v1 known of
    Just p => ?Mgoal_aux_1
    Nothing => Nothing
   
             
             
goal_final : (l:Nat) -> (c:ZZ) -> (bit0:ZZ) -> (bit1:ZZ) 
               -> (x:ZZ) -> (x1:ZZ) -> (v:ZZ) -> (v1:ZZ)
               -> (known : (plusZ (plusZ c bit0) bit1 = plusZ x1 (plusZ x x))) ->
           (Binary l (plusZ x1 
                                (plusZ 
                                    (plusZ 
                                        (plusZ x v) 
                                        v1)
                                    (plusZ 
                                        (plusZ 
                                            (plusZ x v) 
                                            v1) 
                                        (Pos 0))
                                )
                        )
		  -> Binary l (plusZ 
                            (plusZ c 
                                   (plusZ bit0 
                                          (plusZ v 
                                                (plusZ v (Pos 0))
                                           )
                                    )
                             )
                             (plusZ bit1 
                                    (plusZ v1 v1)
                             )
                         )
		    )
goal_final l c bit0 bit1 x x1 v v1 known = getJust (goal_aux l c bit0 bit1 x x1 v v1 known)
                    
-- -----------------------------------------
	-- END OF TEST WHAT WE CAN DO AT THE MOMENT
-- -----------------------------------------       
  
  
---------- Proofs ----------
-- Old proof, done by hand
{-                  
Main.adc_lemma_2 = proof {
    intro c,w,v,bit0,num0;
    intro b0,v1,bit1,num1,b1;
    intro bc,x,x1,bX,bX1;
    rewrite sym (plusZeroRightNeutralZ x);
    rewrite sym (plusZeroRightNeutralZ v1);
    rewrite sym (plusZeroRightNeutralZ (plusZ (plusZ x v) v1));
    rewrite sym (plusZeroRightNeutralZ v);
    intros;
    rewrite sym (plusAssociativeZ (plusZ c (plusZ bit0 (plusZ v v))) bit1 (plusZ v1 v1));
    rewrite (plusAssociativeZ c (plusZ bit0 (plusZ v v)) bit1);
    rewrite (plusAssociativeZ bit0 (plusZ v v) bit1);
    rewrite plusCommutativeZ bit1 (plusZ v v);
    rewrite sym (plusAssociativeZ c bit0 (plusZ bit1 (plusZ v v)));
    rewrite sym (plusAssociativeZ (plusZ c bit0) bit1 (plusZ v v));
    rewrite sym b;
    rewrite plusAssociativeZ x1 (plusZ x x) (plusZ v v);
    rewrite plusAssociativeZ x x (plusZ v v);
    rewrite sym (plusAssociativeZ x v v);
    rewrite plusCommutativeZ v (plusZ x v);
    rewrite sym (plusAssociativeZ x v (plusZ x v));
    rewrite (plusAssociativeZ x1 (plusZ (plusZ x v) (plusZ x v)) (plusZ v1 v1));
    rewrite sym (plusAssociativeZ (plusZ (plusZ x v) (plusZ x v)) v1 v1);
    rewrite (plusAssociativeZ (plusZ x v) (plusZ x v) v1);
    rewrite (plusCommutativeZ v1 (plusZ x v));
    rewrite sym (plusAssociativeZ (plusZ x v) v1 (plusZ x v));
    rewrite (plusAssociativeZ (plusZ (plusZ x v) v1) (plusZ x v) v1);
    trivial;
}
-}

Main.adc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutralZ c) ;
    trivial;
}


Main.Mgoal_1 = proof
  intros
  rewrite leftKnown_equals_leftKnown'bis 
  rewrite known
  exact refl

Main.Mgoal_2 = proof
  intros
  mrefine Just
  rewrite (sym LHS_equals_LHS'bis) 
  rewrite (sym RHS_equals_RHS'bis) 
  rewrite newKnownEquality 
  exact refl

Main.Mgoal_aux_1 = proof
  intros
  rewrite p
  exact (Just (\x => x))

  
  
  
  

  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

---------- Proofs ----------

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
  rewrite (sym(plusZeroRightNeutralZ vCarry0 ))
  rewrite (sym(plusZeroRightNeutralZ v1))
  intro
  exact (goal_final (S (S w)) c bit bit1 vCarry0 vLsb v v1 b)
  


  
  
  