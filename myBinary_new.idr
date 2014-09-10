-- myBinary_new.idr
-- This one uses the adapted solver (commutative monoid, for Nat)

module Main


import commutativeMonoid_test -- For the instance (CommutativeMonoid Nat)


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
term syntax bitpair [x] [y] = (_ ** (_ ** (x, y, refl)))

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

adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc zero zero carry ?= zero # carry
adc (numx # bX) (numy # bY) carry
   ?= let (vCarry0 ** (vLsb ** (carry0, lsb, _))) = addBit bX bY carry in
          adc numx numy carry0 # lsb
      
      
      
-- LHS
LHSreflected : (c:Nat) -> (bit0:Nat) -> (bit1:Nat) 
               -> (x:Nat) -> (x1:Nat) -> (v:Nat) -> (v1:Nat) 
               -> ExprCM (%instance) [c, bit0, bit1, x, x1, v, v1] 
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
        PlusCM (VarCM _ (fS (fS fZ)))
               (PlusCM
                        (PlusCM
                            (PlusCM (VarCM _ (fS (fS (fS fZ)))) (VarCM _ (fS fZ)))
                            (VarCM _ fZ))
                        (PlusCM
                            (PlusCM
                                (PlusCM (VarCM _ (fS (fS (fS fZ)))) (VarCM _ (fS fZ)))
                                (VarCM _ fZ))
                            (ConstCM _ _ Z))
                )
        



        
        
        
        
      