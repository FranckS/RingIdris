-- myBinary_new.idr
-- This one uses the adapted solver (commutative monoid, for Nat)

module Main

import Data.Fin



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
addBit b0 b0 b0 = (_ ** (_ ** (b0, b0, Refl)))     -- 02 + 02 + 02 = (00)2
addBit b0 b0 b1 = (_ ** (_ ** (b0, b1, Refl)))     -- 02 + 02 + 12 = (01)2
addBit b0 b1 b0 = (_ ** (_ ** (b0, b1, Refl)))     -- 02 + 12 + 02 = (01)2
addBit b0 b1 b1 = (_ ** (_ ** (b1, b0, Refl)))     -- 02 + 12 + 12 = (10)2
addBit b1 b0 b0 = (_ ** (_ ** (b0, b1, Refl)))     -- 12 + 02 + 02 = (01)2
addBit b1 b0 b1 = (_ ** (_ ** (b1, b0, Refl)))     -- 12 + 02 + 12 = (10)2
addBit b1 b1 b0 = (_ ** (_ ** (b1, b0, Refl)))     -- 12 + 12 + 02 = (10)2
addBit b1 b1 b1 = (_ ** (_ ** (b1, b1, Refl)))     -- 12 + 12 + 12 = (11)2

adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc zero zero carry ?= zero # carry
adc (numx # bX) (numy # bY) carry
   = let (vCarry0 ** (vLsb ** (carry0, lsb, _))) = addBit bX bY carry in
          (adc numx numy carry0) # lsb
      
      
   

