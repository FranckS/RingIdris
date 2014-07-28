-- myBinary.idr

module Main



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
          

          
          
          
          
          
myLemma : 
          (c : Nat) ->
          (v : Nat) ->
          (bit : Nat) ->
          (v1 : Nat) ->
          (bit1 : Nat) ->
          (vCarry0 : Nat) ->
          (vLsb : Nat) ->

                 (plus vLsb
                       (plus (plus (plus vCarry0 v) v1)
                             (plus (plus (plus vCarry0 v) v1) 0)))
                 =
                 (plus (plus c (plus bit (plus v (plus v 0))))
                       (plus bit1 (plus v1 (plus v1 0))))
          
myLemma c v bit v1 bit1 vCarry0 vLsb = ?MX
          

          
---------- Proofs ----------      
{-            
Main.adc_lemma_2 = proof {
    intro c,w,v,bit0,num0;
    intro b0,v1,bit1,num1,b1;
    intro bc,x,x1,bX,bX1;
    rewrite sym (plusZeroRightNeutral x);
    rewrite sym (plusZeroRightNeutral v1);
    rewrite sym (plusZeroRightNeutral (plus (plus x v) v1));
    rewrite sym (plusZeroRightNeutral v);
    intros;
    rewrite sym (plusAssociative (plus c (plus bit0 (plus v v))) bit1 (plus v1 v1));
    rewrite (plusAssociative c (plus bit0 (plus v v)) bit1);
    rewrite (plusAssociative bit0 (plus v v) bit1);
    rewrite plusCommutative bit1 (plus v v);
    rewrite sym (plusAssociative c bit0 (plus bit1 (plus v v)));
    rewrite sym (plusAssociative (plus c bit0) bit1 (plus v v));
    rewrite sym b;
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
-}



Main.adc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral c) ;
    trivial;
}