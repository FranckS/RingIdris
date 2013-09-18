-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File tools.idr
-- Various tools needed for the implementation of the ring tactic for Idris
-------------------------------------------------------------------

module tools

And_True_neutral : (b:Bool) -> (True && b = b)
And_True_neutral _ = refl

And_False_absorbent : (b:Bool) -> (False && b = False)
And_False_absorbent _ = refl

And_assoc : (a:Bool) -> (b:Bool) -> (c:Bool) -> ((a && (b && c)) = ((a && b) && c))
And_assoc True True True = refl
And_assoc True True False = refl
And_assoc True False True = refl
And_assoc True False False = refl
And_assoc False True True = refl
And_assoc False True False = refl
And_assoc False False True = refl
And_assoc False False False = refl

And_assoc2 : (a:Bool) -> (b:Bool) -> (c:Bool) -> (((a && b) && c) = (a && (b && c)))
And_assoc2 True True True = refl
And_assoc2 True True False = refl
And_assoc2 True False True = refl
And_assoc2 True False False = refl
And_assoc2 False True True = refl
And_assoc2 False True False = refl
And_assoc2 False False True = refl
And_assoc2 False False False = refl

-- To add in the depository for Idris
total plusAssociativeZ : (left : ZZ) -> (centre : ZZ) -> (right : ZZ) ->
  left + (centre + right) = (left + centre) + right
plusAssociativeZ (Pos n) (Pos m) = ?MplusAssociativeZ_1
plusAssociativeZ (Pos n) (NegS m) = ?MplusAssociativeZ_2
plusAssociativeZ (NegS n) (Pos m) = ?MplusAssociativeZ_3
plusAssociativeZ (NegS n) (NegS m) = ?MplusAssociativeZ_4