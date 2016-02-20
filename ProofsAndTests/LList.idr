-- Franck Slama
-- University of St Andrews
-- ------------------------------

module LList


-- import Decidable.Equality
-- import Data.Fin
import Data.Vect


%access public export

%default total




codata LList : (T:Type) -> Type where    
  LLNil : {T:Type} -> LList T
  LLCons : {T:Type} -> (h:T) -> (t:LList T) -> LList T

  
LLappend : {T:Type} -> (LList T) -> (LList T) -> (LList T)
LLappend LLNil l2 = l2
LLappend (LLCons h1 t1) l2 = LLCons h1 (LLappend t1 l2)
  

LLmap : {T:Type} -> {U:Type} -> (f:T -> U) -> (LList T) -> LList U  
LLmap f LLNil = LLNil
LLmap f (LLCons h t) = LLCons (f h) (LLmap f t)
  
  
  
codata LLall : {T:Type} -> (LList T) -> (P:T -> Type) -> Type where
  LLall_Nil : {T:Type} -> (P:T -> Type) -> LLall LLNil P
  LLall_Cons : {T:Type} -> (P:T -> Type) -> (h:T) -> (t:LList T) -> (ph : P h) -> (pt : LLall t P) -> LLall (LLCons h t) P

  
 
unfold_n_times : {T:Type} -> (LList T) -> (n:Nat) -> Maybe(Vect n T)
-- Unfolding LLNil
unfold_n_times LLNil Z = Just []
unfold_n_times LLNil _ = Nothing
-- Unfolding an LLCons
unfold_n_times (LLCons h t) Z = Just []
unfold_n_times (LLCons h t) (S pn) = case (unfold_n_times t pn) of 
					Just vectResultRec => Just (h::vectResultRec)
					Nothing => Nothing


-- If the provided LList isn't big enough, we will pad the rsult with the padding value givn 
unfold_n_times_with_padding : {T:Type} -> (LList T) -> (n:Nat) -> (paddingValue:T) -> Vect n T
-- Unfolding LLNil
unfold_n_times_with_padding LLNil Z paddingValue = []
unfold_n_times_with_padding LLNil (S pn) paddingValue = paddingValue::(unfold_n_times_with_padding LLNil pn paddingValue)
-- Unfolding an LLCons
unfold_n_times_with_padding (LLCons h t) Z paddingValue = []
unfold_n_times_with_padding (LLCons h t) (S pn) paddingValue = h::(unfold_n_times_with_padding t pn paddingValue) 




