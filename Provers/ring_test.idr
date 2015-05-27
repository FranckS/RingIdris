module Provers.ring_test

import Data.ZZ
import Data.Vect
import Data.Fin
import Provers.globalDef
import Provers.dataTypes
import Provers.tools
import Provers.ring_reduce
import Provers.commutativeGroup_test
import Provers.group_test
import Provers.monoid_test
import Provers.semiGroup_test
import Provers.magma_test



-- In Nat, 0 * n = 0
total
mult_zero : (n:Nat) -> (mult Z n = Z)
mult_zero n = Refl

-- In Nat, n * 0 = 0
total
mult_zero' : (n:Nat) -> (mult n Z = Z)
mult_zero' Z = Refl
mult_zero' (S pn) = mult_zero' pn
						

-- In ZZ, 0 * z = 0
total
mult_ZZ_zero : (z:ZZ) -> (multZ (Pos Z) z = (Pos Z))
mult_ZZ_zero (Pos Z) = Refl
mult_ZZ_zero (Pos (S pa)) = Refl
mult_ZZ_zero (NegS Z) = Refl
mult_ZZ_zero (NegS (S pa)) = Refl

-- In ZZ, z * 0 = 0
total
mult_ZZ_zero' : (z:ZZ) -> (multZ z (Pos Z) = (Pos Z))
mult_ZZ_zero' (Pos Z) = Refl
mult_ZZ_zero' (Pos (S pa)) = f_equal _ _ _ (mult_zero' pa)
mult_ZZ_zero' (NegS Z) = Refl
mult_ZZ_zero' (NegS (S pa)) = 
	let paux:(mult pa Z = Z) = mult_zero' pa in
		?Mmult_ZZ_zero'_1

						

mult_ZZ_assoc : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (multZ (multZ x y) z = multZ x (multZ y z))
mult_ZZ_assoc (Pos a) (Pos b) (Pos c) = f_equal _ _ _ (sym (multAssociative a b c))

mult_ZZ_assoc (Pos Z) (Pos Z) (NegS Z) = Refl
mult_ZZ_assoc (Pos Z) (Pos Z) (NegS (S pc)) = Refl
mult_ZZ_assoc (Pos Z) (Pos (S pb)) (NegS Z) = Refl
mult_ZZ_assoc (Pos Z) (Pos (S pb)) (NegS (S pc)) = Refl
mult_ZZ_assoc (Pos (S pa)) (Pos Z) (NegS Z) = ?Mmult_ZZ_assoc_1
mult_ZZ_assoc (Pos (S pa)) (Pos Z) (NegS (S pc)) = ?Mmult_ZZ_assoc_2
mult_ZZ_assoc (Pos (S pa)) (Pos (S pb)) (NegS Z) = ?M1_7
mult_ZZ_assoc (Pos (S pa)) (Pos (S pb)) (NegS (S pc)) = ?M1_8




mult_ZZ_assoc (Pos a) (NegS b) (Pos c) = ?MC
mult_ZZ_assoc (Pos a) (NegS b) (NegS c) = ?MD
mult_ZZ_assoc (NegS a) (Pos b) (Pos c) = ?ME
mult_ZZ_assoc (NegS a) (Pos b) (NegS c) = ?MF
mult_ZZ_assoc (NegS a) (NegS b) (Pos c) = ?MG
mult_ZZ_assoc (NegS a) (NegS b) (NegS c) = ?MH


instance dataTypes.Ring ZZ where
    One = Pos Z
    Mult = multZ
    Mult_preserves_equiv {c1=c1} {c2=c2} {c1'=c1'} {c2'=c2'} pEq1 pEq2 = 
		-- Just types conversion : c1~=c1' is in fact c1=c1' since ~= is the syntactical = here
		let pEq1':(c1=c1') = pEq1 in 
		let pEq2':(c2=c2') = pEq2 in
			?Mmult_preserves_equiv_ZZ_1
    Mult_assoc c1 c2 c3 = mult_ZZ_assoc c1 c2 c3
    

    
    
    
    
    
    
    
    
    
    
---------- Proofs ----------
Provers.ring_test.Mmult_ZZ_zero'_1 = proof
  intros
  rewrite (sym paux)
  mrefine Refl

Provers.ring_test.Mmult_preserves_equiv_ZZ_1 = proof
  intros
  rewrite pEq1'
  rewrite pEq2'
  mrefine Refl  
  
Provers.ring_test.Mmult_ZZ_assoc_1 = proof
  intros
  rewrite (sym (mult_zero' pa))
  exact Refl

Provers.ring_test.Mmult_ZZ_assoc_2 = proof
  intros
  rewrite (sym (mult_zero' pa))
  exact Refl  