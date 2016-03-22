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

%access public export


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


total
mult_ZZ_assoc : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (multZ (multZ x y) z = multZ x (multZ y z))
{-
mult_ZZ_assoc (Pos a) (Pos b) (Pos c) = f_equal _ _ _ (sym (multAssociative a b c))

mult_ZZ_assoc (Pos Z) (Pos Z) (NegS Z) = Refl
mult_ZZ_assoc (Pos Z) (Pos Z) (NegS (S pc)) = Refl
mult_ZZ_assoc (Pos Z) (Pos (S pb)) (NegS Z) = Refl
mult_ZZ_assoc (Pos Z) (Pos (S pb)) (NegS (S pc)) = Refl
mult_ZZ_assoc (Pos (S pa)) (Pos Z) (NegS Z) = ?Mmult_ZZ_assoc_1 --done
mult_ZZ_assoc (Pos (S pa)) (Pos Z) (NegS (S pc)) = ?Mmult_ZZ_assoc_2 --done
mult_ZZ_assoc (Pos (S pa)) (Pos (S pb)) (NegS Z) = ?MB7
mult_ZZ_assoc (Pos (S pa)) (Pos (S pb)) (NegS (S pc)) = ?MB8

mult_ZZ_assoc (Pos Z) (NegS Z) (Pos Z) = ?MC1
mult_ZZ_assoc (Pos Z) (NegS Z) (Pos (S pc)) = ?MC2
mult_ZZ_assoc (Pos Z) (NegS (S pb)) (Pos Z) = ?MC3
mult_ZZ_assoc (Pos Z) (NegS (S pb)) (Pos (S pc)) = ?MC4
mult_ZZ_assoc (Pos (S pa)) (NegS Z) (Pos Z) = ?MC5
mult_ZZ_assoc (Pos (S pa)) (NegS Z) (Pos (S pc)) = ?MC6
mult_ZZ_assoc (Pos (S pa)) (NegS (S pb)) (Pos Z) = ?MC7
mult_ZZ_assoc (Pos (S pa)) (NegS (S pb)) (Pos (S pc)) = ?MC8

mult_ZZ_assoc (Pos Z) (NegS Z) (NegS Z) = ?MD1
mult_ZZ_assoc (Pos Z) (NegS Z) (NegS (S pc)) = ?MD2
mult_ZZ_assoc (Pos Z) (NegS (S pb)) (NegS Z) = ?MD3
mult_ZZ_assoc (Pos Z) (NegS (S pb)) (NegS (S pc)) = ?MD4
mult_ZZ_assoc (Pos (S pa)) (NegS Z) (NegS Z) = ?MD5
mult_ZZ_assoc (Pos (S pa)) (NegS Z) (NegS (S pc)) = ?MD6
mult_ZZ_assoc (Pos (S pa)) (NegS (S pb)) (NegS Z) = ?MD7
mult_ZZ_assoc (Pos (S pa)) (NegS (S pb)) (NegS (S pc)) = ?MD8

mult_ZZ_assoc (NegS Z) (Pos Z) (Pos Z) = ?ME1
mult_ZZ_assoc (NegS Z) (Pos Z) (Pos (S pc)) = ?ME2
mult_ZZ_assoc (NegS Z) (Pos (S pb)) (Pos Z) = ?ME3
mult_ZZ_assoc (NegS Z) (Pos (S pb)) (Pos (S pc)) = ?ME4
mult_ZZ_assoc (NegS (S pa)) (Pos Z) (Pos Z) = ?ME5
mult_ZZ_assoc (NegS (S pa)) (Pos Z) (Pos (S pc)) = ?ME6
mult_ZZ_assoc (NegS (S pa)) (Pos (S pb)) (Pos Z) = ?ME7
mult_ZZ_assoc (NegS (S pa)) (Pos (S pb)) (Pos (S pc)) = ?ME8

mult_ZZ_assoc (NegS Z) (Pos Z) (NegS Z) = ?MF1
mult_ZZ_assoc (NegS Z) (Pos Z) (NegS (S pc)) = ?MF2
mult_ZZ_assoc (NegS Z) (Pos (S pb)) (NegS Z) = ?MF3
mult_ZZ_assoc (NegS Z) (Pos (S pb)) (NegS (S pc)) = ?MF4
mult_ZZ_assoc (NegS (S pa)) (Pos Z) (NegS Z) = ?MF5
mult_ZZ_assoc (NegS (S pa)) (Pos Z) (NegS (S pc)) = ?MF6
mult_ZZ_assoc (NegS (S pa)) (Pos (S pb)) (NegS Z) = ?MF7
mult_ZZ_assoc (NegS (S pa)) (Pos (S pb)) (NegS (S pc)) = ?MF8

mult_ZZ_assoc (NegS Z) (NegS Z) (Pos Z) = ?MG1
mult_ZZ_assoc (NegS Z) (NegS Z) (Pos (S pc)) = ?MG2
mult_ZZ_assoc (NegS Z) (NegS (S pb)) (Pos Z) = ?MG3
mult_ZZ_assoc (NegS Z) (NegS (S pb)) (Pos (S pc)) = ?MG4
mult_ZZ_assoc (NegS (S pa)) (NegS Z) (Pos Z) = ?MG5
mult_ZZ_assoc (NegS (S pa)) (NegS Z) (Pos (S pc)) = ?MG6
mult_ZZ_assoc (NegS (S pa)) (NegS (S pb)) (Pos Z) = ?MG7
mult_ZZ_assoc (NegS (S pa)) (NegS (S pb)) (Pos (S pc)) = ?MG8

mult_ZZ_assoc (NegS Z) (NegS Z) (NegS Z) = ?MH1
mult_ZZ_assoc (NegS Z) (NegS Z) (NegS (S pc)) = ?MH2
mult_ZZ_assoc (NegS Z) (NegS (S pb)) (NegS Z) = ?MH3
mult_ZZ_assoc (NegS Z) (NegS (S pb)) (NegS (S pc)) = ?MH4
mult_ZZ_assoc (NegS (S pa)) (NegS Z) (NegS Z) = ?MH5
mult_ZZ_assoc (NegS (S pa)) (NegS Z) (NegS (S pc)) = ?MH6
mult_ZZ_assoc (NegS (S pa)) (NegS (S pb)) (NegS Z) = ?MH7
mult_ZZ_assoc (NegS (S pa)) (NegS (S pb)) (NegS (S pc)) = ?MH8
-}


mult_ZZ_dist : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (multZ x (plusZ y z)) = (plusZ (multZ x y) (multZ x z))
{-
mult_ZZ_dist (Pos a) (Pos b) (Pos c) = f_equal _ _ _ (multDistributesOverPlusRight a b c)
mult_ZZ_dist (Pos a) (Pos b) (NegS c) = ?MX2
mult_ZZ_dist (Pos a) (NegS b) (Pos c) = ?MX3
mult_ZZ_dist (Pos a) (NegS b) (NegS c) = ?MX4
mult_ZZ_dist (NegS a) (Pos b) (Pos c) = ?MX5
mult_ZZ_dist (NegS a) (Pos b) (NegS c) = ?MX6
mult_ZZ_dist (NegS a) (NegS b) (Pos c) = ?MX7
mult_ZZ_dist (NegS a) (NegS b) (NegS c) = ?MX8
-}

mult_ZZ_comm : (x:ZZ) -> (y:ZZ) -> (multZ x y = multZ y x)


total
mult_ZZ_dist2 : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> (multZ (plusZ x y) z) = (plusZ (multZ x z) (multZ y z))
-- We can use the fact that * is commutative in ZZ. ((ZZ, +, *) form a Commutative Ring even if we're going to only use it as a Ring
mult_ZZ_dist2 x y z = 
	let paux1:((multZ z (plusZ x y))=(plusZ (multZ z x) (multZ z y))) = mult_ZZ_dist z x y in
	let paux2:(multZ z x = multZ x z) = mult_ZZ_comm z x in
	let paux3:(multZ z y = multZ y z) = mult_ZZ_comm z y in
	let paux4:((multZ z (plusZ x y))=(plusZ (multZ x z) (multZ y z))) = ?Mmult_ZZ_dist2_1 in
		?Mmult_ZZ_dist2_2


-- In ZZ, z * 1 = z
total
mult_ZZ_neutral1 : (z:ZZ) -> ((multZ z (Pos (S Z))) = z)
mult_ZZ_neutral1 (Pos Z) = Refl
mult_ZZ_neutral1 (Pos (S pa)) = (f_equal _ _ _ (f_equal (\x => S x) _ _ (multOneRightNeutral pa)))
mult_ZZ_neutral1 (NegS Z) = Refl
mult_ZZ_neutral1 (NegS (S pa)) = (f_equal _ _ _ (f_equal (\x => S x) _ _ (multOneRightNeutral pa)))


-- In ZZ, 1 * z = z
total
mult_ZZ_neutral2 : (z:ZZ) -> (multZ (Pos (S Z)) z = z)
mult_ZZ_neutral2 (Pos Z) = Refl
mult_ZZ_neutral2 (Pos (S pa)) = (f_equal _ _ _ (f_equal (\x => S x) _ _ (multOneLeftNeutral pa)))
mult_ZZ_neutral2 (NegS Z) = Refl
mult_ZZ_neutral2 (NegS (S pa)) = (f_equal _ _ _ (f_equal (\x => S x) _ _ (multOneLeftNeutral pa)))



implementation dataTypes.Ring ZZ where
    One = Pos (S Z)
    Mult = multZ
    Mult_preserves_equiv {c1=c1} {c2=c2} {c1'=c1'} {c2'=c2'} pEq1 pEq2 = 
		-- Just types conversion : c1~=c1' is in fact c1=c1' since ~= is the syntactical = here
		let pEq1':(c1=c1') = pEq1 in 
		let pEq2':(c2=c2') = pEq2 in
			?Mmult_preserves_equiv_ZZ_1
    Mult_assoc c1 c2 c3 = mult_ZZ_assoc c1 c2 c3
    Mult_dist c1 c2 c3 = mult_ZZ_dist c1 c2 c3
    Mult_dist_2 c1 c2 c3 = mult_ZZ_dist2 c1 c2 c3
    Mult_neutral c1 = (mult_ZZ_neutral1 c1, mult_ZZ_neutral2 c1)

    
    
 

-- x * (y + 3)
expAr : (x:ZZ)  -> (y:ZZ) -> ExprR (%instance) [x,y] (x * (y + 3))
expAr x y = MultR (VarR _ (RealVariable _ _ _ _ FZ)) (PlusR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (ConstR _ _ 3))


-- x*3 + xy
expBr : (x:ZZ)  -> (y:ZZ) -> ExprR (%instance) [x,y] (x*3 + x*y)
expBr x y = PlusR (MultR (VarR _ (RealVariable _ _ _ _ FZ)) (ConstR _ _ 3)) (MultR (VarR _ (RealVariable _ _ _ _ FZ)) (VarR _ (RealVariable _ _ _ _ (FS FZ))))

 
 
-- ---------------------------------
-- TEST 1 : Test if x * (y + 3) = x*3 + xy
-- ---------------------------------
compare_expAr_expBr : (x:ZZ) -> (y:ZZ) -> Maybe (x * (y + 3) = x*3 + x*y)
compare_expAr_expBr x y = ringDecideEq (%instance) (expAr x y) (expBr x y) 

-- Later, we will have a real tactic "Ring" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_expAr_expBr : (x:ZZ) -> (y:ZZ) -> (x * (y + 3) = x*3 + x*y)
proof_expAr_expBr x y = let (Just ok) = compare_expAr_expBr x y in ok
-- RESULT : IS OK FOR ALL X AND Y NOW !
    
-- Let's debug it 
-- evaluate :
--(\x,y => debugRing (%instance) (%instance) (expAr x y) (expBr x y))



-- ---------------------------------
-- TEST 2 : Test if ((((3*x)*(y*2))*u) + (x * (y - y))) + (3*((x*y)*(5*g))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))
-- ---------------------------------

--  ((((3*x)*(y*2))*u) + (x * (y - y))) + (3*((x*y)*(5*g)))
{-
x = VarR _ (RealVariable _ _ _ _ FZ)
y = VarR _ (RealVariable _ _ _ _ (FS FZ))
u = VarR _ (RealVariable _ _ _ _ (FS (FS FZ))))
g = VarR _ (RealVariable _ _ _ _ (FS (FS (FS FZ))
-}

expCr : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ExprR (%instance) [x,y,u,g] (((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g))))
expCr x y u g = PlusR
					(PlusR
						(MultR
							(MultR 
								(MultR (ConstR _ _ 3) (VarR _ (RealVariable _ _ _ _ FZ))) -- 3*x
								(MultR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (ConstR _ _ 2)) -- y*2
							)
							(VarR _ (RealVariable _ _ _ _ (FS (FS FZ)))) -- u
						)
						(MultR
							(VarR _ (RealVariable _ _ _ _ FZ)) -- x
							(MinusR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (VarR _ (RealVariable _ _ _ _ (FS FZ)))) -- y-y
						)
					)	
					(MultR
						(ConstR _ _ 3) -- 3
						(MultR
							(MultR (VarR _ (RealVariable _ _ _ _ FZ)) (VarR _ (RealVariable _ _ _ _ (FS FZ)))) -- x*y 
							(MultR (ConstR _ _ 5) (VarR _ (RealVariable _ _ _ _ (FS (FS (FS FZ)))))) -- 5*g
						)
					)	
					
-- Evaluate this to debug :	
-- (\x,y,u,g => debugRing (%instance) (%instance) (expCr x y u g) (expDr x y u g))
-- WORKS NOW !


-- (((3*x)*(y*5))*g) + (3*((x*y)*(2*u)))
expC2r : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ExprR (%instance) [x,y,u,g] ((((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
expC2r x y u g =
            PlusR
                (MultR
                    (MultR
                        (MultR (ConstR _ _ 3) (VarR _ (RealVariable _ _ _ _ FZ)))
                        (MultR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (ConstR _ _ 5))
                    )
                    (VarR _ (RealVariable _ _ _ _ (FS (FS (FS FZ)))))
                )
            
                (MultR
                    (ConstR _ _ 3)
                    (MultR
                        (MultR (VarR _ (RealVariable _ _ _ _ FZ)) (VarR _ (RealVariable _ _ _ _ (FS FZ))))
                        (MultR (ConstR _ _ 2) (VarR _ (RealVariable _ _ _ _ (FS (FS FZ)))))
                    )
                )
            
compare_expCr_expC2r : (x:ZZ) -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> Maybe ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
compare_expCr_expC2r x y u g = ringDecideEq (%instance) (expCr x y u g) (expC2r x y u g) 

-- Later, we will have a real tactic "Ring" which can fail. At this point, we will
-- not have a missing case for "Nothing", which enables now to manipulate some false proof
-- (which causes a crash only when you apply then to a specific value for x)
proof_expCr_expC2r : (x:ZZ) -> (y:ZZ) -> (u:ZZ) -> (g:ZZ) -> ((((((3*x)*(y*2))*u) + (x * (y-y))) + (3*((x*y)*(5*g)))) = (((3*x)*(y*5))*g) + (3*((x*y)*(2*u))))
proof_expCr_expC2r x y u g = let (Just ok) = compare_expCr_expC2r x y u g in ok
-- RESULT : IT WORKS !!!!!!!!!!
    
-- You can also see the normalised terms :
-- evaluate :
-- (\x,y,u,g => debugRing (%instance) (%instance) (expCr x y u g) (expC2r x y u g))
-- THAT ALSO SHOWS SOMETHING GREAT WHICH IS THAT WHAT TAKES A LONG TIME IS THE PRINTING OF THE PROOF !
-- BECAUSE WHEN WE JUST PRINT THE NORMALISED TERMS (WITH debugRing), THIS IS REALLY FAST (INSTANT !)
-- AND SINCE IT CAN'T BE THE SYNTACTICAL TEST WHICH TAKES SO MUCH TIME, WE CONCLUDE THAT
-- IT'S THE PRINTING OF THE PROOF WHICH IS THE BOTTLENECK. NOT ITS GENERATION ! GREAT !



-- -------------------------------------------------------------
-- TEST OF A + B + C where B normalise to Zero or to a constant
-- -------------------------------------------------------------

-- When B reduces to Zero

expAring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> ExprR (%instance) [x,y,z] ((x + (y * (1-1))) + z)
expAring x y z = PlusR 
				(PlusR (VarR _ (RealVariable _ _ _ _ FZ))
				       (MultR (VarR _ (RealVariable _ _ _ _ (FS FZ)))
					          (MinusR (ConstR _ _ 1)
							          (ConstR _ _ 1))))
				(VarR _ (RealVariable _ _ _ _ (FS (FS FZ))))



expBring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> ExprR (%instance) [x,y,z] (z+x)
expBring x y z = PlusR (VarR _ (RealVariable _ _ _ _ (FS (FS FZ))))
						(VarR _ (RealVariable _ _ _ _ FZ))


compare_expAring_expBring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> Maybe (((x + (y * (1-1))) + z) = (z+x))
compare_expAring_expBring x y z = ringDecideEq (%instance) (expAring x y z) (expBring x y z)
-- Ok, works for all x, y and z


-- When B reduces to a constant

expCring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> ExprR (%instance) [x,y,z] ((x + ((1+(y-y)) * 5)) + z)
expCring x y z = PlusR 
				(PlusR (VarR _ (RealVariable _ _ _ _ FZ))
				       (MultR (PlusR (ConstR _ _ 1)
				       				 (MinusR (VarR _ (RealVariable _ _ _ _ (FS FZ)))
				       				 		 (VarR _ (RealVariable _ _ _ _ (FS FZ)))))
				       		  (ConstR _ _ 5)))
				(VarR _ (RealVariable _ _ _ _ (FS (FS (FZ)))))



expDring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> ExprR (%instance) [x,y,z] (z+(5+x))
expDring x y z = PlusR (VarR _ (RealVariable _ _ _ _ (FS (FS FZ))))
						(PlusR (ConstR _ _ 5)
								(VarR _ (RealVariable _ _ _ _ FZ)))


compare_expCring_expDring : (x:ZZ) -> (y:ZZ) -> (z:ZZ) -> Maybe (((x + ((1+(y-y)) * 5)) + z) = (z+(5+x)))
compare_expCring_expDring x y z = ringDecideEq (%instance) (expCring x y z) (expDring x y z)
-- Ok, works for all x, y and z


-- -------------------------------------------------------------
-- TEST OF 1 * something
-- -------------------------------------------------------------

expEring : (x:ZZ) -> ExprR (%instance) [x] x
expEring x = VarR _ (RealVariable _ _ _ _ FZ)

expFring : (x:ZZ) -> ExprR (%instance) [x] (1*(1*x))
expFring x = MultR (ConstR _ _ 1)
					(MultR (ConstR _ _ 1)
						  (VarR _ (RealVariable _ _ _ _ FZ)))

expGring : (x:ZZ) -> ExprR (%instance) [x] (x*1)
expGring x = MultR (VarR _ (RealVariable _ _ _ _ FZ))
					(ConstR _ _ 1)


compare_expEring_expFring : (x:ZZ) -> Maybe (x = 1*(1*x))
compare_expEring_expFring x = ringDecideEq (%instance) (expEring x) (expFring x)
-- ok !


compare_expEring_expGring : (x:ZZ) -> Maybe (x = x*1)
compare_expEring_expGring x = ringDecideEq (%instance) (expEring x) (expGring x)
-- now it's ok !

-- -------------------------------------------------------------
-- TEST OF -1 * something
-- -------------------------------------------------------------

expHring : (x:ZZ) -> ExprR (%instance) [x] (-x)
expHring x = NegR (VarR _ (RealVariable _ _ _ _ FZ))

expIring : (x:ZZ) -> ExprR (%instance) [x] ((-1)*x)
expIring x = MultR (ConstR _ _ (-1))
					(VarR _ (RealVariable _ _ _ _ FZ))

expI'ring : (x:ZZ) -> ExprR (%instance) [x] ((-1)*x)
expI'ring x = MultR (NegR (ConstR _ _ 1))
					(VarR _ (RealVariable _ _ _ _ FZ))

expJring : (x:ZZ) -> ExprR (%instance) [x] (x*(-1))
expJring x = MultR (VarR _ (RealVariable _ _ _ _ FZ))
					(ConstR _ _ (-1))

expJ'ring : (x:ZZ) -> ExprR (%instance) [x] (x*(-1))
expJ'ring x = MultR (VarR _ (RealVariable _ _ _ _ FZ))
					(NegR (ConstR _ _ 1))


-- Does -x = -1 * x ? (two attemps)
compare_expHring_expIring : (x:ZZ) -> Maybe (-x = (-1)*x)
compare_expHring_expIring x = ringDecideEq (%instance) (expHring x) (expIring x)
-- does not work

compare_expHring_expI'ring : (x:ZZ) -> Maybe (-x = (-1)*x)
compare_expHring_expI'ring x = ringDecideEq (%instance) (expHring x) (expI'ring x)
-- works

-- Does -x = x * (-1) ? (two attemps also)

compare_expHring_expJring : (x:ZZ) -> Maybe (-x = x * (-1))
compare_expHring_expJring x = ringDecideEq (%instance) (expHring x) (expJring x)
-- does not work

compare_expHring_expJ'ring : (x:ZZ) -> Maybe (-x = x * (-1))
compare_expHring_expJ'ring x = ringDecideEq (%instance) (expHring x) (expJ'ring x)
-- now it works !


-- -------------------------------------------------------------
-- TEST OF x * 0
-- -------------------------------------------------------------
expKring : (x:ZZ) -> ExprR (%instance) [x] 0
expKring x = ConstR _ _ 0

expLring : (x:ZZ) -> ExprR (%instance) [x] (x*0)
expLring x = MultR (VarR _ (RealVariable _ _ _ _ FZ))
					(ConstR _ _ 0)

expMring : (x:ZZ) -> ExprR (%instance) [x] (0*x)
expMring x = MultR (ConstR _ _ 0)
					(VarR _ (RealVariable _ _ _ _ FZ))

-- Does 0 = 0*x ?
compare_expKring_expLring : (x:ZZ) -> Maybe (0 = 0*x)
compare_expKring_expLring x = ringDecideEq (%instance) (expKring x) (expMring x)
-- works

-- Does 0 = x*0 ?
compare_expKring_expMring : (x:ZZ) -> Maybe (0 = x*0)
compare_expKring_expMring x = ringDecideEq (%instance) (expKring x) (expLring x)
-- now it works !



-- ---------------------------------
-- PREVIOUS LITTLE TESTS
-- ---------------------------------
    
   
expDr : (x:ZZ)  -> (y:ZZ) -> (u:ZZ) -> ExprR (%instance) [x,y,u] (((((3*x)*(y*2))*u)))
expDr x y u =  MultR
				(MultR 
					(MultR (ConstR _ _ 3) (VarR _ (RealVariable _ _ _ _ FZ))) -- 3*x
					(MultR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (ConstR _ _ 2)) -- y*2
				)
				(VarR _ (RealVariable _ _ _ _ (FS (FS FZ)))) -- u

-- Evaluate this to debug :	
-- (\x,y,u => debugRing (%instance) (%instance) (expDr x y u) (expDr x y u))
-- WORKS NOW !


-- Something different to understand the problem
expEr : (x:ZZ)  -> (y:ZZ) -> ExprR (%instance) [x,y] ((3+x)*(y+2))
expEr x y = (MultR 
				(PlusR (ConstR _ _ 3) (VarR _ (RealVariable _ _ _ _ FZ))) -- 3*x
				(PlusR (VarR _ (RealVariable _ _ _ _ (FS FZ))) (ConstR _ _ 2)) -- y*2
			)   
-- This one is ok   
   

   
expFr : (x:ZZ)  -> (y:ZZ) -> ExprR (%instance) [x,y] ((3*x)*y)
expFr x y =  MultR 
				(MultR (ConstR _ _ 3) (VarR _ (RealVariable _ _ _ _ FZ))) -- 3*x
				(VarR _ (RealVariable _ _ _ _ (FS FZ))) -- y

				
-- Evaluate this to debug :	
-- (\x,y => debugRing (%instance) (%instance) (expFr x y) (expFr x y))
-- WORKS NOW !				
				
   
   
   
-- --------------------------------------------------------------
-- NEW TEST : Test if 3xy + 8xy = 11xy. Answer : NO, will need some actorisation
-- -------------------------------------------------------------- 
threeXY : (x:ZZ) -> (y:ZZ) -> ExprR (%instance) [x,y] (3*(x*y))
threeXY x y = MultR (ConstR _ _ 3)
					(MultR (VarR _ (RealVariable _ _ _ _ FZ))
							(VarR _ (RealVariable _ _ _ _ (FS FZ))))
					

eightXY : (x:ZZ) -> (y:ZZ) -> ExprR (%instance) [x,y] (8*(x*y)) 
eightXY x y = MultR (ConstR _ _ 8)
					(MultR (VarR _ (RealVariable _ _ _ _ FZ))
							(VarR _ (RealVariable _ _ _ _ (FS FZ))))

thesum : (x:ZZ) -> (y:ZZ) -> ExprR (%instance) [x,y] ((3*(x*y)) + (8*(x*y)))
thesum x y = PlusR (threeXY x y) (eightXY x y)	


elevenXY : (x:ZZ) -> (y:ZZ) -> ExprR (%instance) [x,y] (11*(x*y))
elevenXY x y = MultR (ConstR _ _ 11)
					(MultR (VarR _ (RealVariable _ _ _ _ FZ))
							(VarR _ (RealVariable _ _ _ _ (FS FZ))))
							
							
-- Does 3xy + 8xy = 11xy ?
compare_thesum_elevenXY : (x:ZZ) -> (y:ZZ) -> Maybe (((3*(x*y)) + (8*(x*y))) = (11*(x*y)))
compare_thesum_elevenXY x y = ringDecideEq (%instance) (thesum x y) (elevenXY x y)
   
   
-- --------------------------------------------------------------
-- NEW TEST : Test the normalisation of 3xy + 2z + 8xy
-- --------------------------------------------------------------    
bigsum : (x:ZZ) -> (y:ZZ) -> (z:ZZ) ->  ExprR (%instance) [x,y,z] ((3*(x*y)) + ((2*z) + (8*(x*y))))
bigsum x y z = PlusR (MultR (ConstR _ _ 3) (MultR (VarR _ (RealVariable _ _ _ _ FZ)) (VarR _ (RealVariable _ _ _ _ (FS FZ)))))
					(PlusR (MultR (ConstR _ _ 2) (VarR _ (RealVariable _ _ _ _ (FS (FS FZ)))))
						(MultR (ConstR _ _ 8) (MultR (VarR _ (RealVariable _ _ _ _ FZ)) (VarR _ (RealVariable _ _ _ _ (FS FZ)))))
					)

 -- To test : 
 -- (\x,y,z => debugRing (%instance) (%instance) (bigsum x y z) (bigsum x y z))  
 -- seems OK !
    
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
  
{-  
Provers.ring_test.Mmult_ZZ_assoc_1 = proof
  intros
  rewrite (sym (mult_zero' pa))
  exact Refl

Provers.ring_test.Mmult_ZZ_assoc_2 = proof
  intros
  rewrite (sym (mult_zero' pa))
  exact Refl  
-}  
  
Provers.ring_test.Mmult_ZZ_dist2_1 = proof
  intros
  rewrite (sym paux1)
  rewrite (sym paux2)
  rewrite (sym paux3)
  exact Refl  
  
Provers.ring_test.Mmult_ZZ_dist2_2 = proof
  intros
  rewrite paux4
  mrefine mult_ZZ_comm   
  
  
  
  
  