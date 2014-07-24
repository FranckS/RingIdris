-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File commutativeGroup_reduce.idr
-- Normalize an expression reflecting an element in a commutative group
-------------------------------------------------------------------

module commutativeGroup_reduce

import Decidable.Equality
import dataTypes
import group_reduce
import tools
import Prelude.Vect

-- Order : Variable (in order) and then constants


-- Finally not needed

assoc_and_commute : {c:Type} -> {p:CommutativeGroup c} -> (x : c) -> (y : c) -> (z : c) -> (Plus (Plus x y) z = Plus (Plus y z) x)
assoc_and_commute x y z = let aux : (Plus (Plus x y) z = Plus x (Plus y z)) = Plus_assoc x y z in
								?Massoc_and_commute_1


-- A usufel lemma for most rewriting in this section
assoc_commute_and_assoc : {c:Type} -> {p:CommutativeGroup c} -> (x : c) -> (y : c) -> (z : c) -> (Plus (Plus x y) z = Plus (Plus x z) y)
assoc_commute_and_assoc x y z = let aux : (Plus (Plus x y) z = Plus x (Plus y z)) = Plus_assoc x y z in
								let aux2 : (Plus x (Plus y z) = Plus x (Plus z y)) = (rewrite Plus_comm y z in refl) in
								let aux3 : (Plus x (Plus z y) = Plus (Plus x z) y) = (sym (Plus_assoc x z y)) in
									?Massoc_commute_and_assoc_1

									
assoc_and_neutral : {c:Type} -> {p:dataTypes.Group c} -> (x : c) -> (y : c) -> (Plus x (Plus (Neg x) y) = y)
assoc_and_neutral x y = let aux : (Plus x (Plus (Neg x) y) = Plus (Plus x (Neg x)) y) = (sym (Plus_assoc x (Neg x) y)) in
						let aux2 : (Plus x (Neg x) = Zero) = left (Plus_inverse x) in
						let aux3 : (Plus Zero y = y) = Plus_neutral_1 y in
							?Massoc_and_neutral_1

assoc_and_neutral_bis : {c:Type} -> {p:dataTypes.Group c} -> (x : c) -> (y : c) -> (Plus (Neg x) (Plus x y) = y)
assoc_and_neutral_bis x y = let aux : (Plus (Neg x) (Plus x y) = Plus (Plus (Neg x) x) y) = (sym (Plus_assoc (Neg x) x y)) in
							let aux2 : (Plus (Neg x) x = Zero) = right (Plus_inverse x) in
							let aux3 : (Plus Zero y = y) = Plus_neutral_1 y in
							?Massoc_and_neutral_bis_1
							
									
-- 4 FUNCTIONS WHICH ADD A TERM TO AN EXPRESSION ALREADY "SORTED" (of the right forme)
-- -----------------------------------------------------------------------------------
									
--%default total
-- The expression is already in the form a + (b + (c + ...)) where a,b,c can only be constants, variables, and negations of constants and variables
putVarOnPlace : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> {varValue:c} 
   -> (Variable (commutativeGroup_eq_as_elem_of_set p) Neg g varValue) 
   -> (c2 ** (ExprCG p g c2, Plus c1 varValue=c2))
putVarOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) (RealVariable _ _ _ i) = 
    if minusOrEqual_Fin i0 i 
        then let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
             (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?MputVarOnPlace_1))
        else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (VarCG p (RealVariable _ _ _ i0)) e), ?MputVarOnPlace_2))
putVarOnPlace p (PlusCG (ConstCG _ _ c0) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (ConstCG _ _ c0) e), ?MputVarOnPlace_3)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
        
putVarOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) (RealVariable _ _ _ i) = 
	 if minusOrEqual_Fin i0 i 
		then let (r_ihn ** (e_ihn, p_ihn)) = (putVarOnPlace p e (RealVariable _ _ _ i)) in
			 (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, ?MputVarOnPlace_4))
		else (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e), ?MputVarOnPlace_5))
putVarOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i)) (PlusCG (NegCG (ConstCG _ _ c0)) e), ?MputVarOnPlace_6)) -- the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !

	

putConstantOnPlace : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> (constValue:c) 
   -> (c2 ** (ExprCG p g c2, Plus c1 constValue=c2))
putConstantOnPlace p (PlusCG (ConstCG _ _ c0) e) constValue = (_ ** (PlusCG (ConstCG _ _ (Plus c0 constValue)) e, ?MputConstantOnPlace_1))
putConstantOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) constValue = 
	let (r_ihn ** (e_ihn, p_ihn)) = putConstantOnPlace p e constValue in
		(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?MputConstantOnPlace_2))
putConstantOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) constValue = (_ ** (PlusCG (ConstCG _ _ (Plus (Neg c0) constValue)) e, ?MputConstantOnPlace_3)) -- Perhaps useless because I think that NegCG (ConstCG c) is always ConstCG (Neg c) at this stage
putConstantOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) constValue = 
    	let (r_ihn ** (e_ihn, p_ihn)) = putConstantOnPlace p e constValue in
		(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, ?MputConstantOnPlace_4))
        

putNegVarOnPlace : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> {varValue:c} 
   -> (Variable (commutativeGroup_eq_as_elem_of_set p) Neg g varValue) 
   -> (c2 ** (ExprCG p g c2, Plus c1 (Neg varValue)=c2))
putNegVarOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) (RealVariable _ _ _ i) = 
    if minusOrEqual_Fin i0 i 
        then let (r_ihn ** (e_ihn, p_ihn)) = (putNegVarOnPlace p e (RealVariable _ _ _ i)) in
             (_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?MputNegVarOnPlace_1))
		else (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i))) (PlusCG (VarCG p (RealVariable _ _ _ i0)) e), ?MputNegVarOnPlace_2))
putNegVarOnPlace p (PlusCG (ConstCG _ _ c0) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i))) (PlusCG (ConstCG _ _ c0) e), ?MputNegVarOnPlace_3)) -- the negation of the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
        
putNegVarOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) (RealVariable _ _ _ i) =
	 if minusOrEqual_Fin i0 i 
		then let (r_ihn ** (e_ihn, p_ihn)) = (putNegVarOnPlace p e (RealVariable _ _ _ i)) in
			 (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, ?MputNegVarOnPlace_4))
		else (_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i))) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e), ?MputNegVarOnPlace_5))
putNegVarOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) (RealVariable _ _ _ i) = 
	(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i))) (PlusCG (NegCG (ConstCG _ _ c0)) e), ?MputNegVarOnPlace_6)) -- the negation of the variable becomes the first one, and e is already sorted, there's no need to do a recursive call here !
		


putNegConstantOnPlace : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} 
   -> (ExprCG p g c1) -> (constValue:c) 
   -> (c2 ** (ExprCG p g c2, Plus c1 (Neg constValue)=c2))
putNegConstantOnPlace p (PlusCG (ConstCG _ _ c0) e) constValue = (_ ** (PlusCG (ConstCG _ _ (Plus c0 (Neg constValue))) e, ?MputNegConstantOnPlace_1))
putNegConstantOnPlace p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) constValue = 
	let (r_ihn ** (e_ihn, p_ihn)) = putNegConstantOnPlace p e constValue in
		(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, ?MputNegConstantOnPlace_2))
putNegConstantOnPlace p (PlusCG (NegCG (ConstCG _ _ c0)) e) constValue = (_ ** (PlusCG (ConstCG _ _ (Plus (Neg c0) (Neg constValue))) e, ?MputNegConstantOnPlace_3)) -- Perhaps useless because I think that NegCG (ConstCG c) is always ConstCG (Neg c) at this stage
putNegConstantOnPlace p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) constValue = 
    	let (r_ihn ** (e_ihn, p_ihn)) = putNegConstantOnPlace p e constValue in
		(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, ?MputNegConstantOnPlace_4))


-- FUNCTION WHICH REORGANIZE AN EXPRESSION	
-- -----------------------------------------

-- The general pattern is reorganize (Plus term exp) = putTermOnPlace (reorganize exp) term
reorganize : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))
reorganize p (PlusCG (VarCG p (RealVariable _ _ _ i0)) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize p e in
	let (r_add ** (e_add, p_add)) = putVarOnPlace p e_ihn (RealVariable _ _ _ i0) in
		(_ ** (e_add, ?Mreorganize_1))
reorganize p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize p e in
	let (r_add ** (e_add, p_add)) = putNegVarOnPlace p e_ihn (RealVariable _ _ _ i0) in
		(_ ** (e_add, ?Mreorganize_2))	
reorganize p (PlusCG (ConstCG _ _ c0) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize p e in
	let (r_add ** (e_add, p_add)) = putConstantOnPlace p e_ihn c0 in
		(_ ** (e_add, ?Mreorganize_3))	
reorganize p (PlusCG (NegCG (ConstCG _ _ c0)) e) = 
	let (r_ihn ** (e_ihn, p_ihn)) = reorganize p e in
	let (r_add ** (e_add, p_add)) = putNegConstantOnPlace p e_ihn c0 in
		(_ ** (e_add, ?Mreorganize_4))	
reorganize p e = (_ ** (e, refl))


-- SIMPLIFY BY DELETING TERMS AND THEIR SYMMETRICS	
-- ------------------------------------------------
		
simplifyAfterReorg : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))
simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i1))) e)) with (eq_dec_fin i0 i1)
	simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e)) | (Just refl) = 
		let (r_ihn ** (e_ihn, p_ihn)) = simplifyAfterReorg p e in
			(_ ** (e_ihn, ?MsimplifyAfterReorg_1))
	simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i1))) e)) | (Nothing) = 
		let (r_ihn ** (e_ihn, p_ihn)) = simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i1))) e) in
			(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) e_ihn, rewrite p_ihn in refl))
		
simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (PlusCG (VarCG p (RealVariable _ _ _ i1)) e)) with (eq_dec_fin i0 i1)
	simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (PlusCG (VarCG p (RealVariable _ _ _ i0)) e)) | (Just refl) = 
		let (r_ihn ** (e_ihn, p_ihn)) = simplifyAfterReorg p e in
			(_ ** (e_ihn, ?MsimplifyAfterReorg_2))
	simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (PlusCG (VarCG p (RealVariable _ _ _ i1)) e)) | (Nothing) = 	
		let (r_ihn ** (e_ihn, p_ihn)) = simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i1)) e) in
			(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) e_ihn, rewrite p_ihn in refl)) 
	
-- Any other case with the first two elements not simplifiable
simplifyAfterReorg p (PlusCG t1 (PlusCG t2 exp)) = 
	let (r_ihn ** (e_ihn, p_ihn)) = simplifyAfterReorg p (PlusCG t2 exp) in
		(_ ** (PlusCG t1 e_ihn, ?MsimplifyAfterReorg_3))

-- Just a plus with two terms
simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (NegCG (VarCG p (RealVariable _ _ _ i1)))) with (eq_dec_fin i0 i1)
	simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (NegCG (VarCG p (RealVariable _ _ _ i0)))) | (Just refl) =
		(_ ** (ConstCG _ _ Zero, ?MsimplifyAfterReorg_4))
	simplifyAfterReorg p (PlusCG (VarCG p (RealVariable _ _ _ i0)) (NegCG (VarCG p (RealVariable _ _ _ i1)))) | (Nothing) =
		(_ ** (PlusCG (VarCG p (RealVariable _ _ _ i0)) (NegCG (VarCG p (RealVariable _ _ _ i1))), refl))
		
simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (VarCG p (RealVariable _ _ _ i1))) with (eq_dec_fin i0 i1)
	simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (VarCG p (RealVariable _ _ _ i0))) | (Just refl) =
		(_ ** (ConstCG _ _ Zero, ?MsimplifyAfterReorg_5))
	simplifyAfterReorg p (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (VarCG p (RealVariable _ _ _ i1))) | (Nothing) =
		(_ ** (PlusCG (NegCG (VarCG p (RealVariable _ _ _ i0))) (VarCG p (RealVariable _ _ _ i1)), refl))
		
--Anything else simply gives the same value
simplifyAfterReorg p e = (_ ** (e, refl))



simplifyAfterReorg_fix : {c:Type} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))
simplifyAfterReorg_fix p e = 
	let (r_1 ** (e_1, p_1)) = simplifyAfterReorg p e in
		case exprCG_eq p _ e e_1 of -- Look for syntactical equality (ie, if we have done some simplification in the last passe)!
			Just pr => (r_1 ** (e_1, p_1)) -- Previous and current term are the same : we stop here
			Nothing => let (r_ih1 ** (e_ih1, p_ih1)) = simplifyAfterReorg_fix p e_1 in -- We do another passe
							(r_ih1 ** (e_ih1, ?MsimplifyAfterReorg_fix_1))


commutativeGroupReduce : (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> (ExprCG p g c1) -> (c2 ** (ExprCG p g c2, c1=c2))
commutativeGroupReduce p e =
	let e_1 = commutativeGroup_to_group e in
	let (r_2 ** (e_2, p_2)) = groupReduce _ e_1 in
	let e_3 = group_to_commutativeGroup p e_2 in
        let (r_4 ** (e_4, p_4)) = reorganize p e_3 in
        let (r_5 ** (e_5, p_5)) = simplifyAfterReorg_fix p e_3 in
		(_ ** (e_4, ?McommutativeGroupReduce_1))

		
buildProofCommutativeGroup : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> {g:Vect n c} -> {x : c} -> {y : c} -> {c1:c} -> {c2:c} -> (ExprCG p g c1) -> (ExprCG p g c2) -> (x = c1) -> (y = c2) -> (Maybe (x = y))
buildProofCommutativeGroup p e1 e2 lp rp with (exprCG_eq p _ e1 e2)
	buildProofCommutativeGroup p e1 e1 lp rp | Just refl = ?MbuildProofCommutativeGroup
	buildProofCommutativeGroup p e1 e2 lp rp | Nothing = Nothing

		
commutativeGroupDecideEq : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> {g:Vect n c} -> {x : c} -> {y : c} -> (ExprCG p g x) -> (ExprCG p g y) -> Maybe (x = y)
-- e1 is the left side, e2 is the right side
commutativeGroupDecideEq p e1 e2 =
	let (r_e1 ** (e_e1, p_e1)) = commutativeGroupReduce p e1 in
	let (r_e2 ** (e_e2, p_e2)) = commutativeGroupReduce p e2 in
		buildProofCommutativeGroup p e_e1 e_e2 p_e1 p_e2	
		
		
---------- Proofs ----------
commutativeGroup_reduce.Massoc_and_commute_1 = proof
  intros
  rewrite (sym aux)
  mrefine Plus_comm
  
commutativeGroup_reduce.Massoc_commute_and_assoc_1 = proof
  intros
  rewrite (sym aux)
  rewrite (sym aux2)
  rewrite (sym aux3)
  exact refl  

commutativeGroup_reduce.Massoc_and_neutral_1 = proof
  intros
  rewrite (sym aux)
  rewrite (sym aux2)
  rewrite (sym aux3)
  exact refl 
  
commutativeGroup_reduce.Massoc_and_neutral_bis_1 = proof
  intros
  rewrite (sym aux)
  rewrite (sym aux2)
  rewrite (sym aux3)
  exact refl  
    
commutativeGroup_reduce.MputVarOnPlace_1 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc
  
commutativeGroup_reduce.MputVarOnPlace_2 = proof
  intros
  mrefine Plus_comm 

commutativeGroup_reduce.MputVarOnPlace_3 = proof
  intros
  mrefine Plus_comm 
  
commutativeGroup_reduce.MputVarOnPlace_4 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc
  
commutativeGroup_reduce.MputVarOnPlace_5 = proof
  intros
  mrefine Plus_comm 

commutativeGroup_reduce.MputVarOnPlace_6 = proof
  intros
  mrefine Plus_comm 
  
commutativeGroup_reduce.MputConstantOnPlace_1 = proof
  intros
  mrefine assoc_commute_and_assoc 
  
commutativeGroup_reduce.MputConstantOnPlace_2 = proof
  intros
  rewrite p_ihn 
  mrefine  Plus_assoc
  
commutativeGroup_reduce.MputConstantOnPlace_3 = proof
  intros
  mrefine assoc_commute_and_assoc    

commutativeGroup_reduce.MputConstantOnPlace_4 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc 

commutativeGroup_reduce.MputNegVarOnPlace_1 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc 

commutativeGroup_reduce.MputNegVarOnPlace_2 = proof
  intros
  mrefine Plus_comm 

commutativeGroup_reduce.MputNegVarOnPlace_3 = proof
  intros
  mrefine Plus_comm 
  
commutativeGroup_reduce.MputNegVarOnPlace_4 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc
  
commutativeGroup_reduce.MputNegVarOnPlace_5 = proof
  intros
  mrefine Plus_comm 

commutativeGroup_reduce.MputNegVarOnPlace_6 = proof
  intros
  mrefine Plus_comm  
  
commutativeGroup_reduce.MputNegConstantOnPlace_1 = proof
  intros
  mrefine assoc_commute_and_assoc 

commutativeGroup_reduce.MputNegConstantOnPlace_2 = proof
  intros
  rewrite p_ihn 
  mrefine  Plus_assoc 

commutativeGroup_reduce.MputNegConstantOnPlace_3 = proof
  intros
  mrefine assoc_commute_and_assoc 
  
commutativeGroup_reduce.MputNegConstantOnPlace_4 = proof
  intros
  rewrite p_ihn 
  mrefine Plus_assoc 

commutativeGroup_reduce.Mreorganize_1 = proof
  intros
  rewrite p_add 
  rewrite p_ihn 
  mrefine Plus_comm 
  
commutativeGroup_reduce.Mreorganize_2 = proof
  intros
  rewrite p_add 
  rewrite p_ihn 
  mrefine Plus_comm 

commutativeGroup_reduce.Mreorganize_3 = proof
  intros
  rewrite p_add
  rewrite p_ihn 
  mrefine Plus_comm  
  
commutativeGroup_reduce.Mreorganize_4 = proof
  intros
  rewrite p_add 
  rewrite p_ihn 
  mrefine Plus_comm 

commutativeGroup_reduce.MsimplifyAfterReorg_1 = proof
  intros
  rewrite p_ihn 
  mrefine assoc_and_neutral 
    
commutativeGroup_reduce.MsimplifyAfterReorg_2 = proof
  intros
  rewrite p_ihn 
  mrefine assoc_and_neutral_bis  
  
commutativeGroup_reduce.MsimplifyAfterReorg_3 = proof
  intros
  rewrite p_ihn 
  exact refl
  
commutativeGroup_reduce.MsimplifyAfterReorg_4 = proof
  intros
  rewrite (sym (left (Plus_inverse (index_reverse i0 g))))
  exact refl
  
commutativeGroup_reduce.MsimplifyAfterReorg_5 = proof
  intros
  rewrite (sym (right (Plus_inverse (index_reverse i0 g))))
  exact refl
  
commutativeGroup_reduce.MsimplifyAfterReorg_fix_1 = proof
  intros
  rewrite (sym p_1)
  rewrite (sym p_ih1)
  exact refl  

commutativeGroup_reduce.McommutativeGroupReduce_1 = proof
  intros
  rewrite p_4
  rewrite p_2
  exact refl  
  
commutativeGroup_reduce.MbuildProofCommutativeGroup = proof
  intros
  refine Just
  rewrite (sym lp)
  rewrite (sym rp)
  exact refl  
  





  
  