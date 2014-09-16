-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File dataTypes.idr
-- Groups, commutative groups, rings, commutative rings, and corresponding reflected terms
-------------------------------------------------------------------

module Solver.dataTypes


%default total


eq_dec_fin : {n:Nat} -> (i:Fin n) -> (j:Fin n) -> (Maybe (i=j))
eq_dec_fin fZ fZ = Just refl
eq_dec_fin fZ (fS j') = Nothing
eq_dec_fin (fS i') fZ = Nothing
eq_dec_fin (fS i') (fS j') with (eq_dec_fin i' j')
	eq_dec_fin (fS i') (fS i') | (Just refl) = Just refl
	eq_dec_fin (fS i') (fS j') | Nothing = Nothing


-- No longer needed : we're back to the orignal order
{-
index_reverse : {a:Type} -> {n:Nat} -> (Fin n) -> (Vect n a) -> a
index_reverse j g = index j (reverse g)
-}




class Set c where
    -- We just requires a (weak) decidable relation over the elements of the "set"
    -- which means that two elements are EQuivalent.
    -- (Note : that's no longer an equality, but just a relation, since that's more general)
    set_eq_undec : (x:c) -> (y:c) -> Type -- The (undecidable) relation
    set_eq : (x:c) -> (y:c) -> Maybe(set_eq_undec x y) -- The "weak" decidable relation (week because only gives a proof when it holds)
    
    -- The binary relation should be reflexive
    set_eq_undec_refl : (x:c) -> set_eq_undec x x
        
        
        
class Set c => Magma c where
    Plus : c -> c -> c -- A magma just has a plus operation, and we have no properties about it
    -- Plus should preserve the equivalence defined at the Set level 
    Plus_preserves_equiv : {c1:c} -> {c2:c} -> {c1':c} -> {c2':c} -> (set_eq_undec c1 c1') -> (set_eq_undec c2 c2') -> (set_eq_undec (Plus c1 c2) (Plus c1' c2'))

class Magma c => SemiGroup c where
    Plus_assoc : (c1:c) -> (c2:c) -> (c3:c) -> (Plus (Plus c1 c2) c3 = Plus c1 (Plus c2 c3))

class SemiGroup c => Monoid c where
    Zero : c
    
    Plus_neutral_1 : (c1:c) -> (set_eq_undec (Plus Zero c1) c1)    
    Plus_neutral_2 : (c1:c) -> (set_eq_undec (Plus c1 Zero) c1)

-- NEW : That's something usefull for Nat for example, since we don't have negatives numbers
class dataTypes.Monoid c => CommutativeMonoid c where
    Plus_comm' : (c1:c) -> (c2:c) -> (set_eq_undec (Plus c1 c2) (Plus c2 c1))


-- We define the fact to have a symmetric as a notion on a monoid. And this will help to define the property of being a group
hasSymmetric : (c:Type) -> (p:dataTypes.Monoid c) -> c -> c -> Type
hasSymmetric c p a b = (set_eq_undec (Plus a b) Zero, set_eq_undec (Plus b a) (the c Zero))    
    
-- An abstract group
--%logging 1    
class dataTypes.Monoid c => dataTypes.Group c where
    Neg : c -> c
    Minus : c -> c -> c 
    
    -- Neg should preserve the quivalence
    Neg_preserves_equiv : {c1:c} -> {c2:c} -> (set_eq_undec c1 c2) -> (set_eq_undec (Neg c1) (Neg c2))

    Minus_simpl : (c1:c) -> (c2:c) -> set_eq_undec (Minus c1 c2) (Plus c1 (Neg c2)) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse : (c1:c) -> hasSymmetric c (%instance) c1 (Neg c1) -- Every element 'x' has a symmetric which is (Neg x)
--%logging 0



-- We only ask the "user" for the proof that Neg preserves the quivalence, and we automatically deduce that Minus also preserves the equivalence (since Minus is defined by using Neg)
Minus_preserves_equiv : {c:Type} -> (dataTypes.Group c)
                        -> ((c1:c) -> (c2:c) -> (c1':c) -> (c2':c) -> (set_eq_undec c1 c1') -> (set_eq_undec c2 c2') -> (set_eq_undec (Minus c1 c2) (Minus c1' c2')))
Minus_preserves_equiv ggj = ?MAAAAA



-- An abstract commutative group
class dataTypes.Group c => CommutativeGroup c where
    Plus_comm : (c1:c) -> (c2:c) -> (set_eq_undec (Plus c1 c2) (Plus c2 c1))
    


-- An abstract ring    
class CommutativeGroup c => Ring c where
    One : c
    Mult : c -> c -> c
    
    Mult_assoc : (c1:c) -> (c2:c) -> (c3:c) -> set_eq_undec (Mult (Mult c1 c2) c3) (Mult c1 (Mult c2 c3))
    Mult_dist : (c1:c) -> (c2:c) -> (c3:c) -> set_eq_undec (Mult c1 (Plus c2 c3)) (Plus (Mult c1 c2) (Mult c1 c3))
    Mult_dist_2 : (c1:c) -> (c2:c) -> (c3:c) -> set_eq_undec (Mult (Plus c1 c2) c3) (Plus (Mult c1 c3) (Mult c2 c3)) -- Needed because we don't have commutativity of * in a ring
    Mult_neutral : (c1:c) -> ((set_eq_undec (Mult c1 One) (Mult One c1)), (set_eq_undec (Mult One c1) c1))

-- An abstract commutative ring    
class dataTypes.Ring c => CommutativeRing c where
    Mult_comm : (c1:c) -> (c2:c) -> (set_eq_undec (Mult c1 c2) (Mult c2 c1))

------------------------------
-- Functions of conversion ---
------------------------------
-- Magma -> Set
magma_to_set_class : (Magma c) -> (Set c)
magma_to_set_class x = (%instance)

-- SemiGroup -> Magma
semiGroup_to_magma_class : (SemiGroup c) -> (Magma c)
semiGroup_to_magma_class p = (%instance)

-- Monoid -> SemiGroup
monoid_to_semiGroup_class : (dataTypes.Monoid c) -> (SemiGroup c)
monoid_to_semiGroup_class p = (%instance)

-- Group -> Monoid (needed for tools.idr, for unicity of symmetric)
group_to_monoid_class : (dataTypes.Group c) -> (dataTypes.Monoid c)
group_to_monoid_class p = (%instance)

-- CommutativeMonoid -> Monoid
-- NEW
commutativeMonoid_to_monoid_class : (CommutativeMonoid c) -> (dataTypes.Monoid c)
commutativeMonoid_to_monoid_class p = (%instance)

-- CommutativeGroup -> Group
commutativeGroup_to_group_class : (CommutativeGroup c) -> (dataTypes.Group c)
commutativeGroup_to_group_class p = (%instance)

-- CommutativeRing -> Ring
cr_to_r_class : CommutativeRing c -> dataTypes.Ring c
cr_to_r_class p = %instance -- finds the instance automatically from p


-- -----------------------------------------
-- (getters) Equality as elements of set ---
--------------------------------------------
set_eq_as_elem_of_set : (Set c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
set_eq_as_elem_of_set x = set_eq

-- Magma
magma_eq_as_elem_of_set : (Magma c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
magma_eq_as_elem_of_set x = set_eq_as_elem_of_set (magma_to_set_class x)

-- Semi group
semiGroup_to_set : (SemiGroup c) -> (Set c)
semiGroup_to_set x = (%instance)

semiGroup_eq_as_elem_of_set : (SemiGroup c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
semiGroup_eq_as_elem_of_set x = set_eq_as_elem_of_set (semiGroup_to_set x)

-- Monoid
monoid_to_set : (dataTypes.Monoid c) -> (Set c)
monoid_to_set x = (%instance)

monoid_eq_as_elem_of_set : (dataTypes.Monoid c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
monoid_eq_as_elem_of_set x = set_eq_as_elem_of_set (monoid_to_set x)


-- Commutative Monoid
commutativeMonoid_to_set : (CommutativeMonoid c) -> (Set c)
commutativeMonoid_to_set x = (%instance)

commutativeMonoid_eq_as_elem_of_set : (CommutativeMonoid c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
commutativeMonoid_eq_as_elem_of_set x = set_eq_as_elem_of_set (commutativeMonoid_to_set x)


-- Group
group_to_set : (dataTypes.Group c) -> (Set c)
group_to_set x = (%instance)

group_eq_as_elem_of_set : (dataTypes.Group c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
group_eq_as_elem_of_set x = set_eq_as_elem_of_set (group_to_set x)


-- Commutative Group
commutativeGroup_to_set : (CommutativeGroup c) -> (Set c)
commutativeGroup_to_set x = (%instance)

commutativeGroup_eq_as_elem_of_set : (CommutativeGroup c) -> ((x:c) -> (y:c) -> Maybe(set_eq_undec x y))
commutativeGroup_eq_as_elem_of_set x = set_eq_as_elem_of_set (commutativeGroup_to_set x)

-- ----------------------------
-- ---- Reflected Terms ---- --
-- ----------------------------

-- NEW : We require 'c' to be "at least" a set, instead of just asking for the "equivalence relation" (which was previously an equality)
data Variable : {c:Type} -> (c_set: Set c) -> {n:Nat} -> (neg:c->c) -> (Vect n c) -> c -> Type where
    RealVariable : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> Variable c_set neg g (index i g) -- neg is not used here
    EncodingGroupTerm_var : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> Variable c_set neg g (neg (index i g)) -- neg is used here
    --EncodingGroupTerm_const : {c:Type} -> {n:Nat} -> (c_equal:(c1:c)->(c2:c)->Maybe(c1=c2)) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> VariableA c_equal neg g (neg c1) -- and here
    -- Encoding fot constants is no longer needed since we can just put a constant of value (Neg c) : we can still use Neg during the conversion because we still have a Group, even though we convert to a Monoid !

Variable_eq : {c:Type} -> {c_set:Set c} -> {n:Nat} -> {c1:c} -> {c2:c} -> (neg:c->c) -> (g:Vect n c) -> (v1:Variable c_set neg g c1) -> (v2:Variable c_set neg g c2) -> Maybe (v1=v2)
Variable_eq neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) with (decEq i1 i2)
    Variable_eq neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i1) | (Yes refl) = Just refl
    Variable_eq neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) | _ = Nothing
Variable_eq neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) with (decEq i1 i2) 
    Variable_eq neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i1) | (Yes refl) = Just refl
    Variable_eq neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) | _ = Nothing
--Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) with (c_equal c1 c2)
--    Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c1) | (Just refl) = Just refl
--    Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) | _ = Nothing
Variable_eq neg g _ _ = Nothing
   
      
print_Variable : {c1:c} -> {c_set:Set c} -> (f:c -> String) -> {neg:c->c} -> {g:Vect n c} -> Variable c_set neg g c1 -> String
print_Variable f (RealVariable _ _ _ i) = "Var " ++ (show (cast i))
print_Variable f (EncodingGroupTerm_var _ _ _ i) = "[Encoding_var (" ++ (show(cast i)) ++ ") ]"
--print_VariableA f (EncodingGroupTerm_const _ _ _ c1) = "[Encoding_const (" ++ (f c1) ++ ") ]"



-- Reflected terms in a magma
data ExprMa : {c:Type} -> {n:Nat} -> Magma c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstMa : {c:Type} -> {n:Nat} -> (p : Magma c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c)  -> ExprMa p neg g c1 
    PlusMa : {c:Type} -> {n:Nat} -> {p : Magma c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMa p neg g c1 -> ExprMa p neg g c2 -> ExprMa p neg g (Plus c1 c2) 
    VarMa : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> Variable (magma_to_set_class p) neg g c1 -> ExprMa p neg g c1

-- I wanted it to only produce a bool, which tells if the two expression are "syntactically equivalent" (that mean equal, appart for the constants where we only ask for the equivalence)
-- BUT, we will need to prove a lemma which says that if two expressions are "syntactically equivalent" then (c_eq c1 c2). So instead, we directly produce a Maybe(c_eq c1 c2)
exprMa_eq : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMa p neg g c1) -> (e2:ExprMa p neg g c2) -> Maybe(set_eq_undec c1 c2)
exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ x' y') with (exprMa_eq p neg g x x', exprMa_eq p neg g y y')
    exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ _ _) | _ = Nothing
exprMa_eq p neg g (VarMa _ _ {c1=c1} v1) (VarMa _ _ v2) with (Variable_eq neg g v1 v2) 
    exprMa_eq p neg g (VarMa _ _ {c1=c1} v1) (VarMa _ _ v1) | (Just refl) = Just (set_eq_undec_refl c1)
    exprMa_eq p neg g (VarMa _ _ v1) (VarMa _ _ v2) | _ = Nothing
exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const2) with ((magma_eq_as_elem_of_set p) const1 const2)
    exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const1) | (Just const_eq) = Just const_eq
    exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const2) | _ = Nothing
exprMa_eq p neg g e1 e2 = Nothing



-- Reflected terms in semigroup
data ExprSG : {c:Type} -> {n:Nat} -> SemiGroup c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstSG : {c:Type} -> {n:Nat} -> (p : SemiGroup c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> ExprSG p neg g c1
    PlusSG : {c:Type} -> {n:Nat} -> {p : SemiGroup c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprSG p neg g c1 -> ExprSG p neg g c2 -> ExprSG p neg g (Plus c1 c2)
    VarSG : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> Variable (semiGroup_to_set p) neg g c1 -> ExprSG p neg g c1

exprSG_eq : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprSG p neg g c1) -> (e2:ExprSG p neg g c2) -> Maybe(set_eq_undec c1 c2)
exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ x' y') with (exprSG_eq p neg g x x', exprSG_eq p neg g y y')
    exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ _ _) | _ = Nothing
exprSG_eq p neg g (VarSG _ _ {c1=c1} v1) (VarSG _ _ v2) with (Variable_eq neg g v1 v2)
    exprSG_eq p neg g (VarSG _ _ {c1=c1} v1) (VarSG _ _ v1) | (Just refl) = Just (set_eq_undec_refl c1)
    exprSG_eq p neg g (VarSG _ _ v1) (VarSG _ _ v2) | _ = Nothing
exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const2) with ((semiGroup_eq_as_elem_of_set p) const1 const2)
    exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const1) | (Just const_eq) = Just const_eq
    exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const2) | _ = Nothing
exprSG_eq p neg g _ _ = Nothing


print_ExprSG : {c:Type} -> {n:Nat} -> {p:SemiGroup c} -> {r1:c} -> (c -> String) -> {neg:c->c} -> {g:Vect n c} -> ExprSG p neg g r1 -> String
print_ExprSG c_print (ConstSG _ _ _ const) = c_print const
print_ExprSG c_print (PlusSG _ e1 e2) = "(" ++ (print_ExprSG c_print e1) ++ ") + (" ++ (print_ExprSG c_print e2) ++ ")"
print_ExprSG c_print (VarSG _ _ v) = print_Variable c_print v


-- Reflected terms in a monoid
data ExprMo : {c:Type} -> {n:Nat} -> dataTypes.Monoid c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> ExprMo p neg g c1
    PlusMo : {c:Type} -> {n:Nat} -> {p : dataTypes.Monoid c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMo p neg g c1 -> ExprMo p neg g c2 -> ExprMo p neg g (Plus c1 c2)
    VarMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> Variable (monoid_to_set p) neg g c1 -> ExprMo p neg g c1

exprMo_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Monoid c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMo p neg g c1) -> (e2:ExprMo p neg g c2) -> Maybe(set_eq_undec c1 c2)
exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ x' y') with (exprMo_eq p neg g x x', exprMo_eq p neg g y y')
    exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ _ _) | _ = Nothing
exprMo_eq p neg g (VarMo _ _ {c1=c1} v1) (VarMo _ _ v2) with (Variable_eq neg g v1 v2)
    exprMo_eq p neg g (VarMo _ _ {c1=c1} v1) (VarMo _ _ v1) | (Just refl) = Just (set_eq_undec_refl c1)
    exprMo_eq p neg g (VarMo _ _ v1) (VarMo _ _ v2) | _ = Nothing
exprMo_eq p neg g (ConstMo _ _ _ const1) (ConstMo _ _ _ const2) with ((monoid_eq_as_elem_of_set p) const1 const2)
    exprMo_eq p neg g (ConstMo _ _ _  const1) (ConstMo _ _ _ const1) | (Just const_eq) = Just const_eq
    exprMo_eq p neg g (ConstMo _ _ _ const1) (ConstMo _ _ _ const2) | _ = Nothing
exprMo_eq p neg g _ _  = Nothing


-- Reflected terms in a commutative monoid
data ExprCM : {c:Type} -> {n:Nat} -> (CommutativeMonoid c) -> (Vect n c) -> c -> Type where
    ConstCM : {c:Type} -> {n:Nat} -> (p : CommutativeMonoid c) -> (g:Vect n c) -> (c1:c) -> ExprCM p g c1
    PlusCM : {c:Type} -> {n:Nat} -> {p : CommutativeMonoid c} -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprCM p g c1 -> ExprCM p g c2 -> ExprCM p g (Plus c1 c2)
    VarCM : {c:Type} -> {n:Nat} -> (p : CommutativeMonoid c) -> {g:Vect n c} -> (i:Fin n) -> ExprCM p g (index i g)

exprCM_eq : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprCM p g c1) -> (e2:ExprCM p g c2) -> Maybe(set_eq_undec c1 c2)
exprCM_eq p g (PlusCM x y) (PlusCM x' y') with (exprCM_eq p g x x', exprCM_eq p g y y')
    exprCM_eq p g (PlusCM x y) (PlusCM _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprCM_eq p g (PlusCM x y) (PlusCM _ _) | _ = Nothing
exprCM_eq p g (VarCM _ i1) (VarCM _ i2) with (eq_dec_fin i1 i2)
    exprCM_eq p g (VarCM _ i1) (VarCM _ i1) | (Just refl) = Just (set_eq_undec_refl (index i1 g))
    exprCM_eq p g (VarCM _ i1) (VarCM _ i2) | _ = Nothing
exprCM_eq p g (ConstCM _ _ const1) (ConstCM _ _ const2) with ((commutativeMonoid_eq_as_elem_of_set p) const1 const2)
    exprCM_eq p g (ConstCM _ _  const1) (ConstCM _ _ const1) | (Just const_eq) = Just ?MCCC
    exprCM_eq p g (ConstCM _ _ const1) (ConstCM _ _ const2) | _ = Nothing
exprCM_eq p g _ _  = Nothing



-- Reflected terms in a group  
data ExprG :  {c:Type} -> {n:Nat} -> dataTypes.Group c -> (Vect n c) -> c -> Type where
    ConstG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> (g:Vect n c) -> (c1:c) -> ExprG p g c1
    PlusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprG p g c1 -> ExprG p g c2 -> ExprG p g (Plus c1 c2)
    MinusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprG p g c1 -> ExprG p g c2 -> ExprG p g (Minus c1 c2)
    NegG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> {g:Vect n c} -> {c1:c} -> ExprG p g c1 -> ExprG p g (Neg c1)
    VarG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> {g:Vect n c} -> {c1:c} -> Variable (group_to_set p) Neg g c1 -> ExprG p g c1


exprG_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprG p g c1) -> (e2:ExprG p g c2) -> Maybe(set_eq_undec c1 c2)
exprG_eq p g (PlusG x y) (PlusG x' y') with (exprG_eq p g x x', exprG_eq p g y y')
        exprG_eq p g (PlusG x y) (PlusG _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
        exprG_eq p g (PlusG x y) (PlusG _ _) | _ = Nothing
exprG_eq p g (VarG _ {c1=c1} v1) (VarG _ v2) with (Variable_eq Neg g v1 v2)
        exprG_eq p g (VarG _ {c1=c1} v1) (VarG _ v1) | (Just refl) = Just (set_eq_undec_refl c1)
        exprG_eq p g (VarG _ v1) (VarG _ v2) | _ = Nothing
exprG_eq p g (ConstG _ _ const1) (ConstG _ _ const2) with ((group_eq_as_elem_of_set p) const1 const2)
        exprG_eq p g (ConstG _ _ const1) (ConstG _ _ const1) | (Just const_eq) = Just ?MDDDDD
        exprG_eq p g (ConstG _ _ const1) (ConstG _ _ const2) | _ = Nothing
exprG_eq p g (NegG e1) (NegG e2) with (exprG_eq p g e1 e2)
        exprG_eq p g (NegG e1) (NegG _) | (Just p1) = Just ?MX
        exprG_eq p g (NegG e1) (NegG e2) | _ = Nothing
exprG_eq p g (MinusG x y) (MinusG x' y') with (exprG_eq p g x x', exprG_eq p g y y')
        exprG_eq p g (MinusG x y) (MinusG _ _) | (Just p1, Just p2) = Just ?MY
        exprG_eq p g (MinusG x y) (MinusG _ _) | _ = Nothing	
exprG_eq p g _ _  = Nothing
    
    
print_ExprG : {c:Type} -> {n:Nat} -> {p:dataTypes.Group c} -> {r1:c} -> (c -> String) -> {g:Vect n c} -> ExprG p g r1 -> String
print_ExprG c_print (ConstG _ _ const) = c_print const
print_ExprG c_print (PlusG e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") + (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (MinusG e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") - (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (VarG _ v) = print_Variable c_print v
print_ExprG c_print (NegG e) = "(-" ++ (print_ExprG c_print e) ++ ")"


-- Reflected terms in a commutative group       
data ExprCG : {c:Type} -> {n:Nat} -> CommutativeGroup c -> (Vect n c) -> c -> Type where
    ConstCG : {c:Type} -> {n:Nat} -> (p:CommutativeGroup c) -> (g:Vect n c) -> (c1:c) -> ExprCG p g c1
    PlusCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprCG p g c1 -> ExprCG p g c2 -> ExprCG p g (Plus c1 c2)
    MinusCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprCG p g c1 -> ExprCG p g c2 -> ExprCG p g (Minus c1 c2)
    NegCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> {g:Vect n c} -> {c1:c} -> ExprCG p g c1 -> ExprCG p g (Neg c1)
    VarCG : {c:Type} -> {n:Nat} -> (p:CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> Variable (commutativeGroup_to_set p) Neg g c1 -> ExprCG p g c1
    
    
exprCG_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprCG p g c1) -> (e2:ExprCG p g c2) -> (Maybe (c1=c2))
exprCG_eq p g (PlusCG x y) (PlusCG x' y') with (exprCG_eq p g x x', exprCG_eq p g y y')
        exprG_eq p g (PlusCG x y) (PlusCG x y) | (Just refl, Just refl) = Just refl
        exprG_eq p g (PlusCG x y) (PlusCG _ _) | _ = Nothing
exprCG_eq p g (VarCG _ v1) (VarCG _ v2) with (Variable_eq Neg g v1 v2)
        exprG_eq p g (VarCG _ v1) (VarCG _ v1) | (Just refl) = Just refl
        exprG_eq p g (VarCG _ v1) (VarCG _ v2) | _ = Nothing
exprCG_eq p g (ConstCG _ _ const1) (ConstCG _ _ const2) with ((commutativeGroup_eq_as_elem_of_set p) const1 const2)
        exprG_eq p g (ConstCG _ _ const1) (ConstCG _ _ const1) | (Just const_eq) = Just ?MEEEEE
        exprG_eq p g (ConstCG _ _ const1) (ConstCG _ _ const2) | _ = Nothing
exprCG_eq p g (NegCG e1) (NegCG e2) with (exprCG_eq p g e1 e2)
        exprG_eq p g (NegCG e1) (NegCG e1) | (Just refl) = Just refl
        exprG_eq p g (NegCG e1) (NegCG e2) | _ = Nothing
exprCG_eq p g (MinusCG x y) (MinusCG x' y') with (exprCG_eq p g x x', exprCG_eq p g y y')
        exprG_eq p g (MinusCG x y) (MinusCG x y) | (Just refl, Just refl) = Just refl
        exprG_eq p g (MinusCG x y) (MinusCG _ _) | _ = Nothing	
exprCG_eq p g _ _  = Nothing


print_ExprCG : {c:Type} -> {n:Nat} -> {p:dataTypes.CommutativeGroup c} -> {r1:c} -> (c -> String) -> {g:Vect n c} -> ExprCG p g r1 -> String
print_ExprCG c_print (ConstCG _ _ const) = c_print const
print_ExprCG c_print (PlusCG e1 e2) = "(" ++ (print_ExprCG c_print e1) ++ ") + (" ++ (print_ExprCG c_print e2) ++ ")"
print_ExprCG c_print (MinusCG e1 e2) = "(" ++ (print_ExprCG c_print e1) ++ ") --- (" ++ (print_ExprCG c_print e2) ++ ")"
print_ExprCG c_print (VarCG _ v) = print_Variable c_print v
print_ExprCG c_print (NegCG e) = "(-" ++ (print_ExprCG c_print e) ++ ")"

    
{-
-- Reflected terms in a ring       
        data ExprR : dataTypes.Ring c -> (Vect n c) -> c -> Type where
            ConstR : (p:dataTypes.Ring c) -> (c1:c) -> ExprR p g c1  
            --ZeroR : ExprR p g Zero
            --OneR : ExprR p g One
            PlusR : {p:dataTypes.Ring c} -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Plus c1 c2)
            MultR : {p:dataTypes.Ring c} -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Mult c1 c2)
            VarR : (p:dataTypes.Ring c) -> {c1:c} -> VariableA g c1 -> ExprR p g c1

        print_ExprR : {p:dataTypes.Ring c} -> {r1:c} -> (c -> String) -> ExprR p g r1 -> String
        print_ExprR c_print (ConstR p const) = c_print const
        print_ExprR c_print (PlusR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") + (" ++ (print_ExprR c_print e2) ++ ")"
        print_ExprR c_print (MultR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") * (" ++ (print_ExprR c_print e2) ++ ")"
        print_ExprR c_print (VarR p v) = print_VariableA c_print v
      
-- Reflected terms in a commutative ring   
        data ExprCR : CommutativeRing c -> (Vect n c) -> c -> Type where
            ConstCR : (p:CommutativeRing c) -> (c1:c) -> ExprCR p g c1   
            --ZeroCR : ExprCR p g Zero
            --OneCR : ExprCR p g One
            PlusCR : {p:CommutativeRing c} -> {c1:c} -> {c2:c} -> ExprCR p g c1 -> ExprCR p g c2 -> ExprCR p g (Plus c1 c2)
            MultCR : {p:CommutativeRing c} -> {c1:c} -> {c2:c} -> ExprCR p g c1 -> ExprCR p g c2 -> ExprCR p g (Mult c1 c2)
            VarCR : (p:CommutativeRing c) -> {c1:c} -> VariableA g c1 -> ExprCR p g c1
-}


-- ----------------------------------------
-- ---- Conversion of encoded terms ---- --
-- ----------------------------------------

-- SemiGroup -> Magma
semiGroup_to_magma : {c:Type} -> {n:Nat} -> {p:SemiGroup c} -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> ExprSG p neg g c1 -> ExprMa (semiGroup_to_magma_class p) neg g c1
semiGroup_to_magma (ConstSG p _ _ cst) = ConstMa (semiGroup_to_magma_class p) _ _ cst
semiGroup_to_magma (PlusSG _ e1 e2) = PlusMa _ (semiGroup_to_magma e1) (semiGroup_to_magma e2)
semiGroup_to_magma (VarSG p _ v) = VarMa (semiGroup_to_magma_class p) _ v

magma_to_semiGroup : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> ExprMa (semiGroup_to_magma_class p) neg g c1 -> ExprSG p neg g c1
magma_to_semiGroup p (ConstMa _ _ _ cst) = ConstSG p _ _ cst
magma_to_semiGroup p (PlusMa _ e1 e2) = PlusSG _ (magma_to_semiGroup p e1) (magma_to_semiGroup p e2)
magma_to_semiGroup p (VarMa _ _ v) = VarSG p _ v


-- Monoid -> SemiGroup
monoid_to_semiGroup : {c:Type} -> {n:Nat} -> {p:dataTypes.Monoid c} -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> ExprMo p neg g c1 -> ExprSG (monoid_to_semiGroup_class p) neg g c1
monoid_to_semiGroup (ConstMo p _ _ cst) = ConstSG (monoid_to_semiGroup_class p) _ _ cst
monoid_to_semiGroup (PlusMo _ e1 e2) = PlusSG _ (monoid_to_semiGroup e1) (monoid_to_semiGroup e2)
monoid_to_semiGroup (VarMo p _ v) = VarSG (monoid_to_semiGroup_class p) _ v

semiGroup_to_monoid : {c:Type} -> {n:Nat} -> (p:dataTypes.Monoid c) -> {neg:c->c} -> {g:Vect n c} -> {c1:c} -> ExprSG (monoid_to_semiGroup_class p) neg g c1 -> ExprMo p neg g c1
semiGroup_to_monoid p (ConstSG _ _ _ cst) = ConstMo p _ _ cst
semiGroup_to_monoid p (PlusSG _ e1 e2) = PlusMo _ (semiGroup_to_monoid p e1) (semiGroup_to_monoid p e2)
semiGroup_to_monoid p (VarSG _ _ v) = VarMo p _ v


-- CommutativeMonoid -> Monoid
-- NEW
commutativeMonoid_to_monoid : {c:Type} -> {n:Nat} -> {p:CommutativeMonoid c} -> {g:Vect n c} -> {c1:c} -> ExprCM p g c1 -> ExprMo (commutativeMonoid_to_monoid_class p) (\x => x) g c1 -- there is no negations to encode, that's why we use the identity function here
commutativeMonoid_to_monoid (ConstCM p _ cst) = ConstMo (commutativeMonoid_to_monoid_class p) _ _ cst
commutativeMonoid_to_monoid (PlusCM e1 e2) = PlusMo _ (commutativeMonoid_to_monoid e1) (commutativeMonoid_to_monoid e2)
commutativeMonoid_to_monoid (VarCM p v) = VarMo (commutativeMonoid_to_monoid_class p) _ (RealVariable _ (\x => x) _ v)

monoid_to_commutativeMonoid : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {g:Vect n c} -> {c1:c} -> ExprMo (commutativeMonoid_to_monoid_class p) (\x => x) g c1 -> ExprCM p g c1 -- we know that no negations have been encoded
monoid_to_commutativeMonoid p (ConstMo _ _ _ cst) = (ConstCM p _ cst)
monoid_to_commutativeMonoid p (PlusMo _ e1 e2) = PlusCM (monoid_to_commutativeMonoid p e1) (monoid_to_commutativeMonoid p e2)
monoid_to_commutativeMonoid p (VarMo _ _ (RealVariable _ _ g i)) = VarCM _ i 
-- This case can't happen, this we only decode what we have previously encoded, and we've never encoded something with a "EncodingGroupTerm_var". Anyway, it has to be total...
monoid_to_commutativeMonoid p (VarMo _ _ (EncodingGroupTerm_var _ _ g i)) = VarCM _ i


-- CommutativeGroup -> Group
commutativeGroup_to_group : {c:Type} -> {n:Nat} -> {p:dataTypes.CommutativeGroup c} -> {g:Vect n c} -> {c1:c} -> ExprCG p g c1 -> ExprG (commutativeGroup_to_group_class p) g c1
commutativeGroup_to_group (ConstCG p g c1) = ConstG (commutativeGroup_to_group_class p) g c1
commutativeGroup_to_group (PlusCG e1 e2) = PlusG (commutativeGroup_to_group e1) (commutativeGroup_to_group e2)
commutativeGroup_to_group (MinusCG e1 e2) = MinusG (commutativeGroup_to_group e1) (commutativeGroup_to_group e2)
commutativeGroup_to_group (NegCG e) = NegG (commutativeGroup_to_group e)
commutativeGroup_to_group (VarCG p v) = VarG (commutativeGroup_to_group_class p) v

group_to_commutativeGroup : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> {g:Vect n c} -> {c1:c} -> ExprG (commutativeGroup_to_group_class p) g c1 -> ExprCG p g c1
group_to_commutativeGroup p (ConstG _ g c1) = ConstCG p g c1
group_to_commutativeGroup p (PlusG e1 e2) = PlusCG (group_to_commutativeGroup p e1) (group_to_commutativeGroup p e2)
group_to_commutativeGroup p (MinusG e1 e2) = MinusCG (group_to_commutativeGroup p e1) (group_to_commutativeGroup p e2)
group_to_commutativeGroup p (NegG e) = NegCG (group_to_commutativeGroup p e)
group_to_commutativeGroup p (VarG _ v) = VarCG p v


{-

cr_to_r : {p:CommutativeRing c} -> {g:Vect n c} -> {c1:c} -> ExprCR p g c1 -> ExprR (cr_to_r_class p) g c1
cr_to_r (ConstCR p cst) = ConstR (cr_to_r_class p) cst
cr_to_r (PlusCR e1 e2) = PlusR (cr_to_r e1) (cr_to_r e2)
cr_to_r (MultCR e1 e2) = MultR (cr_to_r e1) (cr_to_r e2)
cr_to_r (VarCR p v) = VarR (cr_to_r_class p) v

r_to_cr : (p:CommutativeRing c) -> {g:Vect n c} -> {c1:c} -> ExprR (cr_to_r_class p) g c1 -> ExprCR p g c1
r_to_cr p (ConstR _ cst) = ConstCR p cst
r_to_cr p (PlusR e1 e2) = PlusCR (r_to_cr p e1) (r_to_cr p e2)
r_to_cr p (MultR e1 e2) = MultCR (r_to_cr p e1) (r_to_cr p e2)
r_to_cr p (VarR _ v) = VarCR p v


-}






