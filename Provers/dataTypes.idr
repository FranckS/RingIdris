-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File dataTypes.idr
-- Groups, commutative groups, rings, commutative rings, and corresponding reflected terms
-------------------------------------------------------------------

module Provers.dataTypes

import Data.Fin
import Data.Vect

%default total


eq_dec_fin : {n:Nat} -> (i:Fin n) -> (j:Fin n) -> (Maybe (i=j))
eq_dec_fin FZ FZ = Just Refl
eq_dec_fin FZ (FS j') = Nothing
eq_dec_fin (FS i') FZ = Nothing
eq_dec_fin (FS i') (FS j') with (eq_dec_fin i' j')
	eq_dec_fin (FS i') (FS i') | (Just Refl) = Just Refl
	eq_dec_fin (FS i') (FS j') | Nothing = Nothing


-- No longer needed : we're back to the orignal order
{-
index_reverse : {a:Type} -> {n:Nat} -> (Fin n) -> (Vect n a) -> a
index_reverse j g = index j (reverse g)
-}



infixl 5 ~=
class Set c where
    -- We just requires a (weak) decidable relation over the elements of the "set"
    -- which means that two elements are EQuivalent.
    -- (Note : that's no longer an equality, but just a relation, since that's more general)
    (~=) : (x:c) -> (y:c) -> Type -- The (undecidable) relation
    set_eq : (x:c) -> (y:c) -> Maybe(x~=y) -- The "weak" decidable relation (week because only gives a proof when it holds)
    
    -- The binary relation should be an equivalence relation, ie
    -- Reflexive,
    set_eq_undec_refl : (x:c) -> x~=x
    -- Symmetric,
    set_eq_undec_sym : {x:c} -> {y:c} -> (x~=y) -> (y~=x)
    -- And transitive
    set_eq_undec_trans : {x:c} -> {y:c} -> {z:c} -> (x~=y) -> (y~=z) -> (x~=z)
    

eq_preserves_eq : {c:Type} -> (Set c) -> (x:c) -> (y:c) -> (c1:c) -> (c2:c) -> (x~=c1) -> (y~=c2) -> (c1~=c2) -> (x~=y)
eq_preserves_eq p x y c1 c2 p1 p2 p3 = 
    let paux : (x~=c2) = ?Meq_preserves_eq_1 in
    let paux2 : (c2~=y) = ?Meq_preserves_eq_2 in
        ?Meq_preserves_eq_3
        
        
        
class Set c => Magma c where
    Plus : c -> c -> c -- A magma just has a plus operation, and we have no properties about it
    -- Plus should preserve the equivalence defined at the Set level 
    Plus_preserves_equiv : {c1:c} -> {c2:c} -> {c1':c} -> {c2':c} -> (c1~=c1') -> (c2~=c2') -> ((Plus c1 c2) ~= (Plus c1' c2'))


class Magma c => SemiGroup c where
    Plus_assoc : (c1:c) -> (c2:c) -> (c3:c) -> (Plus (Plus c1 c2) c3 ~= Plus c1 (Plus c2 c3))

class SemiGroup c => Monoid c where
    Zero : c
    
    Plus_neutral_1 : (c1:c) -> ((Plus Zero c1) ~= c1)    
    Plus_neutral_2 : (c1:c) -> ((Plus c1 Zero) ~= c1)
    
    
    
add_zero_left : {c:Type} -> (dataTypes.Monoid c) -> (x:c) -> (y:c) -> (x~=Zero) -> (Plus x y ~= y)
add_zero_left p x y H = ?Madd_zero_left_1

add_zero_right : {c:Type} -> (dataTypes.Monoid c) -> (x:c) -> (y:c) -> (x~=Zero) -> (Plus y x ~= y)
add_zero_right p x y H = ?Madd_zero_right_1


-- NEW : That's something usefull for dealing with Nat for example, since we don't have negatives numbers
class dataTypes.Monoid c => CommutativeMonoid c where
    Plus_comm' : (c1:c) -> (c2:c) -> ((Plus c1 c2) ~= (Plus c2 c1))


-- We define the fact to have a symmetric as a notion on a monoid. And this will help to define the property of being a group
hasSymmetric : (c:Type) -> (p:dataTypes.Monoid c) -> c -> c -> Type
hasSymmetric c p a b = ((Plus a b) ~= Zero, (Plus b a) ~= (the c Zero))    
    
-- An abstract group
--%logging 1    
class dataTypes.Monoid c => dataTypes.Group c where
    Neg : c -> c
    Minus : c -> c -> c 
    
    -- Neg should preserve the quivalence
    Neg_preserves_equiv : {c1:c} -> {c2:c} -> (c1 ~= c2) -> ((Neg c1) ~= (Neg c2))

    Minus_simpl : (c1:c) -> (c2:c) -> (Minus c1 c2) ~= (Plus c1 (Neg c2)) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse : (c1:c) -> hasSymmetric c (%instance) c1 (Neg c1) -- Every element 'x' has a symmetric which is (Neg x)
--%logging 0


-- We only ask the "user" for the proof that Neg preserves the quivalence, and we automatically deduce that Minus also preserves the equivalence (since Minus is defined by using Neg)
Minus_preserves_equiv : {c:Type} -> (dataTypes.Group c)
                        -> {c1:c} -> {c2:c} -> {c1':c} -> {c2':c} -> (c1 ~= c1') -> (c2 ~= c2') -> ((Minus c1 c2) ~= (Minus c1' c2'))
Minus_preserves_equiv p H1 H2 = ?MMinus_preserves_equiv_1



-- An abstract commutative group
class dataTypes.Group c => CommutativeGroup c where
    Plus_comm : (c1:c) -> (c2:c) -> ((Plus c1 c2) ~= (Plus c2 c1))
    

    
-- An abstract ring    
class CommutativeGroup c => Ring c where
    One : c
    Mult : c -> c -> c
    
    -- The new Mult operation should preserve the quivalence
    Mult_preserves_equiv : {c1:c} -> {c2:c} -> {c1':c} -> {c2':c} -> (c1~=c1') -> (c2~=c2') -> ((Mult c1 c2) ~= (Mult c1' c2'))
    
    Mult_assoc : (c1:c) -> (c2:c) -> (c3:c) -> (Mult (Mult c1 c2) c3) ~= (Mult c1 (Mult c2 c3))
    Mult_dist : (c1:c) -> (c2:c) -> (c3:c) -> (Mult c1 (Plus c2 c3)) ~= (Plus (Mult c1 c2) (Mult c1 c3))
    Mult_dist_2 : (c1:c) -> (c2:c) -> (c3:c) -> (Mult (Plus c1 c2) c3) ~= (Plus (Mult c1 c3) (Mult c2 c3)) -- Needed because we don't have commutativity of * in a ring (in general)
    Mult_neutral : (c1:c) -> ((Mult c1 One) ~= (Mult One c1), (Mult One c1) ~= c1)

-- An abstract commutative ring    
class dataTypes.Ring c => CommutativeRing c where
    Mult_comm : (c1:c) -> (c2:c) -> ((Mult c1 c2) ~= (Mult c2 c1))

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
-- Returns the equivalence relation of a set
eq : {c:Type} -> (Set c) -> (x:c) -> (y:c) -> Type
eq c_set x y = (x~=y)

set_eq_as_elem_of_set : (Set c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
set_eq_as_elem_of_set x = set_eq

-- Magma
magma_eq_as_elem_of_set : (Magma c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
magma_eq_as_elem_of_set x = set_eq_as_elem_of_set (magma_to_set_class x)

-- Semi group
semiGroup_to_set : (SemiGroup c) -> (Set c)
semiGroup_to_set x = (%instance)

semiGroup_eq_as_elem_of_set : (SemiGroup c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
semiGroup_eq_as_elem_of_set x = set_eq_as_elem_of_set (semiGroup_to_set x)

-- Monoid
monoid_to_set : (dataTypes.Monoid c) -> (Set c)
monoid_to_set x = (%instance)

monoid_eq_as_elem_of_set : (dataTypes.Monoid c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
monoid_eq_as_elem_of_set x = set_eq_as_elem_of_set (monoid_to_set x)


-- Commutative Monoid
commutativeMonoid_to_set : (CommutativeMonoid c) -> (Set c)
commutativeMonoid_to_set x = (%instance)

commutativeMonoid_eq_as_elem_of_set : (CommutativeMonoid c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
commutativeMonoid_eq_as_elem_of_set x = set_eq_as_elem_of_set (commutativeMonoid_to_set x)


-- Group
group_to_set : (dataTypes.Group c) -> (Set c)
group_to_set x = (%instance)

group_eq_as_elem_of_set : (dataTypes.Group c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
group_eq_as_elem_of_set x = set_eq_as_elem_of_set (group_to_set x)


-- Commutative Group
commutativeGroup_to_set : (CommutativeGroup c) -> (Set c)
commutativeGroup_to_set x = (%instance)

commutativeGroup_eq_as_elem_of_set : (CommutativeGroup c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
commutativeGroup_eq_as_elem_of_set x = set_eq_as_elem_of_set (commutativeGroup_to_set x)


-- Ring
ring_to_set : (dataTypes.Ring c) -> (Set c)
ring_to_set x = (%instance)

ring_eq_as_elem_of_set : (dataTypes.Ring c) -> ((x:c) -> (y:c) -> Maybe(x~=y))
ring_eq_as_elem_of_set x = set_eq_as_elem_of_set (ring_to_set x)


-- ----------------------------
-- ---- Reflected Terms ---- --
-- ----------------------------

-- This bit is for the trasnlation Ring -> Commutative Group
-- -----------------------------------------------------------


record SetWithMult : (c:Type) -> (Set c) -> Type where
  MkSetWithMult : {c:Type} -> (c_set:Set c) -> (mult:c->c->c) -> (mult_preserves_equiv : {c1:c} -> {c2:c} -> {c1':c} -> {c2':c} -> (c1~=c1') -> (c2~=c2') -> ((mult c1 c2) ~= (mult c1' c2'))) -> SetWithMult c c_set

  
    

-- Things like "x" (simple case), "x*y", "x*(y*z)", ... (all in the form right associative)
data ProductOfVariables : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> (Vect n c) -> c -> Type where
	LastVar : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (g:Vect n c) -> (setAndMult:SetWithMult c c_set) -> (k:Fin n) -> ProductOfVariables setAndMult g (index k g) 
	VarMultProduct : {c:Type} -> {n:Nat} -> {c_set:Set c} -> {g:Vect n c} -> (setAndMult:SetWithMult c c_set) -> (k:Fin n) -> {c_prod : c} -> (pov:ProductOfVariables setAndMult g c_prod) -> ProductOfVariables setAndMult g ((mult setAndMult) (index k g) c_prod)

total
productOfVariables_eq : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> {g : Vect n c} -> {c1:c} -> (prod1 : ProductOfVariables setAndMult g c1) -> {c2:c} -> (prod2 : ProductOfVariables setAndMult g c2) -> Maybe (eq c_set c1 c2)
productOfVariables_eq setAndMult (LastVar _ _ k1) (LastVar _ _ k2) with (eq_dec_fin k1 k2)
    productOfVariables_eq setAndMult (LastVar _ _ k1) (LastVar _ _ k1) | (Just Refl) = Just (set_eq_undec_refl _) -- computation of c_is_set is needed because we need to bring the instance of Set in scope (in the context)
    productOfVariables_eq setAndMult (LastVar _ _ k1) (LastVar _ _ k2) | _ = Nothing
productOfVariables_eq setAndMult (VarMultProduct _ k1 prod1) (VarMultProduct _ k2 prod2) with (eq_dec_fin k1 k2, productOfVariables_eq setAndMult prod1 prod2)
    productOfVariables_eq setAndMult (VarMultProduct _ k1 prod1) (VarMultProduct _ k1 prod2) | (Just Refl, Just prEquivProd) = ?MproductOfVariables_eq_1
    productOfVariables_eq setAndMult (VarMultProduct _ k1 prod1) (VarMultProduct _ k2 prod2) | _ = Nothing
productOfVariables_eq _ _ _ = Nothing



-- Things like "x*y" (simple case), "5*(x*y)", "18*(x*(y*z))", ... (again, all in the form right associative)
data Monomial : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> (Vect n c) -> c -> Type where
    ProdOfVar : {c:Type} -> {n:Nat} -> {c_set:Set c} -> {g:Vect n c} -> (setAndMult:SetWithMult c c_set) -> {c_prod:c} -> ProductOfVariables setAndMult g c_prod -> Monomial setAndMult g c_prod
    ProdOfVarWithConst : {c:Type} -> {n:Nat} -> {c_set:Set c} -> {g:Vect n c} -> (setAndMult:SetWithMult c c_set) -> (const1:c) -> {c_prod:c} -> (ProductOfVariables setAndMult g c_prod) -> Monomial setAndMult g ((mult setAndMult) const1 c_prod)

total
monomial_eq : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> {g : Vect n c} -> {c1:c} -> (mon1 : Monomial setAndMult g c1) -> {c2:c} -> (mon2 : Monomial setAndMult g c2) -> Maybe (eq c_set c1 c2)
monomial_eq setAndMult (ProdOfVar _ prod1) (ProdOfVar _ prod2) with (productOfVariables_eq setAndMult prod1 prod2)
    monomial_eq setAndMult (ProdOfVar _ prod1) (ProdOfVar _ prod2) | (Just prEquivProducts) = Just prEquivProducts
    monomial_eq setAndMult (ProdOfVar _ prod1) (ProdOfVar _ prod2) | _ = Nothing
monomial_eq setAndMult (ProdOfVarWithConst _ c1 prod1) (ProdOfVarWithConst _ c2 prod2) with (set_eq_as_elem_of_set (c_set setAndMult) c1 c2, productOfVariables_eq setAndMult prod1 prod2)
    monomial_eq setAndMult (ProdOfVarWithConst _ c1 prod1) (ProdOfVarWithConst _ c2 prod2) | (Just c1_equiv_c2, Just prEquivProducts) = ?Mmonomial_eq_1
    monomial_eq setAndMult (ProdOfVarWithConst _ c1 prod1) (ProdOfVarWithConst _ c2 prod2) | _ = Nothing
monomial_eq _ _ _ = Nothing



-- Things like "5*(x*y)" (simple case), "[5*(x*y)] * [18*(x*(y*z)]", ... (each monomial being in the form right associative)
data ProductOfMonomials : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> (Vect n c) -> c -> Type where
    LastMonomial : {c:Type} -> {n:Nat} -> {c_set:Set c} -> {g:Vect n c} -> (setAndMult:SetWithMult c c_set) -> {c_prod:c} -> Monomial setAndMult g c_prod -> ProductOfMonomials setAndMult g c_prod
    MonomialMultProduct : {c:Type} -> {n:Nat} -> {c_set:Set c} -> {g:Vect n c} -> (setAndMult:SetWithMult c c_set) -> {c_mon:c} -> (Monomial setAndMult g c_mon) -> {c_prod:c} -> (ProductOfMonomials setAndMult g c_prod) -> ProductOfMonomials setAndMult g ((mult setAndMult) c_mon c_prod)
    

productOfMonomials_eq : {c:Type} -> {n:Nat} -> {c_set:Set c} -> (setAndMult:SetWithMult c c_set) -> {g : Vect n c} -> {c1:c} -> (prod1 : ProductOfMonomials setAndMult g c1) -> {c2:c} -> (prod2 : ProductOfMonomials setAndMult g c2) -> Maybe (eq c_set c1 c2)
productOfMonomials_eq setAndMult (LastMonomial _ mon1) (LastMonomial _ mon2) with (monomial_eq setAndMult mon1 mon2)
    productOfMonomials_eq setAndMult (LastMonomial _ mon1) (LastMonomial _ mon2) | (Just mon1_equiv_mon2) = Just mon1_equiv_mon2
    productOfMonomials_eq setAndMult (LastMonomial _ mon1) (LastMonomial _ mon2) | _ = Nothing
productOfMonomials_eq setAndMult (MonomialMultProduct _ mon1 prod1) (MonomialMultProduct _ mon2 prod2) with (monomial_eq setAndMult mon1 mon2, productOfMonomials_eq setAndMult prod1 prod2)
    productOfMonomials_eq setAndMult (MonomialMultProduct _ mon1 prod1) (MonomialMultProduct _ mon2 prod2) | (Just mon1_equiv_mon2, Just prod1_equiv_prod2) = ?MproductsOfMonomials_eq_1
    productOfMonomials_eq setAndMult (MonomialMultProduct _ mon1 prod1) (MonomialMultProduct _ mon2 prod2) | _ = Nothing
productOfMonomials_eq _ _ _ = Nothing
    

    
-- -----------------------------------------------------------

-- NEW : We require 'c' to be "at least" a set, instead of just asking for the "equivalence relation" (which was previously an equality)
data Variable : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> (setAndMult:Maybe (SetWithMult c c_set)) -> (Vect n c) -> c -> Type where
    RealVariable : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> Variable c_set neg Nothing g (index i g) -- neg is not used here
    EncodingGroupTerm_var : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> Variable c_set neg Nothing g (neg (index i g)) -- neg is used here
    --Note : I'd have prefered to not have to pass a "neg" function as argument, since I could be directly indexed over the real "Neg", but that doesn't work for Variable_eq definition
    EncodingProductOfMonomials : {c:Type} -> (c_set:Set c) -> {n:Nat} -> (neg:c->c) -> {g:Vect n c} -> {setAndMult:SetWithMult c c_set} -> (c_prod:c) -> (ProductOfMonomials setAndMult g c_prod) -> Variable c_set neg (Just setAndMult) g c_prod
    --EncodingGroupTerm_const : {c:Type} -> {n:Nat} -> (c_equal:(c1:c)->(c2:c)->Maybe(c1=c2)) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> VariableA c_equal neg g (neg c1) -- and here
    -- Encoding fot constants is no longer needed since we can just put a constant of value (Neg c) : we can still use Neg during the conversion because we still have a Group, even though we convert to a Monoid !

Variable_eq : {c:Type} -> {c_set:Set c} -> {n:Nat} -> {c1:c} -> {c2:c} -> (neg:c->c) -> (optSetAndMult:Maybe (SetWithMult c c_set)) -> (g:Vect n c) -> (v1:Variable c_set neg optSetAndMult g c1) -> (v2:Variable c_set neg optSetAndMult g c2) -> Maybe (c1~=c2)
Variable_eq neg Nothing g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) with (decEq i1 i2)
    Variable_eq neg Nothing g (RealVariable _ _ _ i1) (RealVariable _ _ _ i1) | (Yes Refl) = Just (set_eq_undec_refl _)
    Variable_eq neg Nothing g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) | _ = Nothing
Variable_eq neg Nothing g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) with (decEq i1 i2) 
    Variable_eq neg Nothing g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i1) | (Yes Refl) = Just (set_eq_undec_refl _)
    Variable_eq neg Nothing g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) | _ = Nothing
Variable_eq neg (Just setAndMult) g (EncodingProductOfMonomials _ _ _ prod1) (EncodingProductOfMonomials _ _ _ prod2) with (productOfMonomials_eq setAndMult prod1 prod2)
    Variable_eq neg (Just setAndMult) g (EncodingProductOfMonomials _ _ _ prod1) (EncodingProductOfMonomials _ _ _ prod2) | (Just prod1_equiv_prod2) = Just (prod1_equiv_prod2)
    Variable_eq neg (Just setAndMult) g (EncodingProductOfMonomials _ _ _ prod1) (EncodingProductOfMonomials _ _ _ prod2) | _ = Nothing
--Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) with (c_equal c1 c2)
--    Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c1) | (Just Refl) = Just Refl
--    Variable_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) | _ = Nothing
Variable_eq neg optSetAndMult g _ _ = Nothing
   
      
print_Variable : {c:Type} -> {c_set:Set c} -> {n:Nat} -> {c1:c} -> (f:c -> String) -> {neg:c->c} -> {setAndMult:Maybe (SetWithMult c c_set)} -> {g:Vect n c} -> Variable c_set neg setAndMult g c1 -> String
print_Variable f (RealVariable _ _ _ i) = "Var " ++ (show (cast i))
print_Variable f (EncodingGroupTerm_var _ _ _ i) = "[Encoding_var (" ++ (show(cast i)) ++ ") ]"
print_Variable f (EncodingProductOfMonomials _ _ _ prod) = "encoding of product of monomials" -- Perhaps will need to print something more useful here for debug
--print_VariableA f (EncodingGroupTerm_const _ _ _ c1) = "[Encoding_const (" ++ (f c1) ++ ") ]"



-- Reflected terms in a magma
data ExprMa : {c:Type} -> {n:Nat} -> Magma c -> (neg:c->c) -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstMa : {c:Type} -> {n:Nat} -> (p : Magma c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c)  -> ExprMa p neg mult g c1 
    PlusMa : {c:Type} -> {n:Nat} -> {p : Magma c} -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMa p neg mult g c1 -> ExprMa p neg mult g c2 -> ExprMa p neg mult g (Plus c1 c2) 
    VarMa : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (magma_to_set_class p) neg mult g c1 -> ExprMa p neg mult g c1

-- I wanted it to only produce a bool, which tells if the two expression are "syntactically equivalent" (that mean equal, appart for the constants where we only ask for the equivalence)
-- BUT, we will need to prove a lemma which says that if two expressions are "syntactically equivalent" then (c_eq c1 c2). So instead, we directly produce a Maybe(c_eq c1 c2)
exprMa_eq : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMa p neg mult g c1) -> (e2:ExprMa p neg mult g c2) -> Maybe(c1~=c2)
exprMa_eq p neg mult g (PlusMa _ _ x y) (PlusMa _ _ x' y') with (exprMa_eq p neg mult g x x', exprMa_eq p neg mult g y y')
    exprMa_eq p neg mult g (PlusMa _ _ x y) (PlusMa _ _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprMa_eq p neg mult g (PlusMa _ _ x y) (PlusMa _ _ _ _) | _ = Nothing
exprMa_eq p neg mult g (VarMa _ _ _ {c1=c1} v1) (VarMa _ _ _ v2) with (Variable_eq neg mult g v1 v2) 
    exprMa_eq p neg mult g (VarMa _ _ _ {c1=c1} v1) (VarMa _ _ _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
    exprMa_eq p neg mult g (VarMa _ _ _ v1) (VarMa _ _ _ v2) | _ = Nothing
exprMa_eq p neg mult g (ConstMa _ _ _ _ const1) (ConstMa _ _ _ _ const2) with ((magma_eq_as_elem_of_set p) const1 const2)
    exprMa_eq p neg mult g (ConstMa _ _ _ _ const1) (ConstMa _ _ _ _ const2) | (Just const_eq) = Just const_eq
    exprMa_eq p neg mult g (ConstMa _ _ _ _ const1) (ConstMa _ _ _ _ const2) | _ = Nothing
exprMa_eq p neg mult g e1 e2 = Nothing



-- Reflected terms in semigroup
data ExprSG : {c:Type} -> {n:Nat} -> SemiGroup c -> (neg:c->c) -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstSG : {c:Type} -> {n:Nat} -> (p : SemiGroup c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c) -> ExprSG p neg mult g c1
    PlusSG : {c:Type} -> {n:Nat} -> {p : SemiGroup c} -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprSG p neg mult g c1 -> ExprSG p neg mult g c2 -> ExprSG p neg mult g (Plus c1 c2)
    VarSG : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (semiGroup_to_set p) neg mult g c1 -> ExprSG p neg mult g c1

exprSG_eq : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprSG p neg mult g c1) -> (e2:ExprSG p neg mult g c2) -> Maybe(c1~=c2)
exprSG_eq p neg mult g (PlusSG _ _ x y) (PlusSG _ _ x' y') with (exprSG_eq p neg mult g x x', exprSG_eq p neg mult g y y')
    exprSG_eq p neg mult g (PlusSG _ _ x y) (PlusSG _ _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprSG_eq p neg mult g (PlusSG _ _ x y) (PlusSG _ _ _ _) | _ = Nothing
exprSG_eq p neg mult g (VarSG _ _ _ {c1=c1} v1) (VarSG _ _ _ v2) with (Variable_eq neg mult g v1 v2)
    exprSG_eq p neg mult g (VarSG _ _ _ {c1=c1} v1) (VarSG _ _ _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
    exprSG_eq p neg mult g (VarSG _ _ _ v1) (VarSG _ _ _ v2) | _ = Nothing
exprSG_eq p neg mult g (ConstSG _ _ _ _ const1) (ConstSG _ _ _ _ const2) with ((semiGroup_eq_as_elem_of_set p) const1 const2)
    exprSG_eq p neg mult g (ConstSG _ _ _ _ const1) (ConstSG _ _ _ _ const2) | (Just const_eq) = Just const_eq
    exprSG_eq p neg mult g (ConstSG _ _ _ _ const1) (ConstSG _ _ _ _ const2) | _ = Nothing
exprSG_eq p neg mult g _ _ = Nothing


print_ExprSG : {c:Type} -> {n:Nat} -> {p:SemiGroup c} -> {r1:c} -> (c -> String) -> {neg:c->c} -> {mult:c->c->c} -> {g:Vect n c} -> ExprSG p neg mult g r1 -> String
print_ExprSG c_print (ConstSG _ _ _ _ const) = c_print const
print_ExprSG c_print (PlusSG _ _ e1 e2) = "(" ++ (print_ExprSG c_print e1) ++ ") + (" ++ (print_ExprSG c_print e2) ++ ")"
print_ExprSG c_print (VarSG _ _ _ v) = print_Variable c_print v


-- Reflected terms in a monoid
data ExprMo : {c:Type} -> {n:Nat} -> dataTypes.Monoid c -> (neg:c->c) -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c) -> ExprMo p neg mult g c1
    PlusMo : {c:Type} -> {n:Nat} -> {p : dataTypes.Monoid c} -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMo p neg mult g c1 -> ExprMo p neg mult g c2 -> ExprMo p neg mult g (Plus c1 c2)
    VarMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (monoid_to_set p) neg mult g c1 -> ExprMo p neg mult g c1

exprMo_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Monoid c) -> (neg:c->c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMo p neg mult g c1) -> (e2:ExprMo p neg mult g c2) -> Maybe(c1~=c2)
exprMo_eq p neg mult g (PlusMo _ _ x y) (PlusMo _ _ x' y') with (exprMo_eq p neg mult g x x', exprMo_eq p neg mult g y y')
    exprMo_eq p neg mult g (PlusMo _ _ x y) (PlusMo _ _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprMo_eq p neg mult g (PlusMo _ _ x y) (PlusMo _ _ _ _) | _ = Nothing
exprMo_eq p neg mult g (VarMo _ _ _ {c1=c1} v1) (VarMo _ _ _ v2) with (Variable_eq neg mult g v1 v2)
    exprMo_eq p neg mult g (VarMo _ _ _ {c1=c1} v1) (VarMo _ _ _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
    exprMo_eq p neg mult g (VarMo _ _ _ v1) (VarMo _ _ _ v2) | _ = Nothing
exprMo_eq p neg mult g (ConstMo _ _ _ _ const1) (ConstMo _ _ _ _ const2) with ((monoid_eq_as_elem_of_set p) const1 const2)
    exprMo_eq p neg mult g (ConstMo _ _ _ _  const1) (ConstMo _ _ _ _ const2) | (Just const_eq) = Just const_eq
    exprMo_eq p neg mult g (ConstMo _ _ _ _ const1) (ConstMo _ _ _ _ const2) | _ = Nothing
exprMo_eq p neg mult g _ _  = Nothing


-- Reflected terms in a commutative monoid
data ExprCM : {c:Type} -> {n:Nat} -> (CommutativeMonoid c) -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstCM : {c:Type} -> {n:Nat} -> (p : CommutativeMonoid c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c) -> ExprCM p mult g c1
    PlusCM : {c:Type} -> {n:Nat} -> {p : CommutativeMonoid c} -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprCM p mult g c1 -> ExprCM p mult g c2 -> ExprCM p mult g (Plus c1 c2)
    VarCM : {c:Type} -> {n:Nat} -> (p : CommutativeMonoid c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (commutativeMonoid_to_set p) (\x=>x) mult g c1 -> ExprCM p mult g c1

exprCM_eq : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprCM p mult g c1) -> (e2:ExprCM p mult g c2) -> Maybe(c1~=c2)
exprCM_eq p mult g (PlusCM _ x y) (PlusCM _ x' y') with (exprCM_eq p mult g x x', exprCM_eq p mult g y y')
    exprCM_eq p mult g (PlusCM _ x y) (PlusCM _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
    exprCM_eq p mult g (PlusCM _ x y) (PlusCM _ _ _) | _ = Nothing
exprCM_eq p mult g (VarCM _ _ v1) (VarCM _ _ v2) with (Variable_eq (\x=>x) mult g v1 v2)
    exprCM_eq p mult g (VarCM _ _ v1) (VarCM _ _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
    exprCM_eq p mult g (VarCM _ _ v1) (VarCM _ _ v2) | _ = Nothing
exprCM_eq p mult g (ConstCM _ _ _ const1) (ConstCM _ _ _ const2) with ((commutativeMonoid_eq_as_elem_of_set p) const1 const2)
    exprCM_eq p mult g (ConstCM _ _ _  const1) (ConstCM _ _ _ const2) | (Just const_eq) = Just const_eq
    exprCM_eq p mult g (ConstCM _ _ _ const1) (ConstCM _ _ _ const2) | _ = Nothing
exprCM_eq p mult g _ _  = Nothing



-- Reflected terms in a group  
data ExprG :  {c:Type} -> {n:Nat} -> dataTypes.Group c -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c) -> ExprG p mult g c1
    PlusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprG p mult g c1 -> ExprG p mult g c2 -> ExprG p mult g (Plus c1 c2)
    MinusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprG p mult g c1 -> ExprG p mult g c2 -> ExprG p mult g (Minus c1 c2)
    NegG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> ExprG p mult g c1 -> ExprG p mult g (Neg c1)
    VarG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (group_to_set p) Neg mult g c1 -> ExprG p mult g c1


exprG_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprG p mult g c1) -> (e2:ExprG p mult g c2) -> Maybe(c1~=c2)
exprG_eq p mult g (PlusG _ x y) (PlusG _ x' y') with (exprG_eq p mult g x x', exprG_eq p mult g y y')
        exprG_eq p mult g (PlusG _ x y) (PlusG _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
        exprG_eq p mult g (PlusG _ x y) (PlusG _ _ _) | _ = Nothing
exprG_eq p mult g (VarG _ _ {c1=c1} v1) (VarG _ _ v2) with (Variable_eq Neg mult g v1 v2)
        exprG_eq p mult g (VarG _ _ {c1=c1} v1) (VarG _ _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
        exprG_eq p mult g (VarG _ _ v1) (VarG _ _ v2) | _ = Nothing
exprG_eq p mult g (ConstG _ _ _ const1) (ConstG _ _ _ const2) with ((group_eq_as_elem_of_set p) const1 const2)
        exprG_eq p mult g (ConstG _ _ _ const1) (ConstG _ _ _ const2) | (Just const_eq) = Just const_eq
        exprG_eq p mult g (ConstG _ _ _ const1) (ConstG _ _ _ const2) | _ = Nothing
exprG_eq p mult g (NegG _ e1) (NegG _ e2) with (exprG_eq p mult g e1 e2)
        exprG_eq p mult g (NegG _ e1) (NegG _ _) | (Just p1) = Just (Neg_preserves_equiv p1)
        exprG_eq p mult g (NegG _ e1) (NegG _ e2) | _ = Nothing
exprG_eq p mult g (MinusG _ x y) (MinusG _ x' y') with (exprG_eq p mult g x x', exprG_eq p mult g y y')
        exprG_eq p mult g (MinusG _ x y) (MinusG _ _ _) | (Just p1, Just p2) = ?MexprG_eq_1 -- Just (Minus_preserves_equiv p1 p2) THIS IS STRANGE ! WHY DO I NEED TO DO THIS PROOF IN PROOF MODE ! I PRODUCE THE SAME LAMBDA TERM !
        exprG_eq p mult g (MinusG _ x y) (MinusG _ _ _) | _ = Nothing	
exprG_eq p mult g _ _  = Nothing
    
    
print_ExprG : {c:Type} -> {n:Nat} -> {p:dataTypes.Group c} -> {mult:c->c->c} -> {r1:c} -> (c -> String) -> {g:Vect n c} -> ExprG p mult g r1 -> String
print_ExprG c_print (ConstG _ _ _ const) = c_print const
print_ExprG c_print (PlusG _ e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") + (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (MinusG _ e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") - (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (VarG _ _ v) = print_Variable c_print v
print_ExprG c_print (NegG _ e) = "(-" ++ (print_ExprG c_print e) ++ ")"


-- Reflected terms in a commutative group       
data ExprCG : {c:Type} -> {n:Nat} -> CommutativeGroup c -> (mult:c->c->c) -> (Vect n c) -> c -> Type where
    ConstCG : {c:Type} -> {n:Nat} -> (p:CommutativeGroup c) -> (mult:c->c->c) -> (g:Vect n c) -> (c1:c) -> ExprCG p mult g c1
    PlusCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> (mult:c->c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprCG p mult g c1 -> ExprCG p mult g c2 -> ExprCG p mult g (Plus c1 c2)
    MinusCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprCG p mult g c1 -> ExprCG p mult g c2 -> ExprCG p mult g (Minus c1 c2)
    NegCG : {c:Type} -> {n:Nat} -> {p:CommutativeGroup c} -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> ExprCG p mult g c1 -> ExprCG p mult g (Neg c1)
    VarCG : {c:Type} -> {n:Nat} -> (p:CommutativeGroup c) -> (mult:c->c->c) -> {g:Vect n c} -> {c1:c} -> Variable (commutativeGroup_to_set p) Neg mult g c1 -> ExprCG p mult g c1
    
    
exprCG_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> (mult:c->c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprCG p mult g c1) -> (e2:ExprCG p mult g c2) -> (Maybe (c1~=c2))
exprCG_eq p mult g (PlusCG _ x y) (PlusCG _ x' y') with (exprCG_eq p mult g x x', exprCG_eq p mult g y y')
        exprG_eq p mult g (PlusCG _ x y) (PlusCG _ _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
        exprG_eq p mult g (PlusCG _ x y) (PlusCG _ _ _) | _ = Nothing
exprCG_eq p mult g (VarCG _ _ {c1=c1} v1) (VarCG _ _ v2) with (Variable_eq Neg mult g v1 v2)
        exprG_eq p mult g (VarCG _ _ {g=g} {c1=c1} v1) (VarCG _ _ {g=g} v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
        exprG_eq p mult g (VarCG _ _ {g=g} v1) (VarCG _ _ {g=g} v2) | _ = Nothing
exprCG_eq p mult g (ConstCG _ _ _ const1) (ConstCG _ _ _ const2) with ((commutativeGroup_eq_as_elem_of_set p) const1 const2)
        exprG_eq p mult g (ConstCG _ _ _ const1) (ConstCG _ _ _ const2) | (Just const_eq) = Just const_eq
        exprG_eq p mult g (ConstCG _ _ _ const1) (ConstCG _ _ _ const2) | _ = Nothing
exprCG_eq p mult g (NegCG _ e1) (NegCG _ e2) with (exprCG_eq p mult g e1 e2)
        exprG_eq p mult g (NegCG _ e1) (NegCG _ _) | (Just p1) = Just (Neg_preserves_equiv p1)
        exprG_eq p mult g (NegCG _ e1) (NegCG _ e2) | _ = Nothing
exprCG_eq p mult g (MinusCG _ x y) (MinusCG _ x' y') with (exprCG_eq p mult g x x', exprCG_eq p mult g y y')
        exprG_eq p mult g (MinusCG _ x y) (MinusCG _ _ _) | (Just p1, Just p2) = ?MexprCG_eq_1 -- Just (Minus_preserves_equiv p1 p2) THIS IS STRANGE ! WHY DO I NEED TO DO THIS PROOF IN PROOF MODE ! I PRODUCE THE SAME LAMBDA TERM !
        exprG_eq p mult g (MinusCG _ x y) (MinusCG _ _ _) | _ = Nothing	
exprCG_eq p mult g _ _  = Nothing


print_ExprCG : {c:Type} -> {n:Nat} -> {p:dataTypes.CommutativeGroup c} -> {mult:c->c->c} -> {r1:c} -> (c -> String) -> {g:Vect n c} -> ExprCG p mult g r1 -> String
print_ExprCG c_print (ConstCG _ _ _ const) = c_print const
print_ExprCG c_print (PlusCG _ e1 e2) = "(" ++ (print_ExprCG c_print e1) ++ ") + (" ++ (print_ExprCG c_print e2) ++ ")"
print_ExprCG c_print (MinusCG _ e1 e2) = "(" ++ (print_ExprCG c_print e1) ++ ") --- (" ++ (print_ExprCG c_print e2) ++ ")"
print_ExprCG c_print (VarCG _ _ v) = print_Variable c_print v
print_ExprCG c_print (NegCG _ e) = "(-" ++ (print_ExprCG c_print e) ++ ")"

    

-- Reflected terms in a ring       
data ExprR : {c:Type} -> {n:Nat} -> dataTypes.Ring c -> (Vect n c) -> c -> Type where
    ConstR : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> (c1:c) -> ExprR p g c1
    PlusR : {c:Type} -> {n:Nat} -> {p:dataTypes.Ring c} -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Plus c1 c2)
    MultR : {c:Type} -> {n:Nat} -> {p:dataTypes.Ring c} -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Mult c1 c2)
    MinusR: {c:Type} -> {n:Nat} -> {p:dataTypes.Ring c} -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Minus c1 c2)
    NegR : {c:Type} -> {n:Nat} -> {p:dataTypes.Ring c} -> {g:Vect n c} -> {c1:c} -> ExprR p g c1 -> ExprR p g (Neg c1)
    VarR : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> {g:Vect n c} -> {c1:c} -> Variable (ring_to_set p) Neg Mult g c1 -> ExprR p g c1
   

exprR_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Ring c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprR p g c1) -> (e2:ExprR p g c2) -> (Maybe (c1~=c2))
exprR_eq p g (PlusR x y) (PlusR x' y') with (exprR_eq p g x x', exprR_eq p g y y')
        exprG_eq p g (PlusR x y) (PlusR _ _) | (Just p1, Just p2) = Just (Plus_preserves_equiv p1 p2)
        exprG_eq p g (PlusR x y) (PlusR _ _) | _ = Nothing
exprR_eq p g (VarR _ {c1=c1} v1) (VarR _ v2) with (Variable_eq Neg Mult g v1 v2)
        exprG_eq p g (VarR _ {c1=c1} v1) (VarR _ v2) | (Just v1_equiv_v2) = Just v1_equiv_v2
        exprG_eq p g (VarR _ v1) (VarR _ v2) | _ = Nothing
exprR_eq p g (ConstR _ _ const1) (ConstR _ _ const2) with ((ring_eq_as_elem_of_set p) const1 const2)
        exprG_eq p g (ConstR _ _ const1) (ConstR _ _ const2) | (Just const_eq) = Just const_eq
        exprG_eq p g (ConstR _ _ const1) (ConstR _ _ const2) | _ = Nothing
exprR_eq p g (NegR e1) (NegR e2) with (exprR_eq p g e1 e2)
        exprG_eq p g (NegR e1) (NegR _) | (Just p1) = Just (Neg_preserves_equiv p1)
        exprG_eq p g (NegR e1) (NegR e2) | _ = Nothing
exprR_eq p g (MinusR x y) (MinusR x' y') with (exprR_eq p g x x', exprR_eq p g y y')
        exprG_eq p g (MinusR x y) (MinusR _ _) | (Just p1, Just p2) = ?MexprR_eq_1 -- Just (Minus_preserves_equiv p1 p2) THIS IS STRANGE ! WHY DO I NEED TO DO THIS PROOF IN PROOF MODE ! I PRODUCE THE SAME LAMBDA TERM !
        exprG_eq p g (MinusR x y) (MinusR _ _) | _ = Nothing
exprR_eq p g (MultR x y) (MultR x' y') with (exprR_eq p g x x', exprR_eq p g y y')
        exprG_eq p g (MultR x y) (MultR _ _) | (Just p1, Just p2) = ?MexprR_eq_2 -- Just (Minus_preserves_equiv p1 p2) THIS IS STRANGE ! WHY DO I NEED TO DO THIS PROOF IN PROOF MODE ! I PRODUCE THE SAME LAMBDA TERM !
        exprG_eq p g (MultR x y) (MultR _ _) | _ = Nothing
exprR_eq p g _ _  = Nothing   
   
   
print_ExprR : {c:Type} -> {n:Nat} -> {p:dataTypes.Ring c} -> {r1:c} -> (c -> String) -> {g:Vect n c} -> ExprR p g r1 -> String
print_ExprR c_print (ConstR _ _ const) = c_print const
print_ExprR c_print (PlusR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") + (" ++ (print_ExprR c_print e2) ++ ")"
print_ExprR c_print (MultR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") * (" ++ (print_ExprR c_print e2) ++ ")"
print_ExprR c_print (MinusR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") --- (" ++ (print_ExprR c_print e2) ++ ")"
print_ExprR c_print (VarR _ v) = print_Variable c_print v
print_ExprR c_print (NegR e) = "(-" ++ (print_ExprR c_print e) ++ ")"

    
{-
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
semiGroup_to_magma : {c:Type} -> {n:Nat} -> {p:SemiGroup c} -> {neg:c->c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprSG p neg mult g c1 -> ExprMa (semiGroup_to_magma_class p) neg mult g c1
semiGroup_to_magma (ConstSG p _ _ _ cst) = ConstMa (semiGroup_to_magma_class p) _ _ _ cst
semiGroup_to_magma (PlusSG _ _ e1 e2) = PlusMa _ _ (semiGroup_to_magma e1) (semiGroup_to_magma e2)
semiGroup_to_magma (VarSG p _ _ v) = VarMa (semiGroup_to_magma_class p) _ _ v

magma_to_semiGroup : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> {neg:c->c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprMa (semiGroup_to_magma_class p) neg mult g c1 -> ExprSG p neg mult g c1
magma_to_semiGroup p (ConstMa _ _ _ _ cst) = ConstSG p _ _ _ cst
magma_to_semiGroup p (PlusMa _ _ e1 e2) = PlusSG _ _ (magma_to_semiGroup p e1) (magma_to_semiGroup p e2)
magma_to_semiGroup p (VarMa _ _ _ v) = VarSG p _ _ v


-- Monoid -> SemiGroup
monoid_to_semiGroup : {c:Type} -> {n:Nat} -> {p:dataTypes.Monoid c} -> {neg:c->c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprMo p neg mult g c1 -> ExprSG (monoid_to_semiGroup_class p) neg mult g c1
monoid_to_semiGroup (ConstMo p _ _ _ cst) = ConstSG (monoid_to_semiGroup_class p) _ _ _ cst
monoid_to_semiGroup (PlusMo _ _ e1 e2) = PlusSG _ _ (monoid_to_semiGroup e1) (monoid_to_semiGroup e2)
monoid_to_semiGroup (VarMo p _ _ v) = VarSG (monoid_to_semiGroup_class p) _ _ v

semiGroup_to_monoid : {c:Type} -> {n:Nat} -> (p:dataTypes.Monoid c) -> {neg:c->c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprSG (monoid_to_semiGroup_class p) neg mult g c1 -> ExprMo p neg mult g c1
semiGroup_to_monoid p (ConstSG _ _ _ _ cst) = ConstMo p _ _ _ cst
semiGroup_to_monoid p (PlusSG _ _ e1 e2) = PlusMo _ _ (semiGroup_to_monoid p e1) (semiGroup_to_monoid p e2)
semiGroup_to_monoid p (VarSG _ _ _ v) = VarMo p _ _ v


-- CommutativeMonoid -> Monoid
-- NEW
commutativeMonoid_to_monoid : {c:Type} -> {n:Nat} -> {p:CommutativeMonoid c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprCM p mult g c1 -> ExprMo (commutativeMonoid_to_monoid_class p) (\x=>x) mult g c1 -- there is no negations to encode, that's why we use the identity function here
commutativeMonoid_to_monoid (ConstCM p _ _ cst) = ConstMo (commutativeMonoid_to_monoid_class p) _ _ _ cst
commutativeMonoid_to_monoid (PlusCM _ e1 e2) = PlusMo _ _ (commutativeMonoid_to_monoid e1) (commutativeMonoid_to_monoid e2)
commutativeMonoid_to_monoid (VarCM p _ v) = VarMo (commutativeMonoid_to_monoid_class p) _ _ v

monoid_to_commutativeMonoid : {c:Type} -> {n:Nat} -> (p:CommutativeMonoid c) -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprMo (commutativeMonoid_to_monoid_class p) (\x => x) mult g c1 -> ExprCM p mult g c1 -- we know that no negations have been encoded
monoid_to_commutativeMonoid p (ConstMo _ _ _ _ cst) = (ConstCM p _ _ cst)
monoid_to_commutativeMonoid p (PlusMo _ _ e1 e2) = PlusCM _ (monoid_to_commutativeMonoid p e1) (monoid_to_commutativeMonoid p e2)
monoid_to_commutativeMonoid p (VarMo _ _ _ v) = VarCM _ _ v


-- CommutativeGroup -> Group
commutativeGroup_to_group : {c:Type} -> {n:Nat} -> {p:dataTypes.CommutativeGroup c} -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprCG p mult g c1 -> ExprG (commutativeGroup_to_group_class p) mult g c1
commutativeGroup_to_group (ConstCG p _ g c1) = ConstG (commutativeGroup_to_group_class p) _ g c1
commutativeGroup_to_group (PlusCG _ e1 e2) = PlusG _ (commutativeGroup_to_group e1) (commutativeGroup_to_group e2)
commutativeGroup_to_group (MinusCG _ e1 e2) = MinusG _ (commutativeGroup_to_group e1) (commutativeGroup_to_group e2)
commutativeGroup_to_group (NegCG _ e) = NegG _ (commutativeGroup_to_group e)
commutativeGroup_to_group (VarCG p _ v) = VarG (commutativeGroup_to_group_class p) _ v

group_to_commutativeGroup : {c:Type} -> {n:Nat} -> (p:dataTypes.CommutativeGroup c) -> {mult:c->c->c} -> {g:Vect n c} -> {c1:c} -> ExprG (commutativeGroup_to_group_class p) mult g c1 -> ExprCG p mult g c1
group_to_commutativeGroup p (ConstG _ _ g c1) = ConstCG p _ g c1
group_to_commutativeGroup p (PlusG _ e1 e2) = PlusCG _ (group_to_commutativeGroup p e1) (group_to_commutativeGroup p e2)
group_to_commutativeGroup p (MinusG _ e1 e2) = MinusCG _ (group_to_commutativeGroup p e1) (group_to_commutativeGroup p e2)
group_to_commutativeGroup p (NegG _ e) = NegCG _ (group_to_commutativeGroup p e)
group_to_commutativeGroup p (VarG _ _ v) = VarCG p _ v


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




---------- Proofs ----------
{-
Provers.dataTypes.MproductsOfMonomials_eq_1 = proof
  intros
  mrefine Just
  mrefine Mult_preserves_equiv 
  exact mon1_equiv_mon2 
  exact prod1_equiv_prod2 


Provers.dataTypes.Mmonomial_eq_1 = proof
  intros
  refine Just
  mrefine Mult_preserves_equiv 
  exact c1_equiv_c2 
  exact prEquivProducts 


Provers.dataTypes.MproductOfVariables_eq_1 = proof
  intros
  mrefine Just
  mrefine Mult_preserves_equiv 
  mrefine set_eq_undec_refl 
  exact prEquivProd 
  -}

Provers.dataTypes.Meq_preserves_eq_1 = proof
  intros
  mrefine set_eq_undec_trans 
  exact c1
  exact p1
  exact p3

Provers.dataTypes.Meq_preserves_eq_2 = proof
  intros
  exact (set_eq_undec_sym p2)

Provers.dataTypes.Meq_preserves_eq_3 = proof
  intros
  exact (set_eq_undec_trans paux paux2)

Provers.dataTypes.Madd_zero_left_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus Zero y)
  exact y
  mrefine Plus_preserves_equiv 
  exact (set_eq_undec_refl y)
  exact (Plus_neutral_1 y)
  exact H
  exact (set_eq_undec_refl y)
  
Provers.dataTypes.Madd_zero_right_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus y Zero)
  exact y
  mrefine Plus_preserves_equiv 
  exact (set_eq_undec_refl y)
  exact (Plus_neutral_2 y)
  exact (set_eq_undec_refl y)
  exact H
  
Provers.dataTypes.MMinus_preserves_equiv_1 = proof
  intros
  mrefine eq_preserves_eq 
  exact (Plus c1 (Neg c2))
  exact (Plus c1' (Neg c2'))
  exact (Minus_simpl c1 c2)
  exact (Minus_simpl c1' c2')
  mrefine Plus_preserves_equiv 
  exact H1
  mrefine Neg_preserves_equiv 
  exact H2  
    
Provers.dataTypes.MexprG_eq_1 = proof
  intros
  mrefine Just
  mrefine Minus_preserves_equiv 
  exact p1
  exact p2
  
Provers.dataTypes.MexprCG_eq_1 = proof
  intros
  mrefine Just
  mrefine Minus_preserves_equiv 
  exact p1
  exact p2  

Provers.dataTypes.MexprR_eq_1 = proof
  intros
  mrefine Just
  mrefine Minus_preserves_equiv 
  exact p1
  exact p2  
  
Provers.dataTypes.MexprR_eq_2 = proof
  intros
  mrefine Just
  mrefine Mult_preserves_equiv 
  exact p1
  exact p2

  

