-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File dataTypes.idr
-- Groups, commutative groups, rings, commutative rings, and corresponding reflected terms
-------------------------------------------------------------------

module dataTypes


%default total

index_reverse : {a:Type} -> {n:Nat} -> (Fin n) -> (Vect n a) -> a
index_reverse j g = index j (reverse g)


-- For technical reason : because in Idris this is not yet possible to talk about
-- a field which is introduced in the current typeclass, we need to define some
-- operators in other structures
class ZeroC c where
    Zero : c
class NegMinus c where
    Neg : c -> c
    Minus : c -> c -> c 
    
-- Real stuff starts here   

class Set c where
    -- We just requires a (weak) decidable equality over the elements of the "set"
    set_eq : (x:c) -> (y:c) -> Maybe (x=y)
        
class Set c => Magma c where
    Plus : c -> c -> c

class Magma c => SemiGroup c where
    Plus_assoc : (c1:c) -> (c2:c) -> (c3:c) -> (Plus (Plus c1 c2) c3 = Plus c1 (Plus c2 c3))

class (SemiGroup c, ZeroC c) => Monoid c where
    Plus_neutral_1 : (c1:c) -> (Plus Zero c1 = c1)    
    Plus_neutral_2 : (c1:c) -> (Plus c1 Zero = c1)

-- We define the fact to have a symmetric as a notion in a monoid. And this will define the property of being a group
hasSymmetric : (c:Type) -> (p:dataTypes.Monoid c) -> c -> c -> Type
hasSymmetric c p a b = (Plus a b = Zero, Plus b a = the c Zero)    
    
-- An abstract group
--%logging 1    
class (dataTypes.Monoid c, NegMinus c) => dataTypes.Group c where
    Minus_simpl : (c1:c) -> (c2:c) -> Minus c1 c2 = Plus c1 (Neg c2) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse : (c1:c) -> hasSymmetric c (%instance) c1 (Neg c1) -- Every element 'x' has a symmetric which is (Neg x)
--%logging 0

-- An abstract commutative group
class dataTypes.Group c => CommutativeGroup c where
    Plus_comm : (c1:c) -> (c2:c) -> (Plus c1 c2 = Plus c2 c1)
    
class OneMult c where
    One : c
    Mult : c -> c -> c

-- An abstract ring    
class (CommutativeGroup c, OneMult c) => Ring c where
    Mult_assoc : (c1:c) -> (c2:c) -> (c3:c) -> Mult (Mult c1 c2) c3 = Mult c1 (Mult c2 c3)
    Mult_dist : (c1:c) -> (c2:c) -> (c3:c) -> Mult c1 (Plus c2 c3) = Plus (Mult c1 c2) (Mult c1 c3)
    Mult_dist_2 : (c1:c) -> (c2:c) -> (c3:c) -> Mult (Plus c1 c2) c3 = Plus (Mult c1 c3) (Mult c2 c3) -- Needed because we don't have commutativity of * in a ring
    Mult_neutral : (c1:c) -> ((Mult c1 One = Mult One c1), (Mult One c1 = c1))

-- An abstract commutative ring    
class dataTypes.Ring c => CommutativeRing c where
    Mult_comm : (c1:c) -> (c2:c) -> (Mult c1 c2 = Mult c2 c1)

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

-- CommutativeRing -> Ring
cr_to_r_class : CommutativeRing c -> dataTypes.Ring c
cr_to_r_class p = %instance -- finds the instance automatically from p


-- -----------------------------------------
-- (getters) Equality as elements of set ---
--------------------------------------------
set_eq_as_elem_of_set : (Set c) -> ((x:c) -> (y:c) -> (Maybe (x=y)))
set_eq_as_elem_of_set x = set_eq

-- Magma
magma_eq_as_elem_of_set : (Magma c) -> ((x:c) -> (y:c) -> (Maybe (x=y)))
magma_eq_as_elem_of_set x = set_eq_as_elem_of_set (magma_to_set_class x)

-- Semi group
semiGroup_to_set : (SemiGroup c) -> (Set c)
semiGroup_to_set x = (%instance)

semiGroup_eq_as_elem_of_set : (SemiGroup c) -> ((x:c) -> (y:c) -> (Maybe (x=y)))
semiGroup_eq_as_elem_of_set x = set_eq_as_elem_of_set (semiGroup_to_set x)

-- Monoid
monoid_to_set : (dataTypes.Monoid c) -> (Set c)
monoid_to_set x = (%instance)

monoid_eq_as_elem_of_set : (dataTypes.Monoid c) -> ((x:c) -> (y:c) -> (Maybe (x=y)))
monoid_eq_as_elem_of_set x = set_eq_as_elem_of_set (monoid_to_set x)

-- Group
group_to_set : (dataTypes.Group c) -> (Set c)
group_to_set x = (%instance)

group_eq_as_elem_of_set : (dataTypes.Group c) -> ((x:c) -> (y:c) -> (Maybe (x=y)))
group_eq_as_elem_of_set x = set_eq_as_elem_of_set (group_to_set x)


-- ----------------------------
-- ---- Reflected Terms ---- --
-- ----------------------------

data VariableA : {c:Type} -> {n:Nat} -> (c_equal : (c1:c) -> (c2:c) -> Maybe(c1=c2)) -> (neg:c->c) -> (Vect n c) -> c -> Type where
    RealVariable : {c:Type} -> {n:Nat} -> (c_equal:(c1:c)->(c2:c)->Maybe(c1=c2)) -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> VariableA c_equal neg g (index_reverse i g) -- neg is not used here
    EncodingGroupTerm_var : {c:Type} -> {n:Nat} -> (c_equal:(c1:c)->(c2:c)->Maybe(c1=c2)) -> (neg:c->c) -> (g:Vect n c) -> (i:Fin n) -> VariableA c_equal neg g (neg (index_reverse i g)) -- neg is used here
    EncodingGroupTerm_const : {c:Type} -> {n:Nat} -> (c_equal:(c1:c)->(c2:c)->Maybe(c1=c2)) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> VariableA c_equal neg g (neg c1) -- and here
    

VariableA_eq : {c:Type} -> {n:Nat} -> {c1:c} -> {c2:c} -> (c_equal:(cx:c)->(cy:c)->Maybe(cx=cy)) -> (neg:c->c) -> (g:Vect n c) -> (v1:VariableA c_equal neg g c1) -> (v2:VariableA c_equal neg g c2) -> Maybe (v1=v2)
VariableA_eq c_equal neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) with (decEq i1 i2)
    VariableA_eq c_equal neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i1) | (Yes refl) = Just refl
    VariableA_eq c_equal neg g (RealVariable _ _ _ i1) (RealVariable _ _ _ i2) | _ = Nothing
VariableA_eq c_equal neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) with (decEq i1 i2) 
    VariableA_eq c_equal neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i1) | (Yes refl) = Just refl
    VariableA_eq c_equal neg g (EncodingGroupTerm_var _ _ _ i1) (EncodingGroupTerm_var _ _ _ i2) | _ = Nothing
VariableA_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) with (c_equal c1 c2)
    VariableA_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c1) | (Just refl) = Just refl
    VariableA_eq c_equal neg g (EncodingGroupTerm_const _ _ _ c1) (EncodingGroupTerm_const _ _ _ c2) | _ = Nothing
VariableA_eq c_equal neg g _ _ = Nothing
   
      
print_VariableA : {c1:c} -> (f:c -> String) -> {c_equal:(cx:c)->(cy:c)->Maybe(cx=cy)} -> {neg:c->c} -> {g:Vect n c} -> VariableA c_equal neg g c1 -> String
print_VariableA f (RealVariable _ _ _ i) = "Var " ++ (show (cast i))
print_VariableA f (EncodingGroupTerm_var _ _ _ i) = "[Encoding_var (" ++ (show(cast i)) ++ ") ]"
print_VariableA f (EncodingGroupTerm_const _ _ _ c1) = "[Encoding_const (" ++ (f c1) ++ ") ]"


-- Reflected terms in a magma
data ExprMa : {c:Type} -> {n:Nat} -> Magma c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstMa : {c:Type} -> {n:Nat} -> (p : Magma c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c)  -> ExprMa p neg g c1 
    PlusMa : {c:Type} -> {n:Nat} -> {p : Magma c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMa p neg g c1 -> ExprMa p neg g c2 -> ExprMa p neg g (Plus c1 c2) 
    VarMa : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> VariableA (magma_eq_as_elem_of_set p) neg g c1 -> ExprMa p neg g c1

exprMa_eq : {c:Type} -> {n:Nat} -> (p:Magma c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMa p neg g c1) -> (e2:ExprMa p neg g c2) -> (Maybe (e1=e2))
exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ x' y') with (exprMa_eq p neg g x x', exprMa_eq p neg g y y')
    exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ x y) | (Just refl, Just refl) = Just refl
    exprMa_eq p neg g (PlusMa _ x y) (PlusMa _ _ _) | _ = Nothing
exprMa_eq p neg g (VarMa _ _ v1) (VarMa _ _ v2) with (VariableA_eq _ neg g v1 v2) -- Note : the "_" on the with clause correspond to (magma_eq_as_elem_of_set p) : both VarMo shares the same p, and given the definition of the type ExprMo, the argument c_equal is forced to be (magma_eq_as_elem_of_set p)
    exprMa_eq p neg g (VarMa _ _ v1) (VarMa _ _ v1) | (Just refl) = Just refl
    exprMa_eq p neg g (VarMa _ _ v1) (VarMa _ _ v2) | _ = Nothing      
exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const2) with ((magma_eq_as_elem_of_set p) const1 const2)
    exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprMa_eq p neg g (ConstMa _ _ _ const1) (ConstMa _ _ _ const2) | _ = Nothing
exprMa_eq p neg g e1 e2 = Nothing



-- Reflected terms in semigroup
data ExprSG : {c:Type} -> {n:Nat} -> SemiGroup c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstSG : {c:Type} -> {n:Nat} -> (p : SemiGroup c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> ExprSG p neg g c1
    PlusSG : {c:Type} -> {n:Nat} -> {p : SemiGroup c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprSG p neg g c1 -> ExprSG p neg g c2 -> ExprSG p neg g (Plus c1 c2)
    VarSG : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> VariableA (semiGroup_eq_as_elem_of_set p) neg g c1 -> ExprSG p neg g c1

exprSG_eq : {c:Type} -> {n:Nat} -> (p:SemiGroup c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprSG p neg g c1) -> (e2:ExprSG p neg g c2) -> (Maybe (e1=e2))
exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ x' y') with (exprSG_eq p neg g x x', exprSG_eq p neg g y y')
    exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ x y) | (Just refl, Just refl) = Just refl
    exprSG_eq p neg g (PlusSG _ x y) (PlusSG _ _ _) | _ = Nothing
exprSG_eq p neg g (VarSG _ _ v1) (VarSG _ _ v2) with (VariableA_eq _ neg g v1 v2)
    exprSG_eq p neg g (VarSG _ _ v1) (VarSG _ _ v1) | (Just refl) = Just refl
    exprSG_eq p neg g (VarSG _ _ v1) (VarSG _ _ v2) | _ = Nothing
exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const2) with ((semiGroup_eq_as_elem_of_set p) const1 const2)
    exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprSG_eq p neg g (ConstSG _ _ _ const1) (ConstSG _ _ _ const2) | _ = Nothing
exprSG_eq p neg g _ _ = Nothing


print_ExprSG : {c:Type} -> {n:Nat} -> {p:SemiGroup c} -> {r1:c} -> (c -> String) -> {neg:c->c} -> {g:Vect n c} -> ExprSG p neg g r1 -> String
print_ExprSG c_print (ConstSG _ _ _ const) = c_print const
print_ExprSG c_print (PlusSG _ e1 e2) = "(" ++ (print_ExprSG c_print e1) ++ ") + (" ++ (print_ExprSG c_print e2) ++ ")"
print_ExprSG c_print (VarSG _ _ v) = print_VariableA c_print v



-- Reflected terms in a monoid
data ExprMo : {c:Type} -> {n:Nat} -> dataTypes.Monoid c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> ExprMo p neg g c1
    PlusMo : {c:Type} -> {n:Nat} -> {p : dataTypes.Monoid c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprMo p neg g c1 -> ExprMo p neg g c2 -> ExprMo p neg g (Plus c1 c2)
    VarMo : {c:Type} -> {n:Nat} -> (p : dataTypes.Monoid c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> VariableA (monoid_eq_as_elem_of_set p) neg g c1 -> ExprMo p neg g c1

exprMo_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Monoid c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprMo p neg g c1) -> (e2:ExprMo p neg g c2) -> (Maybe (e1=e2))
exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ x' y') with (exprMo_eq p neg g x x', exprMo_eq p neg g y y')
    exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ x y) | (Just refl, Just refl) = Just refl
    exprMo_eq p neg g (PlusMo _ x y) (PlusMo _ _ _) | _ = Nothing
exprMo_eq p neg g (VarMo _ _ v1) (VarMo _ _ v2) with (VariableA_eq _ neg g v1 v2)
    exprMo_eq p neg g (VarMo _ _ v1) (VarMo _ _ v1) | (Just refl) = Just refl
    exprMo_eq p neg g (VarMo _ _ v1) (VarMo _ _ v2) | _ = Nothing
exprMo_eq p neg g (ConstMo _ _ _ const1) (ConstMo _ _ _ const2) with ((monoid_eq_as_elem_of_set p) const1 const2)
    exprMo_eq p neg g (ConstMo _ _ _  const1) (ConstMo _ _ _ const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
    exprMo_eq p neg g (ConstMo _ _ _ const1) (ConstMo _ _ _ const2) | _ = Nothing
exprMo_eq p neg g _ _  = Nothing



-- Reflected terms in a group  
data ExprG :  {c:Type} -> {n:Nat} -> dataTypes.Group c -> (neg:c->c) -> (Vect n c) -> c -> Type where
    ConstG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> (neg:c->c) -> (g:Vect n c) -> (c1:c) -> ExprG p neg g c1
    PlusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (neg:c->c) -> {g:Vect n c}  -> {c1:c} -> {c2:c} -> ExprG p neg g c1 -> ExprG p neg g c2 -> ExprG p neg g (Plus c1 c2)
    MinusG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> {c2:c} -> ExprG p neg g c1 -> ExprG p neg g c2 -> ExprG p neg g (Minus c1 c2)
    NegG : {c:Type} -> {n:Nat} -> {p : dataTypes.Group c} -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> ExprG p neg g c1 -> ExprG p neg g (Neg c1)
    VarG : {c:Type} -> {n:Nat} -> (p : dataTypes.Group c) -> (neg:c->c) -> {g:Vect n c} -> {c1:c} -> VariableA (group_eq_as_elem_of_set p) neg g c1 -> ExprG p neg g c1


exprG_eq : {c:Type} -> {n:Nat} -> (p:dataTypes.Group c) -> (neg:c->c) -> (g:Vect n c) -> {c1 : c} -> {c2 : c} -> (e1:ExprG p neg g c1) -> (e2:ExprG p neg g c2) -> (Maybe (e1=e2))
exprG_eq p neg g (PlusG _ x y) (PlusG _ x' y') with (exprG_eq p neg g x x', exprG_eq p neg g y y')
        exprG_eq p neg g (PlusG _ x y) (PlusG _ x y) | (Just refl, Just refl) = Just refl
        exprG_eq p neg g (PlusG _ x y) (PlusG _ _ _) | _ = Nothing
exprG_eq p neg g (VarG _ _ v1) (VarG _ _ v2) with (VariableA_eq _ neg g v1 v2)
        exprG_eq p neg g (VarG _ _ v1) (VarG _ _ v1) | (Just refl) = Just refl
        exprG_eq p neg g (VarG _ _ v1) (VarG _ _ v2) | _ = Nothing
exprG_eq p neg g (ConstG _ _ _ const1) (ConstG _ _ _ const2) with ((group_eq_as_elem_of_set p) const1 const2)
        exprG_eq p neg g (ConstG _ _ _ const1) (ConstG _ _ _ const1) | (Just refl) = Just refl -- Attention, the clause is with "Just refl", and not "Yes refl"
        exprG_eq p neg g (ConstG _ _ _ const1) (ConstG _ _ _ const2) | _ = Nothing
exprG_eq p neg g (NegG _ e1) (NegG _ e2) with (exprG_eq p neg g e1 e2)
        exprG_eq p neg g (NegG _ e1) (NegG _ e1) | (Just refl) = Just refl
        exprG_eq p neg g (NegG _ e1) (NegG _ e2) | _ = Nothing
exprG_eq p neg g (MinusG _ x y) (MinusG _ x' y') with (exprG_eq p neg g x x', exprG_eq p neg g y y')
        exprG_eq p neg g (MinusG _ x y) (MinusG _ x y) | (Just refl, Just refl) = Just refl
        exprG_eq p neg g (MinusG _ x y) (MinusG _ _ _) | _ = Nothing	
exprG_eq p neg g _ _  = Nothing
    
    
print_ExprG : {c:Type} -> {n:Nat} -> {p:dataTypes.Group c} -> {r1:c} -> (c -> String) -> {neg:c->c} -> {g:Vect n c} -> ExprG p neg g r1 -> String
print_ExprG c_print (ConstG _ _ _ const) = c_print const
print_ExprG c_print (PlusG _ e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") + (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (MinusG _ e1 e2) = "(" ++ (print_ExprG c_print e1) ++ ") --- (" ++ (print_ExprG c_print e2) ++ ")"
print_ExprG c_print (VarG _ _ v) = print_VariableA c_print v
print_ExprG c_print (NegG _ e) = "(--" ++ (print_ExprG c_print e) ++ ")"

{-
-- Reflected terms in a commutative group       
        data ExprCG : CommutativeGroup c -> (Vect n c) -> c -> Type where
            ConstCG : (p:CommutativeGroup c) -> (c1:c) -> ExprCG p g c1
            --ZeroCG : ExprCG p g Zero
            PlusCG : {p : CommutativeGroup c} -> {c1:c} -> {c2:c} -> ExprCG p g c1 -> ExprCG p g c2 -> ExprCG p g (Plus c1 c2)
            VarCG : (p:CommutativeGroup c) -> {c1:c} -> VariableA g c1 -> ExprCG p g c1
          
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
semiGroup_to_monoid p (ConstSG p _ _ cst) = ConstMo p _ _ cst
semiGroup_to_monoid p (PlusSG _ e1 e2) = PlusMo _ (semiGroup_to_monoid p e1) (semiGroup_to_monoid p e2)
semiGroup_to_monoid p (VarSG _ _ v) = VarMo p _ v

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






