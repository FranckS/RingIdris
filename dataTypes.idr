-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File dataTypes.idr
-- Groups, commutative groups, rings, commutative rings, and corresponding reflected terms
-------------------------------------------------------------------

module dataTypes

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

-- An abstract group
--%logging 1    
class (dataTypes.Monoid c, NegMinus c) => dataTypes.Group c where
    Minus_simpl : (c1:c) -> (c2:c) -> Minus c1 c2 = Plus c1 (Neg c2) --Minus should not be primitive and should be simplifiable
    -- The most important stuff for a group is the following :
    Plus_inverse : (c1:c) -> ((Plus c1 (Neg c1) = Plus (Neg c1) c1), (Plus (Neg c1) c1 = the c Zero)) -- "the c Zero" used to make clear that we talk about Zero in c and not the one in CommutativeRing (last defined first tried ?)
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
    
using (g : Vect n c)

-- Reflected terms in a magma
    data ExprMa : Magma c -> (Vect n c) -> c -> Type where
        ConstMa : (p : Magma c) -> (c1:c) -> ExprMa p g c1
        PlusMa : {p : Magma c} -> {c1:c} -> {c2:c} -> ExprMa p g c1 -> ExprMa p g c2 -> ExprMa p g (Plus c1 c2)
        VarMa : (p : Magma c) -> (i:Fin n) -> ExprMa p g (index i g)

-- Reflected terms in semigroup
    data ExprSG : SemiGroup c -> (Vect n c) -> c -> Type where
        ConstSG : (p : SemiGroup c) -> (c1:c) -> ExprSG p g c1
        PlusSG : {p : SemiGroup c} -> {c1:c} -> {c2:c} -> ExprSG p g c1 -> ExprSG p g c2 -> ExprSG p g (Plus c1 c2)
        VarSG : (p : SemiGroup c) -> (i:Fin n) -> ExprSG p g (index i g)

    print_ExprSG : {p:SemiGroup c} -> {r1:c} -> (c -> String) -> ExprSG p g r1 -> String
    print_ExprSG c_print (ConstSG p const) = c_print const
    print_ExprSG c_print (PlusSG e1 e2) = "(" ++ (print_ExprSG c_print e1) ++ ") + (" ++ (print_ExprSG c_print e2) ++ ")"
    print_ExprSG c_print (VarSG p i) = "Var " ++ (show (cast i))

-- Reflected terms in a monoid
    data ExprMo : dataTypes.Monoid c -> (Vect n c) -> c -> Type where
        ConstMo : (p : dataTypes.Monoid c) -> (c1:c) -> ExprMo p g c1
        PlusMo : {p : dataTypes.Monoid c} -> {c1:c} -> {c2:c} -> ExprMo p g c1 -> ExprMo p g c2 -> ExprMo p g (Plus c1 c2)
        VarMo : (p : dataTypes.Monoid c) -> (i:Fin n) -> ExprMo p g (index i g)

-- Reflected terms in a group  
    data ExprG :  dataTypes.Group c -> (Vect n c) -> c -> Type where
        ConstG : (p : dataTypes.Group c) -> (c1:c) -> ExprG p g c1
        --ZeroG : ExprG p g Zero
        PlusG : {p : dataTypes.Group c} -> {c1:c} -> {c2:c} -> ExprG p g c1 -> ExprG p g c2 -> ExprG p g (Plus c1 c2)
        VarG : (p : dataTypes.Group c) -> (i:Fin n) -> ExprG p g (index i g)
 
-- Reflected terms in a commutative group       
    data ExprCG : CommutativeGroup c -> (Vect n c) -> c -> Type where
        ConstCG : (p:CommutativeGroup c) -> (c1:c) -> ExprCG p g c1
        --ZeroCG : ExprCG p g Zero
        PlusCG : {p : CommutativeGroup c} -> {c1:c} -> {c2:c} -> ExprCG p g c1 -> ExprCG p g c2 -> ExprCG p g (Plus c1 c2)
        VarCG : (p : CommutativeGroup c) -> (i:Fin n) -> ExprCG p g (index i g)
          
-- Reflected terms in a ring       
    data ExprR : dataTypes.Ring c -> (Vect n c) -> c -> Type where
        ConstR : (p:dataTypes.Ring c) -> (c1:c) -> ExprR p g c1  
        --ZeroR : ExprR p g Zero
        --OneR : ExprR p g One
        PlusR : {p:dataTypes.Ring c} -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Plus c1 c2)
        MultR : {p:dataTypes.Ring c} -> {c1:c} -> {c2:c} -> ExprR p g c1 -> ExprR p g c2 -> ExprR p g (Mult c1 c2)
        VarR : (p:dataTypes.Ring c) -> (i:Fin n) -> ExprR p g (index i g)

    print_ExprR : {p:dataTypes.Ring c} -> {r1:c} -> (c -> String) -> ExprR p g r1 -> String
    print_ExprR c_print (ConstR p const) = c_print const
    print_ExprR c_print (PlusR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") + (" ++ (print_ExprR c_print e2) ++ ")"
    print_ExprR c_print (MultR e1 e2) = "(" ++ (print_ExprR c_print e1) ++ ") * (" ++ (print_ExprR c_print e2) ++ ")"
    print_ExprR c_print (VarR p i) = "Var " ++ (show (cast i))
      
-- Reflected terms in a commutative ring   
    data ExprCR : CommutativeRing c -> (Vect n c) -> c -> Type where
        ConstCR : (p:CommutativeRing c) -> (c1:c) -> ExprCR p g c1   
        --ZeroCR : ExprCR p g Zero
        --OneCR : ExprCR p g One
        PlusCR : {p:CommutativeRing c} -> {c1:c} -> {c2:c} -> ExprCR p g c1 -> ExprCR p g c2 -> ExprCR p g (Plus c1 c2)
        MultCR : {p:CommutativeRing c} -> {c1:c} -> {c2:c} -> ExprCR p g c1 -> ExprCR p g c2 -> ExprCR p g (Mult c1 c2)
        VarCR : (p:CommutativeRing c) -> (i:Fin n) -> ExprCR p g (index i g)

------------------------------
-- Functions of conversion ---
------------------------------
-- Magma -> Set
magma_to_set_class : (Magma c) -> (Set c)
magma_to_set_class x = (%instance)

-- Monoid -> SemiGroup
monoid_to_semiGroup_class : (dataTypes.Monoid c) -> (SemiGroup c)
monoid_to_semiGroup_class p = (%instance)

monoid_to_semiGroup : {p:dataTypes.Monoid c} -> {g:Vect n c} -> {c1:c} -> ExprMo p g c1 -> ExprSG (monoid_to_semiGroup_class p) g c1
monoid_to_semiGroup (ConstMo p cst) = ConstSG (monoid_to_semiGroup_class p) cst
monoid_to_semiGroup (PlusMo e1 e2) = PlusSG (monoid_to_semiGroup e1) (monoid_to_semiGroup e2)
monoid_to_semiGroup (VarMo p i) = VarSG (monoid_to_semiGroup_class p) i

semiGroup_to_monoid : (p:dataTypes.Monoid c) -> {g:Vect n c} -> {c1:c} -> ExprSG (monoid_to_semiGroup_class p) g c1 -> ExprMo p g c1
semiGroup_to_monoid p (ConstSG _ cst) = ConstMo p cst
semiGroup_to_monoid p (PlusSG e1 e2) = PlusMo (semiGroup_to_monoid p e1) (semiGroup_to_monoid p e2)
semiGroup_to_monoid p (VarSG _ i) = VarMo p i

-- SemiGroup -> Magma
semiGroup_to_magma_class : (SemiGroup c) -> (Magma c)
semiGroup_to_magma_class p = (%instance)

semiGroup_to_magma : {p:SemiGroup c} -> {g:Vect n c} -> {c1:c} -> ExprSG p g c1 -> ExprMa (semiGroup_to_magma_class p) g c1
semiGroup_to_magma (ConstSG p cst) = ConstMa (semiGroup_to_magma_class p) cst
semiGroup_to_magma (PlusSG e1 e2) = PlusMa (semiGroup_to_magma e1) (semiGroup_to_magma e2)
semiGroup_to_magma (VarSG p i) = VarMa (semiGroup_to_magma_class p) i

magma_to_semiGroup : (p:SemiGroup c) -> {g:Vect n c} -> {c1:c} -> ExprMa (semiGroup_to_magma_class p) g c1 -> ExprSG p g c1
magma_to_semiGroup p (ConstMa _ cst) = ConstSG p cst
magma_to_semiGroup p (PlusMa e1 e2) = PlusSG (magma_to_semiGroup p e1) (magma_to_semiGroup p e2)
magma_to_semiGroup p (VarMa _ i) = VarSG p i

-- CommutativeRing -> Ring
cr_to_r_class : CommutativeRing c -> dataTypes.Ring c
cr_to_r_class p = %instance -- finds the instance automatically from p

cr_to_r : {p:CommutativeRing c} -> {g:Vect n c} -> {c1:c} -> ExprCR p g c1 -> ExprR (cr_to_r_class p) g c1
cr_to_r (ConstCR p cst) = ConstR (cr_to_r_class p) cst
cr_to_r (PlusCR e1 e2) = PlusR (cr_to_r e1) (cr_to_r e2)
cr_to_r (MultCR e1 e2) = MultR (cr_to_r e1) (cr_to_r e2)
cr_to_r (VarCR p i) = VarR (cr_to_r_class p) i

r_to_cr : (p:CommutativeRing c) -> {g:Vect n c} -> {c1:c} -> ExprR (cr_to_r_class p) g c1 -> ExprCR p g c1
r_to_cr p (ConstR _ cst) = ConstCR p cst
r_to_cr p (PlusR e1 e2) = PlusCR (r_to_cr p e1) (r_to_cr p e2)
r_to_cr p (MultR e1 e2) = MultCR (r_to_cr p e1) (r_to_cr p e2)
r_to_cr p (VarR _ i) = VarCR p i

-- -----------------------------------
-- Get equality as elements of set ---
--------------------------------------
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

