-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File dataTypes.idr
-- Groups, commutative groups, rings, commutative rings, and corresponding reflected terms
-------------------------------------------------------------------

module dataTypes

class ZeroPlus g where
    Zero : g
    Plus : g -> g -> g

-- An abstract group
--%logging 1    
class ZeroPlus g => Group g where
    Plus_assoc : (c1:g) -> (c2:g) -> (c3:g) -> (Plus (Plus c1 c2) c3 = Plus c1 (Plus c2 c3))
    Plus_neutral : (c:g) -> ((Plus Zero c = Plus c Zero), (Plus c Zero = c))
    Plus_inverse : (c1:g) -> (c2 ** ((Plus c1 c2 = Plus c2 c1), (Plus c2 c1 = Zero)))
--%logging 0

-- An abstract commutative group
class dataTypes.Group g => CommutativeGroup g where
    Plus_comm : (c1:g) -> (c2:g) -> (Plus c1 c2 = Plus c2 c1)
    
class OneMult c where
    One : c
    Mult : c -> c -> c

-- An abstract ring    
class (CommutativeGroup r, OneMult r) => Ring r where
    Mult_assoc : (c1:r) -> (c2:r) -> (c3:r) -> Mult (Mult c1 c2) c3 = Mult c1 (Mult c2 c3)
    Mult_dist : (c1:r) -> (c2:r) -> (c3:r) -> Mult c1 (Plus c2 c3) = Plus (Mult c1 c2) (Mult c1 c3)
    Mult_dist_2 : (c1:r) -> (c2:r) -> (c3:r) -> Mult (Plus c1 c2) c3 = Plus (Mult c1 c3) (Mult c2 c3) -- Needed because we don't have commutativity of * in a ring
    Mult_neutral : (c:r) -> ((Mult c One = Mult One c), (Mult One c = c))

-- An abstract commutative ring    
class dataTypes.Ring r => CommutativeRing r where
    Mult_comm : (c1:r) -> (c2:r) -> (Mult c1 c2 = Mult c2 c1)
    
using (g : Vect n c)
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

-- Functions of conversion

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
