-- Edwin Brady, Franck Slama
-- University of St Andrews
-- File develop.idr
-- Develop the expression reflecting an element of a commutative ring
-- This is the first part of the reduction of an element of a commutative ring
-------------------------------------------------------------------

module develop

import dataTypes

--%default total

-- Step 1 for reduceForR
develop : {p:dataTypes.Ring c} -> {g:Vect n c} -> {c1:c} -> (ExprR p g c1) -> (c2 ** (ExprR p g c2, c1=c2))
develop (ConstR p const) = (_ ** (ConstR p const, refl))

develop (VarR p v) = (_ ** (VarR p v, refl))
develop (PlusR e1 e2) = let (r_ih1 ** (e_ih1, p_ih1)) = (develop e1) in
                         let (r_ih2 ** (e_ih2, p_ih2)) = (develop e2) in
                            ((Plus r_ih1 r_ih2) ** (PlusR e_ih1 e_ih2, ?Mdevelop1))

develop (MultR (ConstR p c1) (ConstR p c2)) = (_ ** (MultR (ConstR p c1) (ConstR p c2), refl))     
develop (MultR (ConstR p c1) (VarR p v)) = (_ ** (MultR (ConstR p c1) (VarR p v), refl))
develop (MultR (ConstR p c1) (PlusR e21 e22)) = let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                    let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_l ** (e_ih_l, p_ih_l)) = develop (MultR (ConstR p c1) e_ih_e21) in
                                                        let (r_ih_r ** (e_ih_r, p_ih_r)) = develop (MultR (ConstR p c1) e_ih_e22) in
                                                            (_ ** (PlusR e_ih_l e_ih_r, ?Mdevelop2)) -- Proof easily doable after 4 rewritings and using Mult_dist, but also strange problem here
develop (MultR (ConstR p c1) (MultR e21 e22)) = let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                    let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih ** (e_ih, p_ih)) = develop (MultR e_ih_e21 e_ih_e22) in
                                                            (_ ** ({- develop -} (MultR (ConstR p c1) e_ih), ?Mdevelop3))

develop (MultR (VarR p v1) (ConstR p c2)) = (_ ** (MultR (VarR p v1) (ConstR p c2), refl))
develop (MultR (VarR p v1) (VarR p v2)) = (_ ** (MultR (VarR p v1) (VarR p v2), refl))
develop (MultR (VarR p v1) (PlusR e21 e22)) = let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                 let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                    let (r_ih_l ** (e_ih_l, p_ih_l)) = develop (MultR (VarR p v1) e_ih_e21) in
                                                    let (r_ih_r ** (e_ih_r, p_ih_r)) = develop (MultR (VarR p v1) e_ih_e22) in
                                                        (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop4))
develop (MultR (VarR p v1) (MultR e21 e22)) = let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                 let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                    let (r_ih ** (e_ih, p_ih)) = develop (MultR e_ih_e21 e_ih_e22) in
                                                        let (r_ih' ** (e_ih', p_ih')) = develop (MultR (VarR p v1) e_ih) in
                                                            (_ ** (e_ih', ?Mdevelop5))
                              
develop (MultR (PlusR {p} e11 e12) (ConstR p c2)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                    let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                        let (r_ih_l ** (e_ih_l, p_ih_l)) = develop (MultR e_ih_e11 (ConstR p c2)) in
                                                        let (r_ih_r ** (e_ih_r, p_ih_r)) = develop (MultR e_ih_e12 (ConstR p c2)) in
                                                        (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop6))                         
develop (MultR (PlusR {p} e11 e12) (VarR p v2)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                    let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                    let (r_ih_l ** (e_ih_l, p_ih_l)) = develop (MultR e_ih_e11 (VarR p v2)) in
                                                    let (r_ih_r ** (e_ih_r, p_ih_r)) = develop (MultR e_ih_e12 (VarR p v2)) in
                                                        (_ ** ((PlusR e_ih_l e_ih_r), ?Mdevelop7))
{-
develop (MultR (PlusR e11 e12) (PlusR e21 e22)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                     let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                     let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                     let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_a ** (e_ih_a, p_ih_a)) = develop (MultR e_ih_e11 e_ih_e21) in
                                                        let (r_ih_b ** (e_ih_b, p_ih_b)) = develop (MultR e_ih_e11 e_ih_e22) in
                                                        let (r_ih_c ** (e_ih_c, p_ih_c)) = develop (MultR e_ih_e12 e_ih_e21) in
                                                        let (r_ih_d ** (e_ih_d, p_ih_d)) = develop (MultR e_ih_e12 e_ih_e22) in
                                                            (_ ** (PlusR e_ih_a (PlusR e_ih_b (PlusR e_ih_c e_ih_d)), ?Mdevelop8))
-}

develop (MultR (PlusR e11 e12) (PlusR e21 e22)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                     let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                     let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                     let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_a ** (e_ih_a, p_ih_a)) = develop (MultR e_ih_e11 (PlusR e_ih_e21 e_ih_e22)) in
                                                        let (r_ih_b ** (e_ih_b, p_ih_b)) = develop (MultR e_ih_e12 (PlusR e_ih_e21 e_ih_e22)) in
                                                            (_ ** (PlusR e_ih_a e_ih_b, ?Mdevelop8))

develop (MultR (PlusR e11 e12) (MultR e21 e22)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                     let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                     let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                     let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_a ** (e_ih_a, p_ih_a)) = develop (MultR e_ih_e21 e_ih_e22) in
                                                        let (r_ih_b ** (e_ih_b, p_ih_b)) = develop (MultR e_ih_e11 e_ih_a) in
                                                        let (r_ih_c ** (e_ih_c, p_ih_c)) = develop (MultR e_ih_e12 e_ih_a) in
                                                            (_ ** (PlusR e_ih_b e_ih_c, ?Mdevelop9)) 
                            
develop (MultR (MultR {p} e11 e12) (ConstR p c2)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                    let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                        let (r_ih ** (e_ih, p_ih)) = develop (MultR e_ih_e11 e_ih_e12) in
                                                            (_ ** ({- develop -} (MultR e_ih (ConstR p c2)), ?Mdevelop10))
develop (MultR (MultR {p} e11 e12) (VarR p v2)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                    let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                        let (r_ih ** (e_ih, p_ih)) = develop (MultR e_ih_e11 e_ih_e12) in
                                                            (_ ** ({- develop -} (MultR e_ih (VarR p v2)), ?Mdevelop11))                 
develop (MultR (MultR e11 e12) (PlusR e21 e22)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                     let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                     let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                     let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_l1 ** (e_ih_l1, p_ih_l1)) = develop (MultR e_ih_e11 e_ih_e12) in
                                                            let (r_ih_l2 ** (e_ih_l2, p_ih_l2)) = develop (MultR e_ih_l1 e_ih_e21) in
                                                            let (r_ih_r2 ** (e_ih_r2, p_ih_r2)) = develop (MultR e_ih_l1 e_ih_e22) in
                                                                (_ ** (PlusR e_ih_l2 e_ih_r2, ?Mdevelop12))
develop (MultR (MultR e11 e12) (MultR e21 e22)) = let (r_ih_e11 ** (e_ih_e11, p_ih_e11)) = develop e11 in
                                                     let (r_ih_e12 ** (e_ih_e12, p_ih_e12)) = develop e12 in
                                                     let (r_ih_e21 ** (e_ih_e21, p_ih_e21)) = develop e21 in
                                                     let (r_ih_e22 ** (e_ih_e22, p_ih_e22)) = develop e22 in
                                                        let (r_ih_l1 ** (e_ih_l1, p_ih_l1)) = develop (MultR e_ih_e11 e_ih_e12) in
                                                        let (r_ih_l2 ** (e_ih_l2, p_ih_l2)) = develop (MultR e_ih_e21 e_ih_e22) in
                                                        let (r_ih_l3 ** (e_ih_l3, p_ih_l3)) = develop (MultR e_ih_l1 e_ih_l2) in
                                                                (_ ** (e_ih_l3, ?Mdevelop13))
                                                                -- Equivalent à "{- develop -} (PMult ({-develop-} (PMult p11_dev p12_dev)) ({-develop-} (PMult p21_dev p22_dev)))"                                

---------- Proofs ----------                                                            
develop.Mdevelop1 = proof {
  intros;
  rewrite p_ih1;
  rewrite p_ih2;
  trivial;
}

develop.Mdevelop2 = proof {
  intros;
  rewrite p_ih_l;
  rewrite p_ih_r;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  refine Mult_dist;
  refine p;
  refine c1;
  refine c2;
  refine c3;
}

develop.Mdevelop3 = proof {
  intros;
  rewrite p_ih;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  trivial;
}

develop.Mdevelop4 = proof {
  intros;
  rewrite p_ih_l;
  rewrite p_ih_r;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  mrefine Mult_dist;
}

develop.Mdevelop5 = proof {
  intros;
  rewrite p_ih';
  rewrite p_ih;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  trivial;
}

develop.Mdevelop6 = proof {
  intros;
  rewrite p_ih_l;
  rewrite p_ih_r;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  mrefine Mult_dist_2;
}

develop.Mdevelop7 = proof {
  intros;
  rewrite p_ih_l;
  rewrite p_ih_e11;
  rewrite p_ih_r;
  rewrite p_ih_e12;
  mrefine Mult_dist_2;
}

develop.Mdevelop8 = proof {
  intros;
  rewrite p_ih_a;
  rewrite p_ih_b;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  mrefine Mult_dist_2;
}

develop.Mdevelop9 = proof {
  intros;
  rewrite p_ih_b;
  rewrite p_ih_a;
  rewrite p_ih_e11;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  rewrite p_ih_c;
  rewrite p_ih_e12;
  rewrite p_ih_a;
  rewrite p_ih_e21;
  rewrite p_ih_e22;
  mrefine Mult_dist_2;
}

develop.Mdevelop10 = proof {
  intros;
  rewrite p_ih;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  trivial;
}

develop.Mdevelop11 = proof {
  intros;
  rewrite p_ih;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  trivial;
}

develop.Mdevelop12 = proof {
  intros;
  rewrite p_ih_l2;
  rewrite p_ih_l1;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  rewrite p_ih_e21;
  rewrite p_ih_r2;
  rewrite p_ih_l1;
  rewrite p_ih_e12;
  rewrite p_ih_e22;
  rewrite p_ih_e11;
  mrefine Mult_dist;
}

develop.Mdevelop13 = proof {
  intros;
  rewrite p_ih_l3;
  rewrite p_ih_l1;
  rewrite p_ih_e11;
  rewrite p_ih_e12;
  rewrite p_ih_l2;
  rewrite p_ih_e22;
  rewrite p_ih_e21;
  trivial;
}
