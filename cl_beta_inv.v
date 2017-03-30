(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import cl cl_eq cl_beta.

Set Implicit Arguments.

Section inversion_lemmas.
  
  Lemma cl_beta_inv f g : 
       f -b-> g 
    -> f = I o g
    \/ (exists y, f = K o g o y)
    \/ (exists x y z, f = S o x o y o z /\ g = x o z o (y o z))
    \/ (exists u v a, f = u o a /\ g = v o a /\ u -b-> v)
    \/ (exists u a b, f = u o a /\ g = u o b /\ a -b-> b).
  Proof.
    induction 1.
    do 0 right; left; auto.
    do 1 right; left; exists y; auto.
    do 2 right; left; exists x, y, z; auto.
    do 3 right; left; exists f, g, a; auto.
    do 4 right; exists f, a, b; auto.
  Qed.
  
  Fact cl_beta_app_inv f g v :
       f o g -b-> v
    -> (f = I /\ g = v)
    \/ (f = K o v)
    \/ (exists a b, f = S o a o b /\ v = a o g o (b o g))
    \/ (exists f', v = f' o g /\ f -b-> f')
    \/ (exists g', v = f o g' /\ g -b-> g').
  Proof.
    intros H.
    apply cl_beta_inv in H.
    destruct H as [ H 
                | [ (y & H)
                | [ (x & y & z & H1 & H2)
                | [ (x & y & z & H1 & H2 & H3)
                  | (x & y & z & H1 & H2 & H3) ] ] ] ].
    apply cl_app_inj in H; auto.
  Admitted.

  Fact cl_beta_var_0_inv p v : µ p -b-> v -> False.
  Proof.
    intros H.
    apply cl_beta_inv in H.
    destruct H as [ H 
                | [ (y & H)
                | [ (x & y & z & H & _)
                | [ (x & y & z & H & _ & _)
                  | (x & y & z & H & _ & _) ] ] ] ]; try discriminate H.
  Qed.

  Fact cl_beta_var_1_inv p a v : µ p o a -b-> v -> exists b, v = µ p o b /\ a -b-> b.
  Proof.
    intros H.
    apply cl_beta_app_inv in H.
    destruct H as [ (H & H2)
                | [  H
                | [ (f & g & H & _)
                | [ (f & H1 & H2)
                  | (f & H1 & H2) ] ] ] ]; subst; try discriminate H.
  Admitted.
  
  Fact cl_beta_var_2_inv p a b v : µ p o a o b -b-> v -> (exists a', v = µ p o a' o b /\ a -b-> a')
                                                      \/ (exists b', v = µ p o a o b' /\ b -b-> b').
  Proof.
    intros H.
    apply cl_beta_app_inv in H.
    destruct H as [ (H & H2)
                | [  H
                | [ (f & g & H & H2)
                | [ (f & H & H2)
                  | (f & H & H2) ] ] ] ]; subst; try discriminate H.
  Admitted.
  
  Fact cl_beta_K_0_inv v : K -b-> v -> False.
  Proof.
    intros H.
    apply cl_beta_inv in H.
    destruct H as [ H 
                | [ (y & H)
                | [ (x & y & z & H & _)
                | [ (x & y & z & H & _ & _)
                  | (x & y & z & H & _ & _) ] ] ] ]; try discriminate H.
  Qed.

  Fact cl_beta_K_1_inv a v : K o a -b-> v -> exists b, v = K o b /\ a -b-> b.
  Proof.
  Admitted.
  
  Fact cl_beta_K_2 a b v : K o a o b -b-> v -> v = a 
                                            \/ (exists a', v = K o a' o b /\ a -b-> a')
                                            \/ (exists b', v = K o a o b' /\ b -b-> b').
  Proof.
  Admitted.
  
  Fact cl_beta_S_0_inv v : S -b-> v -> False.
  Proof.
    intros H.
    apply cl_beta_inv in H.
    destruct H as [ H 
                | [ (y & H)
                | [ (x & y & z & H & _)
                | [ (x & y & z & H & _ & _)
                  | (x & y & z & H & _ & _) ] ] ] ]; try discriminate H.
  Qed.

  Fact cl_beta_S_1_inv a v : S o a -b-> v -> exists b, v = S o b /\ a -b-> b.
  Proof.
  Admitted.

  Fact cl_beta_S_2_inv a b v :  S o a o b -b-> v
                         -> exists d, (v = S o d o b /\ a -b-> d)
                                   \/ (v = S o a o d /\ b -b-> d).
  Proof.
  Admitted.
  
  Fact cl_beta_I_0_inv v : I -b-> v -> False.
  Proof.
  Admitted.

End inversion_lemmas.
