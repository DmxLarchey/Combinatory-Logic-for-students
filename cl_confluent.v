(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import rel square cl.

Set Implicit Arguments.

Section cl_confluent.

  Reserved Notation "x '-r->' y" (at level 70).

  Inductive cl_rho : clterm -> clterm -> Prop :=
  
    | in_cl_rho_I : forall x,               I o x -r-> x
  
    | in_cl_rho_K : forall x y,         K o x o y -r-> x

    | in_cl_rho_S : forall x y z,   S o x o y o z -r-> x o z o (y o z)

    | in_cl_rho_0 : forall f,                   f -r-> f
    
    | in_cl_rho_1 : forall f g a b,         f     -r-> g 
                                 ->             a -r->     b 
                                 ->         f o a -r-> g o b

  where "x -r-> y" := (cl_rho x y).
  
  Infix "-r>>" := (crt cl_rho) (at level 70).

  Fact cl_rho_I_inv v : I -r-> v -> v = I.
  Proof. inversion_clear 1; auto. Qed.

  Fact cl_rho_K_inv v : K -r-> v -> v = K.
  Proof. inversion_clear 1; auto. Qed.

  Fact cl_rho_S_inv v : S -r-> v -> v = S.
  Proof. inversion_clear 1; auto. Qed.
  
  Fact cl_rho_var_inv p v : µ p -r-> v -> v = µ p.
  Proof. inversion_clear 1; auto. Qed.
  
  Fact cl_rho_inv f g : 
       f -r-> g 
    -> f = I o g
    \/ (exists y, f = K o g o y)
    \/ (exists x y z, f = S o x o y o z /\ g = x o z o (y o z))
    \/ f = g
    \/ (exists u v a b, f = u o a /\ g = v o b /\ u -r-> v /\ a -r-> b).
  Proof.
    induction 1.
    do 0 right; left; auto.
    do 1 right; left; exists y; auto.
    do 2 right; left; exists x, y, z; auto.
    do 3 right; left; auto.
    do 4 right; exists f, g, a, b; auto.
  Qed.

  Fact cl_rho_app_inv f a v : 
      f o a -r-> v 
   -> (exists g b, v = g o b /\ f -r-> g /\ a -r-> b)
   \/ (f = I /\ a = v)
   \/ (f = K o v)
   \/ (exists x y, f = S o x o y /\ v = x o a o (y o a)).
  Proof.
    intros H.
    apply cl_rho_inv in H.
    destruct H as [ H 
                | [ (y & H) 
                | [ (x & y & z & H & ?)
                | [ H
                | (x & y & z & k & H & ? & ? & ?) ] ] ] ]; subst.
    apply cl_app_inj in H; destruct H; subst.
    right; left; auto.
  Admitted.

  Fact cl_rho_I_app_inv a v : 
         I o a -r-> v 
      -> (exists b, v = I o b /\ a -r-> b)
       \/ a = v.
  Proof.
    intros H.
    apply cl_rho_app_inv in H.
    destruct H as [ (g1 & b1 & ? & G1 & G2)  
                | [ ? 
                | [ ?
                  | (x1 & y1 & G1 & G2) ] ] ].
    apply cl_rho_I_inv in G1; subst.
    left; exists b1; auto.
  Admitted.

  Fact cl_rho_K_app_inv a v : K o a -r-> v -> exists b, v = K o b /\ a -r-> b.
  Proof.
    intros H.
    apply cl_rho_app_inv in H.
    destruct H as [ (g1 & b1 & ? & G1 & G2)  
                | [ ? 
                | [ ?
                  | (x1 & y1 & G1 & G2) ] ] ].
    apply cl_rho_K_inv in G1; subst; auto.
  Admitted.

  Fact cl_rho_S_app_inv a v : S o a -r-> v -> exists b, v = S o b /\ a -r-> b.
  Proof.
  Admitted.

  Fact cl_rho_S_app2_inv a b v : S o a o b -r-> v -> exists x y, v = S o x o y /\ a -r-> x /\ b -r-> y.
  Proof.
    intros H.
    apply cl_rho_app_inv in H.
    destruct H as [ (g1 & b1 & ? & G1 & G2)  
                | [ ? 
                | [ ?
                  | (x1 & y1 & G1 & G2) ] ] ].
    apply cl_rho_S_app_inv in G1.
    destruct G1 as (c & ? & ?); subst.
    exists c, b1; auto.
    discriminate (proj1 H).
    discriminate H.
    discriminate G1.
  Qed.
  
  Ltac cl_rho_inv_0 :=
    match goal with 
      | H : S      -r-> ?v |- _ => apply cl_rho_S_inv in H; subst v
      | H : K      -r-> ?v |- _ => apply cl_rho_K_inv in H; subst v
      | H : I      -r-> ?v |- _ => apply cl_rho_I_inv in H; subst v
      | H : µ _    -r-> ?v |- _ => apply cl_rho_var_inv in H; subst v
    end.
    
  Ltac cl_rho_inv_1 b :=
    match goal with 
      | H : S o ?x -r-> ?v |- _ => apply cl_rho_S_app_inv in H; destruct H as (b & E & H); subst v
      | H : K o ?x -r-> ?v |- _ => apply cl_rho_K_app_inv in H; destruct H as (b & E & H); subst v
    end.
    
  Ltac cl_rho_inv_2 a b :=
    match goal with 
      | H : S o ?x o ?y -r-> ?v |- _ => apply cl_rho_S_app2_inv in H; destruct H as (a & b & E & H & ?); subst v
    end.

  Theorem cl_rho_square : square cl_rho.
  Proof.
    intros f.
    induction f as [ | | | f Hf a Ha | p ]; intros u v.

    intros; do 2 cl_rho_inv_0.
    exists S; split; constructor 4.

    intros; do 2 cl_rho_inv_0.
    exists K; split; constructor 4.
    
    intros; do 2 cl_rho_inv_0.
    exists I; split; constructor 4.

    Focus 2.
    intros; do 2 cl_rho_inv_0.
    exists (µ p); split; constructor 4.

    intros H1 H2.
    apply cl_rho_app_inv in H1.
    apply cl_rho_app_inv in H2.
    destruct H1 as [ (g1 & b1 & G0 & G1 & G2)  
             | [ (G1 & G2) | [ G1 | (x1 & y1 & G1 & G2) ] ] ];
    destruct H2 as [ (g2 & b2 & H0 & H1 & H2)  
             | [ (H1 & H2) | [ H1 | (x2 & y2 & H1 & H2) ] ] ]; subst.

    admit.

    cl_rho_inv_0.
    exists b1; split; auto; constructor.

    cl_rho_inv_1 w.
    exists w; split; auto; constructor.

    cl_rho_inv_2 x3 y3.
    exists (x3 o b1 o (y3 o b1)); split.
    constructor 3.
    do 2 constructor 5; auto.
    
    admit.
    
    exists v; split; constructor.
    
    discriminate H1.
    
    admit.
    
    admit.
   
    admit.
    
    admit.

    discriminate H1.
    
    cl_rho_inv_2 x3 y3.
    exists (x3 o b2 o (y3 o b2)); split.
    do 2 constructor 5; auto.
    constructor.

    admit.
    
    admit.
    
    apply cl_app_inj in H1; destruct H1 as (H1 & ?); subst y2.
    apply cl_app_inj, proj2 in H1; subst x2.
    exists (x1 o a o (y1 o a)); split; constructor.
  Admitted.
  
  Corollary cl_rho_confluent : confluent cl_rho.
  Proof.
    apply square_crt, cl_rho_square.
  Qed.

End cl_confluent.
