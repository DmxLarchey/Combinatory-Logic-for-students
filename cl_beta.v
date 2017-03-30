(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Bool.

Require Import tacs rel square cl cl_eq cl_confluent.

Set Implicit Arguments.

(* The notation of reduction in combinatory logic *)

Reserved Notation "x '-b->' y" (at level 70).

Inductive cl_beta : clterm -> clterm -> Prop :=

  | in_cl_beta_I   : forall x,     I o x          -b-> x
    
  | in_cl_beta_K   : forall x y,   K o x o y      -b-> x
  
  | in_cl_beta_S   : forall x y z, S o x o y o z  -b-> x o z o (y o z)

  | in_cl_beta_lft : forall f g a,          f     -b-> g 
                                         -> f o a -b-> g o a

  | in_cl_beta_rt  : forall f a b,              a -b->     b
                                         -> f o a -b-> f o b

where "x -b-> y" := (cl_beta x y).

Notation "x '-b>>' y" := (crt cl_beta x y) (at level 70).
Notation "x '~b' y" := (crst cl_beta x y) (at level 70).

Fact cl_beta_rt_beta_eq f g : f -b>> g -> f ~b g.
Proof. apply crt_inc_crst. Qed.
  
Fact cl_beta_cl_eq f g : f -b-> g -> f ~cl g.
Proof.
  induction 1.
  constructor.
Admitted.
  
Fact cl_beta_rt_cl_eq f g : f -b>> g -> f ~cl g.
Proof.
  induction 1 as [ | | f g h ].
Admitted.

Fact cl_beta_rt_app f g a b : f -b>> g -> a -b>> b -> f o a -b>> g o b.
Proof.
  intros H1 H2.
  constructor 3 with (f o b).
  induction H2 as [ | | a y b ].
  constructor 1; constructor 5; auto.
  constructor 2.
  constructor 3 with (f o y); auto.
  induction H1 as [ | | f h g ].
  constructor 1; constructor 4; auto.
  constructor 2.
  constructor 3 with (h o b); auto.
Qed.
  
Fact cl_beta_eq_cl_eq f g : f ~b g -> f ~cl g.
Proof.
  induction 1 as [ | | | f g h ].
Admitted.

Fact cl_beta_eq_app f g a b : f ~b g -> a ~b b -> f o a ~b g o b.
Proof.
Admitted.

Fact cl_beta_equiv_cl_eq f g : f ~b g <-> f ~cl g.
Proof.
  split.
  apply cl_beta_eq_cl_eq.
  induction 1 as [ | | | | x y | | | ].
Admitted.

(* See the definition of cl_rho in file cl_confluent *)

Local Notation "x '-r->' y" := (cl_rho x y) (at level 70).
Local Notation "x '-r>>' y" := (crt cl_rho x y) (at level 70).

Fact cl_beta_rho f g : f -b-> g -> f -r-> g.
Proof.
  induction 1.
Admitted.

Fact cl_rho_beta_rt f g : f -r-> g -> f -b>> g.
Proof.
  induction 1.
Admitted.

Lemma cl_rho_rt_beta_rt_eq f g : f -r>> g <-> f -b>> g.
Proof.
  split.
    
  induction 1 as [ | | x y ]; admit.

  induction 1 as [ | | x y ]; admit.
Admitted.

Corollary cl_rho_cl_eq f g : f -r-> g -> f ~cl g.
Proof.
  intro; apply cl_beta_rt_cl_eq, cl_rho_beta_rt; auto.
Qed.

(* Since (crt cl_rho) and (crt cl_beta) are equivalent
   and since cl_rho is confluent then so is cl_beta *)

Theorem cl_beta_confluent : confluent cl_beta.
Proof.
  intros f a b.
  do 2 rewrite <- cl_rho_rt_beta_rt_eq.
  intros H2 H3.
  destruct (cl_rho_confluent H2 H3) as (g & H4 & H5).
  exists g; do 2 rewrite <- cl_rho_rt_beta_rt_eq; auto.
Qed.

Fact cl_beta_cr f g : f ~b g <-> exists h, f -b>> h /\ g -b>> h.
Proof.
  apply confluent_church_rosser, cl_beta_confluent.
Qed.
  
