(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith.

Require Import tacs.

Set Implicit Arguments.

Notation "R 'inc2' S" := (forall x y, R x y -> S x y) (at level 71).
Notation "R '~eq2' S" := (R inc2 S /\ S inc2 R) (at level 71).

Section included2.

  Variable (X Y : Type).
  
  Implicit Type (R T U : X -> Y -> Prop).
  
  Fact inc2_refl R : R inc2 R.
  Proof. auto. Qed.
  
  Fact inc2_trans R T U : R inc2 T -> T inc2 U -> R inc2 U.
  Proof. auto. Qed.
  
  Fact e2_refl R : R ~eq2 R.
  Proof. auto. Qed.
  
  Fact eq2_trans R T U : R ~eq2 T -> T ~eq2 U -> R ~eq2 U.
  Proof. intros [] []; split; auto. Qed.
  
End included2.

Reserved Notation "x '[' R '*>' y" (at level 70).
Reserved Notation "x '~[' R ']' y" (at level 70).

Section usual_closures.

  Variable (X : Type).
  
  Implicit Type (R T : X -> X -> Prop).
  
  (* Reflexivite and transitive closure *)
  
  Inductive crt R : X -> X -> Prop :=
    | in_crt_1 : forall x y,        R x y 
                          ->       x [R*> y
                          
    | in_crt_2 : forall x,         x [R*> x

    | in_crt_3 : forall x y z,     x [R*> y 
                          ->       y [R*> z 
                          ->       x [R*> z
  where "x [ R *> y" := (crt R x y).
  
  (* Reflexivite, symmetric and transitive closure *)
   
  Inductive crst R : X -> X -> Prop :=
    | in_crst_1 : forall x y,       R x y
                          ->       x ~[R] y
                          
    | in_crst_2 : forall x,        x ~[R] x
    
    | in_crst_3 : forall x y,      x ~[R] y 
                          ->       y ~[R] x
                          
    | in_crst_4 : forall x y z,    x ~[R] y 
                          ->       y ~[R] z 
                          ->       x ~[R] z
  where "x ~[ R ] y" := (crst R x y).

  (* Symmetric closure *)
  
  Inductive cs R : X -> X -> Prop :=
    | in_cs_1 : forall x y,       R x y
                        ->     cs R x y
                          
    | in_cs_2 : forall x y,    cs R x y 
                        ->     cs R y x.

  Fact crt_inc R : R inc2 crt R.
  Proof.
    apply in_crt_1.
  Qed.
  
  Fact crt_mono R T : R inc2 T -> crt R inc2 crt T.
  Proof.
    intros H x y. 
    induction 1 as [ | | x y ].
    constructor 1; auto.
  Admitted.

  Fact crt_idem R : crt (crt R) inc2 crt R.
  Proof.
    induction 1 as [ | | x y ]; auto.
  Admitted.
  
  Lemma crt_closure R T : R inc2 crt T <-> crt R inc2 crt T.
  Proof.
    split; intros H.
    apply inc2_trans with (2 := @crt_idem T).
    apply crt_mono, H.
    apply inc2_trans with (2 := H), crt_inc.
  Qed.
  
  Fact crst_inc R : R inc2 crst R.
  Proof.
  Admitted.
  
  Fact crst_mono R T : R inc2 T -> crst R inc2 crst T.
  Proof.
  Admitted.
  
  Fact crst_idem R : crst (crst R) inc2 crst R.
  Proof.
  Admitted.
  
  Lemma crst_closure R T : R inc2 crst T <-> crst R inc2 crst T.
  Proof.
  Admitted.
  
  Fact cs_inc R : R inc2 cs R.
  Proof. constructor 1; auto. Qed.
  
  Fact cs_mono R T : R inc2 T -> cs R inc2 cs T.
  Proof.
    intros H x y. 
    induction 1.
    constructor 1; auto.
    constructor 2; auto.
  Qed.
  
  Fact cs_idem R : cs (cs R) inc2 cs R.
  Proof.
    induction 1; auto.
    constructor 2; auto.
  Qed.
  
  Fact crt_inc_crst R x y : x [R*> y -> x ~[R] y.
  Proof.
    induction 1 as [ | | ? y ].
  Admitted.
  
  Fact cs_inc_crst R : cs R inc2 crst R.
  Proof.
    induction 1.
  Admitted.
  
  Lemma crt_sym R : cs R inc2 R -> cs (crt R) inc2 crt R.
  Proof.
    intros H.
    induction 1 as [ | x y _ IHxy ]; auto.
    induction IHxy as [ | | x y ].
    constructor 1; apply H; constructor 2; constructor 1; auto.
    constructor 2.
    constructor 3 with y; auto.
  Qed.

  Lemma crst_eq_crt_cs R : crst R ~eq2 crt (cs R).
  Proof.
    split.
    induction 1 as [ | | | x y ].
    constructor 1; constructor 1; auto.
    constructor 2.
    apply crt_sym.
    apply cs_idem.
    constructor 2; constructor 1; auto.
    constructor 3 with y; auto.
    apply inc2_trans with (2 := @crst_idem _).
    apply inc2_trans with (2 := @crt_inc_crst _).
    apply crt_mono, cs_inc_crst.
  Qed.

End usual_closures.

Notation "x [ R *> y" := (crt R x y) (at level 70).
Notation "x ~[ R ] y" := (crst R x y) (at level 70).

Reserved Notation "x '[' R ',' n '>>' y" (at level 70).
 
Section rel_iter.

  Variable (X : Type).
  
  Implicit Type (R : X -> X -> Prop).
  
  Fixpoint rel_iter R n (x y : X) : Prop :=
    match n with
      | 0   => x = y
      | S n => exists a, R x a /\ a [ R , n >> y
    end
  where "x [ R , n >> y" := (rel_iter R n x y).
    
  Fact rel_iter_one R x y : R x y <-> x [R,1>> y.
  Proof.
    simpl; split.
    exists y; split; auto.
    intros (a & ? & ?); subst a; auto.
  Qed.

  Fact rel_iter_plus R n m x y : x [R,n+m>> y <-> exists a, x [R,n>> a /\ a [R,m>> y.
  Proof.
    revert x y; induction n as [ | n IHn ]; intros x y; split; simpl.
    
    exists x; auto.
    intros (a & ? & Ha); subst a; auto.
    
    intros (a & H1 & H2).
    apply IHn in H2.
    destruct H2 as (b & H2 & H3).
    exists b; split; auto; exists a; auto.
    
    intros (a & (b & H1 & H2) & H3).
    exists b; split; auto.
    apply IHn; exists a; auto.
  Qed.
  
  Fact rel_iter_inv R n x y : x [R,1+n>> y <-> exists a, x [R,n>> a /\ R a y.
  Proof.
    rewrite plus_comm, rel_iter_plus.
    split; intros (a & ? & ?); exists a; 
    split; auto; apply (rel_iter_one R); auto.
  Qed.

  Lemma rel_iter_eq_crt R x y : x [R*> y <-> exists n, x [R,n>> y.
  Proof.
    split.
  
    induction 1 as [ | | x y z H1 (n1 & Hn1) H2 (n2 & Hn2) ].
    exists 1, y; simpl; auto.
    exists 0; simpl; auto.
    exists (n1+n2). 
    apply rel_iter_plus.
    exists y; auto.
  
    intros (n & Hn).
    revert x y Hn; induction n as [ | n IHn ]; simpl; intros x z H.
    subst; constructor 2.
    destruct H as (y & H1 & H2).
    constructor 3 with y; auto.
    constructor 1; auto.
  Qed.
  
End rel_iter.

Notation "x [ R , n >> y" := (rel_iter R n x y) (at level 70).

Section normal.

  Variable (X : Type) (R : X -> X -> Prop).

  Definition normal m := forall x, ~ R m x.

  Fact normal_crt_stop m : normal m -> forall y, m [R*> y -> m = y.
  Proof.
    intros Hm y.
    rewrite rel_iter_eq_crt.
    intros ([ | n ] & Hn); simpl in Hn; auto.
    destruct Hn as (z & Hz & _).
    exfalso; revert Hz; apply Hm.
  Qed.
  
End normal.
