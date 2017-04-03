(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import tacs rel.

Set Implicit Arguments.

Definition square X (R : X -> X -> Prop) := forall f a b, R f a -> R f b -> exists g, R a g /\ R b g.

Section square_crt.

  Variables (X : Type) (R : X -> X -> Prop) (HR : @square X R).

  Let ri_square_1 n f a b :
           f [R,1>> a
        -> f [R,n>> b 
        -> exists g, a [R,n>> g
                  /\ b [R,1>> g.
  Proof.
    revert f a.
    induction n as [ | n IHn ]; intros f a Ha Hf; simpl in Hf.
    subst; exists a; simpl; auto.
    destruct Hf as (x & H1 & H2).
    apply rel_iter_one in Ha.
    destruct (HR Ha H1) as (c & H3 & H4).
    rewrite rel_iter_one in H4.
    destruct (IHn _ _ H4 H2) as (g & H5 & H6).
    exists g; split; auto.
    exists c; auto.
  Qed.
  
  Theorem rel_iter_square n m f a b :
           f [R,n>> a 
        -> f [R,m>> b 
        -> exists g, a [R,m>> g
                  /\ b [R,n>> g.
  Proof.
    revert m f a b; induction n as [ | n IHn ]; intros m f a b Ha Hb; simpl in Ha.
    subst; exists b; simpl; auto.
    destruct Ha as (x & H1 & H2).
    rewrite rel_iter_one in H1.
    destruct (ri_square_1 _ _ H1 Hb) as (g & H3 & H4).
    destruct (IHn _ _ _ _ H2 H3) as (h & H5 & H6).
    exists h; simpl; split; auto.
    exists g; split; auto.
    apply rel_iter_one; auto.
  Qed.
  
  Theorem square_crt : square (crt R).
  Proof.
    intros f a b.
    do 2 rewrite rel_iter_eq_crt.
    intros (na & Ha) (nb & Hb).
    destruct rel_iter_square with (1 := Ha) (2 := Hb)
      as (g & H1 & H2); auto.

  Admitted.

End square_crt.

Definition confluent X (R : X -> X -> Prop) := square (crt R).
Definition church_rosser X (R : X -> X -> Prop) := 
    forall a b, crst R a b <-> exists f, crt R a f /\ crt R b f.

Section confluent_church_rosser.

  Variable (X : Type) (R : X -> X -> Prop) (HR : @confluent X R).
  
  Fact confluent_church_rosser : church_rosser R.
  Proof.
    intros a b; split.
    induction 1 as [ x y | x | x y _ (f & H1 & H2) | x y z _ (a & H1 & H2) _ (b & H3 & H4)].
    exists y; split; [ constructor 1 | constructor 2]; auto.
    exists x; split; constructor 2; auto.
    exists f; auto.
    destruct (HR H2 H3) as (f & ? & ?).
    exists f; split.
    constructor 3 with a; auto.
    constructor 3 with b; auto.
    
    intros (f & H1 & H2).
    constructor 4 with f.
    apply crt_inc_crst; auto.
    constructor 3.
    apply crt_inc_crst; auto.
  Qed.
    
End confluent_church_rosser.

Section church_rosser_confluent.

  Variable (X : Type) (R : X -> X -> Prop) (HR : @church_rosser X R).
  
  Fact church_rosser_confluent : confluent R.
  Proof.
    intros f a b Ha Hb.
    apply HR.
    constructor 4 with f.
    constructor 3. 
    apply crt_inc_crst; auto.
    apply crt_inc_crst; auto.
  Qed.
  
End church_rosser_confluent.

