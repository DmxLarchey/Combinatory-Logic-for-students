(* Exercise 3 *)
(* Consider the following definitions *)
(* Note: any theorem --- either proven or admitted --- can be used for proving the following
  ones  *)

Require Import Omega.

Inductive Even : nat -> Prop :=
|  Ev0: Even 0
|  Ev2 : forall n, Even n -> Even (S (S n)).

Definition Odd n := Even (S n).

Lemma Even_inv n : Even n -> n = 0 \/ exists m, n = S (S m) /\ Even m.
Proof.
  intros H.
  induction H as [ | n Hn IHn ].
  left; trivial.
  right; exists n; split; trivial.
Qed.

(* Prove the following lemmas (remove the Admitted) *)


Lemma E6: Even 6.
Proof.
  apply Ev2, Ev2, Ev2, Ev0.
Qed.

Lemma E30: Even 30.
Proof.
  repeat constructor.
Qed.

Lemma O7 : Odd 5.
Proof.
  red. 
  apply E6.
Qed.

Lemma E_double : forall n:nat, Even (2*n).
Proof.
  induction n as [ | n IHn ].
  constructor.
  replace (2 * S n) with (S (S (2*n))).
  constructor; trivial.
  (*
  simpl; f_equal.
  rewrite (plus_comm _ (S _)).
  simpl; f_equal.
  rewrite plus_comm; trivial.
  *)
  omega.
Qed.

Lemma not_E1 : ~ Even 1.
Proof.
  intros H.
  inversion H.
Qed.

Lemma Even_SS_inv : forall n, Even (S (S n)) -> Even n.
Proof.
  intros n Hn.
  apply Even_inv in Hn.
  destruct Hn as [ H | (m & E & Hm) ].
  discriminate.
  injection E; intro; subst; trivial.
Qed.

Lemma Odd_not_Even : forall n, Odd n -> ~ Even n.
Proof.
  intros n H1 H2.
  induction n as [ | n IHn ].
  apply not_E1 in H1; destruct H1.
  apply Even_SS_inv in H1.
  apply (IHn H2), H1.
Qed.

Lemma Odd_not_Even' : forall n, Odd n -> ~ Even n.
Proof.
  intros n H1 H2.
  induction H2 as [ | n Hn IHn ].
  revert H1; apply not_E1.
  apply IHn, Even_SS_inv, H1. 
Qed.

Lemma Even_not_Odd : forall n, Even n -> ~ Odd n.
Proof.
  intros n H1 H2.
  apply (Odd_not_Even _ H2 H1).
Qed.

Lemma Even_double : forall n, Even n -> exists p:nat, n = 2*p.
Proof.
  induction 1 as [ | n Hn IHn ].
  exists 0; trivial.
  destruct IHn as (p & Hp).
  exists (S p); omega.
Qed.

Lemma Odd_S_double : forall n, Odd n -> exists p:nat, n = S( p + p).
Proof.
  intros n Hn.
  apply Even_double in Hn.
  destruct Hn as (p & Hp).
  destruct p.
  discriminate.
  exists p; omega.
Qed.

(* Consider the following  function *)

Fixpoint evenb (n: nat):  bool :=
match  n with O => true
            | 1 => false
            | S (S p) => evenb p
end.

Lemma evenb_Sn : forall n:nat, evenb (S n) = negb (evenb n).
Proof.
  induction n as [ | n IHn ]; trivial.
  rewrite IHn; simpl.
  destruct (evenb n); simpl; trivial.
Qed.

Lemma evenb_if : forall n:nat, if evenb n then Even n else Odd n.
Proof.
  induction n as [ | n IHn ].
  simpl; constructor.
  rewrite evenb_Sn.
  destruct (evenb n); simpl.
  constructor; trivial.
  trivial.
Qed.

Lemma evenb_iff : forall n, evenb n = true  <-> Even n.
Proof.
  intros n.
  generalize (evenb_if n).
  destruct (evenb n).
  split; auto.
  intros H1; split.
  discriminate.
  intros H2.
  exfalso; apply (Odd_not_Even n); trivial.
Qed.


Goal Even 560.
Proof.
rewrite <- evenb_iff.
reflexivity.
Qed.

