(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Fact eq_gen { X } (P : X -> Type) x : (forall y, y = x -> P y) -> P x.
Proof. intros H; apply H, eq_refl. Qed.
  
Ltac gen_eq t y H := apply eq_gen with (x := t); intros y H.

Tactic Notation "generate" "eq" ident(H) "with" constr(t) "as" ident(x) := gen_eq t x H.
