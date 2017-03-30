(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import rel cl cl_eq cl_beta cl_beta_inv.

Set Implicit Arguments.

Notation cl_normal := (normal cl_beta).

Section cl_normal.
  
  Fact cl_S_normal : cl_normal S.          Proof. intros ? Hv; apply (cl_beta_S_0_inv Hv). Qed.
  Fact cl_K_normal : cl_normal K.          Proof. intros ? Hv; apply (cl_beta_K_0_inv Hv). Qed.
  Fact cl_I_normal : cl_normal I.          Proof. intros ? Hv; apply (cl_beta_I_0_inv Hv). Qed.
  Fact cl_var_normal p : cl_normal (µ p).  Proof. intros ? Hv; apply (cl_beta_var_0_inv Hv). Qed.

  Fact cl_var_x_normal p x : cl_normal x -> cl_normal (µ p o x).
  Proof.
    intros H v Hv.
    apply cl_beta_var_1_inv in Hv.
  Admitted.

  Fact cl_var_x_y_normal p x y : cl_normal x -> cl_normal y -> cl_normal (µ p o x o y).
  Proof.
    intros Hx Hy v Hv.
    apply cl_beta_var_2_inv in Hv.
  Admitted.

  Fact cl_K_x_normal x : cl_normal x -> cl_normal (K o x).
  Proof.
  Admitted.
  
  Fact cl_S_x_normal x : cl_normal x -> cl_normal (S o x).
  Proof.
  Admitted.
  
  Fact cl_S_x_y_normal x y : cl_normal x -> cl_normal y -> cl_normal (S o x o y).
  Proof.
    intros Hx Hy v Hv.
    apply cl_beta_S_2_inv in Hv.
  Admitted.

  Fact cl_normal_lft x y : cl_normal (x o y) -> cl_normal x.
  Proof.
    intros H1 a Ha.
    apply (H1 (a o y)).
    constructor 4; auto.
  Qed.
  
  Fact cl_normal_rt x y : cl_normal (x o y) -> cl_normal y.
  Proof.
    intros H1 a Ha.
    apply (H1 (x o a)).
    constructor 5; auto.
  Qed.
  
End cl_normal.
  
(* By Church-Rosser, normal forms are equivalent iff they are equal *)
  
Lemma cl_eq_normal f g : cl_normal f -> cl_normal g -> f ~cl g -> f = g.
Proof.
  rewrite <- cl_beta_equiv_cl_eq, cl_beta_cr.
  intros Hf Hg (h & H1 & H2).
  apply normal_crt_stop with (1 := Hf) in H1.
  apply normal_crt_stop with (1 := Hg) in H2.
  subst; auto.
Qed.
  
Corollary cl_neq_normal f g : cl_normal f -> cl_normal g -> f <> g -> ~ f ~cl g.
Proof.
  intros ? ? H ?; apply H, cl_eq_normal; auto.
Qed.
  
(* Now we can show that normal terms are not equivalent *)
  
Local Hint Resolve cl_S_normal cl_K_normal cl_I_normal
                   cl_K_x_normal cl_S_x_y_normal.

Fact cl_neq_S_K : ~ S ~cl K.
Proof.
  apply cl_neq_normal; auto; discriminate.
Qed.
  
Fact cl_SKI_neq_I : ~ S o K o I ~cl I.
Proof.
Admitted.
  
(**  Hence ~cl is not an extensional congruence:
  
     We have
       a/ for any x, (S o K o I) o x ~cl I o x but it is not
       b/ not (S o K o I ~cl I) 
*)

Fact cl_Kn_normal i : cl_normal (cl_Kn i).
Proof.
  induction i; simpl; auto.
Qed.
   
Local Hint Resolve cl_Kn_normal cl_Kn_inj.
  
(** The equivalence relation ~cl contains an infinite number of 
    equivalence classes because cl_Kn is injective 
    from cl_term/~cl to nat 
*)

Fact cl_Kn_infinite i j : cl_Kn i ~cl cl_Kn j -> i = j.
Proof.
  intros H; apply cl_eq_normal in H; auto.
Qed.

