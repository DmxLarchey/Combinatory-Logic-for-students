(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Bool.

Require Import rel cl cl_eq cl_beta cl_beta_inv cl_normal.

Set Implicit Arguments.

(** A decision procedure for detecting normal forms 
    and associated tactic that performs proof by reflection
**)

Section redex_and_normal_forms.

  (* A redex is either (I o x) or (K o x o y) or (S o x o y o z) 
     for some x, y, z. *)

  Definition cl_redex t :=
    match t with
      | I o _ => true
      | K o _ o _ => true
      | S o _ o _ o _ => true
      | _ => false
    end.
    
  (* This procedure detects if there is a redex inside a clterm
     and return a Boolean value of type bool *)

  Fixpoint cl_redex_free t :=
           negb (cl_redex t) 
        && match t with 
             | f o g => cl_redex_free f && cl_redex_free g 
             | _ => true 
           end.

  Hint Resolve cl_S_normal cl_K_normal cl_I_normal cl_var_normal
               cl_normal_lft cl_normal_rt.
               
  (* We show that normal terms are those which are redex free *)
  
  Theorem cl_redex_free_normal t : cl_normal t <-> cl_redex_free t = true.
  Proof.
    induction t as [ | | | x Hx a Ha | ]; simpl; try (split; auto; fail).
    repeat rewrite andb_true_iff.
    rewrite <- Hx, <- Ha.
    
    destruct x as [ | | | x k | p ]; simpl.
    
    split.
    intros H; split; auto.
    split; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & ? & ?); apply cl_S_x_normal; auto.
    
    split.
    intros H; split; auto.
    split; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & ? & ?); apply cl_K_x_normal; auto.
    
    split.
    intros H; exfalso; apply H with a; constructor 1.
    intros (C & _); discriminate C.
    
    Focus 2.
    split.
    intros H; split; auto.
    split; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & ? & ?); apply cl_var_x_normal; auto.
    
    destruct x as [ | | | x z | p ]; simpl.
    
    split.
    intros H; split; auto.
    split.
    apply cl_normal_lft in H; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & H & ?); apply cl_S_x_y_normal; auto.
    apply cl_normal_rt in H; auto.
    
    split.
    intros H; exfalso; apply H with k; constructor 2.
    intros (C & _); discriminate C.
    
    split.
    intros H; split; auto.
    split.
    apply cl_normal_lft in H; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & C & ?); exfalso.
    apply C with k; constructor 1.
    
    Focus 2.
    split.
    intros H; split; auto.
    split.
    apply cl_normal_lft in H; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & H & ?); apply cl_var_x_y_normal; auto.
    apply cl_normal_rt in H; auto.
    
    destruct x as [ | | | x y | p ]; simpl.
    
    split.
    intros H; exfalso; apply H with (z o a o (k o a)); constructor 3.
    intros (C & _); discriminate C.
    
    split.
    intros H; exfalso; apply H with (z o a); constructor 4; constructor 2.
    intros (_ & C & ?); exfalso.
    apply C with z; constructor 2.
    
    split.
    intros H; exfalso; apply H with (z o k o a); do 2 constructor 4; constructor 1.
    intros (_ & C & ?); exfalso.
    apply C with (z o k); constructor 4; constructor 1.
    
    Focus 2.
    split.
    intros H; split; auto.
    split.
    apply cl_normal_lft in H; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & H1 & H2) v Hv.
    apply cl_beta_app_inv in Hv.
    destruct Hv as [ (Hv & _)
                 | [ Hv 
                 | [ (f & g & Hv & H3)
                 | [ (f & H3 & Hv)
                   | (f & H3 & Hv) ] ] ] ]; try discriminate Hv.
    subst; revert Hv; apply H1.
    revert Hv; apply H2.
    
    split.
    intros H; split; auto.
    split.
    apply cl_normal_lft in H; auto.
    apply cl_normal_rt in H; auto.
    intros (_ & H1 & H2) v Hv.
    apply cl_beta_app_inv in Hv.
    destruct Hv as [ (Hv & _)
                 | [ Hv 
                 | [ (f & g & Hv & H3)
                 | [ (f & H3 & Hv)
                   | (f & H3 & Hv) ] ] ] ]; try discriminate Hv.
    subst; revert Hv; apply H1.
    revert Hv; apply H2.
  Qed.

  Ltac cl_normal_tac := apply cl_redex_free_normal; reflexivity.
  
  Fact test1 : cl_normal (K o (K o (S o K o K))).
  Proof. cl_normal_tac. Qed.
  
  Fact test2 p q : cl_normal (µ p o (K o S) o µ q).
  Proof. cl_normal_tac. Qed.
  
End redex_and_normal_forms.

