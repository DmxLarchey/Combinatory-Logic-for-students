(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Set Implicit Arguments.

Parameter Var : Type.

(* Definition of the terms of combinatory algebras *)

Inductive clterm : Type :=
 | cl_S   : clterm
 | cl_K   : clterm
 | cl_I   : clterm
 | cl_app : clterm -> clterm -> clterm
 | cl_var : Var -> clterm.
   
(* Some short notations *)
   
Infix "o" := (@cl_app) (at level 61, left associativity).
Notation " 'µ' x " := (@cl_var x) (at level 0).
  
(* an n-iterate of cl_K *)
  
Fixpoint cl_Kn n :=
  match n with
    | 0   => cl_K
    | S n => cl_K o cl_Kn n
  end.
    
(* A measure of the size of terms *)

Fixpoint cl_size f :=
  match f with
    | f o g => 1 + cl_size f + cl_size g
    | _     => 1
  end.
    
(** Some more short notations 
    Beware that S masks the S : nat -> nat
    successor constructor of the type nat 
*)

Notation K := cl_K.
Notation S := cl_S.
Notation I := cl_I.
  
(* cl_* constructors are injective *)
  
Fact cl_var_inj p q : µ p = µ q -> p = q.
Proof.
  injection 1; auto.
Qed.
  
Fact cl_app_inj f g a b : f o a = g o b -> f = g /\ a = b.
Proof.
  injection 1; auto.
Qed.

(* The size of cl_Kn *)

Fact cl_Kn_size i : cl_size (cl_Kn i) = 2*i+1.
Proof.
  induction i; simpl; omega.
Qed.

(* The map n -> cl_Kn is injective as well *)

Corollary cl_Kn_inj i j : cl_Kn i = cl_Kn j -> i = j.
Proof.
  intros H.
  apply f_equal with (f := cl_size) in H.
  do 2 rewrite cl_Kn_size in H.
  omega.
Qed.

