(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                           Group Theory in Coq                            *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*									    *)
(*                                  INRIA                                   *)
(*                             Sophia-Antipolis                             *)
(*									    *)
(*				 January 1996				    *)
(*                                                                          *)
(****************************************************************************)

Require Import Ensembles.
Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.
Require Import Zle.
Require Import Classical_Prop.
Require Import Relations_1.
Require Import Relations_1_facts.
Require Import Partial_Order.
Require Import Cpo.
Require Import Powerset.
Require Import Powerset_facts.
Require Import Gt.
Require Import Lt.
Require Import Compare.
Require Import Arith.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Image.
Require Import Infinite_sets.
Require Import Integers.
Require Import Laws.
Require Import Group_definitions.
Require Export gr.
Require Export g1.

Section Cinq.
Variable H : Ensemble U.
Variable H_inhabited : Inhabited U H.
Variable H_included_in_G : Included U H G.
Variable stability : endo_operation U H star.
Variable H_Finite : Finite U H.

Let h : forall x y : U, In U H x -> In U H y -> In U H (star x y).
Proof.
intros.
destruct H_inhabited.
eauto.
Qed.
Hint Resolve h.

Definition phi (a : U) (n : nat) : U := exp (pos n) a.

Lemma phi_unfold :
 forall (a : U) (n : nat), In U G a -> phi a (S n) = star a (phi a n).
Proof.
intros.
eauto.
Qed.

Lemma positive_powers :
 forall (a : U) (n : nat), In U H a -> In U H (phi a n).
Proof.
induction n.
intros.
eauto.
intros.
eauto.
Qed.

Lemma tech_exp :
 forall (a : U) (n : nat), In U G a -> star (phi a n) a = phi a (S n).
Proof.
Admitted.

Lemma tech_exp' : forall n : nat, phi e n = e.
Proof.
Admitted.

Lemma phi_exp :
 forall (a : U) (n m : nat),
 In U G a -> star (phi a n) (phi a m) = phi a (S (n + m)).
Proof.
Admitted.

Lemma powers_repeat :
 forall (a : U) (n m : nat),
 In U G a -> phi a n = phi a (S (S (n + m))) -> phi a m = inv a.
Proof.
Admitted.

Definition psi := phi.

Lemma psi_not_inj : forall a : U, In U H a -> ~ injective nat U (psi a).
Proof.
Admitted.

Theorem remaining :
 forall a : U,
 In U H a ->
 exists r : nat, (exists m : nat, phi a r = phi a (S (S (r + m)))).
Proof.
Admitted.

Theorem T_1_6_4 : Setsubgroup U H Gr.
Proof.
Admitted.
