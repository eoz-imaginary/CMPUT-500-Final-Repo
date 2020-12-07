(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Nat_complements.v                             *)
(****************************************************************************)
Require Import Arith.
Require Import Compare_dec.


Lemma eq_gt_O_dec : forall n : nat, {n = 0} + {n > 0}.
Proof.
induction n.
eauto.
destruct IHn.
subst.
generalize O.
intros.
eauto.
eauto.
Qed.


Lemma technical_lemma :
 forall y m : nat, S (y * m + (y + m) + m) = S y * m + (S y + m).
Proof.
intros.
simpl.
ring.
Qed.


Lemma lt_minus2 : forall n m : nat, n < m -> 0 < m - n.
Proof.
induction n.
intros.
destruct m.
eauto.
eauto.
induction m.
intros.
unfold Init.Nat.sub.
easy.
intros.
simpl.
intuition.
Qed.


Lemma minus_n_Sm : forall n m : nat, m < n -> pred (n - m) = n - S m.
Proof.
unfold lt.
unfold Init.Nat.sub.
induction n.
simpl.
intros.
eauto.
induction m.
destruct n.
reflexivity.
eauto.
destruct n.
eauto.
intuition.
Qed.
