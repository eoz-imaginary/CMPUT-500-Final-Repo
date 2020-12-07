(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Arith.
Require Import Zbase.

Definition succZ (x : Z) :=
  match x return Z with
  | OZ => IZ
  | pos n => pos (S n)
  | neg n => match n return Z with
             | O => OZ
             | S m => neg m
             end
  end.

Definition predZ (x : Z) :=
  match x return Z with
  | OZ => neg 0
  | pos n => match n return Z with
             | O => OZ
             | S m => pos m
             end
  | neg n => neg (S n)
  end.

Lemma pred_succZ : forall x : Z, predZ (succZ x) = x.
Proof.
intros.
unfold predZ.
destruct x.
eauto.
reflexivity.
simpl.
destruct n.
eauto.
eauto.
Qed.

Lemma succ_predZ : forall x : Z, succZ (predZ x) = x.
Proof.
intros.
unfold succZ.
destruct x.
reflexivity.
simpl.
destruct n.
eauto.
eauto.
simpl.
eauto.
Qed.

Lemma succ_pred_pred_succZ : forall x : Z, succZ (predZ x) = predZ (succZ x).
Proof.
intros.
unfold succZ.
destruct x.
reflexivity.
simpl.
destruct n.
eauto.
eauto.
simpl.
destruct n.
eauto.
eauto.
Qed.

Lemma tech_pred_posZ : forall n : nat, 0 < n -> predZ (pos n) = pos (pred n).
Proof.
induction n.
easy.
intros.
unfold predZ.
simpl.
eauto.
Qed.
