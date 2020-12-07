(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Arith.
Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.

Definition leZ (x y : Z) :=
  match x return Prop with
  | OZ =>
      match y return Prop with
      | OZ => True
      | pos n => True
      | neg n => False
      end
  | pos n =>
      match y return Prop with
      | OZ => False
      | pos m => n <= m
      | neg m => False
      end
  | neg n =>
      match y return Prop with
      | OZ => True
      | pos m => True
      | neg m => m <= n
      end
  end.

Lemma sign_absZ : forall x : Z, leZ OZ (absZ x).
Proof.
intros.
unfold leZ.
destruct x.
simpl.
eauto.
simpl.
eauto.
simpl.
eauto.
Qed.

Lemma tech_le_pos_abs : forall x : Z, leZ OZ x -> absZ x = x.
Proof.
intros.
destruct x.
eauto.
eauto.
simpl.
destruct H.
Qed.

Theorem leZ_antisymmetric : forall x y : Z, leZ x y -> leZ y x -> x = y.
Proof.
unfold leZ.
destruct x.
destruct y.
intros.
eauto.
intros.
destruct n.
intuition.
intuition.
intros.
destruct H.
destruct y.
intros.
destruct H.
destruct n.
intuition.
intuition.
tauto.
destruct y.
tauto.
tauto.
destruct n.
intuition.
intuition.
Qed.

Definition ltZ (x y : Z) := leZ (succZ x) y.

Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

Lemma tech_lt_abs_OZ : forall x : Z, lt_absZ x (pos 0) -> x = OZ.
Proof.
Admitted.

Lemma tech_posOZ_pos : forall n : nat, leZ OZ (posOZ n).
Proof.
intros.
destruct n.
simpl.
eauto.
econstructor.
Qed.

Lemma le_opp_OZ_l : forall x : Z, leZ OZ x -> leZ (oppZ x) OZ.
Proof.
intros.
red.
destruct x.
simpl.
eauto.
simpl.
eauto.
simpl.
eauto.
Qed.

Lemma le_opp_OZ :
 forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = OZ.
Proof.
induction x.
intros.
eauto.
simpl.
destruct y.
intros.
rewrite H.
eauto.
simpl.
intros.
congruence.
simpl.
tauto.
simpl.
intros.
apply tech_lt_abs_OZ.
easy.
Qed.

Let opp_inv : forall x y : Z, x = oppZ y -> y = oppZ x.
Proof.
intros.
rewrite H.
unfold oppZ.
destruct y.
eauto.
eauto.
eauto.
Qed.
