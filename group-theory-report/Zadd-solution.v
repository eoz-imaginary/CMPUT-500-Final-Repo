(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Arith.
Require Import Nat_complements.
Require Import Zbase.
Require Import Z_succ_pred.

(*Recursive Definition addZ : Z -> Z -> Z :=
      OZ   y => y
    | (pos O)   y => (succZ y)
    | (pos (S n1))   y => (succZ (addZ (pos n1) y))
    | (neg O)   y => (predZ y)
    | (neg (S n1))   y => (predZ (addZ (neg n1) y)).
*)

Fixpoint add1 (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => succZ x2
  | S n0 => succZ (add1 x2 n0)
  end
 
 with add2 (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => predZ x2
  | S n0 => predZ (add2 x2 n0)
  end.

Definition addZ (x1 x2 : Z) : Z :=
  match x1 with
  | OZ => x2
  | pos n => add1 x2 n
  | neg n => add2 x2 n
  end.

Lemma addZ_eq1 : forall y : Z, addZ OZ y = y. Proof.
intros.
eauto.
Qed.

Lemma addZ_eq2 : forall y : Z, addZ (pos 0) y = succZ y.
Proof.
intros.
destruct y.
eauto.
reflexivity.
reflexivity.
Qed.

Lemma addZ_eq3 :
 forall (n1 : nat) (y : Z), addZ (pos (S n1)) y = succZ (addZ (pos n1) y).
Proof.
intros.
easy.
Qed.

Lemma addZ_eq4 : forall y : Z, addZ (neg 0) y = predZ y.
Proof.
intros.
destruct y.
eauto.
reflexivity.
reflexivity.
Qed.

Lemma addZ_eq5 :
 forall (n1 : nat) (y : Z), addZ (neg (S n1)) y = predZ (addZ (neg n1) y).
Proof.
intros.
easy.
Qed.



Lemma succ_addZ_l : forall x y : Z, addZ (succZ x) y = succZ (addZ x y).
Proof.
Admitted.

Lemma pred_addZ_l : forall x y : Z, addZ (predZ x) y = predZ (addZ x y).
Proof.
Admitted.

Lemma tech_add_pos_succZ :
 forall (x : nat) (y : Z), addZ (pos (S x)) y = succZ (addZ (pos x) y).
Proof.
intros.
apply addZ_eq3.
Qed.

Lemma tech_add_neg_predZ :
 forall (x : nat) (y : Z), addZ (neg (S x)) y = predZ (addZ (neg x) y).
Proof.
intros.
apply addZ_eq5.
Qed.

Lemma succ_addZ_r : forall x y : Z, addZ x (succZ y) = succZ (addZ x y).
Proof.
Admitted.

Lemma pred_addZ_r : forall x y : Z, addZ x (predZ y) = predZ (addZ x y).
Proof.
Admitted.

Lemma add_OZ : forall x : Z, addZ x OZ = x.
Proof.
Admitted.

Lemma add_IZ_succZ : forall x : Z, addZ x IZ = succZ x.
Proof.
Admitted.

Lemma add_mIZ_predZ : forall x : Z, addZ x (neg 0) = predZ x.
Proof.
Admitted.

Definition commutative (U : Set) (op : U -> U -> U) :=
  forall x y : U, op x y = op y x.

Theorem addZ_commutativity : commutative Z addZ.
Proof.
Admitted.

Lemma tech_add_pos_neg_posZ :
 forall n1 n2 : nat, n2 < n1 -> addZ (pos n1) (neg n2) = pos (n1 - S n2).
Proof.
Admitted.

Definition associative (U : Set) (op : U -> U -> U) :=
  forall x y z : U, op x (op y z) = op (op x y) z.

Theorem addZ_associativity : associative Z addZ.
Proof.
Admitted.

Definition IdZ (x : Z) := True.

Definition neutral (S : Set) (G : S -> Prop) (Add : S -> S -> S) 
  (O : S) := G O /\ (forall x : S, G x -> Add x O = x /\ Add O x = x).

Theorem addZ_neutral : neutral Z IdZ addZ OZ.
Proof.
red.
split.
easy.
intros.
split.
rewrite add_OZ.
eauto.
eauto.
Qed.

Definition oppZ (x : Z) :=
  match x return Z with
  | OZ => OZ
  | pos n => neg n
  | neg n => pos n
  end.

Lemma opp_succZ : forall x : Z, oppZ (succZ x) = predZ (oppZ x).
Proof.
intros.
unfold oppZ.
destruct x.
reflexivity.
eauto.
simpl.
destruct n.
eauto.
eauto.
Qed.

Lemma opp_predZ : forall x : Z, oppZ (predZ x) = succZ (oppZ x).
Proof.
intros.
unfold oppZ.
destruct x.
reflexivity.
simpl.
destruct n.
eauto.
eauto.
eauto.
Qed.

Lemma tech_add_pos_negZ : forall n : nat, addZ (pos n) (neg n) = OZ.
Proof.
Admitted.

Lemma tech_add_neg_posZ : forall n : nat, addZ (neg n) (pos n) = OZ.
Proof.
Admitted.

Lemma tech_add_pos_posZ :
 forall n m : nat, addZ (pos n) (pos m) = pos (S (n + m)).
Proof.
Admitted.

Lemma tech_add_neg_negZ :
 forall n m : nat, addZ (neg n) (neg m) = neg (S (n + m)).
Proof.
Admitted.

Theorem abs_eq_or_oppZ : forall x : Z, {absZ x = x} + {absZ x = oppZ x}.
Proof.
intros.
unfold absZ.
destruct x.
simpl.
eauto.
simpl.
try constructor.
eauto.
eauto.
Qed.
