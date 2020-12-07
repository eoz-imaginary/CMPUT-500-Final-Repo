(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Import Arith.
Require Export Euclid.
Require Import ZArith.

 
Theorem lt_mult_right : forall x y z t : nat, x < z -> y < t -> x * y < z * t.
Proof.
Admitted.
 
Theorem le_mult_right : forall x y : nat, 0 < y -> x <= x * y.
Proof.
Admitted.
(***********************************************************************
  **********************************************************************
  **********************************************************************
  	FACTORIAL*)
 
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.
(***********************************************************************
  **********************************************************************
  **********************************************************************
  	POWER*)
 
Fixpoint power (x n : nat) {struct n} : nat :=
  match n with
  | O => 1
  | S n' => x * power x n'
  end.
 
Lemma power_SO : forall x : nat, power 1 x = 1.
Proof.
Admitted.
 
Lemma power_lt_O : forall x n : nat, 0 < x -> 0 < power x n.
Proof.
Admitted.
 
Lemma power_le : forall x n : nat, 0 < n -> x <= power x n.
Proof.
induction n.
intros.
destruct x.
try omega.
simpl.
try omega.
destruct x.
intros.
omega.
destruct n.
simpl.
intros.
try omega.
simpl.
intuition.
Qed.
 
Lemma power_mult :
 forall x a b : nat, power x a * power x b = power x (a + b).
Proof.
Admitted.
 
Lemma power_power : forall x a b : nat, power (power x a) b = power x (a * b).
Proof.
Admitted.
 
Lemma SO_power : forall x : nat, power 1 x = 1.
Proof.
intros.
apply power_SO.
Qed.
 
Lemma power_O : forall n : nat, 1 <= n -> power 0 n = 0.
Proof.
intros.
destruct n.
simpl.
intuition.
intuition.
Qed.
(**************************************************************************
  *************************************************************************
                                                                         *)
 
Definition plus_eq := f_equal2 plus.
 
Definition mult_eq := f_equal2 mult.
 
Definition minus_eq := f_equal2 minus.
 
Lemma lt_minus_O_lt : forall n m : nat, m < n -> 0 < n - m.
Proof.
intros.
omega.
Qed.
 
Lemma eq_minus : forall a b c : nat, c < a -> a - c = b - c -> a = b.
Proof.
induction a.
simpl.
intros.
rewrite H0.
intuition.
simpl.
destruct b.
simpl.
destruct c.
eauto.
intuition.
destruct c.
intros.
eauto.
intuition.
Qed.
 
Lemma eq_minus' :
 forall a b c : nat, c <= a -> c <= b -> a - c = b - c -> a = b.
Proof.
induction a.
simpl.
intros.
rewrite H1.
intuition.
destruct a.
destruct b.
try destruct c.
intros.
eauto.
intros.
easy.
destruct b.
intros.
eauto.
destruct c.
eauto.
omega.
destruct b.
destruct c.
simpl.
congruence.
simpl.
omega.
destruct c.
simpl.
omega.
omega.
Qed.
 
Lemma eq_plus : forall a b c : nat, c + a = c + b -> a = b.
Proof.
induction a.
destruct b.
intros.
eauto.
destruct b.
try destruct c.
intros.
eauto.
simpl.
intuition.
destruct c.
intros.
eauto.
destruct c.
eauto.
intuition.
destruct b.
intros.
destruct c.
try discriminate.
intuition.
destruct c.
intros.
eauto.
simpl.
intuition.
Qed.
 
Lemma plus_eqO : forall x y : nat, x + y = 0 -> x = 0.
Proof.
intros.
destruct x.
eauto.
intuition.
Qed.
 
Lemma mult_eqO : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
Proof.
intros.
destruct a.
eauto.
right.
destruct b.
eauto.
simpl in H.
try discriminate.
Qed.
 
Lemma mult_SO : forall x y : nat, x * y = 1 -> x = 1.
Proof.
induction x.
intros.
eauto.
simpl.
unfold Init.Nat.add.
destruct y.
intuition.
destruct y.
intuition.
try discriminate.
Qed.
 
Lemma mult_eq_Sn : forall a b : nat, 0 < b -> a * b = b -> a = 1.
Proof.
Admitted.
(*****************************************************************************)
 
Inductive is_div : nat -> nat -> nat -> nat -> Prop :=
    is_div_def :
      forall a b q r : nat, r < b -> a = q * b + r -> is_div a b q r.
 
Inductive ex_div : nat -> nat -> Prop :=
    ex_div_def : forall a b q r : nat, is_div a b q r -> ex_div a b.
 
Lemma div_x_nO : forall x y q r : nat, is_div x y q r -> y <> 0.
Proof.
destruct x.
destruct q.
destruct r.
intuition.
inversion H.
omega.
intuition.
inversion H.
omega.
destruct r.
intros.
destruct H.
intuition.
intuition.
inversion H.
omega.
intros.
destruct H.
intuition.
Qed.
 
Lemma div_x_O_r : forall x q r : nat, is_div 0 x q r -> r = 0.
Proof.
Admitted.
 
Lemma div_x_O_q : forall x q r : nat, is_div 0 x q r -> q = 0.
Proof.
Admitted.
 
Lemma div_pred :
 forall x y q : nat,
 0 < x -> is_div x y q 0 -> is_div (pred x) y (pred q) (pred y).
Proof.
Admitted.
 
Lemma div_SxS :
 forall x y q r : nat,
 0 < r -> is_div x y q r -> is_div (pred x) y q (pred r).
Proof.
Admitted.
 
Lemma div_unic_r :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> r1 = r2.
Proof.
Admitted.
 
Theorem simpl_mult_r : forall n m p : nat, 0 < n -> m * n = p * n -> m = p.
Proof.
induction n.
intros.
easy.
induction m.
intros.
destruct p.
eauto.
try discriminate.
simpl.
induction p.
simpl.
congruence.
simpl.
intuition.
Qed.
 
Lemma div_unic_q :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> q1 = q2.
Proof.
Admitted.
 
Lemma quot_eq :
 forall a b c q1 r1 q2 r2 : nat,
 a = b -> is_div a c q1 r1 -> is_div b c q2 r2 -> q1 = q2.
Proof.
Admitted.
 
Lemma mult_div_r : forall x y q r : nat, is_div (x * y) y q r -> r = 0.
Proof.
Admitted.
 
Lemma mult_div_q : forall x y q r : nat, is_div (x * y) y q r -> q = x.
Proof.
Admitted.
 
Lemma diveucl_divex :
 forall a b : nat,
 diveucl a b -> exists q : _, (exists r : _, is_div a b q r).
Proof.
Admitted.
 
Lemma div_ex :
 forall a b : nat, b <> 0 -> exists q : _, (exists r : _, is_div a b q r).
Proof.
Admitted.
 
Lemma eq_mult : forall a b c : nat, c <> 0 -> c * a = c * b -> a = b.
Proof.
Admitted.
 
Lemma le_plus_le : forall a b c d : nat, a <= b -> a + c = b + d -> d <= c.
Proof.
intros.
omega.
Qed.
