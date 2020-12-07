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
Require Import Wf_nat.
Require Export MiscRsa.
(***********************************************************************
**********************************************************************
**********************************************************************

	ITERATED SUMS
*)

Fixpoint sum_nm (n : nat) : nat -> (nat -> nat) -> nat :=
  fun (m : nat) (f : nat -> nat) =>
  match n with
  | O => f m
  | S n' => f m + sum_nm n' (S m) f
  end.

Lemma sum_nm_i :
 forall (m n : nat) (f : nat -> nat),
 sum_nm (S n) m f = f m + sum_nm n (S m) f.
Proof.
intros.
eauto.
Qed.

Lemma sum_nm_f :
 forall (m n : nat) (f : nat -> nat),
 sum_nm (S n) m f = sum_nm n m f + f (m + S n).
Proof.
Admitted.

Lemma sum_nm_ext :
 forall (m n : nat) (f g : nat -> nat),
 (forall x : nat, x <= n -> f (m + x) = g (m + x)) ->
 sum_nm n m f = sum_nm n m g.
Proof.
Admitted.

Lemma sum_nm_add :
 forall (m n : nat) (f g : nat -> nat),
 sum_nm n m f + sum_nm n m g = sum_nm n m (fun i : nat => f i + g i).
Proof.
Admitted.

Lemma sum_nm_times :
 forall (m n x : nat) (f : nat -> nat),
 x * sum_nm n m f = sum_nm n m (fun i : nat => x * f i).
Proof.
Admitted.

Lemma inv_sum_nm :
 forall (P : nat -> Prop) (i n : nat) (f : nat -> nat),
 (forall a b : nat, P a -> P b -> P (a + b)) ->
 (forall x : nat, x <= n -> P (f (i + x))) -> P (sum_nm n i f).
Proof.
Admitted.

Lemma t_sum_Svars :
 forall (n k : nat) (f : nat -> nat),
 sum_nm k n f = sum_nm k (S n) (fun i : nat => f (pred i)).
Proof.
Admitted.
(***********************************************************************
**********************************************************************
**********************************************************************

	BINOMIAL
*)

Fixpoint binomial (a : nat) : nat -> nat :=
  fun b : nat =>
  match a, b with
  | _, O => 1
  | O, S b' => 0
  | S a', S b' => binomial a' (S b') + binomial a' b'
  end.

Lemma binomial_def1 : forall n : nat, binomial n 0 = 1.
Proof.
intros.
destruct n.
eauto.
eauto.
Qed.

Lemma binomial_def2 : forall n m : nat, n < m -> binomial n m = 0.
Proof.
Admitted.

Lemma binomial_def3 : forall n : nat, binomial n n = 1.
Proof.
Admitted.

Lemma binomial_def4 :
 forall n k : nat,
 k < n -> binomial (S n) (S k) = binomial n (S k) + binomial n k.
Proof.
intros.
simpl.
f_equal.
Qed.

Lemma binomial_fact :
 forall m n : nat,
 binomial (n + m) n * (factorial n * factorial m) = factorial (n + m).
Proof.
Admitted.
