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
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
Require Export MiscRsa.
(******************************************************************************)
 
Inductive divides : nat -> nat -> Prop :=
    dividesDef : forall a b q : nat, b = q * a -> divides a b.
 
Lemma div_ref : forall a : nat, divides a a.
Proof.
Admitted.
 
Lemma div_divides :
 forall x y : nat, (exists q : _, is_div x y q 0) -> divides y x.
Proof.
Admitted.
 
Lemma divides_div :
 forall x y : nat, 0 < y -> divides y x -> exists q : _, is_div x y q 0.
Proof.
intros.
destruct H0.
subst.
exists q.
econstructor.
eauto.
eauto.
Qed.
 
Lemma divides_dec' :
 forall x y : nat,
 {(exists q : _, is_div x y q 0)} + {~ (exists q : _, is_div x y q 0)}.
Proof.
Admitted.
 
Lemma divides_dec : forall x y : nat, {divides x y} + {~ divides x y}.
Proof.
Admitted.
 
Lemma all_divides_O : forall n : nat, divides n 0.
Proof.
Admitted.
 
Lemma SO_divides_all : forall n : nat, divides 1 n.
Proof.
Admitted.
 
Lemma divides_plus1 :
 forall a b c : nat, divides a b -> divides a c -> divides a (b + c).
Proof.
Admitted.
 
Lemma divides_plus2 :
 forall a b c : nat, divides a b -> divides a (b + c) -> divides a c.
Proof.
Admitted.
 
Theorem divides_le : forall a b : nat, b <> 0 -> divides a b -> a <= b.
Proof.
intros.
destruct H0.
subst b.
destruct q.
simpl.
tauto.
simpl.
intuition.
Qed.
 
Lemma divides_antisym : forall a b : nat, divides a b -> divides b a -> a = b.
Proof.
Admitted.
 
Lemma not_lt_div : forall a b : nat, 0 < b -> b < a -> ~ divides a b.
Proof.
Admitted.
(********************************************************************)
 
Inductive prime : nat -> Prop :=
    primeDef :
      forall a : nat,
      a <> 1 -> (forall b : nat, divides b a -> b <> 1 -> a = b) -> prime a.
 
Lemma not_prime_O : ~ prime 0.
Proof.
Admitted.
 
Lemma not_prime_1 : ~ prime 1.
Proof.
generalize not_prime_O.
generalize not_prime_O.
compute.
intros.
inversion H1.
eauto.
Qed.
Hint Resolve div_ref all_divides_O SO_divides_all not_prime_O not_prime_1.
 
Lemma lt_prime : forall p : nat, prime p -> 1 < p.
Proof.
Admitted.
(**********************************************************************)
 
Inductive is_gcd (a b c : nat) : Prop :=
    is_gcd_intro :
      divides c a ->
      divides c b ->
      (forall d : nat, divides d a -> divides d b -> divides d c) ->
      is_gcd a b c.
 
Lemma is_gcd_unic :
 forall a b c d : nat, is_gcd a b c -> is_gcd a b d -> c = d.
Proof.
Admitted.
 
Lemma is_gcd_ref : forall x : nat, is_gcd x x x.
Proof.
intros.
destruct x.
econstructor.
eauto.
eauto.
intros.
apply all_divides_O.
split.
eauto.
eauto.
intros.
destruct d.
eauto.
eauto.
Qed.
 
Lemma is_gcd_sym : forall a b c : nat, is_gcd a b c -> is_gcd b a c.
Proof.
induction a.
destruct b.
intros.
inversion H.
econstructor.
eauto.
eauto.
eauto.
intros.
destruct H.
econstructor.
eauto.
eauto.
eauto.
destruct b.
intros.
inversion H.
econstructor.
eauto.
eauto.
eauto.
intros.
destruct H.
econstructor.
eauto.
eauto.
eauto.
Qed.
 
Lemma is_gcd_O' : forall a r : nat, is_gcd a 0 r -> a = r.
Proof.
Admitted.
 
Lemma is_gcd_Ol : forall a : nat, is_gcd a 0 a.
Proof.
intros.
destruct a.
econstructor.
eauto.
eauto.
intros.
apply all_divides_O.
econstructor.
eauto.
eauto.
eauto.
Qed.
 
Lemma is_gcd_Or : forall a : nat, is_gcd 0 a a.
Proof.
intros.
destruct a.
apply is_gcd_Ol.
econstructor.
eauto.
eauto.
eauto.
Qed.
 
Lemma prime_gcd : forall p n : nat, prime p -> ~ divides p n -> is_gcd n p 1.
Proof.
Admitted.
 
Lemma gcd_rec :
 forall P : nat -> nat -> Set,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
Proof.
Admitted.
 
Lemma gcd_ind :
 forall P : nat -> nat -> Prop,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
Proof.
Admitted.
 
Inductive gcd_spec : nat -> nat -> nat -> Prop :=
  | gcd_spec_ex0 : forall a : nat, gcd_spec a 0 a
  | gcd_spec_ex1 : forall b : nat, gcd_spec 0 b b
  | gcd_spec_ex2 :
      forall a b c : nat, a < b -> gcd_spec a (b - a) c -> gcd_spec a b c
  | gcd_spec_ex3 :
      forall a b c : nat, b <= a -> gcd_spec (a - b) b c -> gcd_spec a b c.
Hint Resolve gcd_spec_ex0 gcd_spec_ex1.
 
Theorem gcd_inv_Or_aux : forall a b c : nat, gcd_spec a b c -> b = 0 -> a = c.
Proof.
Admitted.
 
Theorem gcd_inv_Or : forall a b : nat, gcd_spec a 0 b -> a = b.
Proof.
intros.
eapply gcd_inv_Or_aux.
eauto.
eauto.
Qed.
 
Theorem gcd_inv_Ol_aux : forall a b c : nat, gcd_spec a b c -> a = 0 -> b = c.
Proof.
Admitted.
 
Theorem gcd_inv_Ol : forall a b : nat, gcd_spec 0 a b -> a = b.
Proof.
Admitted.
 
Definition gcd' :=
  gcd_rec (fun _ _ : nat => nat) (fun x : nat => x) 
    (fun x : nat => x) (fun x y r : nat => r) (fun x y r : nat => r).
 
Lemma gcd_ex : forall a b : nat, {r : nat | gcd_spec a b r}.
Proof.
Admitted.
 
Definition gcd (a b : nat) := proj1_sig (gcd_ex a b).
 
Lemma gcd_correct : forall a b : nat, gcd_spec a b (gcd a b).
Proof.
Admitted.
Hint Resolve gcd_correct.
 
Lemma gcd_spec_uniq :
 forall a b r1 r2 : nat, gcd_spec a b r1 -> gcd_spec a b r2 -> r1 = r2.
Proof.
Admitted.
 
Lemma gcd_correct2 : forall a b r : nat, gcd_spec a b r -> gcd a b = r.
Proof.
unfold gcd.
unfold proj1_sig.
intros.
eapply gcd_spec_uniq.
apply gcd_correct.
eauto.
Qed.
 
Lemma gcd_def0l : forall x : nat, gcd 0 x = x.
Proof.
Admitted.
 
Lemma gcd_def0r : forall x : nat, gcd x 0 = x.
Proof.
Admitted.
 
Lemma gcd_def1 : forall x : nat, gcd x x = x.
Proof.
Admitted.
 
Lemma gcd_def2 : forall a b : nat, gcd a b = gcd a (b + a).
Proof.
Admitted.
 
Lemma gcd_def3 : forall a b : nat, gcd a b = gcd (a + b) b.
Proof.
Admitted.
 
Lemma gcd_is_gcd : forall a b : nat, is_gcd a b (gcd a b).
Proof.
Admitted.
 
Lemma preEuclid :
 forall a b c m : nat,
 divides c (m * a) -> divides c (m * b) -> divides c (m * gcd a b).
Proof.
Admitted.
 
Theorem L_Euclides :
 forall x a b : nat, is_gcd x a 1 -> divides x (a * b) -> divides x b.
Proof.
Admitted.
 
Lemma L_Euclides1 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> ~ divides p a -> divides p b.
Proof.
Admitted.
 
Lemma L_Euclides2 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> divides p a \/ divides p b.
Proof.
Admitted.
 
Theorem div_power_prime :
 forall p w n : nat, prime p -> divides p (power w n) -> divides p w.
Proof.
Admitted.
Section CD.
Variable n : nat.
(**********************************************************************)
 
Inductive congruent : nat -> nat -> Prop :=
    congruentDef :
      forall a b u v : nat, a + u * n = b + v * n -> congruent a b.
 
Lemma cong_ref : forall a : nat, congruent a a.
Proof.
intros.
econstructor.
eauto.
Unshelve.
apply n.
Qed.
 
Lemma cong_sym : forall a b : nat, congruent a b -> congruent b a.
Proof.
intros.
destruct H.
destruct b.
econstructor.
eauto.
econstructor.
eauto.
Qed.
 
Lemma cong_trans :
 forall a b c : nat, congruent a b -> congruent b c -> congruent a c.
Proof.
Admitted.
 
Lemma cong_mult_O : forall a b : nat, congruent a 0 -> congruent (a * b) 0.
Proof.
Admitted.
 
Lemma cong_plus :
 forall a b c d : nat,
 congruent a b -> congruent c d -> congruent (a + c) (b + d).
Proof.
Admitted.
 
Lemma cong_add :
 forall a b c : nat, congruent a b -> congruent (a + c) (b + c).
Proof.
intros.
apply cong_plus.
eauto.
apply cong_ref.
Qed.
 
Lemma cong_times :
 forall a b c : nat, congruent a b -> congruent (a * c) (b * c).
Proof.
Admitted.
 
Lemma cong_mult :
 forall a b c d : nat,
 congruent a b -> congruent c d -> congruent (a * c) (b * d).
Proof.
Admitted.
 
Lemma cong_pow :
 forall a b c : nat, congruent a b -> congruent (power a c) (power b c).
Proof.
induction b.
induction c.
intros.
econstructor.
eauto.
Unshelve.
eauto.
intros.
simpl.
apply cong_mult_O.
eauto.
induction c.
intros.
econstructor.
eauto.
Unshelve.
eauto.
intros.
inversion H.
apply cong_mult.
eauto.
eauto.
Qed.
 
Theorem congruent' :
 forall a b : nat, b <= a -> congruent a b -> exists k : nat, a = k * n + b.
Proof.
Admitted.
 
Lemma cong1_le : forall x : nat, 1 < n -> congruent x 1 -> 1 <= x.
Proof.
Admitted.
 
Lemma divides_cong : forall x : nat, divides n x -> congruent 0 x.
Proof.
Admitted.
 
Theorem cong_divides :
 forall a b : nat, b <= a -> congruent a b -> divides n (a - b).
Proof.
Admitted.
