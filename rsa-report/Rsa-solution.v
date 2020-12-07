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



(****************************************************************
*  Rsa.g                                                      *
****************************************************************)
Require Import Arith.
Require Export Fermat.
Section RSA.
Variable p q : nat.
Variable prime_p : prime p.
Variable prime_q : prime q.
Variable neq_pq : p <> q.
Variable e d : nat.
Variable pq : nat.
Hypothesis pqnot_zero : pq <> 0.
Hypothesis pq_div_p : divides (p - 1) pq.
Hypothesis pq_div_q : divides (q - 1) pq.
Variable ed_inv : congruent pq (e * d) 1.

Definition encrypt (w : nat) : nat := power w e.

Definition decrypt (w : nat) : nat := power w d.

Lemma gcd_pq_SO : is_gcd p q 1.
Proof.
Admitted.

Lemma Chinese :
 forall a b : nat,
 b <= a -> congruent p a b -> congruent q a b -> congruent (p * q) a b.
Proof.
Admitted.

Lemma prime_2_or_more : forall r : nat, prime r -> r = 2 \/ 2 < r.
Proof.
Admitted.

Lemma phi_gt_SO : 1 < pq.
Proof.
Admitted.

Theorem rsa_correct :
 forall w : nat, congruent (p * q) (decrypt (encrypt w)) w.
Proof.
Admitted.
End RSA.
Section RSAI.
Variable p q : nat.
Variable prime_p : prime p.
Variable prime_q : prime q.
Variable neq_pq : p <> q.
Variable e d : nat.
Variable ed_inv : congruent ((p - 1) * (q - 1)) (e * d) 1.

Theorem rsa_correct' :
 forall w : nat, congruent (p * q) (decrypt d (encrypt e w)) w.
Proof.
Admitted.
