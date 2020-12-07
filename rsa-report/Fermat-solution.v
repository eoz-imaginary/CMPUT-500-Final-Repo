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
Require Export Divides.
Require Export Binomials.

Lemma div_fact :
 forall p k : nat,
 prime p ->
 0 < k ->
 divides p (factorial k) -> exists j : nat, 0 < j /\ j <= k /\ divides p j.
Proof.
Admitted.

Lemma p_div_bin :
 forall k p : nat, prime p -> 0 < k -> k < p -> divides p (binomial p k).
Proof.
Admitted.

Lemma Fermat1 :
 forall x p : nat, prime p -> congruent p (power (x + 1) p) (power x p + 1).
Proof.
Admitted.

Lemma Fermat2 : forall x p : nat, prime p -> congruent p (power x p) x.
Proof.
Admitted.
