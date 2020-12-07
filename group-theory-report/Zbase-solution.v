(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)


Inductive Z : Set :=
  | OZ : Z
  | pos : nat -> Z
  | neg : nat -> Z.

Definition IZ := pos 0.


Definition is_posn (x y : Z) :=
  match x, y with
  | pos n, pos m => n = m
  | _, _ => False
  end.


Lemma tech_pos_not_posZ : forall n m : nat, n <> m -> pos n <> pos m.
Proof.
intros.
congruence.
Qed.

Lemma eq_OZ_dec : forall x : Z, {x = OZ} + {x <> OZ}.
Proof.
Admitted.
