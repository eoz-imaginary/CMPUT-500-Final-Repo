(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(*                           Group Theory in Coq                            *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*									    *)
(*                                  INRIA                                   *)
(*                             Sophia-Antipolis                             *)
(*									    *)
(*				 January 1996				    *)
(*                                                                          *)
(****************************************************************************)

Require Import Ensembles.
Require Import Laws.
Require Import Group_definitions.
Section group_trivialities.
Variable U : Type.
Variable Gr : Group U.

Let G : Ensemble U := G_ U Gr.

Let star : U -> U -> U := star_ U Gr.

Let inv : U -> U := inv_ U Gr.

Let e : U := e_ U Gr.

Definition G0 : forall a b : U, In U G a -> In U G b -> In U G (star a b) :=
  G0_ U Gr.

Definition G1 : forall a b c : U, star a (star b c) = star (star a b) c :=
  G1_ U Gr.

Definition G2a : In U G e := G2a_ U Gr.

Definition G2b : forall a : U, star e a = a := G2b_ U Gr.

Definition G2c : forall a : U, star a e = a := G2c_ U Gr.

Definition G3a : forall a : U, In U G a -> In U G (inv a) := G3a_ U Gr.

Definition G3b : forall a : U, star a (inv a) = e := G3b_ U Gr.

Definition G3c : forall a : U, star (inv a) a = e := G3c_ U Gr.
Hint Resolve G1.
Hint Resolve G2a G2b G2c.
Hint Resolve G3a G3b G3c.
Hint Resolve G0.

Theorem triv1 : forall a b : U, star (inv a) (star a b) = b.
Proof.
intros.
unfold star.
unfold inv.
destruct Gr.
simpl.
congruence.
Qed.

Theorem triv2 : forall a b : U, star (star b a) (inv a) = b.
Proof.
intros.
unfold star.
unfold inv.
destruct Gr.
simpl.
congruence.
Qed.

Theorem resolve : forall a b : U, star b a = e -> b = inv a.
Proof.
Admitted.

Theorem self_inv : e = inv e.
Proof.
Admitted.

Theorem inv_star : forall a b : U, star (inv b) (inv a) = inv (star a b).
Proof.
Admitted.

Theorem cancellation : forall a b : U, star a b = a -> b = e.
Proof.
Admitted.

Theorem inv_involution : forall a : U, a = inv (inv a).
Proof.
Admitted.
