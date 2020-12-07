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
Require Import gr.
Require Import g1.

Theorem auxsub :
 forall (H : Group U) (x : U), subgroup U H Gr -> In U (G_ U H) x -> In U G x.
Proof.
intros.
destruct H0.
eauto.
Qed.

Section Trois.

Variable H K : Group U.
Variable subH : subgroup U H Gr.
Variable subK : subgroup U K Gr.

Inductive Prod : Ensemble U :=
    Definition_of_Prod :
      forall x y z : U,
      In U (G_ U H) x -> In U (G_ U K) y -> star x y = z -> In U Prod z.
End Trois.

Section Quatre.
Variable H K : Group U.
Variable subH : subgroup U H Gr.
Variable subK : subgroup U K Gr.

Theorem T4 : Same_set U (Prod H K) (Prod K H) -> Setsubgroup U (Prod H K) Gr.
Proof.
Admitted.

Theorem T4R : Setsubgroup U (Prod H K) Gr -> Included U (Prod H K) (Prod K H).
Proof.
Admitted.

Theorem T4R1 :
 Setsubgroup U (Prod H K) Gr -> Included U (Prod K H) (Prod H K).
Proof.
Admitted.
Hint Resolve T4 T4R T4R1.

Theorem T_1_6_8 :
 Same_set U (Prod H K) (Prod K H) <-> Setsubgroup U (Prod H K) Gr.
Proof.
split.
intros.
eauto.
intros.
econstructor.
eauto.
eauto.
Qed.
