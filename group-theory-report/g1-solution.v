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
Parameter U : Type.
Parameter Gr : Group U.

Definition G : Ensemble U := G_ U Gr.

Definition star : U -> U -> U := star_ U Gr.

Definition inv : U -> U := inv_ U Gr.

Definition e : U := e_ U Gr.

Definition G0' : forall a b : U, In U G a -> In U G b -> In U G (star a b) :=
  G0 U Gr.

Definition G1' : forall a b c : U, star a (star b c) = star (star a b) c :=
  G1 U Gr.

Definition G2a' : In U G e := G2a U Gr.

Definition G2b' : forall a : U, star e a = a := G2b U Gr.

Definition G2c' : forall a : U, star a e = a := G2c U Gr.

Definition G3a' : forall a : U, In U G a -> In U G (inv a) := G3a U Gr.

Definition G3b' : forall a : U, star a (inv a) = e := G3b U Gr.

Definition G3c' : forall a : U, star (inv a) a = e := G3c U Gr.
Hint Resolve G1'.
Hint Resolve G2a' G2b' G2c'.
Hint Resolve G3a' G3b' G3c'.
Hint Resolve G0'.

Definition triv1' : forall a b : U, star (inv a) (star a b) = b := triv1 U Gr.

Definition triv2' : forall a b : U, star (star b a) (inv a) = b := triv2 U Gr.

Definition resolve' : forall a b : U, star b a = e -> b = inv a :=
  resolve U Gr.

Definition self_inv' : e = inv e := self_inv U Gr.

Definition inv_star' :
  forall a b : U, star (inv b) (inv a) = inv (star a b) := 
  inv_star U Gr.

Definition cancellation' : forall a b : U, star a b = a -> b = e :=
  cancellation U Gr.

Definition inv_involution' : forall a : U, a = inv (inv a) :=
  inv_involution U Gr.
Hint Resolve triv1' triv2' inv_star' resolve' inv_involution'.

Section Elements.
Variable H : Group U.
Variable sub : subgroup U H Gr.

Lemma l1 : Included U (G_ U H) G.
Proof.
red.
intros.
destruct sub.
eauto.
Qed.
Hint Resolve l1.

Lemma eH_in_G : In U G (e_ U H).
Proof.
eauto.
Qed.
Hint Resolve eH_in_G.

Lemma starH_is_star : star_ U H = star.
Proof.
destruct H.
simpl.
apply sub.
Qed.
Hint Resolve starH_is_star.

Lemma eh_is_e : e_ U H = e.
Proof.
Admitted.
Hint Resolve eh_is_e.

Theorem invH_is_inv : forall a : U, In U (G_ U H) a -> inv_ U H a = inv a.
Proof.
Admitted.

Theorem Subgroup_inhabited : Inhabited U (G_ U H).
Proof.
econstructor.
eauto.
Qed.

Theorem star_endo : endo_operation U (G_ U H) star.
Proof.
Admitted.

Theorem inv_endo : endo_function U (G_ U H) inv.
Proof.
Admitted.

End Elements.

Section Premier.

Variable H : Ensemble U.
Variable witness : U.
Variable inhabited : In U H witness.
Variable subset : Included U H G.
Variable hstar : endo_operation U H star.
Variable hinv : endo_function U H inv.
Hint Resolve inhabited subset hstar hinv.

Let assoc : associative U star.
Proof.
eauto.
Qed.
Hint Resolve assoc.

Let eH : U := star (inv witness) witness.

Let eH_in_H : In U H eH.
Proof.
eauto.
Qed.

Let eH_left_neutral : left_neutral U star eH.
Proof.
Admitted.

Let eH_right_neutral : right_neutral U star eH.
Proof.
Admitted.

Let inv_left_inverse : left_inverse U star inv eH.
Proof.
Admitted.

Let inv_right_inverse : right_inverse U star inv eH.
Proof.
Admitted.

Let GrH : Group U :=
  group U H star inv eH hstar assoc eH_in_H eH_left_neutral eH_right_neutral
    hinv inv_right_inverse inv_left_inverse.
Hint Resolve Definition_of_subgroup.

Theorem T_1_6_2 : Setsubgroup U H Gr.
Proof.
red.
exists GrH.
split.
eauto.
eauto.
Qed.

End Premier.

Require Import Zbase.
Require Import Z_succ_pred.
Require Import Zadd.

Definition exp : Z -> U -> U.
Proof.
  intros n a.
  elim n.
    clear n.
    exact e.
    clear n.
    intro n.
    elim n.
      clear n.
      exact a.
      clear n.
      intros n valrec.
      exact (star a valrec).
    clear n.
    intro n.
    elim n.
      clear n.
      exact (inv a).
      clear n.
      intros n valrec.
      exact (star (inv a) valrec).
Defined.


Theorem exp_endo : forall (a : U) (n : Z), In U G a -> In U G (exp n a).
Proof.
Admitted.
Hint Resolve exp_endo.

Lemma exp_unfold_pos :
 forall (a : U) (n : nat),
 In U G a -> exp (pos (S n)) a = star a (exp (pos n) a).
Proof.
intros.
eauto.
Qed.

Lemma exp_unfold_neg :
 forall (a : U) (n : nat),
 In U G a -> exp (neg (S n)) a = star (inv a) (exp (neg n) a).
Proof.
intros.
eauto.
Qed.

Lemma exp_l1 :
 forall (a : U) (n : nat),
 In U G a -> star a (exp (neg (S n)) a) = exp (neg n) a.
Proof.
Admitted.
Hint Resolve exp_l1.

Lemma exp_l2 :
 forall (a : U) (n : Z), In U G a -> star a (exp n a) = exp (succZ n) a.
Proof.
Admitted.

Lemma exp_l2' :
 forall (a : U) (n : Z), In U G a -> star (inv a) (exp n a) = exp (predZ n) a.
Proof.
induction n.
intros.
eauto.
simpl.
unfold In.
destruct n.
intros.
eauto.
simpl.
eauto.
intros.
eauto.
Qed.
Hint Resolve exp_l2 exp_l2' exp_unfold_pos exp_unfold_neg.
Hint Immediate sym_eq.

Theorem add_exponents :
 forall (a : U) (m n : Z),
 In U G a -> star (exp m a) (exp n a) = exp (addZ m n) a.
Proof.
Admitted.

Lemma exp_commut1 :
 forall (a : U) (m : Z), In U G a -> star (exp m a) a = star a (exp m a).
Proof.
Admitted.

Lemma tech_opp_pos_negZ1 : forall n : nat, oppZ (pos n) = neg n.
Proof.
intros.
eauto.
Qed.

Lemma tech_opp_pos_negZ2 : forall n : nat, oppZ (neg n) = pos n.
Proof.
intros.
eauto.
Qed.

Theorem change_exponent_sign :
 forall (a : U) (m : Z), In U G a -> inv (exp m a) = exp (oppZ m) a.
Proof.
Admitted.

Inductive powers (a : U) : Ensemble U :=
    In_powers : forall (m : Z) (x : U), x = exp m a -> In U (powers a) x.

Theorem powers_of_one_element :
 forall a : U, In U G a -> Setsubgroup U (powers a) Gr.
Proof.
Admitted.

Section Second.

Variable H : Ensemble U.
Variable witness : U.
Variable h0 : In U H witness.
Variable h1 : Included U H G.
Variable h2 : forall a b : U, In U H a -> In U H b -> In U H (star a (inv b)).

Let eH : U := star witness (inv witness).

Theorem T_1_6_3 : Setsubgroup U H Gr.
Proof.
Admitted.

End Second.

Theorem Ex1 : Setsubgroup U (Singleton U e) Gr.
Proof.
Admitted.

Theorem Ex2 : Setsubgroup U (Singleton U e) Gr.
Proof.
apply Ex1.
Qed.

Lemma Ex3 : forall n : Z, exp n e = e.
Proof.
Admitted.

Lemma Ex4 : powers e = Singleton U e.
Proof.
Admitted.
