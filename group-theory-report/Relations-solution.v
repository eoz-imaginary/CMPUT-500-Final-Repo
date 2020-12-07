(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(* Initial Version: Frederic Prost, July 1993                               *)
(* Revised Version: Gilles Kahn, September 1993                             *)
(*             INRIA Sophia-Antipolis, FRANCE                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Relations.v                                *)
(****************************************************************************)

Section Relations.
   Variable U : Type.
   
   Definition Relation := U -> U -> Prop.
   Variable R : Relation.
   
   Definition Reflexive : Prop := forall x : U, R x x.
   
   Definition Transitive : Prop := forall x y z : U, R x y -> R y z -> R x z.
   
   Definition Antisymmetric : Prop := forall x y : U, R x y /\ R y x -> x = y.
   
   Definition Order : Prop := (Reflexive /\ Transitive) /\ Antisymmetric.
   
   Definition Symmetric : Prop := forall x y : U, R x y -> R y x.
   
   Definition Equivalence : Prop := (Reflexive /\ Symmetric) /\ Transitive.
   
   Definition PER : Prop := Symmetric /\ Transitive.
   
End Relations.
Hint Unfold Reflexive.
Hint Unfold Transitive.
Hint Unfold Antisymmetric.
Hint Unfold Order.
Hint Unfold Symmetric.
Hint Unfold Equivalence.
Hint Unfold PER.

Theorem sym_not_P :
 forall (U : Type) (P : Relation U) (x y : U),
 Symmetric U P -> ~ P x y -> ~ P y x.
Proof.
intros.
red.
intros.
elim H0.
eauto.
Qed.

Theorem Equiv_from_order :
 forall (U : Type) (R : Relation U),
 Order U R -> Equivalence U (fun x y : U => R x y /\ R y x).
Proof.
Admitted.
