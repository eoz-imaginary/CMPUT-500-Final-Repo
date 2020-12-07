(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
 
Definition orthocentre (H A B C : PO) :=
  (orthogonal (vec H A) (vec B C) /\ orthogonal (vec H B) (vec A C)) /\
  orthogonal (vec H C) (vec A B).
Section Theoreme.
Parameter H A B C : PO.
Hypothesis triangle : ~ colineaire (vec A B) (vec A C).
Hypothesis H_orthocentre : orthocentre H A B C.
 
Lemma orthocentre_double :
 R (double (cons (vec H C) (vec H B))) (double (cons (vec A B) (vec A C))).
Proof.
Admitted.
 
Theorem symetrique_orthocentre_cercle :
 forall H' : PO,
 R (cons (vec H' B) (vec B C)) (cons (vec B C) (vec H B)) ->
 R (cons (vec H' C) (vec B C)) (cons (vec B C) (vec H C)) ->
 sont_cocycliques A B C H'.
Proof.
Admitted.
