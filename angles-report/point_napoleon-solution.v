(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
 
Lemma colineaire_sym : forall u v : V, colineaire u v -> colineaire v u.
Proof.
Admitted.
Hint Resolve colineaire_sym.
 
Lemma colineaire_modulo_pi :
 forall u v u' v' : V,
 colineaire u u' ->
 colineaire v v' -> R (double (cons u' v')) (double (cons u v)).
Proof.
Admitted.
Hint Resolve colineaire_modulo_pi.
 
Lemma orthogonal_opp : forall u v : V, orthogonal u v -> orthogonal u (opp v).
Proof.
Admitted.
Hint Resolve orthogonal_opp.
 
Lemma orthogonal_colineaire :
 forall u v w : V, orthogonal u v -> colineaire v w -> orthogonal u w.
Proof.
Admitted.
 
Lemma colineaire_transitive :
 forall u v w : V, colineaire u v -> colineaire v w -> colineaire u w.
Proof.
Admitted.
 
Lemma double_orthogonal :
 forall u u' v v' : V,
 orthogonal u u' ->
 orthogonal v v' -> R (double (cons u v)) (double (cons u' v')).
Proof.
Admitted.
Hint Resolve double_orthogonal.
 
Lemma critere_orthogonal :
 forall u v : V, R (cons u v) (cons v (opp u)) -> orthogonal u v.
Proof.
Admitted.
 
Lemma critere_orthogonal_reciproque :
 forall u v : V, orthogonal u v -> R (cons u v) (cons v (opp u)).
Proof.
Admitted.
Hint Resolve critere_orthogonal critere_orthogonal_reciproque.
 
Definition bissectrice (I A B C : PO) :=
  R (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C)).
 
Lemma bissectrice_double :
 forall I A B C : PO,
 bissectrice I A B C ->
 R (double (cons (vec A I) (vec A C))) (cons (vec A B) (vec A C)).
Proof.
Admitted.
Hint Resolve bissectrice_double.
 
Lemma bissectrice_unicite :
 forall I A B C J : PO,
 bissectrice I A B C -> bissectrice J A B C -> colineaire (vec A I) (vec A J).
Proof.
Admitted.
Hint Resolve bissectrice_unicite.
 
Lemma bissectrice_direction :
 forall (I A B C : PO) (u : V),
 bissectrice I A B C ->
 R (cons (vec A B) u) (cons u (vec A C)) -> colineaire (vec A I) u.
Proof.
Admitted.
Hint Resolve bissectrice_direction.
 
Lemma isocele_bissectrice_hauteur :
 forall I A B C : PO,
 bissectrice I A B C -> isocele A B C -> orthogonal (vec A I) (vec B C).
Proof.
Admitted.
 
Lemma orthogonal_bissectrice :
 forall u v : V, orthogonal u v -> R (cons (opp v) u) (cons u v).
Proof.
Admitted.
Hint Resolve orthogonal_bissectrice.
 
Lemma bissectrice_hauteur_isocele :
 forall I A B C : PO,
 bissectrice I A B C -> orthogonal (vec A I) (vec B C) -> isocele A B C.
Proof.
Admitted.
 
Lemma isocele_hauteur_bissectrice :
 forall I A B C : PO,
 isocele A B C -> orthogonal (vec A I) (vec B C) -> bissectrice I A B C.
Proof.
Admitted.
 
Lemma bissectrice_deux_isoceles :
 forall I A B C D : PO,
 bissectrice I A B C ->
 isocele A B C ->
 isocele D B C -> R (cons (vec D B) (vec A I)) (cons (vec A I) (vec D C)).
Proof.
Admitted.
 
Lemma bissectrice_droite :
 forall u v w t : V,
 R (cons v u) (cons u w) -> colineaire u t -> R (cons v t) (cons t w).
Proof.
Admitted.
Hint Resolve bissectrice_droite.
 
Definition milieu (I B C : PO) :=
  colineaire (vec B I) (vec B C) /\
  (forall A : PO, isocele A B C -> bissectrice I A B C).
 
Axiom existence_milieu : forall B C : PO, exists I : PO, milieu I B C.
 
Lemma milieu_isocele :
 forall I A B C : PO, isocele A B C -> milieu I B C -> bissectrice I A B C.
Proof.
unfold milieu.
intros.
apply H0.
eauto.
Qed.
 
Axiom
  point_aligne :
    forall A B C : PO,
    colineaire (vec A B) (vec C B) -> colineaire (vec A B) (vec A C).
 
Lemma existence_mediatrice_base_isocele :
 forall A B C D : PO,
 isocele A B C -> isocele D B C -> bissectrice D A B C /\ bissectrice A D B C.
Proof.
Admitted.
 
Lemma concours_3circonscrits :
 forall A B C P Q T O1 O2 I : PO,
 circonscrit T A B O1 ->
 circonscrit I A B O1 ->
 circonscrit Q A C O2 ->
 circonscrit I A C O2 ->
 ~ colineaire (vec P B) (vec P C) ->
 R
   (plus (cons (vec P C) (vec P B))
      (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))) pi ->
 sont_cocycliques P B C I.
Proof.
Admitted.
 
Lemma circonscrit_3centres :
 forall A B C O1 O2 O3 I : PO,
 circonscrit I A B O1 ->
 circonscrit I A C O2 ->
 circonscrit I B C O3 ->
 R (double (cons (vec O1 O2) (vec O1 O3)))
   (double (cons (vec I A) (vec I B))) /\
 R (double (cons (vec O1 O3) (vec O2 O3)))
   (double (cons (vec I B) (vec I C))) /\
 R (double (cons (vec O1 O2) (vec O2 O3)))
   (double (cons (vec I A) (vec I C))).
Proof.
Admitted.
