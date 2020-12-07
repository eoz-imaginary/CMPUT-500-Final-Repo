(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_angle.
 
Lemma calcul4 :
 forall a b c d : AV,
 R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Proof.
Admitted.
 
Theorem angle_inscrit :
 forall A B M O : PO,
 isocele O M A ->
 isocele O M B ->
 R (double (cons (vec M A) (vec M B))) (cons (vec O A) (vec O B)).
Proof.
Admitted.
 
Theorem tangente :
 forall A B O T : PO,
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 R (double (cons (vec A T) (vec A B))) (cons (vec O A) (vec O B)).
Proof.
Admitted.
 
Theorem tangente_reciproque :
 forall A B O T T' : PO,
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 R (double (cons (vec A T') (vec A B))) (cons (vec O A) (vec O B)) ->
 colineaire (vec A T) (vec A T').
Proof.
Admitted.
 
Theorem cocyclique :
 forall M A B O M' : PO,
 isocele O A B ->
 isocele O M A ->
 isocele O M B ->
 isocele O M' A ->
 isocele O M' B ->
 R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))).
Proof.
Admitted.
 
Lemma exists_opp_angle : forall a : AV, exists b : AV, R (plus a b) zero.
Proof.
Admitted.
Parameter pisurdeux : AV.
 
Axiom double_pisurdeux : R (double pisurdeux) pi.
Hint Resolve double_pisurdeux.
 
Lemma construction_orthogonal : forall u : V, exists v : V, orthogonal v u.
Proof.
Admitted.
 
Lemma unicite_circonscrit :
 forall M A B O O' : PO,
 isocele O A B ->
 isocele O M B ->
 isocele O M A ->
 isocele O' A B ->
 isocele O' M B ->
 isocele O' M A ->
 (colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B)) /\
 colineaire (vec O M) (vec O' M).
Proof.
Admitted.
 
Lemma construction_isocele_base :
 forall (A B : PO) (a : AV),
 exists u : V,
   (exists v : V,
      R (cons (vec A B) u) (cons v (vec B A)) /\ R (cons u v) (double a)).
Proof.
Admitted.
 
Lemma abba : forall A B : PO, R (cons (vec A B) (vec B A)) pi.
Proof.
Admitted.
Hint Resolve abba.
 
Lemma calcul5 :
 forall a b c d : AV,
 R (plus (plus a (plus b c)) (plus d d))
   (plus a (plus (plus d b) (plus d c))).
Proof.
Admitted.
 
Lemma construction_circonscrit_vecteur :
 forall M A B : PO,
 ex
   (fun u : V =>
    ex
      (fun v : V =>
       ex
         (fun w : V =>
          (R (cons u v) (double (cons (vec M A) (vec M B))) /\
           R (cons u w) (double (cons (vec B A) (vec B M))) /\
           R (cons v w) (double (cons (vec A B) (vec A M)))) /\
          R (cons (vec A B) u) (cons v (vec B A)) /\
          R (cons w (vec M B)) (cons (vec B M) v) /\
          R (cons (vec M A) w) (cons u (vec A M))))).
Proof.
Admitted.
 
Axiom
  construction_circonscrit :
    forall M A B : PO,
    ~ colineaire (vec M A) (vec M B) ->
    exists O : PO, isocele O A B /\ isocele O A M /\ isocele O B M.
 
Definition circonscrit (M A B O : PO) :=
  isocele O A B /\ isocele O A M /\ isocele O B M.
 
Definition sont_cocycliques (M A B M' : PO) :=
  ex
    (fun O : PO =>
     ex
       (fun O' : PO =>
        (circonscrit M A B O /\ circonscrit M' A B O') /\
        colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B))).
 
Lemma isocele_sym : forall A B C : PO, isocele A B C -> isocele A C B.
Proof.
intros.
red.
eauto.
Qed.
Hint Resolve isocele_sym.
 
Lemma unicite_perpendiculaire :
 forall u v u' v' : V,
 colineaire u u' -> orthogonal u v -> orthogonal u' v' -> colineaire v v'.
Proof.
Admitted.
