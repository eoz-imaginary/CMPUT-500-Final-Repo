(* search-width: 5 *)
(* search-depth: 6 *)
(* model: polyarg *)
Set Implicit Arguments.
Unset Strict Implicit.
Parameter V : Type.
Parameter AV : Type.
Parameter cons : V -> V -> AV.
Parameter R : AV -> AV -> Prop.
 
Axiom reflexive : forall a : AV, R a a.
 
Axiom symetrique : forall a b : AV, R a b -> R b a.
 
Axiom transitive : forall a b c : AV, R a b -> R b c -> R a c.
Parameter opp : V -> V.
Parameter zero : AV.
Parameter pi : AV.
 
Axiom angle_nul : forall u : V, R (cons u u) zero.
 
Axiom angle_plat : forall u : V, R (cons u (opp u)) pi.
Parameter plus : AV -> AV -> AV.
 
Axiom Chasles : forall u v w : V, R (plus (cons u v) (cons v w)) (cons u w).
 
Lemma permute : forall u v : V, R (plus (cons u v) (cons v u)) zero.
Proof.
Admitted.
 
Axiom non_vide_V : exists u : V, u = u.
 
Axiom angle_cons : forall (a : AV) (u : V), exists v : V, R a (cons u v).
 
Axiom
  compatible : forall a b c d : AV, R a b -> R c d -> R (plus a c) (plus b d).
Parameter vR : V -> V -> Prop.
 
Axiom v_refl : forall u : V, vR u u.
 
Axiom v_sym : forall u v : V, vR u v -> vR v u.
 
Axiom v_trans : forall u v w : V, vR u v -> vR v w -> vR u w.
 
Axiom opp_compatible : forall u v : V, vR u v -> vR (opp u) (opp v).
 
Axiom
  vR_R_compatible :
    forall u u' v v' : V, vR u u' -> vR v v' -> R (cons u v) (cons u' v').
Parameter PO : Type.
Parameter vec : PO -> PO -> V.
 
Axiom opp_vect : forall A B : PO, vR (opp (vec A B)) (vec B A).
 
Axiom non_vide_P : exists A : PO, A = A.
 
Axiom v_vec : forall (u : V) (A : PO), exists B : PO, vR u (vec A B).
 
Lemma opp_opp : forall u : V, vR (opp (opp u)) u.
Proof.
Admitted.
Hint Resolve opp_opp opp_compatible v_refl v_sym.
 
Lemma oppu_u : forall u : V, R (cons (opp u) u) pi.
Proof.
Admitted.
 
Lemma pi_plus_pi : R (plus pi pi) zero.
Proof.
Admitted.
 
Lemma u_oppv : forall u v : V, R (cons u (opp v)) (plus (cons u v) pi).
Proof.
Admitted.
 
Lemma oppu_v : forall u v : V, R (cons (opp u) v) (plus pi (cons u v)).
Proof.
Admitted.
 
Lemma Chasles_2 :
 forall u v w t : V,
 R (cons u t) (plus (cons u v) (plus (cons v w) (cons w t))).
Proof.
Admitted.
 
Lemma plus_assoc :
 forall a b c : AV, R (plus a (plus b c)) (plus (plus a b) c).
Proof.
Admitted.
 
Lemma compatible_croix :
 forall a b c d : AV, R a b -> R c d -> R (plus a d) (plus b c).
Proof.
Admitted.
 
Lemma plus_zero : forall u v : V, R (plus (cons u v) zero) (cons u v).
Proof.
Admitted.
 
Lemma zero_plus : forall u v : V, R (plus zero (cons u v)) (cons u v).
Proof.
Admitted.
 
Lemma pi_plus_zero : R (plus pi zero) pi.
Proof.
Admitted.
 
Lemma zero_plus_a : forall a : AV, R (plus zero a) a.
Proof.
Admitted.
 
Lemma R_permute :
 forall u v w t : V, R (cons u v) (cons w t) -> R (cons v u) (cons t w).
Proof.
Admitted.
 
Lemma regulier_cons :
 forall u v w t s : V,
 R (cons u v) (cons u w) ->
 R (cons u t) (cons u s) -> R (cons v t) (cons w s).
Proof.
Admitted.
 
Lemma regulier :
 forall a b c d : AV, R a c -> R (plus a b) (plus c d) -> R b d.
Proof.
Admitted.
 
Axiom plus_sym : forall a b : AV, R (plus a b) (plus b a).
 
Lemma calcul : forall a b c : AV, R (plus a (plus b c)) (plus b (plus a c)).
Proof.
Admitted.
 
Lemma oppu_oppv : forall u v : V, R (cons (opp u) (opp v)) (cons u v).
Proof.
Admitted.
 
Lemma rotation :
 forall u v u' v' : V, R (cons u u') (cons v v') -> R (cons u v) (cons u' v').
Proof.
Admitted.
 
Lemma reflexion :
 forall i u v u' v' : V,
 R (cons u' i) (cons i u) ->
 R (cons v' i) (cons i v) -> R (cons u v) (cons v' u').
Proof.
Admitted.
 
Lemma calcul2 :
 forall a b c d : AV,
 R (plus (plus a (plus b c)) d) (plus (plus a (plus b d)) c).
Proof.
Admitted.
 
Lemma somme_pi :
 forall u v w : V,
 R (plus (cons u v) (plus (cons w (opp u)) (cons (opp v) (opp w)))) pi.
Proof.
Admitted.
 
Theorem somme_triangle :
 forall A B C : PO,
 R
   (plus (cons (vec A B) (vec A C))
      (plus (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)))) pi.
Proof.
Admitted.
 
Definition isocele (A B C : PO) : Prop :=
  R (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)).
 
Definition double (a : AV) := plus a a.
 
Lemma triangle_isocele :
 forall A B C : PO,
 isocele A B C ->
 R (plus (cons (vec A B) (vec A C)) (double (cons (vec B C) (vec B A)))) pi.
Proof.
Admitted.
 
Axiom
  calcul3 :
    forall a b c d e f : AV,
    R (plus (plus a (plus b c)) (plus d (plus e f)))
      (plus (plus a d) (plus (plus b e) (plus c f))).
 
Lemma somme_permute :
 forall u v w : V,
 R (plus (cons v u) (plus (cons (opp u) w) (cons (opp w) (opp v)))) pi.
Proof.
Admitted.
 
Lemma isocele_permute :
 forall A B C : PO,
 isocele A B C ->
 R (plus (cons (vec A C) (vec A B)) (double (cons (vec B A) (vec B C)))) pi.
Proof.
Admitted.
Hint Resolve Chasles Chasles_2 angle_plat angle_nul oppu_u permute pi_plus_pi
  u_oppv oppu_oppv oppu_v point_angle.plus_assoc plus_zero zero_plus_a
  R_permute regulier plus_sym reflexive symetrique.
 
Lemma double_zero : R (double zero) zero.
Proof.
apply zero_plus_a.
Qed.
Hint Resolve double_zero.
 
Axiom
  calcul4 :
    forall a b c d : AV,
    R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
 
Lemma double_permute :
 forall u v w t : V,
 R (double (cons u v)) (double (cons w t)) ->
 R (double (cons v u)) (double (cons t w)).
Proof.
Admitted.
Hint Resolve double_permute.
 
Lemma R_double : forall a b : AV, R a b -> R (double a) (double b).
Proof.
intros.
eapply compatible_croix.
eauto.
eauto.
Qed.
Hint Resolve R_double.
 
Lemma double_plus :
 forall a b : AV, R (double (plus a b)) (plus (double a) (double b)).
Proof.
Admitted.
Hint Resolve double_plus.
 
Definition colineaire (u v : V) : Prop := R (double (cons u v)) zero.
 
Definition orthogonal (u v : V) := R (double (cons u v)) pi.
 
Lemma orthogonal_sym : forall u v : V, orthogonal u v -> orthogonal v u.
Proof.
Admitted.
