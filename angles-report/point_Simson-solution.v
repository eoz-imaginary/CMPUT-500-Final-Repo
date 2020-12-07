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
 
Lemma projete_ortho_cote :
 forall A B C M P Q T : PO,
 colineaire (vec C A) (vec C Q) ->
 colineaire (vec P C) (vec P B) ->
 colineaire (vec B A) (vec B T) ->
 orthogonal (vec T M) (vec T B) ->
 orthogonal (vec P M) (vec P B) ->
 orthogonal (vec Q M) (vec Q C) ->
 R (double (cons (vec P Q) (vec P T)))
   (plus (double (cons (vec C A) (vec C M)))
      (double (cons (vec B M) (vec B A)))).
Proof.
Admitted.
