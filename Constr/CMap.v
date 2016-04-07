Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Computable Util.
Require Export CSet MapAgreement MapUpdate LengthEq.

Require Export OrderedTypeEx.
Require Export MapInterface.
Open Scope map_scope.

Require MapFacts.
Module MF := MapFacts.

Require MapAVLInstance.


Definition findt {X} `{OrderedType X} {Y} `{OrderedType Y} (ϱ:Map [X, Y]) (def:Y) (x:X) :=
  match find x ϱ with
    | Some x => x
    | None => def
  end.

Notation "'[]'" := (empty _)(at level 0, no associativity) : map_scope.
Notation "M '[' key ']' " :=
  (find key M)(at level 31, left associativity) : map_scope.
Notation "M '[' key '<-' v ']' " :=
  (add key v M)(at level 29, left associativity) : map_scope.

Fixpoint update_with_list {X} `{OrderedType X} {Y} XL YL (m:Map [X, Y]) :=
  match XL, YL with
    | x::XL, y::YL => (update_with_list XL YL m)[x <- y]
    | _, _ => m
  end.

Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).

Lemma map_update_update_agree X `{OrderedType X} Y `{OrderedType Y} (D:set X) (ϱ:Map [X, Y])
      (def:Y) (x:X) (y:Y)
: agree_on _eq D (update (findt ϱ def) x y) (findt (ϱ [x <- y]) def).
Proof.
  unfold findt. hnf; intros.
  lud.
  rewrite MapFacts.add_eq_o; eauto.
  rewrite MapFacts.add_neq_o; eauto.
Qed.

Lemma map_update_list_update_agree X `{OrderedType X} Y `{OrderedType Y} (D:set X) (ϱ:Map [X, Y])
      (def:Y) (xl:list X) (yl:list Y)
: length xl = length yl
  -> agree_on _eq D (MapUpdate.update_with_list xl yl (findt ϱ def)) (findt (ϱ [xl <-- yl]) def).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1; simpl; eauto.
  etransitivity; try eapply map_update_update_agree; eauto.
  eapply agree_on_update_same; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
