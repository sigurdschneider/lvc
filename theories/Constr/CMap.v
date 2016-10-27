Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util.
Require Export CSet MapAgreement MapUpdate LengthEq.

Require Export OrderedTypeEx.
Require Export MapInterface.
Require Import MapFacts MapNotations.
Require MapAVLInstance.


Definition findt {X} `{OrderedType X} {Y} `{OrderedType Y} (ϱ:Map [X, Y]) (def:Y) (x:X) :=
  match find x ϱ with
    | Some x => x
    | None => def
  end.

Fixpoint update_map_with_list {X} `{OrderedType X} {Y} XL YL (m:Map [X, Y]) : Map [X, Y] :=
  match XL, YL with
    | x::XL, y::YL => (update_map_with_list XL YL m)[- x <- y -]
    | _, _ => m
  end.

Lemma map_update_update_agree X `{OrderedType X} Y `{OrderedType Y} (D:set X) (ϱ:Map [X, Y])
      (def:Y) (x:X) (y:Y)
: agree_on _eq D (findt ϱ def [x <- y]) (findt (ϱ [-x <- y-]) def).
Proof.
  unfold findt. hnf; intros.
  lud.
  rewrite MapFacts.add_eq_o; eauto.
  rewrite MapFacts.add_neq_o; eauto.
Qed.

Notation "f [- w <-- x -]" := (update_map_with_list w x f) (at level 29, left associativity).

Lemma map_update_list_update_agree X `{OrderedType X} Y `{OrderedType Y} (D:set X) (ϱ:Map [X, Y])
      (def:Y) (xl:list X) (yl:list Y)
: length xl = length yl
  -> agree_on _eq D (findt ϱ def [xl <-- yl]) (findt (ϱ [- xl <-- yl -]) def).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1; simpl; eauto.
  etransitivity; try eapply map_update_update_agree; eauto.
  eapply agree_on_update_same; eauto.
Qed.


Lemma map_update_list_update_agree' X `{OrderedType X} Y `{OrderedType Y} (D:set X) (ϱ:Map [X, Y])
      (def:Y) (xl:list X) (yl:list Y)
: length xl = length yl
  -> agree_on eq D (findt ϱ def [ xl <-- yl]) (findt (ϱ [- xl <-- yl -]) def).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1; simpl; eauto.
  - etransitivity.
    + eapply agree_on_update_same; eauto.
    + unfold agree_on, findt; intros. lud.
      repeat rewrite MapFacts.add_eq_o; eauto.
      repeat rewrite MapFacts.add_neq_o; eauto.
Qed.
