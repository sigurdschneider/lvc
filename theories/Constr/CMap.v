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


Lemma InA_eq_key_elt X `{OrderedType X} Y (x:X) (y:Y) L
  : InA eq_key_elt (x, y) L
    -> InA _eq x (fst ⊝ L).
Proof.
  intros IN.
  general induction IN; simpl.
  - inv H0; simpl in *; subst.
    econstructor; eauto.
  - econstructor 2; eauto.
Qed.


Lemma findA_get A B (L:list (A * B)) f v
  : findA f L = Some v
    -> exists x n, get L n x /\ snd x = v /\ f (fst x).
Proof.
  general induction L; simpl; eauto.
  - simpl in H. destruct a. cases in H.
    + inv H.
      eexists (a,v). eexists 0. repeat split; eauto using get.
    + edestruct IHL as [? [? ]]; dcr; eauto.
      do 2 eexists; eauto using get.
Qed.


Ltac mlookup_eq_tac :=
  match goal with
  | [H : ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] ]
    => rewrite (@MapFacts.add_eq_o key OT FM _ elt m x x' _ H)
  | [H : ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] |- _ ]
    => rewrite (@MapFacts.add_eq_o key OT FM _ elt m x x' _ H) in H'
  | [H : ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m) ] ]
    => rewrite (@MapFacts.remove_eq_o key OT FM _ elt m x x' H)
  | [H : ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m) ]  |- _ ]
    => rewrite (@MapFacts.remove_eq_o key OT FM _ elt m x x' H) in H'
  end.

Ltac mlookup_neq_tac :=
   match goal with
    | [ H : ~ ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m)] ]
      => rewrite (@MapFacts.add_neq_o key OT FM _ elt m x x' _ H)
    | [ H : ~ ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m)] |- _ ]
      => rewrite (@MapFacts.add_neq_o key OT FM _ elt m x x' _ H) in H'
    | [ H : ~ ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m)] ]
      => rewrite (@MapFacts.remove_neq_o key OT FM _ elt m x x' H)
    | [ H : ~ ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m)] |- _ ]
      => rewrite (@MapFacts.remove_neq_o key OT FM _ elt m x x' H) in H'
   end.


Tactic Notation "smplmap" :=
  repeat (repeat (subst || mlookup_eq_tac || mlookup_neq_tac)).


Ltac mlud :=
  repeat (smplmap ||
          match goal with
          | [ x: _, x': _ |- context [@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] ]
      =>  match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x === x' -> False |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
          end
    | [ x: _, x': _, H : context[find ?x (add ?x' _ _)] |- _ ]
      => match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x === x' -> False |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
        end
    | [ x: _, x': _ |- context [find ?x' (remove ?x _)] ]
      => match goal with
        | [H' : x === x' |- _ ] => fail 1
        | [H' : ~x === x' |- _ ] => fail 1
        | [H' : x === x' -> False |- _ ] => fail 1
        | [H' : x =/= x' |- _ ] => fail 1
        | [ |- _ ] => decide(x === x')
        end
          end).
