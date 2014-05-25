Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapUpdate.

Set Implicit Arguments.

Section MapLookupList.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Open Scope fmap_scope.

  Fixpoint lookup_list (m:X -> Y) (L:list X) : list Y :=
    match L with
      | nil => nil
      | x::L => m x::lookup_list m L
    end.

  Lemma update_with_list_app (A A' : list X) (B B' : list Y) E
    : length A = length B
    -> update_with_list (A++A') (B++B') E = update_with_list A B (update_with_list A' B' E).
  Proof.
    intros. eapply length_length_eq in H0. general induction H0; simpl; eauto.
    rewrite IHlength_eq; eauto.
  Qed.

  Lemma lookup_list_length (m:X -> Y) (L:list X)
    : length (lookup_list m L) = length L.
  Proof.
    induction L; simpl; eauto.
  Qed.

  Lemma lookup_list_agree (m m':X -> Y) (L:list X)
    : agree_on eq (of_list L) m m'
    -> lookup_list m L = lookup_list m' L.
  Proof.
    general induction L; simpl in * |- *; eauto.
    f_equal. eapply H0; cset_tac; eauto.
    eapply IHL; eapply agree_on_incl; eauto. cset_tac; eauto.
  Qed.

  Lemma of_list_lookup_list `{OrderedType Y} (m:X -> Y) L
    : Proper (_eq ==> _eq) m
      -> of_list (lookup_list m L) [=] lookup_set m (of_list L).
  Proof.
    general induction L; simpl.
    + intros x. cset_tac; firstorder. eapply lookup_set_spec in H2.
      - decompose records; cset_tac; firstorder.
      - eauto.
    + rewrite IHL; eauto. intros x. split; intros.
      - eapply lookup_set_spec; eauto. eapply add_iff in H2; destruct H2.
        * eexists a; split; eauto. eapply add_1; eauto.
        * eapply lookup_set_spec in H2; eauto. decompose records. eexists x0; split; eauto.
          eapply add_2; eauto.
      - eapply lookup_set_spec in H2; eauto. decompose records.
        eapply add_iff in H4; destruct H4.
        * eapply add_1. rewrite H5. eapply H1. eapply H2.
        * eapply add_2. eapply lookup_set_spec; eauto.
  Qed.

End MapLookupList.

Lemma lookup_id X (l:list X)
: lookup_list (@id X) l = l.
Proof.
  general induction l; simpl; eauto.
  f_equal; eauto.
Qed.


Global Instance update_with_list_inst X `{OrderedType X} Y `{OrderedType Y} :
  Proper (eq ==> eq ==> (@feq X Y  _eq ) ==> (@feq _ _ _eq)) (@update_with_list X _ Y).
Proof.
  unfold respectful, Proper; intros. subst.
  general induction y; simpl; eauto.
  destruct y0; eauto. hnf; intros.
  specialize (IHy H Y H0 y2 x1 y1 H3).
  eapply update_inst; eauto.
Qed.

Global Instance lookup_list_inst X `{OrderedType X} Y:
  Proper ((@feq X Y eq) ==> eq ==> eq) (@lookup_list X Y).
Proof.
  unfold respectful, Proper, update, feq; intros; subst.
  general induction y0; eauto.
  simpl. f_equal; eauto.
Qed.


Lemma update_with_list_lookup_list X `{OrderedType X} Y `{OrderedType Y} (E:X -> Y)
     `{Proper _ (_eq ==> _eq) E} (Z : list X)
: @feq _ _ _eq (update_with_list Z (lookup_list E Z) E) E.
Proof.
  general induction Z; simpl.
  + reflexivity.
  + setoid_rewrite IHZ; eauto. rewrite update_id; eauto. reflexivity.
Qed.

Lemma lookup_list_app X Y (A A':list X) (E:X -> Y)
: lookup_list E (A ++ A') = List.app (lookup_list E A) (lookup_list E A').
Proof.
  general induction A; simpl; eauto.
  rewrite IHA; eauto.
Qed.


(*
 *** Local Variables: ***
 *** coq-load-path: (("../" "Lvc")) ***
 *** End: ***
 *)
