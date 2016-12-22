Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide MoreList.
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
    - intros x. cset_tac; firstorder.
    - rewrite IHL; eauto. intros x. split; intros.
      + eapply lookup_set_spec; eauto. eapply add_iff in H2; destruct H2.
        * eexists a; split; eauto. eapply add_1; eauto.
        * eapply lookup_set_spec in H2; eauto. dcr. eexists x0; split; eauto.
          eapply add_2; eauto.
      + eapply lookup_set_spec in H2; eauto. dcr.
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

Lemma lookup_list_nodup X `{OrderedType X} Y (Z:list X) (Z':list Y) f
: length Z = length Z'
  -> NoDupA _eq Z
  -> lookup_list (f [Z <-- Z']) Z = Z'.
Proof.
  intros. length_equify. general induction H0; simpl in *; dcr; eauto.
  - f_equal.
    + lud; intuition.
    + erewrite lookup_list_agree; eauto.
      eapply agree_on_update_dead; eauto. reflexivity.
Qed.

Hint Resolve lookup_list_agree : cset.

Lemma lookup_list_map X Y (f:X->Y) L
  : lookup_list f L = f ⊝ L.
Proof.
  induction L; simpl; f_equal; eauto.
Qed.

Smpl Add match goal with
         | [ |- context [ ❬@lookup_list ?X ?Y ?f ?L❭ ] ] =>
           rewrite (@lookup_list_length X Y f L)
         end : len.


Lemma map_app X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} s t
: map f (s ∪ t) [=] map f s ∪ map f t.
Proof.
  cset_tac.
Qed.

Lemma map_add X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} x t
: map f ({x; t}) [=] {f x; map f t}.
Proof.
  cset_tac.
Qed.

Lemma map_empty X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f}
: map f ∅ [=] ∅.
Proof.
  cset_tac.
Qed.

Instance map_Proper X `{OrderedType X} Y `{OrderedType Y}
  : Proper (@fpeq X Y _eq _ _ ==> _eq ==> _eq) map.
Proof.
  unfold Proper, respectful; intros. inv H1; dcr.
  hnf; intros. cset_tac'.
  - eexists x1. rewrite <- H2, H9. split; eauto. eapply H3.
  - eexists x1. rewrite H2, H9. split; eauto. symmetry. eapply H3.
Qed.

Lemma map_single {X} `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} x
      : map f {{x}} [=] {{f x}}.
Proof.
  hnf; intros. rewrite map_iff; eauto.
  split; intros.
  - destruct H2; dcr. cset_tac'. rewrite H3; eauto.
  - cset_tac.
Qed.

Lemma of_list_map X `{OrderedType X} Y `{OrderedType Y}
      (f:X->Y) `{Proper _ (_eq ==> _eq) f} L
  : of_list (f ⊝ L) [=] map f (of_list L).
Proof.
  general induction L; simpl; eauto.
  - rewrite map_add; eauto.
    rewrite IHL; eauto; reflexivity.
Qed.

Lemma map_union X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{Proper _ (_eq ==> _eq) f} s t
  : map f (s ∪ t) [=] map f s ∪ map f t.
Proof.
  cset_tac; eauto.
Qed.


Lemma agree_on_update_list X `{OrderedType X} Y (L:list X) (L':list Y) (V:X->Y)
      `{Proper _ (_eq ==> eq) V} V' D (Len:❬L❭= ❬L'❭)
  :  agree_on eq (D \ of_list L) V V'
     -> lookup_list V L = L'
     -> agree_on eq D V (V'[L <-- L']).
Proof.
  intros. hnf; intros.
  decide (x ∈ of_list L).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2. rewrite H7.
    rewrite lookup_list_map in H2. subst. inv_get.
    eapply H0; eauto. eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply H1; cset_tac.
Qed.
