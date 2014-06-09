Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide.

Set Implicit Arguments.

Require Import MapBasics MapInjectivity MapLookupList.


Section MapInverse.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.
  Context `{OrderedType Y}.

  Open Scope fmap_scope.

  Definition inverse_on (D:set X) (E:X -> Y) (E': Y -> X)
    := forall x, x ∈ D -> E' (E x) === x.

  Lemma inverse_on_incl (D D':set X) (E:X -> Y) (E':Y -> X)
    : D' ⊆ D -> inverse_on D E E' -> inverse_on D' E E'.
  Proof.
    intros; firstorder.
  Qed.

  Lemma inverse_on_update (D:set X) (E:X -> Y) (E': Y -> X) x
    : inverse_on D E E'
    -> injective_on D E
    -> x ∈ D
    -> inverse_on D (E [x <- E x]) (E' [E x <- x]).
  Proof.
    intros. hnf. intros. lud.
    eapply H2; eauto.
    exfalso; eapply H5; eauto.
    eapply H1; eauto.
  Qed.

  Lemma inverse_on_update_minus (D:set X) (E:X -> Y) (E': Y -> X) x
    : inverse_on (D\{{x}}) E E'
    -> injective_on (D ∪ {{x}}) E
    -> inverse_on D (E [x <- E x]) (E' [E x <- x]).
  Proof.
    intros. hnf. intros. lud.
    eapply H2; eauto; cset_tac; intuition.
    rewrite <- e. eapply H1. cset_tac; intuition.
    eapply H1. cset_tac; intuition.
  Qed.

  Lemma inverse_on_lookup_list lv ϱ ϱ' L
    : inverse_on lv ϱ ϱ'
    -> of_list L ⊆ lv
    -> lookup_list ϱ' (lookup_list ϱ L) === L.
  Proof.
    general induction L; simpl; eauto.
    econstructor. eapply H1; eapply H2; simpl; eapply add_1; eauto.
    eapply IHL; eauto. hnf; intros. eapply H2. simpl. eapply add_2; eauto.
  Qed.

  Lemma update_with_list_proper (ϱ:X->Y) (ϱ':Y->X) Z
    : Proper (_eq ==> _eq) ϱ -> Proper (_eq ==> _eq) ϱ' ->
      Proper (_eq ==> _eq) (update_with_list (lookup_list ϱ Z) Z ϱ').
  Proof.
    intros; unfold Proper, respectful; intros. general induction Z; simpl.
    rewrite H3. eauto.
    lud. exfalso. eapply H6. eauto. exfalso; eauto.
    eapply IHZ. intuition. intuition. eauto.
  Qed.
End MapInverse.

Arguments inverse_on {X} {H} {Y} D E E'.

Lemma inverse_on_lookup_list_eq {X} `{OrderedType X} {Y} `{OrderedType Y}
  lv (ϱ:X->Y) (ϱ':Y->X) Z `{Proper _ (_eq ==> _eq) ϱ} `{Proper _ (_eq ==> _eq) ϱ'}
: inverse_on lv ϱ ϱ'
  -> of_list Z ⊆ lv
  -> @fpeq _ _ _eq _ _ (update_with_list (lookup_list ϱ Z) Z ϱ') ϱ'.
Proof.
  general induction Z; simpl; eauto. split. reflexivity. eauto.
  split. edestruct IHZ; eauto.
  + hnf; intros. eapply H4; simpl; eapply add_2; eauto.
  + decompose records. erewrite H5; eauto. intro.
    lud. rewrite <- H3. rewrite e. reflexivity.
    eapply H4; simpl; eapply add_1; eauto.
  + split. hnf; intros.
    lud; isabsurd.
    eapply update_with_list_proper; intuition.
    intuition.
Qed.


Global Instance inverse_on_morphism {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (Subset ==> (@fpeq X Y _eq _ _)==> (@fpeq Y X _eq _ _) ==> flip impl) inverse_on.
Proof.
  unfold Proper, respectful, flip, impl; intros; hnf; intros.
  destruct H2 as [A [B C]]. destruct H3 as [A' [B' C']].
  setoid_rewrite <- H4 at 3. hnf in A'. rewrite A'.
  hnf in A. rewrite A. eauto. eapply H1; eauto.
Qed.

Global Instance inverse_on_morphism_full {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (Equal ==> (@fpeq X Y _eq _ _)==> (@fpeq Y X _eq _ _) ==> iff) inverse_on.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  split; intros; eapply inverse_on_morphism; eauto.
  rewrite H1; reflexivity.
  destruct H2; split; eauto. symmetry; eauto. intuition.
  destruct H3; split; eauto. symmetry; eauto. intuition.
  rewrite H1; reflexivity.
Qed.

Global Instance inverse_on_morphism_eq {X} `{OrderedType X} {Y}
  : Proper (Subset ==> eq ==> eq ==> flip impl) (@inverse_on X _ Y).
Proof.
  unfold Proper, respectful, flip, impl; intros; hnf; intros.
  subst. setoid_rewrite <- H3 at 3. reflexivity. eapply H0; eauto.
Qed.

Global Instance inverse_on_morphism_eq_eq {X} `{OrderedType X} {Y}
  : Proper (Equal ==> eq ==> eq ==> flip impl) (@inverse_on X _ Y).
Proof.
  unfold Proper, respectful, flip, impl; intros; hnf; intros.
  subst. setoid_rewrite <- H3 at 3. reflexivity. eapply H0; eauto.
Qed.

Global Instance inverse_on_morphism_full_eq {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (Equal ==> eq ==> eq ==> iff) (@inverse_on X _ Y).
Proof.
  unfold Proper, respectful, flip, impl; split; intros; hnf; intros; subst.
  - rewrite H4; eauto. rewrite H1; eauto.
  - rewrite H1 in H5; eauto.
Qed.

Lemma inverse_on_update_with_list {X} `{OrderedType X} {Y} `{OrderedType Y}
  (ϱ:X->Y) (ϱ':Y->X) Z lv `{Proper _ (_eq ==> _eq) ϱ} `{Proper _ (_eq ==> _eq) ϱ'}
: injective_on (lv ∪ of_list Z) ϱ
  -> inverse_on (lv \ of_list Z) ϱ ϱ'
  -> inverse_on (lv) ϱ (update_with_list (lookup_list ϱ Z) Z ϱ').
Proof.
  intros.
  hnf; intros.
  decide (x ∈ of_list Z). clear H4.
  induction Z. exfalso.  simpl in i. eapply not_in_empty in i; eauto.
  simpl. lud. eapply H3; eauto. simpl. eapply union_3. intuition.
  eapply union_2; eauto. eapply IHZ. eapply injective_on_incl; eauto.
  eapply incl_union_lr; eauto. reflexivity. simpl. intuition. simpl in i.
  eapply add_3; eauto. decide (a === x); eauto. exfalso. eapply H4.
  rewrite e; reflexivity.

  assert (ϱ x ∉ of_list(lookup_list ϱ Z)).
  rewrite of_list_lookup_list. rewrite lookup_set_spec. intro; dcr.
  eapply H3 in H9; eauto. eapply n. rewrite H9; eauto. eapply union_2; eauto.
  eapply union_3; eauto. eauto. eauto.
  erewrite update_with_list_no_update; eauto. eapply H4; eauto using in_in_minus.
Qed.

Lemma inverse_on_union {X} `{OrderedType X} {Y} (f:X->Y) (g:Y->X) D D'
  : inverse_on D f g
  -> inverse_on D' f g
  -> inverse_on (D ∪ D') f g.
Proof.
  intros. hnf; intros. cset_tac. destruct H2; eauto.
Qed.

Lemma lookup_list_inverse_on {X} `{OrderedType X} {Y} `{OrderedType Y} f g
  `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) g} L L'
  : lookup_list f L === L'
  -> lookup_list g L' === L
  -> inverse_on (of_list L) f g.
Proof.
  intros. general induction L; simpl in *.
  hnf; intros. exfalso; cset_tac; eauto.
  hnf; intros. eapply add_iff in H5. destruct H5.
  destruct L'; simpl in *; inv H3; inv H4.
  rewrite <- H5. rewrite H9. eauto.
  inv H3; eauto; inv H4; eapply IHL; try eassumption.
Qed.

Lemma update_with_list_inverse_on {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) (g:Y->X) D Z Z'
  : length Z = length Z'
  -> inverse_on D (update_with_list Z Z' f) (update_with_list Z' Z g)
  -> inverse_on (D \ of_list Z) f g.
Proof.
  intros.
  hnf; intros. cset_tac.
  pose proof (H2 _ H4).
  erewrite update_with_list_no_update in H3; eauto.
  erewrite update_with_list_no_update in H3; eauto.
  intro. erewrite update_with_list_no_update in H6; eauto.
  rewrite (update_with_list_no_update _ _ _ H5) in H3; eauto.
  eapply H5. rewrite <- H3. eapply update_with_list_lookup_in; eauto using length_eq_sym.
Qed.

Lemma inverse_on_sym  {X} `{OrderedType X} D f g
  `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) g}
  : inverse_on D f g
  -> inverse_on (lookup_set f D) g f.
Proof.
  intros; hnf; intros.
  eapply lookup_set_spec in H3. destruct H3; dcr.
  rewrite H5. eapply H0. eapply H2. eauto. eauto.
Qed.

Lemma inverse_on_agree_on_2 {X} `{OrderedType X} {Y} `{OrderedType Y}
  D (f f' : X -> Y) (g g': Y -> X)  `{Proper _ (_eq ==> _eq) f}  `{Proper _ (_eq ==> _eq) g}
`{Proper _ (_eq ==> _eq) f'}  `{Proper _ (_eq ==> _eq) g'}
 : inverse_on D f g
   -> inverse_on D f' g'
   -> agree_on _eq D f f'
   -> agree_on _eq (lookup_set f D) g g'.
Proof.
  intros. unfold agree_on. intros.
  eapply lookup_set_spec in H8; eauto. destruct H8; dcr.
  rewrite H10 at 1. assert (f x0 === f' x0).  eapply H7; eauto.
  rewrite H8 in H10.
  rewrite H10. rewrite H5; eauto. rewrite H6; eauto.
Qed.

Lemma inverse_on_agree_on {X} `{OrderedType X} {Y} `{OrderedType Y}
      (f f': X -> Y) (g g': Y -> X) (G:set X)
 `{Proper _ (_eq ==> _eq) f}
 `{Proper _ (_eq ==> _eq) g'}
  : inverse_on G f g
    -> agree_on _eq G f f'
    -> agree_on _eq (lookup_set f G) g g'
    -> inverse_on G f' g'.
Proof.
  intros; hnf; intros.
  hnf in H4. rewrite <- H4; eauto.
  hnf in H5. rewrite <- H5; eauto.
  eapply lookup_set_spec; eauto.
Qed.

Lemma inverse_on_injective_on {X} `{OrderedType X} {Y} `{OrderedType Y}
      (f: X -> Y) (g: Y -> X) `{Proper _ (_eq ==> _eq) g}  G
  : inverse_on G f g -> injective_on G f.
Proof.
  intros; hnf; intros. hnf in H1. rewrite <- H2.
  rewrite H1; eauto. eauto.
Qed.


Lemma inverse_on_id {X} `{OrderedType X} (G:set X)
  : inverse_on G id id.
Proof.
  intros. hnf; intros. reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
