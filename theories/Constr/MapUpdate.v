Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac Get LengthEq.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapAgreement.

Set Implicit Arguments.

Section MapUpdate.
  Open Scope fmap_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Fixpoint update_list (m:X -> Y) (f:X -> Y) (L:list X) :=
    match L with
      | nil => m
      | x::L => (update_list m f L) [x <- f x]
    end.

  Lemma update_list_agree_minus {R} `{Symmetric Y R} `{Transitive Y R} lv (E E' f:X -> Y) XL
  :  agree_on R lv E' E
     -> agree_on R (lv\of_list XL) (update_list E' f XL) E.
  Proof.
    intros. general induction XL; simpl.
    rewrite minus_empty. eassumption.
    rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union.
    eapply agree_on_update_dead; cset_tac.
    eauto using agree_on_incl, incl_minus.
  Qed.

  Corollary update_list_agree_self {R} `{Equivalence Y R} lv (E:X -> Y) L f
    : agree_on R (lv\of_list L) (update_list E f L) E.
  Proof.
    eapply update_list_agree_minus. reflexivity.
  Qed.

  Lemma update_list_no_upd (m:X -> Y) f L x
    : x ∉ of_list L
    -> (update_list m f L) x === m x.
  Proof.
    intros. general induction L; simpl; eauto. lud.
    + exfalso. eapply H0. simpl in * |- *. rewrite e. eapply add_1; eauto.
    + assert (~x ∈ of_list L).
      - intro. eapply H0. simpl. eapply add_2; eauto.
      - eauto.
  Qed.

  Lemma update_list_upd R `{Equivalence Y R} (m:X -> Y) f L x
    : x ∈ of_list L
    -> Proper (_eq ==> R) f
    -> (update_list m f L) x === f x.
  Proof.
    intros. general induction L; simpl; eauto.
    + simpl in *; cset_tac; firstorder.
    + lud.
      - rewrite e; eauto.
      - eapply IHL; eauto. eapply zadd_3; eauto.
  Qed.

End MapUpdate.

Section MapUpdateList.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Open Scope fmap_scope.

  Fixpoint update_with_list XL YL (m:X -> Y) :=
    match XL, YL with
      | x::XL, y::YL => (update_with_list XL YL m)[x <- y]
      | _, _ => m
    end.

  Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).

  Lemma update_unique_commute `{OrderedType Y} (XL:list X) (VL:list Y) E D x y
  : length XL = length VL
    -> unique (x::XL)
    -> agree_on _eq D (E [x <- y] [XL <-- VL]) (E [XL <-- VL] [x <- y]).
  Proof.
    intros. eapply length_length_eq in H1.
    general induction H1; simpl in * |- *; dcr; simpl in *; eauto.
    hnf; intros. lud.
    - exfalso; eauto.
    - etransitivity; [eapply IHlength_eq|]; eauto; lud.
    - etransitivity; [eapply IHlength_eq|]; eauto; lud.
  Qed.

  Lemma update_with_list_no_update (E:X -> Y) Y' Z x
    : x ∉ of_list Z
    -> (E [ Z <-- Y' ]) x = E x.
  Proof.
    intros. general induction Z; simpl; destruct Y'; eauto.
    lud.
    + exfalso. eapply H0. simpl; cset_tac; intuition.
    + simpl in H0. assert (x ∉ of_list Z); eauto.
      - cset_tac; intuition.
  Qed.

  Context `{Equivalence Y}.

  Lemma update_with_list_agree lv (E E':X -> Y) XL YL
    : agree_on R (lv\of_list XL) E E'
    -> length XL = length YL
    -> agree_on R lv (E [ XL <-- YL]) (E' [ XL <-- YL ]).
  Proof.
    intros. eapply length_length_eq in H2.
    general induction XL; simpl in * |- *.
    rewrite (@minus_empty _ _ lv) in H1; eauto.
    inv H2. eapply agree_on_update_same. eapply H0; eauto.
    eapply IHXL; eauto.
    eapply agree_on_incl; eauto. cset_tac; intuition.
  Qed.

  Lemma update_with_list_agree_preserve lv (E E':X -> Y) XL YL
    : agree_on R lv E E'
    -> agree_on R lv (E [ XL <-- YL]) (E' [ XL <-- YL ]).
  Proof.
    intros.
    general induction XL; destruct YL; simpl in * |- *; eauto.
    eapply agree_on_update_same; eauto. reflexivity.
    eapply agree_on_incl; eauto.
  Qed.

  Lemma update_with_list_agree_minus lv (E E':X -> Y) XL YL
    : agree_on R lv E' E
    -> agree_on R (lv\of_list XL) (E' [ XL <-- YL ]) E.
  Proof.
    intros.
    general induction XL; simpl.
    - rewrite minus_empty. eassumption.
    - destruct YL; simpl.
      + eapply agree_on_incl; eauto.
      + rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union.
        eapply agree_on_update_dead. cset_tac.
        eauto using agree_on_incl, incl_minus.
  Qed.

  Hint Resolve minus_single_singleton minus_single_singleton' minus_single_singleton''.

  Lemma update_with_list_agree_inv lv (E E':X -> Y) XL YL
  : length XL = length YL
    -> agree_on R lv (E' [ XL <-- YL ]) E
    -> agree_on R (lv\of_list XL) E' E.
  Proof.
    intros. eapply length_length_eq in H1.
    general induction H1; simpl in * |- *.
    - eapply agree_on_incl; eauto.
    - rewrite add_union_singleton. rewrite <- minus_union.
      eapply IHlength_eq; eauto.
      eapply agree_on_update_inv; eauto.
  Qed.

  Lemma update_with_list_agree_self  `{Defaulted X} lv (E:X -> Y) XL YL
    : agree_on R (lv\of_list XL) (E [ XL <-- YL]) E.
  Proof.
    general induction XL; simpl. rewrite minus_empty. reflexivity.
    destruct YL. reflexivity.
    rewrite add_union_singleton.
    rewrite union_comm. rewrite <- minus_union. eapply agree_on_update_dead.
    cset_tac.
    eapply agree_on_incl. eapply IHXL; eauto.
    instantiate (1:=lv). eapply incl_minus.
  Qed.

  Lemma update_id `{OrderedType Y} (m:X -> Y) x `{Proper _ (_eq ==> _eq) m}
    : @feq _ _ _eq (m [x <- m x])  m.
  Proof.
    intros y. lud. rewrite e; eauto.
  Qed.

End MapUpdateList.

Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).


Lemma update_with_list_lookup_in_list X `{OrderedType X} B E
      (Z:list X) (Y:list B) z
: length Z = length Y
  -> z ∈ of_list Z
  -> exists n y z', get Z n z' /\ get Y n y /\ E [Z <-- Y] z === y /\ z === z'.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl in *; [ isabsurd |].
  decide (z === x).
  - exists 0, y, x; repeat split; eauto using get. lud.
  - cset_tac; [ exfalso; eauto| ].
    edestruct (IHlength_eq _ E z) as [? [? ]]; eauto; dcr.
    exists (S x0), x1, x2. eexists; repeat split; eauto using get.
    lud. exfalso; eauto.
Qed.


Instance update_inst X `{OrderedType X} Y `{OrderedType Y} :
  Proper ((@feq _ _ _eq) ==> _eq ==> _eq ==> (@feq _ _ _eq)) (@update X Y _).
Proof.
  unfold respectful, Proper, update, feq; intros.
  repeat cases; eqs; eauto.
  exfalso. eapply H7. eapply H2.
  exfalso. eapply H8. eapply H2.
Qed.

Instance update_inst_eq X `{OrderedType X} Y
  : Proper ((@feq X Y eq) ==> eq ==> eq ==> (@feq _ _ eq)) (@update X Y _).
Proof.
  unfold respectful, Proper, update, feq; intros.
  repeat cases; eqs; eauto; congruence.
Qed.

Lemma update_with_list_id X `{OrderedType X} (l:list X)
  : @feq _ _ _eq (update_with_list l l id) id.
Proof.
  general induction l; simpl. reflexivity.
  rewrite IHl. change a with (id a) at 2.
  pose proof update_id. specialize (H0 X _ X _ id a).
  eapply H0. firstorder.
Qed.

Lemma update_with_list_lookup_in {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) Z Z' x
  : length Z = length Z'
  -> x ∈ of_list Z
  -> f [ Z <-- Z' ] x ∈ of_list Z'.
Proof.
  intros L. eapply length_length_eq in L.
  general induction L; simpl in * |- *. exfalso; cset_tac; firstorder.
  eapply add_iff in H1. destruct H1.
  lud; try eapply add_1; eauto.
  lud. eapply add_1; eauto.
  eapply add_iff. right. eapply IHL; eauto.
Qed.



Instance proper_update X `{OrderedType X} Y `{OrderedType Y} (ϱ:X -> Y) (x : X) (y :Y)
: Proper (_eq ==> _eq) ϱ
  -> Proper (_eq ==> _eq) (update ϱ x y) | 5.
Proof.
  unfold Proper, respectful; intros; lud; intuition.
Qed.


Instance proper_update_with_list X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) Z Z'
: Proper (_eq ==> _eq) f
  -> Proper (_eq ==> _eq) (f [Z <-- Z']).
Proof.
  intros.
  general induction Z; eauto.
  - destruct Z'; eauto. simpl.
    eapply proper_update. eauto.
Qed.

Hint Resolve proper_update proper_update_with_list.

Lemma lookup_set_update_not_in_Z' X `{OrderedType X} Y `{OrderedType Y}
  Z Z' (f: X-> Y) x
  : f [Z <-- Z'] x ∉ of_list Z' -> f [Z <-- Z'] x = f x.
Proof.
  general induction Z; simpl in *; eauto.
  destruct Z'; eauto.
  lud. simpl in *; exfalso. cset_tac.
  eapply IHZ; eauto. simpl in *. cset_tac.
Qed.

Lemma lookup_set_update_not_in_Z X `{OrderedType X} Y
  Z Z' (f: X-> Y) x
  : x ∉ of_list Z -> f [Z <-- Z'] x = f x.
Proof.
  general induction Z; simpl in *; eauto.
  destruct Z'; eauto.
  lud. simpl in *; cset_tac.
  eapply IHZ; eauto. cset_tac.
Qed.

Lemma lookup_set_update_not_in_Z'_not_in_Z {X} `{OrderedType X} {Y} `{OrderedType Y}
  (f: X-> Y) x Z Z'
: length Z = length Z'
  -> f [Z <-- Z'] x ∉ of_list Z'
  -> Proper (_eq ==> _eq) f
  -> x ∉ of_list Z.
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1; simpl in *; eauto.
  - cset_tac; intuition.
  - lud.
    + exfalso; cset_tac.
    + cset_tac; eauto.
Qed.

Lemma update_with_list_lookup_not_in {X} `{OrderedType X} {Y} `{OrderedType Y}
      (f:X->Y) (Z:list X) (Z':list Y) x y
  : x ∉ of_list Z
    -> f [ Z <-- Z' ] x === y
    -> f x === y.
Proof.
  general induction Z; simpl in * |- *; eauto.
  destruct Z'; eauto. lud.
  - rewrite add_iff in H1;
    exfalso; intuition.
  - eapply IHZ; eauto. cset_tac.
Qed.


Lemma update_with_list_lookup_set_incl {X} `{OrderedType X} {Y} `{OrderedType Y}
(f:X->Y) Z Z' D
  : length Z = length Z'
    -> D ⊆ of_list Z
    -> Proper (_eq ==> _eq) f
    -> lookup_set (f [ Z <-- Z' ]) D ⊆ of_list Z'.
Proof.
  intros. hnf; intros.
  eapply lookup_set_spec in H4; try eapply proper_update_with_list; eauto.
  destruct H4; dcr. rewrite H6. eapply update_with_list_lookup_in; eauto.
Qed.

Instance update_list_morphism {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (@feq X _ _eq ==> @feq X _ _eq ==> eq ==> (@feq _ _ _eq)) (@update_list X _ Y).
Proof.
  unfold Proper, respectful; intros. subst.
  general induction y1. simpl. eauto. simpl.
  rewrite IHy1; eauto. hnf; intros; lud. eapply H2.
Qed.

Lemma lookup_set_add_update {X} `{OrderedType X} {Y} `{OrderedType Y} (ϱ:X->Y) D x y
      `{Proper _ (_eq ==> _eq) ϱ}
: x ∉ D
  -> lookup_set (update ϱ x y) {x; D} [=] {y; lookup_set ϱ D}.
Proof.
  intros. hnf; intros. lset_tac; lud; eauto.
  - eexists x; lud; eauto.
  - eexists x0; lud; eauto.
Qed.

Lemma lookup_update_same X `{OrderedType X} x Z (ϱ:X->X)
: x ∈ of_list Z
  -> ϱ [Z <-- Z] x === x.
Proof.
  general induction Z; simpl; [isabsurd|].
  lud; eauto.
  eapply IHZ. simpl in *. cset_tac.
Qed.


Lemma lookup_set_update_union_minus X `{OrderedType X} Y `{OrderedType Y}
 (f: X->Y) D x y `{Proper _ (_eq ==> _eq) f}
  : lookup_set (update f x y) D \ {{y}} [=] lookup_set f (D \ {{x}}) \ {{ y }}.
Proof.
  split; intros; lset_tac.
  - lud; cset_tac; eauto.
  - eexists x0; lud; cset_tac.
Qed.

Lemma lookup_set_update_union_minus_single X `{OrderedType X} Y `{OrderedType Y}
 (f: X->Y) D x y `{Proper _ (_eq ==> _eq) f}
  : lookup_set (update f x y) D \ singleton y [=] lookup_set f (D \ singleton x) \ singleton y.
Proof.
  split; intros; lset_tac; eauto.
  - lud; cset_tac; eauto.
  - eexists x0; lud; cset_tac.
Qed.

Lemma lookup_set_update_union_minus_list X `{OrderedType X} Y `{OrderedType Y}
 (f:X->Y) D Z Z' `{Proper _ (_eq ==> _eq) f}
: length Z = length Z'
  -> lookup_set (f[ Z <-- Z']) D \ of_list Z' [=] lookup_set f (D \ of_list Z) \ of_list Z'.
Proof.
  split; intros; lset_tac; eauto.
  - rewrite H7 in H5.
    eexists x; cset_tac; eauto.
    eapply lookup_set_update_not_in_Z'_not_in_Z in H5; eauto.
    eapply lookup_set_update_not_in_Z' in H5; eauto.
    rewrite <- H5; eauto.
  - lud; cset_tac.
    eexists x; cset_tac; eauto.
    erewrite lookup_set_update_not_in_Z; eauto.
Qed.

Lemma update_with_list_lookup_list {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} Z Z'
: length Z = length Z'
  -> unique Z
  -> lookup_set (f [ Z <-- Z' ]) (of_list Z) ⊆ of_list Z'.
Proof.
  intros L. eapply length_length_eq in L.
  general induction L; simpl in * |- *; dcr.
  - rewrite lookup_set_empty; eauto.
  - rewrite lookup_set_add; eauto. lud.
    + rewrite lookup_set_agree.
      rewrite IHL; eauto.  eauto. eauto.
      eapply agree_on_update_dead; eauto. intro. eapply InA_in in H2. eauto.
    + exfalso; eapply H2; reflexivity.
Qed.

Lemma lookup_set_update_disj {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} Z Z' G
: disj (of_list Z) G
  -> lookup_set (f [ Z <-- Z' ]) G [=] lookup_set f G.
Proof.
  intros. hnf; intros.
  rewrite lookup_set_spec; eauto.
  split; intros; dcr.
  - rewrite H6. rewrite lookup_set_update_not_in_Z; eauto.
    eapply lookup_set_spec; eauto.
  - eapply lookup_set_spec in H3; eauto; dcr.
    eexists x.
    rewrite lookup_set_update_not_in_Z; eauto.
Qed.

Instance update_with_list_inst X `{OrderedType X} Y `{OrderedType Y} :
  Proper (eq ==> (list_eq (option_eq eq)) ==> (@feq X (option Y) eq ) ==> (@feq _ _ eq))
         (@update_with_list X _ (option Y)).
Proof.
  unfold respectful, Proper; intros. subst.
  general induction H2; simpl; eauto.
  - destruct y; simpl; eauto.
  - destruct y; simpl; eauto.
    hnf; intros. lud.
    inv H; eauto.
    eapply IHlist_eq; eauto.
Qed.
