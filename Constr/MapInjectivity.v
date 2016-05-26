Require Import EqDec Computable Util AutoIndTac LengthEq.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapUpdate MapLookup OrderedTypeEx.

Set Implicit Arguments.


Hint Extern  5 =>
match goal with
| [ H : ?s === ?f ?y, H' : ?x === ?y |- ?f ?x === ?s ] => rewrite H'; symmetry; eapply H
| [ H : ?s === ?f ?y, H' : ?x === ?y |- ?s === ?f ?x ] => rewrite H'; eapply H
| [ H : ?f ?y === ?s, H' : ?x === ?y |- ?f ?x === ?s ] => rewrite H'; eapply H
| [ H : ?f ?y === ?s, H' : ?y === ?x |- ?f ?x === ?s ] => rewrite <- H'; eapply H
| [ H : ?x === ?y, H' : ?y === ?z |- ?x === ?z ] => transitivity y; [eapply H | eapply H']
end.

Section MapInjectivity.
  Open Scope fmap_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.
  Context `{OrderedType Y}.

  Definition injective_on D (f:X->Y) :=
    forall x y, x ∈ D -> y ∈ D -> f x === f y -> x === y.

  Lemma injective_on_incl (D D':set X) (f:X -> Y)
    : injective_on D f -> D' ⊆ D -> injective_on D' f.
  Proof.
    firstorder.
  Qed.

  Lemma injective_on_dead lv (f:X -> Y) x v `{Proper _ (respectful _eq _eq) f}
  : injective_on (lv\ singleton x) f
    -> injective_on (lv\ singleton x) (f[x<-v]).
   Proof.
    intros; hnf; intros. lud; eauto.
    + exfalso; cset_tac.
    + exfalso; cset_tac.
  Qed.

  Lemma injective_on_fresh lv (f:X -> Y) x xr `{Proper _ (_eq ==> _eq) f}
    :    injective_on (lv\ singleton x) f
      -> ~xr ∈ lookup_set f (lv\ singleton x)
      -> injective_on {x; lv} (f[x <- xr]).
  Proof.
    intros. hnf; intros. lud.
    + exfalso; lset_tac.
    + exfalso; lset_tac.
    + eapply H2; cset_tac.
  Qed.

  Lemma injective_on_forget s (f:X -> Y) y `{Proper _ (_eq ==> _eq) f}
  : injective_on s f
    -> injective_on (s\ singleton y) f.
  Proof.
    intros. hnf; intros.
    cset_tac.
  Qed.

  Lemma lookup_set_minus_incl_inj s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : injective_on (s ∪ t) m
    -> lookup_set m (s \ t) ⊆ lookup_set m s \ (lookup_set m t).
  Proof.
    intros; hnf; intros. lset_tac.
    eapply H4. rewrite H2; cset_tac. eqs.
  Qed.


End MapInjectivity.

Global Instance injective_on_morphism {X} `{OrderedType X} {Y} {HY:OrderedType Y}
  : Proper (Equal ==> (@feq X Y (@_eq Y HY)) ==> iff) (@injective_on X H Y HY).
Proof.
  unfold Proper, respectful; intros.
  split; intros; hnf; intros.
  + eapply H2; try rewrite H0 ; eauto.
    hnf in H1. repeat rewrite H1. eauto.
  + rewrite H0 in *. eapply H2; cset_tac; eauto.
    hnf in H1. repeat rewrite <- H1. eauto.
Qed.


Lemma injective_on_update_not_in {X} `{OrderedType X} {Y} `{OrderedType Y}
  D x (f:X -> Y) `{Proper _ (_eq ==> _eq) f}
: injective_on (D \ singleton x) f
  -> f x ∉ lookup_set f (D \ singleton x)
  -> injective_on D f.
Proof.
  intros; hnf; intros.
  decide(x0 === x); decide (x0 === y); eauto.
  - exfalso. lset_tac. eapply H3.
    eexists y. cset_tac; eauto.
  - eapply H2; lset_tac; eauto.
    eapply H3; eauto.
Qed.

Lemma injective_on_update_fresh {X} `{OrderedType X} {Y} `{OrderedType Y}
  D x y f `{Proper _ (_eq ==> _eq) f}
: injective_on (D \ singleton x) f
  -> y ∉ lookup_set f (D \ singleton x)
  -> injective_on D (update f x y).
Proof.
  intros; hnf; intros. lset_tac. lud.
  - exfalso; eauto.
  - exfalso; eauto.
  - eapply H2; cset_tac; eauto.
Qed.

Lemma injective_on_not_in_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y} f D D' x
    `{Proper _ (_eq ==> _eq) f}
    : injective_on D f
      -> D' ⊆ D\ singleton x -> x ∈ D
      -> f x ∉ lookup_set f D'.
Proof.
  intros. lset_tac. specialize (H3 _ H7). cset_tac.
Qed.


Lemma lookup_set_not_in  {X} `{OrderedType X} {Y} `{OrderedType Y} f D x
    `{Proper _ (_eq ==> _eq) f}
  : f x ∉ lookup_set f D
    -> lookup_set f D \ singleton (f x) [=] lookup_set f (D\ singleton x).
Proof.
  intros. lset_tac.
Qed.


Definition injective_on_step {X} {Y} `{OrderedType Y}
f (x : X) (p : set Y * bool) :=
      ({f x; fst p}, if snd p then
        negb (sumbool_bool (@decision_procedure (f x ∈ fst p) _))
       else false).

Lemma injective_on_step_transpose {X} {Y} `{OrderedType Y}
f
  : transpose _eq (@injective_on_step X Y _ f).
Proof.
  hnf; intros.
  unfold injective_on_step. econstructor.
  - destruct z; simpl. econstructor; cset_tac; intuition.
  - destruct z. unfold snd. destruct b; eauto.
    unfold fst, snd.
    decide (f y ∈ s); decide (f x ∈ s); simpl; try reflexivity;
      decide (f x ∈ {f y; s}); decide (f y ∈ {f x; s}); simpl; try reflexivity;
        exfalso; cset_tac.
Qed.

Lemma injective_on_step_spec {X} `{OrderedType X} {Y} `{OrderedType Y}
f (x : X) (p : set Y * bool) (s:set Y) b
:  snd (injective_on_step f x (s,b))
   -> {f x; s} [=] fst (injective_on_step f x (s,b)).
Proof.
  intros. unfold injective_on_step in *.
  destruct b. unfold snd in *. unfold fst; reflexivity.
  reflexivity.
Qed.

Instance injective_on_step_proper
  {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f}
 : Proper (_eq ==> _eq ==> _eq) (injective_on_step f).
Proof.
  unfold Proper, respectful; intros.
  inv H3. econstructor.
  - rewrite H3.
    eapply add_m; eauto.
  - inv H5; simpl. cases; trivial.
    f_equal.
    decide (f x ∈ a); decide (f y ∈ c); simpl; trivial.
    exfalso; eapply n; rewrite <- H2, <- H4; eauto.
    exfalso; eapply n; rewrite H2, H4; eauto.
Qed.

Instance injective_on_step_proper'
  {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> eq) f}
 : Proper (_eq ==> eq ==> eq) (injective_on_step f).
Proof.
  unfold Proper, respectful; intros; subst.
  destruct y0; unfold injective_on_step; simpl.
  rewrite (H1 _ _ H2).
  decide (f x ∈ s); decide (f y ∈ s); simpl; trivial.
Qed.


Definition injective_on_compute {X} `{OrderedType X} {Y} `{OrderedType Y}
  (D:set X) (f: X-> Y) `{Proper _ (_eq ==> _eq) f} : bool
  := snd (fold (injective_on_step f) D (∅, true)).

Lemma injective_on_compute_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y}
   (f: X-> Y) `{Proper _ (_eq ==> _eq) f}
:
  forall D LD',
    lookup_set f D ∪ LD' [=] fst (fold (injective_on_step f) D (LD', true)).
Proof.
  intros.
  eapply (@fold_rec _ _ _ _ _ (fun (D:set X) (fld:set Y * bool) =>
          lookup_set f D ∪ LD' [=] fst fld
         ) _ (LD', true)); intros; simpl.

  - eapply empty_is_empty_1 in H2.
    lset_tac.
    exfalso; eauto.
  - destruct a; simpl in *.
    rewrite <- H5; clear H5. eapply Add_Equal in H4.
    rewrite H4; clear H4.
    lset_tac.
Qed.

Definition injective_on_iff {X} `{OrderedType X} {Y} `{OrderedType Y}
   (f: X-> Y) `{Proper _ (_eq ==> _eq) f} D
: forall D' LD',
    D' ∩ D [=] ∅
    -> lookup_set f D' [=] LD'
    -> injective_on D' f
    -> (snd (fold (injective_on_step f) D (LD', true)) <-> (injective_on (D ∪ D') f)).
Proof.
  pattern D. eapply set_induction; intros.
  - eapply empty_is_empty_1 in H2. intuition. eapply injective_on_incl; eauto.
    rewrite H2. cset_tac; intuition.
    pose proof (@fold_equal X _ _ _ _ _ _ (injective_on_step f) _ (injective_on_step_transpose f) (LD', true) _ _ H2).
    rewrite fold_empty in H7.
    destruct (fold (injective_on_step f) s (LD', true)).
    inv H7. inv H13. eapply I.
  -  pose proof H4 as FOO. eapply Add_Equal in H4.
     pose proof (@fold_equal X _ _ _ _ _ _ (injective_on_step f) _ (injective_on_step_transpose f) (LD', true) _ _ H4).
     destruct (fold (injective_on_step f) s' (LD', true)).
     rewrite (@fold_add X _ _ _ _ _ _ (injective_on_step f) (injective_on_step_proper f) (injective_on_step_transpose f) (LD', true) _ _ H3) in H8.

     decide (x ∈ D'). exfalso. destruct (FOO x).
     cset_tac; intuition.
     assert (D' ∩ s [=] ∅).
     revert H5. rewrite H4. clear_all; cset_tac; intuition.

  specialize (H2 D' _ H9 H6 H7).
  case_eq (fold (injective_on_step f) s (LD', true)); intros; rewrite H10 in *.
  unfold injective_on_step in H8. unfold fst in H8.
  decide (f x ∈ s1).
  destruct b. try now (destruct b0; simpl in *; inv H8; isabsurd).
  simpl; split; intros; isabsurd.

  simpl_pair_eqs.
  pose proof (injective_on_compute_lookup_set s LD').
  rewrite H12 in H10. clear H8.
  rewrite <- H10 in i. rewrite <- H6 in i. rewrite <- lookup_set_union in i.
  eapply lookup_set_spec in i. destruct i; dcr.
  eapply H11 in H15. cset_tac.
  rewrite H4; revert H14 H9; clear_all; intros. cset_tac; intuition.
  rewrite H4.
  revert H14 H9; clear_all; intros.
  cset_tac; intuition. eassumption. eassumption.

  destruct b, b0; try now (simpl in *; inv H8; isabsurd).
  simpl; split; intros; eauto.
  destruct H2. specialize (H2 I).
  simpl_pair_eqs.
  pose proof (injective_on_compute_lookup_set s LD'). simpl.
  rewrite H13 in H10.
  clear H8.
  rewrite <- H10 in n0.
  rewrite <- H6 in n0. rewrite <- lookup_set_union in n0; eauto.
  assert (s ∪ D' [=] (s' ∪ D') \ singleton x).
  rewrite H4. clear H1 H2 H4 H6 H7 H10 H11 H12 H13 H14 n0 s0 FOO.
  cset_tac; intuition.
  rewrite H8 in n0. rewrite H8 in H2.
  pose proof (injective_on_update_not_in H2 n0); eauto.
  simpl in *. split; [isabsurd|]; intros.
  eapply H2. eapply injective_on_incl; eauto.
  rewrite H4. eauto with cset.
Qed.

Global Instance injective_on_computable {X} `{OrderedType X} {Y} `{OrderedType Y}
  (D:set X) (f: X-> Y) `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> eq) f}
: Computable (injective_on D f).
Proof.
  case_eq (@injective_on_compute X _ Y _ D f _); eauto; intros.
  left. pose proof (@injective_on_iff X _ Y _ f _ D ∅ ∅).
  destruct H4; eauto. cset_tac; intuition. isabsurd.
  unfold injective_on_compute in H3.
  rewrite H3 in H4. specialize (H4 I). eapply injective_on_incl ;eauto.
  cset_tac; eauto.
  right. intro.
  pose proof (@injective_on_iff X _ Y _ f _ D ∅ ∅).
  edestruct H5. cset_tac; intuition. cset_tac; intuition.
  isabsurd.
  change False with (Is_true false). rewrite <- H3.
  unfold injective_on_compute in H3. rewrite H3 in H7.
  unfold injective_on_compute. rewrite H3. eapply H7.
  eapply injective_on_incl; eauto with cset.
Defined.

Lemma lookup_set_minus_eq X `{OrderedType X} Y `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
: injective_on (s ∪ t) m
  -> lookup_set m (s \ t) [=] lookup_set m s \ (lookup_set m t).
Proof.
  split; intros. eapply lookup_set_minus_incl_inj; eauto.
  apply lookup_set_minus_incl; eauto.
Qed.

Lemma injective_on_agree X `{OrderedType X} Y `{OrderedType Y} D (ϱ ϱ': X -> Y)
: injective_on D ϱ
  -> agree_on _eq D ϱ ϱ'
  -> injective_on D ϱ'.
Proof.
  intros. hnf; intros. eapply H1; eauto.
  exploit H2; eauto. rewrite H6.
  exploit H2; try eapply H3. rewrite H7. eauto.
Qed.

Lemma injective_on_fresh_list X `{OrderedType X} Y `{OrderedType Y} XL YL (ϱ: X -> Y) `{Proper _ (_eq ==> _eq) ϱ} lv
: injective_on lv ϱ
  -> length XL = length YL
  -> (of_list YL) ∩ (lookup_set ϱ lv) [=] ∅
  -> unique XL
  -> unique YL
  -> injective_on (lv ∪ of_list XL) (ϱ [XL <-- YL]).
Proof.
  intros. eapply length_length_eq in H3.
  general induction H3; simpl in * |- * ; eauto.
  - eapply injective_on_incl; eauto with cset.
  - eapply injective_on_agree. instantiate (1:=ϱ [x <- y] [XL <-- YL]).
    + assert (lv ∪ { x; of_list XL} [=] {x; lv} ∪ of_list XL) by (cset_tac; eauto).
      rewrite H7. dcr.
      eapply IHlength_eq; eauto.
      * eapply injective_on_fresh; eauto.
        eapply injective_on_incl; eauto.
        lset_tac. eapply (H4 y). lset_tac.
      * rewrite lookup_set_add; eauto. lud; eauto.
        split; [| clear_all; cset_tac].
        rewrite <- H4. lset_tac.
        lud; eauto.
    + eapply update_unique_commute; eauto using length_eq_length.
Qed.
