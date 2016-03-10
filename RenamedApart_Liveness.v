Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.
Require Import Liveness Restrict RenamedApart LabelsDefined Indexwise.

Set Implicit Arguments.


Lemma params_length (F:list (params * stmt)) (ans:list (ann (set var * set var)))
: length F = length ans
  -> List.map (fst ∘ length (A:=var)) F
    = List.map (snd ∘ length (A:=var)) (zip Liveness.live_global F (List.map (mapAnn fst) ans)).
Proof.
  intros. length_equify. general induction H; simpl; eauto; f_equal; eauto.
Qed.

Lemma renamedApart_live_functional s ang DL
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> live_sound Functional DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with ann pe cset.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with ann pe cset.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
  - inv_map H4. destruct x; unfold comp in H5; simpl in *.
    econstructor; simpl;
    eauto using live_exp_sound_incl, live_freeVars, get_list_union_map with cset.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars, get_list_union_map
                  with cset pe ann.
  - econstructor; eauto with len.
    + eapply IHrenamedApart. unfold Liveness.live_globals.
      rewrite List.map_app.
      rewrite <- params_length; eauto.
    + intros. inv_map H9. exploit H1; eauto.
      rewrite List.map_app. rewrite <- params_length; eauto.
    + intros. inv_map H9. edestruct H2; eauto; dcr.
      destruct if; split; pe_rewrite; eauto with cset pe ann.
    + eauto with cset pe ann.
Qed.

Lemma indexwise_R_bounded D Dt F ans
:  indexwise_R (funConstr D Dt) F ans
   -> bounded
       (live_globals (Liveness.live_globals F (List.map (mapAnn fst) ans))) D.
Proof.
  intros. unfold live_globals.
  eapply get_bounded. intros.
  inv_map H0. unfold Liveness.live_globals in H1.
  inv_zip H1. inv_map H3. simpl in *.
  edestruct H; eauto; dcr.
  eauto with cset pe ann.
Qed.

Lemma renamedApart_live s ang DL i
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> bounded (live_globals DL) (fst (getAnn ang))
  -> live_sound i DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl in * |- *; pe_rewrite.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset.
  - inv_map H5. destruct x; unfold comp in *; simpl in *.
    econstructor; simpl;
    eauto using live_exp_sound_incl, live_freeVars, get_list_union_map with cset.
    + destruct if; eauto.
      eapply map_get_1 with (f:=fun x : set var * params => ⎣fst x \ of_list (snd x) ⎦) in H3.
      eapply bounded_get; eauto.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto with len.
    + eapply IHrenamedApart; eauto; simpl.
      rewrite List.map_app. rewrite <-params_length; eauto.
      unfold live_globals.
      rewrite List.map_app.
      rewrite bounded_app; split; eauto using indexwise_R_bounded.
    + intros. inv_map H10.
      exploit H1; eauto; simpl.
      rewrite List.map_app. rewrite <-params_length; eauto.
      edestruct H2; eauto; dcr. rewrite H14.
      unfold live_globals. rewrite List.map_app.
      rewrite <- incl_right.
      rewrite bounded_app; split; eauto using indexwise_R_bounded.
    + intros. inv_map H10. edestruct H2; eauto; dcr.
      destruct if; eauto with cset pe ann.
    + eauto with cset pe ann.
Qed.

Definition disjoint (DL:list (option (set var))) (G:set var) :=
  forall n s, get DL n (Some s) -> disj s G.

Instance disjoint_morphism_subset
  : Proper (eq ==> Subset ==> flip impl) disjoint.
Proof.
  unfold Proper, respectful, impl, flip, disj, disjoint; intros; subst.
  rewrite H0; eauto.
Qed.

Instance disjoint_morphism
  : Proper (eq ==> Equal ==> iff) disjoint.
Proof.
  unfold Proper, respectful, iff, disjoint; split; intros; subst.
  - rewrite <- H0; eauto.
  - rewrite H0; eauto.
Qed.

Definition disj1 (x:set var) (y: set var * set var) := disj x (snd y).

Lemma disjoint_let D D' D'' x (DL:list (set var * list var)) an
: D''[=]{x; D'}
  -> disjoint (live_globals DL) (D'')
  -> pe (getAnn an) ({x; D}, D')
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite H in *. simpl. rewrite incl_add'; eauto.
Qed.

Lemma disjoint_if1 D D' Ds Dt (DL:list (set var * list var)) an
:  Ds ∪ Dt [=] D'
  -> disjoint (live_globals DL) D'
  -> pe (getAnn an) (D, Ds)
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_left; eauto.
Qed.

Lemma disjoint_if2 D D' Ds Dt (DL:list (set var * list var)) an
:  Ds ∪ Dt [=] D'
  -> disjoint (live_globals DL) D'
  -> pe (getAnn an) (D, Dt)
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_right; eauto.
Qed.


Definition Subset1 (x : set var) (y : set var * set var) :=
  match y with
    | (y, _) => x[<=] y
  end.

Instance Subset1_morph
: Proper (Equal ==> @pe _ _ ==> iff) Subset1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Lemma disjoint_fun1 D D' Ds Dt (DL:list (set var * list var)) ans als Z s
:   (Ds ∪ Dt) ∪ of_list Z [=] D'
    -> disjoint (live_globals DL) D'
    -> pe (getAnn ans) ((of_list Z ∪ D)%set, Ds)
    -> ann_R Subset1 als ans
    -> renamedApart s ans
    -> disjoint (live_globals ((getAnn als, Z) :: DL)) (snd (getAnn ans)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl in *.
  hnf; intros. inv H4.
  * eapply ann_R_get in H2.
    rewrite H1 in H2. simpl in H2.
    rewrite H2; simpl.
    eapply renamedApart_disj in H3. rewrite H1 in H3. simpl in *.
    rewrite minus_incl; eauto.
  * exploit H0; eauto using map_get_1 with cset.
Qed.


Lemma disjoint_fun2 D D' Ds Dt (DL:list (set var * list var)) ant als Z s ans
:   (Ds ∪ Dt) ∪ of_list Z[=]D'
    -> disjoint (live_globals DL) D'
    -> pe (getAnn ant) (D, Dt)
    -> ann_R Subset1 als ans
    -> renamedApart s ant
    -> pe (getAnn ans) ((of_list Z ∪ D)%set, Ds)
    -> disj (Ds ∪ of_list Z) Dt
    -> disjoint (live_globals ((getAnn als, Z) :: DL)) (snd (getAnn ant)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl in *.
  hnf; intros. inv H6.
  - eapply ann_R_get in H2. rewrite H4 in H2. simpl in H2.
    rewrite H2; simpl.
    eapply renamedApart_disj in H3. rewrite H1 in H3. simpl in *.
    symmetry. rewrite minus_incl. eapply disj_app. split.
    + symmetry. rewrite incl_right; eauto.
    + symmetry; eauto.
  - exploit H0; eauto using map_get_1.
    eapply (disj_2_incl H7); eapply incl_union_left; eapply incl_right.
Qed.


Lemma disjoint_app L L' D
: disjoint (L ++ L') D <-> disjoint L D /\ disjoint L' D.
Proof.
  split; unfold disjoint.
  - split; intros; eauto using get_shift, get_app.
  -intros. eapply get_app_cases in H0; intuition; eauto.
Qed.


Lemma disjoint_funF1 AL D D' F ans Dt lv als
: disjoint (live_globals AL) D'
  -> list_union (zip defVars F ans) ∪ Dt[=]D'
  -> indexwise_R (funConstr D Dt) F ans
  -> (forall n a b, get als n a -> get ans n b -> ann_R Subset1 a b)
  -> lv ⊆ D'
  -> length F = length ans
  -> disj D D'
  -> disjoint (live_globals (Liveness.live_globals F als ++ AL)) lv.
Proof.
  intros. unfold live_globals.
  rewrite List.map_app.
  rewrite disjoint_app; split.
  - hnf; intros n s A.
    inv_map A. unfold Liveness.live_globals in H6.
    inv_zip H6. simpl in *.
    rewrite H3.
    edestruct (get_length_eq _ H7 H4).
    edestruct H1; eauto; dcr. exploit H2; eauto. eapply ann_R_get in H11.
    destruct (getAnn x); simpl in *. rewrite H11.
    rewrite H10.
    eapply disj_1_incl; eauto. clear_all; cset_tac; intuition.
  - rewrite H3; eauto.
Qed.


Lemma lv_incl F ans Dt D' k a Zs
: list_union (zip defVars F ans) ∪ Dt[=]D'
  -> get ans k a
  -> get F k Zs
  -> snd (getAnn a) ⊆ D'.
Proof.
  intros.
  rewrite <- H. eapply incl_union_left.
  eapply incl_list_union. eapply zip_get; try eapply H3; eauto.
  unfold defVars; eapply incl_right.
Qed.


Lemma renamedApart_globals_live s AL alv f ang
: live_sound Imperative AL s alv
  -> renamedApart s ang
  -> isCalled s f
  -> ann_R Subset1 alv ang
  -> disjoint (live_globals AL) (snd (getAnn ang))
  -> exists lvZ, get AL (counted f) lvZ /\ (fst lvZ \ of_list (snd lvZ)) ⊆ getAnn alv.
Proof.
  intros LS RA IC AR.
  general induction IC; invt live_sound; invt renamedApart; invt (@ann_R); simpl in * |- *.
  - edestruct IHIC; dcr; eauto using disjoint_let.
    + eexists; split; eauto.
      exploit H; eauto. eapply map_get_1 with (f:=live_global); eauto.
      rewrite <- H7. eauto with cset.
  - edestruct IHIC; dcr; eauto using disjoint_if1.
    eexists; split; eauto. rewrite H2; eauto.
  - edestruct IHIC; dcr; eauto using disjoint_if2 with cset.
  - eauto.
  - edestruct IHIC; dcr; eauto using disjoint_let.
    + eexists; split; eauto.
      exploit H; eauto. eapply map_get_1 with (f:=live_global); eauto.
      rewrite <- H8. eauto with cset.
  - edestruct (get_length_eq _ H0 H5).
    edestruct (get_length_eq _ H0 H7).
    edestruct IHIC1; eauto; dcr; eauto using disjoint_fun1.
    {
      eapply renamedApart_disj in RA; simpl in *.
      eapply disjoint_funF1; eauto.
      eapply lv_incl; eauto.
    }
    edestruct IHIC2; eauto using disjoint_fun2; dcr.
    {
      eapply disjoint_funF1; eauto.
      pe_rewrite. rewrite <- H16. eapply incl_right.
      eapply renamedApart_disj in RA; eauto.
    }
    destruct l; simpl in *.
    assert (length F = length (Liveness.live_globals F als)).
    unfold Liveness.live_globals. rewrite zip_length2; eauto.
    rewrite H15 in H17. eapply shift_get in H17.
    eapply get_in_range_app in H20; try rewrite <- H15; eauto.
    unfold Liveness.live_globals in H20. inv_zip H20.
    repeat get_functional. subst x4 x3. simpl in *.
    eexists; split; eauto.
    assert ((of_list (fst Zs)) ⊆ D').
    rewrite <- H16. eapply incl_union_left.
    eapply incl_list_union. eapply zip_get; eauto. unfold defVars.
    cset_tac; intuition.
    assert (disj (fst x1 \ of_list (snd x1)) D').
    eapply disj_1_incl. eapply H1.
    unfold live_globals.
    eapply (map_get_1 live_global H17). reflexivity.
    rewrite <- H10. rewrite <- H24. rewrite <- H18.
    rewrite <- H0 in H2. revert H2; unfold disj; clear_all; cset_tac; intuition; eauto.
  - edestruct IHIC; eauto using disjoint_fun2; dcr.
    pe_rewrite.
    {
      eapply disjoint_funF1; eauto.
      rewrite <- H14. eapply incl_right.
      eapply renamedApart_disj in RA; eauto.
    }
    destruct l; simpl in *.
    assert (length F = length (Liveness.live_globals F als)).
    unfold Liveness.live_globals. rewrite zip_length2; eauto.
    rewrite H0 in H1.
    eexists; split; eauto using shift_get.
    rewrite H13; eauto.
Qed.

Lemma renamedApart_live_imperative_is_functional s ang DL alv
: renamedApart s ang
  -> noUnreachableCode s
  -> live_sound Imperative DL s alv
  -> ann_R Subset1 alv ang
  -> disjoint (live_globals DL) (snd (getAnn ang))
  -> live_sound FunctionalAndImperative DL s alv.
Proof.
  intros RA NUC LS AR DISJ.
  general induction LS; invt noUnreachableCode; invt renamedApart; invt (@ann_R);
  eauto 50 using live_sound, disjoint_let, disjoint_if1, disjoint_if2.
  - econstructor; simpl; eauto.
    + eapply IHLS; eauto using disjoint_funF1.
      eapply disjoint_funF1; eauto.
      * simpl. pe_rewrite. rewrite <- H16. eapply incl_right.
      * simpl. eapply renamedApart_disj in RA. eauto.
    + intros. edestruct (get_length_eq _ H4 H9).
      eapply H1; eauto using disjoint_fun2.
      eapply disjoint_funF1; eauto. simpl.
      eapply lv_incl; eauto. simpl.
      eapply renamedApart_disj in RA. eauto.
    + intros. edestruct (get_length_eq _ H4 H9).
      simpl in *.
      edestruct (@renamedApart_globals_live b); eauto using disjoint_fun2; simpl in *; dcr.
      eapply H8. eapply get_range; eauto.
      eapply disjoint_funF1; eauto. pe_rewrite. rewrite <- H16; eapply incl_right.
      eapply renamedApart_disj in RA; eauto.
      eapply get_in_range_app in H18; eauto using get_range.
      unfold Liveness.live_globals in H18. inv_zip H18. simpl in *.
      repeat get_functional. subst x1 x2. rewrite H20; split; eauto.
      edestruct H2; eauto; dcr.
      unfold Liveness.live_globals. rewrite zip_length2. eapply get_range; eauto.
      congruence.
Qed.

Fixpoint mapAnn2 X X' Y (f:X -> X' -> Y) (a:ann X) (b:ann X') : ann Y :=
  match a, b with
    | ann1 a an, ann1 b bn => ann1 (f a b) (mapAnn2 f an bn)
    | ann2 a an1 an2, ann2 b bn1 bn2 => ann2 (f a b) (mapAnn2 f an1 bn1) (mapAnn2 f an2 bn2)
    | ann0 a, ann0 b => ann0 (f a b)
    | annF a anF an2, annF b bnF bn2 =>
      annF (f a b) (zip (mapAnn2 f) anF bnF) (mapAnn2 f an2 bn2)
    | a, b => ann0 (f (getAnn a) (getAnn b))
  end.

Lemma getAnn_mapAnn2 A A' A'' (a:ann A) (b:ann A') (f:A->A'->A'') s
: annotation s a
  -> annotation s b
  -> getAnn (mapAnn2 f a b) = f (getAnn a) (getAnn b).
Proof.
  intros ANa ANb. general induction ANa; inv ANb; simpl; eauto.
Qed.


Lemma renamedApart_annotation s ang
: renamedApart s ang
  -> annotation s ang.
Proof.
  intros. general induction H; eauto 20 using @annotation.
Qed.

Lemma live_exp_sound_meet e D lv
:  Exp.freeVars e[<=]D
   -> live_exp_sound e lv
   -> live_exp_sound e (lv ∩ D).
Proof.
  intros.
  eapply Exp.freeVars_live in H0.
  eapply live_exp_sound_incl; eauto using Exp.live_freeVars.
  rewrite <- H, <- H0. cset_tac; intuition.
Qed.

Definition meet1 (x:set var) (y:set var * set var) :=
  match y with
    | (y, _) => x ∩ y
  end.

Lemma meet1_incl a b
: meet1 a b ⊆ a.
Proof.
  destruct b; simpl. cset_tac; intuition.
Qed.

Lemma meet1_Subset s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset (mapAnn2 meet1 alv ang) alv.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl.
  - econstructor; eauto using meet1_incl. (* todo make HintDb len solve this *)
    rewrite zip_length2; congruence.
    intros. destruct (get_length_eq _ H3 (eq_sym H)).
    inv_zip H2. get_functional; subst.
    eapply H1; eauto.
Qed.

Instance meet1_morphism
: Proper (Subset ==> @pe _ _ ==> Subset) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Instance meet1_morphism'
: Proper (Equal ==> @pe _ _ ==> Equal) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Lemma live_sound_renamedApart_minus s ang DL alv i
: renamedApart s ang
  -> live_sound i DL s alv
  -> bounded (live_globals DL) (fst (getAnn ang))
  -> live_sound i DL s (mapAnn2 meet1 alv ang).
Proof.
  intros RA LS. general induction RA; invt live_sound; simpl in * |- *; pe_rewrite;
                eauto using live_sound, live_exp_sound_meet.
  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let, bounded_incl with cset ann.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      pe_rewrite. rewrite <- minus_meet.
      revert H11; clear_all; cset_tac; intuition.
      eapply H11; cset_tac; intuition.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      pe_rewrite. simpl; cset_tac; eauto.
  - econstructor; eauto using live_exp_sound_meet.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H2; simpl. rewrite H13. reflexivity.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H3; simpl. rewrite H14. reflexivity.
  - econstructor; eauto.
    + destruct if; simpl in *; eauto.
      exploit bounded_get; eauto.
      eapply map_get_1 with (f:=live_global); eauto. simpl in *.
      rewrite <- H2. rewrite <- H5. clear_all; cset_tac; intuition.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto using map_get_1.
  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let with cset.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      pe_rewrite. rewrite <- minus_meet.
      revert H12; clear_all; cset_tac; intuition.
      eapply H12; cset_tac; intuition.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      pe_rewrite. simpl; cset_tac; eauto.
  - constructor; eauto.
    + eapply IHRA; eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        unfold Liveness.live_globals in *.
        eapply PIR2_get; intros.
        inv_zip H7. inv_zip H8. inv_zip H17.
        simpl.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
        repeat get_functional; subst; split; eauto.
        edestruct H2; eauto; dcr.
        eapply meet1_incl.
        unfold Liveness.live_globals in *.
        repeat rewrite zip_length2; eauto. congruence.
      * pe_rewrite.
        unfold live_globals. rewrite List.map_app.
        eapply bounded_app; split; eauto.
        unfold Liveness.live_globals. rewrite map_zip.
        eapply get_bounded; intros.
        inv_zip H7. inv_zip H12. simpl in *.
        unfold live_global, Liveness.live_global in H14. simpl in *.
        invc H14.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x3); simpl in *. rewrite H14.
        clear_all; cset_tac; intuition.
    + rewrite zip_length2; congruence.
    + intros. inv_zip H8.
      eapply (H1 _ _ _ H7 H14); eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        unfold Liveness.live_globals in *.
        eapply PIR2_get; intros.
        inv_zip H16. inv_zip H17. inv_zip H21.
        simpl.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
        repeat get_functional; subst; split; eauto.
        eapply meet1_incl.
        unfold Liveness.live_globals in *.
        repeat rewrite zip_length2; eauto. congruence.
      * unfold live_globals. rewrite List.map_app.
        eapply bounded_app; split; eauto.
        unfold Liveness.live_globals. rewrite map_zip.
        eapply get_bounded; intros.
        inv_zip H16. inv_zip H18. simpl in *.
        unfold live_global, Liveness.live_global in H19. simpl in *.
        invc H19.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x5); simpl in *. rewrite H19.
        edestruct (H2 _ _ _ H7 H14); eauto; dcr. rewrite H22.
        clear_all; cset_tac; intuition.
        edestruct (H2 _ _ _ H7 H14); eauto; dcr. rewrite H16.
        rewrite <- incl_right; eauto.
    + intros. inv_zip H8.
      erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      edestruct H2; eauto; dcr. destruct (getAnn x0); simpl in *.
      edestruct H13; eauto.
      split. rewrite <- H17. rewrite H16. clear_all; cset_tac; intuition.
      destruct if; eauto. rewrite H16. rewrite <- H19.
      clear_all; cset_tac; intuition.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      pe_rewrite. rewrite H15; reflexivity.
Qed.
