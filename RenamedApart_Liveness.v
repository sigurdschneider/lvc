Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.
Require Import Liveness Restrict RenamedApart LabelsDefined Indexwise.

Set Implicit Arguments.


Lemma params_length (F:list (params * stmt)) (ans:list (ann (set var * set var)))
: length F = length ans
  -> List.map (fst ∘ length (A:=var)) F
    = List.map (snd ∘ length (A:=var)) (zip pair (getAnn ⊝ (List.map (mapAnn fst) ans)) (fst ⊝ F)).
Proof.
  intros. length_equify. general induction H; simpl; eauto; f_equal; eauto.
Qed.

Lemma renamedApart_live_functional s ang ZL Lv
: renamedApart s ang
  -> paramsMatch s (@length _ ⊝ ZL)
  -> length ZL = length Lv
  -> live_sound Functional ZL Lv s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - eauto 9 using @live_sound, live_exp_sound_incl, live_freeVars
            with ann pe cset.
  - eauto 9 using @live_sound, live_exp_sound_incl, live_freeVars
    with ann pe cset.
  - eauto using live_sound, live_exp_sound_incl, live_freeVars.
  - inv_get.
    econstructor; simpl;
      eauto using live_exp_sound_incl, live_freeVars, get_list_union_map with cset.
  - econstructor;
    eauto using get_live_exp_sound with cset pe ann.
  - econstructor; eauto with len.
    + eapply IHrenamedApart.
      repeat rewrite List.map_app; eauto with len.
      eauto with len.
    + intros; inv_get. eapply H1; eauto with len.
    + intros; inv_get. edestruct H2; eauto; dcr.
      cases; split; pe_rewrite; eauto with cset pe ann.
    + eauto with cset pe ann.
Qed.

Lemma indexwise_R_bounded D Dt F ans
:  indexwise_R (funConstr D Dt) F ans
   -> bounded
       (Some ⊝ (fst ⊝ getAnn ⊝ ans) \\ (fst ⊝ F)) D.
Proof.
  intros.
  eapply get_bounded.
  intros; inv_get.
  edestruct H; eauto; dcr.
  eauto with cset pe ann.
Qed.

Lemma zip_lminus_get X `{OrderedType X} ZL n Z Lv lv
  : get ZL n Z
    -> get Lv n lv
    -> get (Lv \\ ZL) n (lv \ of_list Z).
Proof.
  intros GetZL GetLv. eapply (zip_get (@lminus _ _) GetLv GetZL).
Qed.

Hint Resolve zip_lminus_get.

Lemma renamedApart_live s ang ZL Lv i
: renamedApart s ang
  -> paramsMatch s (@length _ ⊝ ZL)
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> length ZL = length Lv
  -> live_sound i ZL Lv s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl in * |- *; pe_rewrite.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset.
  - inv_get.
    econstructor; simpl;
    eauto using live_exp_sound_incl, live_freeVars, get_list_union_map with cset.
    + cases; eauto.
      eapply bounded_get; eauto using map_get_1.
  - econstructor;
    eauto using get_live_exp_sound, live_freeVars with cset pe ann.
  - assert (bounded (Some ⊝ (getAnn ⊝ mapAnn fst ⊝ ans ++ Lv) \\ (fst ⊝ F ++ ZL)) D). {
      rewrite zip_app; eauto with len.
      rewrite List.map_app.
      rewrite getAnn_mapAnn_map.
      rewrite bounded_app; split; eauto using indexwise_R_bounded.
    }
    econstructor; eauto with len.
    + eapply IHrenamedApart; eauto with len; simpl.
    + intros. inv_get.
      eapply H1; eauto.
      * edestruct H2; eauto; dcr. rewrite H15.
        rewrite zip_app; eauto with len.
        rewrite List.map_app. rewrite <- incl_right.
        rewrite getAnn_mapAnn_map.
        rewrite bounded_app; split; eauto using indexwise_R_bounded.
      * eauto with len.
    + intros. inv_get. edestruct H2; eauto; dcr.
      cases; eauto with cset pe ann.
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

Lemma disjoint_let D D' D'' x ZL (Lv:list (set var)) an
: D''[=]{x; D'}
  -> disjoint (Some ⊝ Lv \\ ZL) (D'')
  -> pe (getAnn an) ({x; D}, D')
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite H in *. simpl. rewrite incl_add'; eauto.
Qed.

Lemma disjoint_if1 D D' Ds Dt  ZL Lv an
:  Ds ∪ Dt [=] D'
  -> disjoint (Some ⊝ Lv \\ ZL) D'
  -> pe (getAnn an) (D, Ds)
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_left; eauto.
Qed.

Lemma disjoint_if2 D D' Ds Dt ZL Lv an
:  Ds ∪ Dt [=] D'
  -> disjoint (Some ⊝ Lv \\ ZL) D'
  -> pe (getAnn an) (D, Dt)
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_right; eauto.
Qed.


Notation "'Subset1'" := (fun (x : set var) (y : set var * set var) => x[<=] fst y).


Instance Subset1_morph
: Proper (Equal ==> @pe _ _ ==> iff) Subset1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Lemma disjoint_app L L' D
: disjoint (L ++ L') D <-> disjoint L D /\ disjoint L' D.
Proof.
  split; unfold disjoint.
  - split; intros; eauto using get_shift, get_app.
  -intros. eapply get_app_cases in H0; intuition; eauto.
Qed.

Lemma disjoint_funF1 ZL Lv D D' F ans Dt lv als
: disjoint (Some ⊝ Lv \\ ZL) D'
  -> list_union (zip defVars F ans) ∪ Dt[=]D'
  -> indexwise_R (funConstr D Dt) F ans
  -> (forall n a b, get als n a -> get ans n b -> ann_R Subset1 a b)
  -> lv ⊆ D'
  -> length F = length ans
  -> length F = length als
  -> disj D D'
  -> disjoint (Some ⊝ ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))) lv.
Proof.
  intros.
  rewrite zip_app; eauto with len.
  rewrite List.map_app.
  rewrite disjoint_app; split.
  - hnf; intros n s A.
    inv_get; subst; simpl in *.
    edestruct (get_length_eq _ A H4).
    edestruct H1; eauto; dcr. exploit H2; eauto.
    eapply ann_R_get in H11.
    destruct (getAnn x2); simpl in *.
    repeat get_functional.
    rewrite H3. rewrite H11. rewrite H10.
    eauto with cset.
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

Hint Resolve disjoint_funF1 lv_incl : cset.

Lemma incl_minus_incl_union X `{OrderedType X} s t u
  : s \ t ⊆ u
    -> s ⊆ t ∪ u.
Proof.
  intros. rewrite <- H0. cset_tac.
Qed.

Lemma incl_union_lr_eq X `{OrderedType X} s t u v
  : s ∪ t [=] u
    -> v ∪ t ⊆ v ∪ u.
Proof.
  intros. rewrite <- H0. eauto with cset.
Qed.

Lemma incl_union_eq X `{OrderedType X} s t u
  : s ∪ t [=] u
    -> t ⊆ u.
Proof.
  intros. rewrite <- H0. eauto with cset.
Qed.

Lemma incl_add_union_union X `{OrderedType X} s x t u
  : s [=] {x; t}
    -> {x; u} ∪ t ⊆ u ∪ s.
Proof.
  intros. rewrite H0. cset_tac.
Qed.

Hint Immediate incl_minus_incl_union incl_union_lr_eq incl_union_eq incl_add_union_union : cset.

(* Coq ist so doof *)
Lemma renamedApart_disj_F s D D' ans ant
  :  renamedApart s (annF (D, D') ans ant)
     -> disj D D'.
Proof.
  intros H. eapply (renamedApart_disj H).
Qed.

Lemma incl_minus_disj X `{OrderedType X} s t D Ds x
  : s ⊆ t
    -> disj s D
    -> D [=] {x; Ds}
    -> s ⊆ t \ singleton x.
Proof.
  intros. eauto with cset.
Qed.

Hint Immediate incl_minus_disj renamedApart_disj_F : cset.

Lemma funConstr_disjoint_fun_defs F ans alvs D Dt k a
  : length F = length ans
    -> length F = length alvs
    -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
          get alvs n a -> get ans n b -> ann_R Subset1 a b)
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans)
    -> disj D (list_union (defVars ⊜ F ans) ∪ Dt)
    -> get ans k a
    -> disj (fst (getAnn a)) (snd (getAnn a))
    -> disjoint (Some ⊝ (getAnn ⊝ alvs) \\ (fst ⊝ F)) (snd (getAnn a)).
Proof.
  intros. hnf; intros; inv_get.
  edestruct H2; eauto; dcr.
  exploit H1 as A; eauto. eapply ann_R_get in A.
  decide (k = n); subst.
  - repeat get_functional. eauto with cset.
  - exploit H3 as B; [ eauto | eauto using zip_get | eauto using zip_get|].
    unfold defVars in B.
    exploit H1 as C; try eapply H10; eauto. eapply ann_R_get in C.
    edestruct H2; try eapply H10; eauto; dcr.
    rewrite C. rewrite H13.
    eapply disj_1_incl. eapply disj_2_incl. eapply H4.
    + eapply incl_union_left.
      eapply incl_list_union; eauto using zip_get.
      unfold defVars. eapply incl_right.
    + clear_all; cset_tac.
Qed.

Lemma renamedApart_globals_live s ZL Lv alv f ang
: live_sound Imperative ZL Lv s alv
  -> renamedApart s ang
  -> isCalled s f
  -> ann_R Subset1 alv ang
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn ang))
  -> exists lv Z, get ZL (counted f) Z
            /\ get Lv (counted f) lv
            /\ (lv \ of_list Z) ⊆ getAnn alv.
Proof.
  revert ZL Lv alv f ang.
  sind s; destruct s; simpl; intros; invt live_sound;
    invt renamedApart; invt (@ann_R); invt isCalled; simpl in * |- *.
  - edestruct (IH s); dcr; eauto using disjoint_let.
    + do 2 eexists; split; [| split]; eauto with cset.
      exploit H3; eauto.
      rewrite <- H12.
      eauto with cset.
  - edestruct (IH s1); dcr; eauto using disjoint_if1.
    do 2 eexists; split; [| split]; eauto. rewrite <- H13; eauto.
  - edestruct (IH s2); dcr; eauto using disjoint_if2 with cset.
  - eauto.
  - edestruct (IH s); dcr; eauto using disjoint_let.
    + do 2 eexists; split; [| split]; eauto with cset.
      exploit H3; eauto. rewrite <- H13.
      eauto with cset.
  - clear H H1. eapply renamedApart_disj in H0. simpl in *.
    invc H19.
    + exploit (IH s); eauto with cset.
      pe_rewrite. eauto with cset.
      dcr. destruct f; simpl in *.
      inv_get. do 2 eexists; split; [| split]; eauto with cset.
    + exploit (IH s); eauto with cset. pe_rewrite. eauto with cset.
      dcr. simpl in *; inv_get.
      setoid_rewrite <- H13; setoid_rewrite <- H22.
      clear H22 H15 H16 H2 H25 H6 H13 H.
      general induction H4.
      *  inv_get. exploit (IH (snd Zs)); eauto with cset.
         dcr. destruct f; simpl in *.
         inv_get. do 2 eexists; split; [| split]; eauto.
         rewrite <- H15.
         assert ((of_list (fst Zs)) ⊆ D'). {
           rewrite <- H18. eapply incl_union_left.
           eapply incl_list_union. eapply zip_get; eauto.
           unfold defVars. eauto with cset.
         }
         assert (disj (x \ of_list x2) D'). {
           eapply disj_1_incl; [ eapply H3 | ]; eauto using map_get_1.
         }
         eauto with cset.
      * inv_get.
        edestruct (IH (snd Zs0));[ eauto | eauto | eauto | eauto | eauto | eauto | ].
        rewrite zip_app, List.map_app; [| eauto with len].
        eapply disjoint_app. split.
        eapply funConstr_disjoint_fun_defs; eauto. rewrite H18. eauto.
        eapply renamedApart_disj. eauto.
        assert (snd (getAnn x0) ⊆ D').
        rewrite <- H18. eapply incl_union_left.
        eapply incl_list_union; eauto using zip_get.
        unfold defVars. eapply incl_right.
        rewrite H15. eauto.

        dcr. simpl in *. inv_get.
        time (exploit IHisCalledIn). Focus 19. reflexivity.
        eauto. eauto. eauto. eauto.
        eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        dcr.
        do 2 eexists; split; [|split]; eauto.
        rewrite H25.
        destruct f. simpl in *.
        rewrite <- H22.
        assert ((of_list (fst Zs0)) ⊆ D'). {
           rewrite <- H18. eapply incl_union_left.
           eapply incl_list_union. eapply zip_get; eauto.
           unfold defVars. eauto with cset.
         }
        assert (disj (getAnn x2 \ of_list (fst Zs)) D'). {
          eapply disj_1_incl; [ eapply H1 | ].
          exploit H24; eauto. eapply ann_R_get in H20.
          rewrite H20.
          edestruct H12; try eapply H6; eauto. rewrite H26.
          clear_all; cset_tac.
        }
        eauto with cset.
Qed.

Lemma renamedApart_live_imperative_is_functional s ang ZL Lv alv
: renamedApart s ang
  -> noUnreachableCode s
  -> live_sound Imperative ZL Lv s alv
  -> ann_R Subset1 alv ang
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn ang))
  -> live_sound FunctionalAndImperative ZL Lv s alv.
Proof.
  intros RA NUC LS AR DISJ.
  general induction LS; invt noUnreachableCode; invt renamedApart; invt (@ann_R);
  eauto 50 using live_sound, disjoint_let, disjoint_if1, disjoint_if2.
  - econstructor; simpl; eauto.
    + eapply IHLS; eauto using disjoint_funF1.
      eapply disjoint_funF1; eauto.
      * simpl. pe_rewrite. rewrite <- H16. eapply incl_right.
      * simpl. eapply renamedApart_disj in RA. eauto.
    + intros. inv_get.
      eapply H1; eauto.
      eapply disjoint_funF1; eauto. simpl.
      eapply lv_incl; eauto. simpl.
      eapply renamedApart_disj in RA. eauto.
    + intros. inv_get.
      simpl in *.
      edestruct (@renamedApart_globals_live t);
        eauto using get_range; simpl in *; dcr.
      eapply disjoint_funF1; eauto. pe_rewrite.
      rewrite <- H16; eapply incl_right.
      eapply renamedApart_disj in RA; eauto.
      eapply get_in_range_app in H18; eauto using get_range.
      inv_get. simpl in *.
      rewrite H25; split; eauto.
      edestruct H2; eauto; dcr.
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
  : Exp.freeVars e ⊆ D
   -> live_exp_sound e lv
   -> live_exp_sound e (lv ∩ D).
Proof.
  intros.
  eapply Exp.freeVars_live in H0.
  eapply live_exp_sound_incl; eauto using Exp.live_freeVars.
  rewrite <- H, <- H0. cset_tac; intuition.
Qed.

Local Hint Extern 0 => pe_rewrite_step : cset.

Notation "'meet1'" := (fun (x:set var) (y:set var * set var) => x ∩ fst y).

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

Hint Resolve meet1_incl : cset.

Lemma meet1_incl2 a b
: Subset1 (meet1 a b) b.
Proof.
  destruct b; simpl. hnf. cset_tac; intuition.
Qed.

Hint Resolve meet1_incl2 : cset.

Lemma meet1_Subset1 s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset1 (mapAnn2 meet1 alv ang) ang.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl2.
  - econstructor; eauto with cset len.
    + intros; inv_get.
      symmetry in H. edestruct get_length_eq; try eapply H; eauto.
Qed.

Lemma live_sound_renamedApart_minus s ang ZL Lv alv i
: renamedApart s ang
  -> live_sound i ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> live_sound i ZL Lv s (mapAnn2 meet1 alv ang).
Proof.
  intros RA LS.
  general induction RA; invt live_sound; simpl in * |- *; pe_rewrite;
    eauto using live_sound, live_exp_sound_meet.

  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let, bounded_incl with cset ann.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite.
      rewrite minus_dist_intersection. rewrite H12.
      eauto with cset.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite. simpl; cset_tac; eauto.
  - econstructor; eauto using live_exp_sound_meet.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation with cset.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation with cset.
  - econstructor; eauto.
    + cases; simpl in *; eauto.
      exploit bounded_get; eauto.
      eauto with cset.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto.
  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let with cset.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite.
      rewrite minus_dist_intersection. rewrite H13.
      eauto with cset.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite. cset_tac; eauto.
  - constructor; eauto with len.
    + eapply IHRA; eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; eauto 20 with len.
        inv_get.
        simpl.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                                 renamedApart_annotation.
        edestruct H2; eauto; dcr.
        eauto with cset.
      * rewrite zip_app; eauto with len.
        rewrite List.map_app.
        eapply bounded_app; split; eauto.
        eapply get_bounded; intros; inv_get.
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x3); simpl in *.
        unfold lminus.
        rewrite H8.
        clear_all; cset_tac; intuition.
    + intros. inv_get.
      eapply H1; eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        eapply PIR2_get; [intros; inv_get; simpl | eauto 20 with len].
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        eauto with cset.
      * rewrite zip_app; eauto with len.
        rewrite List.map_app.
        eapply bounded_app; split; eauto.
        eapply get_bounded.
        intros; inv_get; simpl.
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x5); unfold lminus; simpl in *.
        rewrite H15.
        edestruct (H2 _ _ _ H7 H8); eauto; dcr. rewrite H19.
        clear_all; cset_tac; intuition.
        edestruct H2; eauto; dcr. rewrite H13.
        rewrite <- incl_right; eauto.
    + intros. inv_get.
      erewrite getAnn_mapAnn2;
        eauto using live_sound_annotation, renamedApart_annotation.
      edestruct H2; eauto; dcr. destruct (getAnn x0); simpl in *.
      exploit H14; eauto; dcr.
      split. eauto with cset.
      cases; eauto. rewrite H13. rewrite <- H21.
      clear_all; cset_tac; intuition.
    + erewrite getAnn_mapAnn2;
        eauto using live_sound_annotation, renamedApart_annotation with cset.
Qed.
