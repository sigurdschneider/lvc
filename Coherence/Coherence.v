Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness Restrict Bisim MoreExp SetOperations.
Require Import DecSolve RenamedApart LabelsDefined InRel.

Set Implicit Arguments.

(** * Definition of Coherence: [srd] *)

Notation "'oglobals' F alF" := (List.map Some ((getAnn ⊝ alF) \\ (fst ⊝ F))) (at level 50, F, alF at level 0).

Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
| srdExp DL x e s lv al
  : srd (restrict DL (lv \ singleton x)) s al
    -> srd DL (stmtLet x e s) (ann1 lv al)
| srdIf DL e s t lv als alt
  : srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf e s t) (ann2 lv als alt)
| srdRet e DL lv
  : srd DL (stmtReturn e) (ann0 lv)
| srdGoto DL lv G' f Y
  : get DL (counted f) (Some G')
    -> srd DL (stmtApp f Y) (ann0 lv)
| srdExtern DL x f Y s lv al
  : srd (restrict DL (lv \ singleton x)) s al
    -> srd DL (stmtExtern x f Y s) (ann1 lv al)
| srdLet DL F t lv als alt
  : length F = length als
    -> (forall n Zs a, get F n Zs -> get als n a ->
                 srd (restrict (oglobals F als ++ DL)
                               (getAnn a \ of_list (fst Zs))) (snd Zs) a)
    -> srd (oglobals F als ++ DL) t alt
    -> srd DL (stmtFun F t) (annF lv als alt).


(** ** Some monotonicity properties *)

Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor. eapply IHsrd; eauto.
    eapply restrict_subset; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite restrict_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.

Lemma srd_monotone2 (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR (flip Subset)) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset2; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor. eapply IHsrd, restrict_subset2; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite restrict_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset2; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.

(** *** Every renamed apart program is coherent *)
(** Note that this lemma also builds the liveness annotation:
    It exploits that we can always claim more variables live *)

Hint Extern 20 =>
match goal with
  | [ H: length ?L = length ?L' |- length ?L = length (List.map ?f ?L')] => rewrite map_length; eauto
end.

Lemma inv_oglobals (F:〔params*stmt〕) als k lv
: length F = length als
  -> get (oglobals F als) k ⎣lv⎦
  -> exists Zs a, get F k Zs /\ get als k a /\ lv = getAnn a \ of_list (fst Zs).
Proof.
  intros. length_equify.
  general induction H; isabsurd.
  - inv H0.
    + eexists; eauto using get.
    + edestruct IHlength_eq as [? []]; eauto; dcr; subst.
      do 2 eexists; eauto using get.
Qed.

Lemma inv_globals (F:〔params*stmt〕) als k lv
: length F = length als
  -> get ((getAnn ⊝ als) \\ (fst ⊝ F)) k lv
  -> exists Zs a, get F k Zs /\ get als k a /\ lv = getAnn a \ of_list (fst Zs).
Proof.
  intros. length_equify.
  general induction H; isabsurd.
  - inv H0.
    + eexists; eauto using get.
    + edestruct IHlength_eq as [? []]; eauto; dcr; subst.
      do 2 eexists; eauto using get.
Qed.

Lemma renamedApart_coherent s ang DL
  : renamedApart s ang
    -> labelsDefined s (length DL)
    -> bounded (List.map Some DL) (fst (getAnn ang))
    -> srd (List.map Some DL) s (mapAnn fst ang).
Proof.
  intros. general induction H; invt labelsDefined; simpl in * |- *; pe_rewrite.
  - econstructor; eauto.
    eapply srd_monotone.
    eapply IHrenamedApart; eauto with cset.
    erewrite bounded_restrict_eq; simpl; eauto. eauto with cset.
  - econstructor; eauto.
  - econstructor.
  - edestruct get_in_range as [a ?]; eauto using map_get_1, srd.
  - econstructor; eauto.
    eapply srd_monotone.
    eapply IHrenamedApart; eauto with cset.
    erewrite bounded_restrict_eq; simpl; eauto. eauto with cset.
  - econstructor; eauto.
    + intros. inv_map H10.
      exploit H1; eauto.
      * instantiate (1:=(getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL).
        rewrite app_length. rewrite zip_length2; eauto with len.
        repeat rewrite map_length. rewrite <- H. eauto.
      * edestruct H2; eauto; dcr.
        rewrite List.map_app. eapply bounded_app; split; eauto.
        rewrite H14. eapply get_bounded.
        intros. inv_map H15. eapply inv_globals in H17.
        destruct H17; dcr; subst.
        inv_map H20. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H22.
        revert H26; clear_all; cset_tac; intuition.
        eauto with len.
        rewrite H14. rewrite <- incl_right; eauto.
      * eapply srd_monotone. eapply H14.
        rewrite getAnn_mapAnn; simpl.
        repeat rewrite restrict_app. rewrite List.map_app.
        eapply PIR2_app.
        erewrite bounded_restrict_eq. reflexivity.
        reflexivity.
        eapply get_bounded.
        intros. eapply inv_oglobals in H15.
        destruct H15; dcr; subst.
        inv_map H16. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H18.
        decide (n=n0); subst. repeat get_functional.
        rewrite H18. clear_all; cset_tac; intuition.
        exploit H3; eauto. eapply zip_get; eauto. eapply zip_get; eauto.
        unfold defVars in H19. simpl in *.
        edestruct H2; try eapply H12; eauto. dcr. rewrite H21.
        revert H22 H27; clear_all; cset_tac; intuition; eauto.
        eauto with len.
        erewrite bounded_restrict_eq; simpl; eauto.
        edestruct H2; eauto; dcr.
        rewrite H15. revert H19; clear_all; cset_tac; intuition; eauto.
    + eapply srd_monotone.
      eapply (IHrenamedApart ((getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL)); eauto.
      * rewrite app_length, zip_length2, map_length, map_length, <- H; eauto with len.
      * pe_rewrite. rewrite List.map_app. rewrite bounded_app. split; eauto.
        eapply get_bounded.
        intros. inv_map H9. eapply inv_globals in H10.
        destruct H10; dcr; subst.
        inv_map H12. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H15.
        clear_all; cset_tac; intuition. eauto with len.
      * rewrite List.map_app. reflexivity.
Qed.

(** *** In a coherent program, the globals of every function that can eventually be called are live *)

Lemma eqReq_oglobals_liveGlobals (F:〔params*stmt〕) als
: length F = length als
  -> PIR2 eqReq (oglobals F als) (zip pair (getAnn ⊝ als) (fst ⊝ F)).
Proof.
  intros. length_equify. general induction H; simpl; eauto using PIR2.
  - econstructor; eauto.
    econstructor; reflexivity.
Qed.


Lemma srd_globals_live s DL AL alv f
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> isCalled s f
  -> exists lv, get DL (counted f) (Some lv) /\ lv ⊆ getAnn alv.
Proof.
  intros. general induction H0; invt live_sound; invt isCalled; simpl in * |- *.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct IHsrd1; eauto. dcr.
    eexists; split; eauto. rewrite <- H12; eauto.
  - edestruct IHsrd2; eauto. dcr.
    eexists; split; eauto. rewrite <- H13; eauto.
  - eexists; split; eauto.
    edestruct PIR2_nth; eauto; dcr. get_functional; subst.
    inv H5; simpl in *. rewrite H4; eauto.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct get_length_eq; eauto.
    edestruct H1; eauto.
    rewrite restrict_app. eapply PIR2_app; eauto using restrict_eqReq.
    eapply restrict_eqReq; eauto using eqReq_oglobals_liveGlobals.
    dcr. destruct f; simpl in *.
    edestruct IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    simpl in *; dcr.
    rewrite restrict_app in H11.
    assert (length F = length (restrict (oglobals F als) (getAnn x \ of_list (fst Zs)))).
    rewrite restrict_length. eauto with len.
    rewrite H7 in H11. eapply shift_get in H11.
    eapply restrict_get in H11; dcr.
    eexists; split; eauto.
    eapply get_app_lt_1 in H19.
    eapply inv_oglobals in H19. destruct H19; dcr. repeat get_functional; subst.
    rewrite H22, H20; eauto. eauto.
    rewrite map_length, zip_length2, map_length, <- H; eauto with len.
  - edestruct IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    destruct f; simpl in *.
    dcr.
    assert (LEN: length F = length (oglobals F als)) by eauto with len.
    erewrite LEN in H7. eapply shift_get in H7.
    eexists; split; eauto. rewrite H8; eauto.
Qed.

(** *** On a coherent program a liveness analysis which is sound imperatively is also sound functionally. *)

Lemma srd_live_functional s DL AL alv
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> noUnreachableCode s
  -> live_sound FunctionalAndImperative AL s alv.
Proof.
  intros. general induction H0; invt live_sound; invt noUnreachableCode; simpl in * |- *;
          eauto using live_sound, restrict_eqReq.
  - econstructor; eauto.
    + eapply IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    + intros. eapply H1; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    + intros. exploit H15; eauto; dcr.
      edestruct srd_globals_live; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
      eapply H10; eauto. eapply get_length; eauto. dcr.
      simpl; split; eauto.
      eapply get_app_lt_1 in H18; simpl.
      eapply inv_oglobals in H18. destruct H18; dcr. simpl in *. repeat get_functional; subst.
      rewrite H19; eauto. eauto.
      rewrite map_length, zip_length2, map_length, <- H; eauto using get_range with len.
Qed.

(** ** Definition of invariance *)

Definition invariant (s:stmt) :=
  forall (E:onv val), bisim (nil:list F.block,E,s) (nil:list I.block,E,s).

(** ** Agreement Invariant *)

Definition rd_agree (DL:list (option (set var)))
           L (E:onv val)
  := forall n blk G', get L n blk -> get DL n (Some G') ->
                      agree_on eq G' E (F.block_E blk).


Lemma rd_agree_update DL L E G x v
 (RA:rd_agree DL L E)
  : rd_agree (restrict DL (G \ singleton x)) L (E [x <- v]).
Proof.
  intros. hnf; intros.
  unfold restrict in H0. eapply map_get_4 in H0; dcr.
  unfold restr in H2. destruct x0; isabsurd. cases in H2; isabsurd.
  inv H2. eapply agree_on_update_dead. rewrite COND. cset_tac.
  eapply RA; eauto.
Qed.

Lemma rd_agree_update_list DL L E E' (G G':set var) Z n vl
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G' [=] ∅)
 (LEQ:length Z = length vl)
 (AG:agree_on eq G' E E')
: rd_agree (restrict (drop n DL) G') (drop n L) (E'[Z <-- vl]).
Proof.
  hnf; intros.
  assert (G'0 ⊆ G'). {
    eapply bounded_get; eauto. eapply bounded_restrict; reflexivity.
  }
  assert (G'0 [=] G'0 \ of_list Z) by (split; cset_tac; intuition eauto).
  rewrite H2. eapply update_with_list_agree_minus; eauto.

  unfold restrict in H0. rewrite drop_map in H0.
  eapply get_drop in H. eapply get_drop in H0.
  eapply map_get_4 in H0; dcr.
  hnf in RA.
  etransitivity; try eapply RA; eauto.
  symmetry. eauto using agree_on_incl.
  eapply restr_iff in H4; dcr; subst; eauto.
Qed.

(** ** Context coherence for IL/F contexts: [approxF] *)

Inductive approx
  : list (option (set var) * (set var * list var)) -> list F.block -> list I.block ->
    option (set var) * (set var * list var) -> F.block -> I.block -> Prop :=
  approxI AL DL o Z E s n lvZ L1 L2
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restrict AL G) s a
                /\ live_sound Imperative DL s a)
     -> snd lvZ = Z
     -> length AL = length DL
     -> approx (zip pair AL DL) L1 L2 (o, lvZ) (F.blockI E Z s n) (I.blockI Z s n).

(** Stability under restriction *)


Unset Printing Records.

Lemma approx_restrict_block AL1 AL2 DL1 DL2 L1 L2 G n AL1' DL1' L1X L2X
: length AL1 = length DL1
  -> length AL2 = length DL2
  -> mutual_block (approx (zip pair AL1 DL1 ++ zip pair AL2 DL2) L1X L2X) n
                 (zip pair AL1' DL1') L1 L2
  -> mutual_block
      (approx (zip pair (restrict AL1 G) DL1 ++ zip pair (restrict AL2 G) DL2) L1X L2X)
      n (zip pair (restrict AL1' G) DL1') L1 L2.
Proof.
  intros. general induction H1.
  - destruct AL1', DL1'; isabsurd; constructor.
  - eapply zip_eq_cons_inv in Heql. destruct Heql as [? [? ?]]; eauto; dcr; subst.
    simpl. econstructor; eauto.
    inv H2. rewrite <- zip_app; try rewrite restrict_length; eauto.
    rewrite <- zip_app in H0; eauto.
    eapply zip_pair_app_inv in H0; dcr; subst; eauto.
    simpl.
    econstructor; eauto.
    intros. eapply restr_iff in H0; dcr; subst. exploit H7; eauto; dcr.
    split; eauto.
    eexists x; eauto.
    rewrite <- restrict_app; eauto. rewrite restrict_idem; eauto with len.
    repeat rewrite app_length. repeat rewrite restrict_length. congruence.
Qed.

Lemma approx_restrict AL DL G L L'
: length AL = length DL
  -> inRel approx (zip pair AL DL) L L'
  -> inRel approx (zip pair (restrict AL G) DL) L L'.
Proof.
  intros. length_equify.
  general induction H0; simpl in *; eauto using inRel.
  - inv H; isabsurd; econstructor.
  - eapply zip_eq_app_inv in Heql; eauto using length_eq_length.
    destruct Heql as [AL1 [AL2 [DL1 [DL2 ?]]]]; dcr; subst.
    rewrite restrict_app. rewrite zip_app; try rewrite restrict_length; eauto.
    econstructor. eapply IHinRel; eauto using length_length_eq.
    eapply approx_restrict_block; eauto.
Qed.


Unset Printing Records.

(** ** Main Theorem about Coherence *)

(** [stripB] removes the environment from a closure  *)
Definition stripB (b:F.block) : I.block :=
  match b with
    | F.blockI E Z s n => I.blockI Z s n
  end.

Definition strip := List.map stripB.

Lemma drop_strip n L
  : drop n (strip L) = strip (drop n L).
Proof.
  unfold strip. rewrite drop_map; eauto.
Qed.

(** The Bisimulation candidate. *)

Inductive srdSim : F.state -> I.state -> Prop :=
  | srdSimI (E EI:onv val) L L' s AL DL a
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: inRel approx (zip pair AL DL) L L')
  (AG:agree_on eq (getAnn a) E EI)
  (LV:live_sound Imperative DL s a)
  (ER:PIR2 eqReq AL DL)
  : srdSim (L, E, s) (L', EI,s).


Lemma zip_zip X X' Y Y' Z (f:X->Y->Z) (g1:X'->Y'->X) (g2:X'->Y'->Y) L L'
: zip f (zip g1 L L') (zip g2 L L') =
  zip (fun x y => f (g1 x y) (g2 x y)) L L'.
Proof.
  intros. general induction L; destruct L'; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma zip_sym X Y Z (f:X->Y->Z) L L'
: zip f L L' = zip (fun x y => f y x) L' L.
Proof.
  general induction L; destruct L'; simpl; eauto.
  f_equal; eauto.
Qed.


Lemma drop_zip X Y Z (f:X->Y->Z) L L' n
: length L = length L'
  -> drop n (zip f L L') = zip f (drop n L) (drop n L').
Proof.
  intros. length_equify.
  general induction H; simpl; eauto.
  - repeat rewrite drop_nil; eauto.
  - destruct n; simpl; eauto.
Qed.


Lemma rd_agree_extend F als AL L E
: length F = length als
  -> rd_agree AL L E
  -> rd_agree (oglobals F als ++ AL) (mapi (F.mkBlock E) F ++ L) E.
Proof.
  intros. hnf; intros.
  assert (length (mapi (F.mkBlock E) F) = length (oglobals F als)) by
  eauto 30 with len.
  assert (length (oglobals F als) = length F) by eauto with len.
  eapply get_app_cases in H2; eauto. destruct H2.
  - eapply get_in_range_app in H1; eauto.
    eapply inv_oglobals in H2; eauto. destruct H2; dcr; subst; eauto.
    inv_get. reflexivity.
    eapply get_range in H2. rewrite H4 in H2.
    erewrite mapi_length_ass; eauto.
  - dcr.
    eapply H0; eauto.
    eapply shift_get; eauto. instantiate (2:=mapi (F.mkBlock E) F).
    orewrite (length (mapi (F.mkBlock E) F) + (n - length (oglobals F als)) = n); eauto.
Qed.


(** The bisimulation is indeed a bisimulation *)

Lemma srdSim_sim σ1 σ2
  : srdSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; inv SRD; inv LV; simpl in *; try provide_invariants_21.
  - case_eq (exp_eval E e); intros.
    one_step.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto.
    eapply srdSim_sim; econstructor;
    eauto using approx_restrict, rd_agree_update, PIR2_length.
    eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl; eauto.
    eauto using restrict_eqReq.
    no_step.
    erewrite <- exp_eval_live in def; eauto. congruence.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_live_agree; eauto.
    case_eq (val2bool v); intros.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    exploit exp_eval_live_agree; eauto.
    no_step.
  - no_step. simpl. eapply exp_eval_live; eauto.
  - decide (length Z = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; eauto.
      exploit (@zip_get _ _ _ pair AL DL); eauto.
      inRel_invs.
      one_step. simpl.
      eapply srdSim_sim.
      exploit H11; eauto; dcr. simpl in *.
      econstructor; simpl; eauto using approx_restrict, PIR2_length.
      assert (restrict AL0 G' = restrict (drop (labN f - n) AL) G').
      rewrite drop_zip in H8. eapply zip_pair_inv in H8; dcr; subst. reflexivity.
      eauto. repeat rewrite length_drop_minus. eapply PIR2_length in ER. omega.
      eauto using PIR2_length.
      rewrite H9.
      eapply rd_agree_update_list; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply (RA _ _ _ H4 H).
      eapply approx_restrict; eauto.
      rewrite H8. eapply (inRel_drop A H4).
      eapply update_with_list_agree; eauto. rewrite H12.
      rewrite union_comm. rewrite union_minus_remove.
      pose proof (RA _ _ G' H4 H); dcr. simpl in *.
      eapply agree_on_sym; eauto. eapply agree_on_incl; eauto using incl_minus.
      etransitivity; eauto. symmetry. hnf in RA.
      eapply agree_on_incl; eauto.
      edestruct PIR2_nth_2; eauto; dcr. get_functional; eauto; subst.
      inv H18. rewrite H16. simpl. eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply restrict_eqReq.
      rewrite drop_zip in H8; eauto using PIR2_length.
      eapply  zip_pair_inv in H8; dcr; subst; eauto.
      eapply PIR2_drop; eauto.
      repeat rewrite length_drop_minus. eapply PIR2_length in ER; eauto.
    + exploit omap_exp_eval_live_agree; eauto.
      no_step.
    + no_step.
  - case_eq (omap (exp_eval E) Y); intros;
    exploit omap_exp_eval_live_agree; eauto.
    extern_step; assert (vl = l) by congruence; subst; eauto.
    + eapply srdSim_sim; econstructor; eauto using approx_restrict, rd_agree_update, PIR2_length.
      eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto.
      eauto using restrict_eqReq; eauto.
    + symmetry in AG.
      exploit omap_exp_eval_live_agree; eauto.
      eapply srdSim_sim; econstructor; eauto using approx_restrict, rd_agree_update, PIR2_length.
      eapply agree_on_update_same. reflexivity.
      symmetry in AG.
      eapply agree_on_incl; eauto.
      eauto using restrict_eqReq; eauto.
    + no_step.
  - one_step.
    eapply srdSim_sim; econstructor;
    eauto using agree_on_incl, PIR2_app, eqReq_oglobals_liveGlobals, rd_agree_extend.
    rewrite zip_app; [|eauto 30 with len]. econstructor; eauto.
    unfold mapi.
    eapply mutual_approx; simpl; eauto 30 with len; try congruence.
    intros. inv_get. rewrite <- zip_app; eauto 20 with len.
    econstructor; eauto.
    intros. invc H2. simpl.
    split. unfold lminus. clear_all; cset_tac; intuition.
    eexists x0. split.
    exploit H11; eauto. dcr; simpl in *.
    unfold lminus. eauto with cset.
    split. exploit H0; eauto.
    exploit H10; eauto.
    eauto 30 using PIR2_length with len.
Qed.

(** ** Coherence implies invariance *)

Lemma srd_implies_invariance s a
: live_sound Imperative nil s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim.
  econstructor; eauto. isabsurd. econstructor. econstructor.
Qed.
