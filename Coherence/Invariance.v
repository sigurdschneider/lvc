Require Import Util IL InRel RenamedApart LabelsDefined.
Require Import Annotation Liveness Coherence Restrict MoreExp SetOperations.
Require Import Bisim BisimTactics.

Set Implicit Arguments.
Unset Printing Records.


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
  : rd_agree (restr (G \ singleton x) ⊝ DL) L (E [x <- v]).
Proof.
  intros. hnf; intros; inv_get.
  eapply agree_on_update_dead. rewrite H1. cset_tac.
  eapply RA; eauto.
Qed.

Lemma rd_agree_update_list DL L E E' (G G':set var) Z n vl
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G' [=] ∅)
 (LEQ:length Z = length vl)
 (AG:agree_on eq G' E E')
: rd_agree (restr G' ⊝ (drop n DL)) (drop n L) (E'[Z <-- vl]).
Proof.
  hnf; intros.
  assert (G'0 ⊆ G'). {
    eapply bounded_get; eauto. eapply bounded_restrict; reflexivity.
  }
  assert (G'0 [=] G'0 \ of_list Z) by (split; cset_tac; intuition eauto).
  rewrite H2. eapply update_with_list_agree_minus; eauto.
  inv_get.
  hnf in RA.
  etransitivity; try eapply RA; eauto.
  symmetry. eauto using agree_on_incl.
Qed.

(** ** Context coherence for IL/F contexts: [approxF] *)

Inductive approx
  : list (option (set var) * (set var * list var)) -> list F.block -> list I.block ->
    option (set var) * (set var * list var) -> F.block -> I.block -> Prop :=
  approxI AL DL o Z E s n lvZ L1 L2
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restr G ⊝ AL) s a
                /\ live_sound Imperative ZL DL s a)
     -> snd lvZ = Z
     -> length AL = length DL
     -> approx (zip pair AL DL) L1 L2 (o, lvZ) (F.blockI E Z s n) (I.blockI Z s n).

(** Stability under restriction *)

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


(** ** Main Theorem about Coherence *)

(** [strip] removes the environment from a closure  *)

Definition strip (b:F.block) : I.block :=
  match b with
    | F.blockI E Z s n => I.blockI Z s n
  end.

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
  destruct H; inv SRD; inv LV; simpl in *.
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
