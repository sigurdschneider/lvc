Require Import Util IL Sawtooth LabelsDefined OptionR.
Require Import Annotation Liveness.Liveness Restrict SetOperations Coherence.
Require Import Sim SimTactics SimCompanion.

Set Implicit Arguments.
Unset Printing Records.


(** ** Definition of invariance *)

Definition invariant (s:stmt) :=
  forall (E:onv val), sim bot3 Bisim (nil:list F.block,E,s) (nil:list I.block,E,s).

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
  eapply agree_on_update_dead.
  rewrite H1. cset_tac.
  eapply RA; eauto.
Qed.

Lemma rd_agree_update_list DL L E E' (G:set var) Z n vl
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G [=] ∅)
 (LEQ:length Z = length vl)
 (AG:agree_on eq G E E')
: rd_agree (restr G ⊝ (drop n DL)) (drop n L) (E'[Z <-- vl]).
Proof.
  hnf; intros.
  assert (G' ⊆ G). {
    eapply bounded_get; eauto. eapply bounded_restrict; reflexivity.
  }
  assert (G' [=] G' \ of_list Z) by (split; cset_tac; intuition eauto).
  rewrite H2. eapply update_with_list_agree_minus; eauto.
  inv_get.
  hnf in RA.
  etransitivity; try eapply RA; eauto.
  symmetry. eauto using agree_on_incl.
Qed.

(** ** Main Theorem about Coherence *)

(** [strip] removes the environment from a closure  *)

Definition strip (b:F.block) : I.block :=
  I.blockI (F.block_Z b) (F.block_s b) (F.block_n b).

Lemma sawtooth_strip L
  : sawtooth L -> sawtooth (strip ⊝ L).
Proof.
  intros. general induction H; simpl; eauto using @sawtooth.
  - rewrite map_app. econstructor; eauto.
    revert H0; clear_all. generalize 0.
    intros.
    general induction H0; simpl; eauto using @tooth.
Qed.

Hint Resolve sawtooth_strip.

Lemma block_Z_strip L
  : I.block_Z ⊝ strip ⊝ L = F.block_Z ⊝ L.
Proof.
  intros. general induction L; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma mkBlock_strip F L E
  : mapi I.mkBlock F ++ strip ⊝ L = strip ⊝ (mapi (F.mkBlock E) F ++ L).
Proof.
  unfold mapi. generalize 0.
  general induction F; simpl; eauto.
  f_equal. erewrite IHF; eauto.
Qed.

(** The Bisimulation candidate. *)

Local Hint Extern 5 =>
match goal with
| [ H : ?m >= ?k, H' : ?k = ?n |- context [ ?n + (?m - ?n) ] ] =>
  let H := fresh "H" in
  assert (H:n + (m - n) = m) by omega;
    rewrite H;
    clear H
| [ H : ?m >= ?k, H' : ?k = ?n |- context [ ?n + (?m - ?k) ] ] =>
  let H := fresh "H" in
  assert (H:n + (m - k) = m) by omega;
    rewrite H;
    clear H
end.

Lemma rd_agree_extend F als AL L E
: length F = length als
  -> rd_agree AL L E
  -> rd_agree (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ AL) (mapi (F.mkBlock E) F ++ L) E.
Proof.
  intros. hnf; intros.
  eapply get_app_cases in H1; eauto. destruct H1; inv_get.
  - reflexivity.
  - dcr.
    eapply H0; eauto.
    assert (❬mapi (F.mkBlock E) F❭ = ❬Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F)❭) by eauto 20 with len.
    eapply shift_get; eauto. instantiate (1:=Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F)).
    eauto.
Qed.

(** The bisimulation is indeed a bisimulation *)

Ltac cone_step :=  eapply SimSilent; [ eapply plus2O; single_step
                          | eapply plus2O; single_step
                          | ].

Ltac cno_step := eapply SimTerm;
          [ | eapply star2_refl | eapply star2_refl | | ];
          [ repeat get_functional; try reflexivity
          | repeat get_functional; stuck2
          | repeat get_functional; stuck2 ].

Ltac cextern_step :=
  let STEP := fresh "STEP" in
  eapply SimExtern;
  [ eapply star2_refl
  | eapply star2_refl
  | try step_activated
  | try step_activated
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  ].

Require Import LivenessCorrect.

Lemma ZL_mapi_F F L E
  : F.block_Z ⊝ (mapi (F.mkBlock E) F ++ L) = fst ⊝ F ++ F.block_Z ⊝ L.
Proof.
  unfold mapi. generalize 0.
  general induction F; simpl; f_equal; eauto.
Qed.

(** ** Context coherence for IL/F contexts: [approxF] *)

(** Stability under restriction *)

Inductive approx Lv AL L f blv o b : Prop :=
| ApproxI lv
  : live_sound Imperative
               (drop (f - block_n b) (block_Z ⊝ L))
               (drop (f - block_n b) Lv) (F.block_s b) lv
    -> getAnn lv [=] blv
    ->  (forall G, o = Some G -> of_list (block_Z b) ∩ G [=] ∅ /\
                          getAnn lv [=] (G ∪ of_list (block_Z b))
                          /\ srd (restr G ⊝ (drop (f - block_n b) AL)) (F.block_s b) lv)
    -> approx Lv AL L f blv o b.


Lemma approx_restrict G Lv AL L f blv o b
  : approx Lv AL L f blv o b
    -> approx Lv (restr G ⊝ AL) L f blv (restr G o) b.
Proof.
  intros. invc H. econstructor; eauto with len.
  intros. eapply restr_iff in H; dcr; subst.
  specialize (H2 G0 eq_refl); eauto; dcr.
  rewrite drop_map in *. rewrite restrict_idem; eauto.
Qed.

Lemma approx_drop Lv AL L blv s g f fb gb
      (ST:sawtooth L) (Getg:get L f fb) (Getf:get L (f - F.block_n fb + g) gb)
  : approx Lv AL L (f - F.block_n fb + g) blv s gb
    -> approx (drop (f - F.block_n fb) Lv)
             (drop (f - F.block_n fb) AL)
             (drop (f - F.block_n fb) L) g blv s gb.
Proof.
  intros. invc H.
  econstructor; eauto.
  sawtooth; eauto.
  intros. specialize (H2 _ H). dcr; subst.
  split; eauto. split; eauto.
  sawtooth. rewrite <- drop_map. eauto.
Qed.

Lemma approx_extend Lv AL L f E F o b blv AL' Lv'
      (ST:sawtooth L) (GETf: get L (f - ❬F❭) b)
      (GE: f >= ❬F❭)
      (Len1:❬F❭ = ❬AL'❭)
      (Len2:❬F❭ = ❬Lv'❭)
  : approx Lv AL L (f - ❬F❭) blv o b
    -> approx (Lv' ++ Lv) (AL' ++ AL)
             (mapi (F.mkBlock E) F ++ L) f blv o b.
Proof.
  intros. invc H. econstructor; eauto.
  rewrite ZL_mapi_F.
  sawtooth. eauto.
  intros; subst. specialize (H2 _ eq_refl); dcr.
  split; eauto. split; eauto.
  sawtooth. rewrite map_app.
  sawtooth. rewrite drop_map in *. eauto.
Qed.


Lemma srdSim_sim AL Lv L
      (E:onv val) s lv
  (SRD:srd AL s lv)
  (RA:rd_agree AL L E)
  (ST:sawtooth L)
  (LA: forall f b blv o, get L f b ->
                  get Lv f blv ->
                  get AL f o ->
                  approx Lv AL L f blv o b)
  (LV:live_sound Imperative (block_Z ⊝ L) Lv s lv)
  (ER:PIR2 (ifFstR Equal) AL (Lv \\ (block_Z ⊝ L)))
  (Len: ❬Lv❭ = ❬AL❭)
  : simc bot3 Bisim (L, E, s) (strip ⊝ L, E, s).
Proof.
  unfold simc.
  revert_all. eapply Tower3.tower_ind3.
  hnf; intros. hnf; intros. eauto.
  intros.
  inv SRD; inv LV; simpl in *.
  - invt live_exp_sound.
    + case_eq (op_eval E e0); intros.
      * cone_step.
        eapply H; eauto using rd_agree_update with len.
        -- intros. inv_get. eapply approx_restrict; eauto.
        -- eauto using restrict_ifFstR.
      * cno_step.
    + case_eq (omap (op_eval E) Y); intros.
      * cextern_step; assert (vl = l) by congruence; subst; eauto.
        -- eapply H; eauto using rd_agree_update, PIR2_length, restrict_ifFstR with len.
           ++ intros; inv_get. eapply approx_restrict; eauto.
        -- eapply H; eauto using rd_agree_update, PIR2_length, restrict_ifFstR with len.
           ++ intros; inv_get. eapply approx_restrict; eauto.
      * cno_step.
  - case_eq (op_eval E e); intros.
    + case_eq (val2bool v); intros;
      cone_step; eauto using agree_on_incl.
    + cno_step.
  - cno_step.
  - decide (length Z = length Y).
    case_eq (omap (op_eval E) Y); intros.
    + inv_get. exploit LA; eauto. invc H2. simpl in *.
      specialize (H7 G' eq_refl). dcr. rewrite <- drop_map in *.
      cone_step; simpl. eauto with len.
      exploit RA; eauto; simpl in *.
      eapply simc_trans_r_left; swap 1 2.
      * eapply H; eauto with len.
        -- eapply rd_agree_update_list; eauto with len.
        -- intros. inv_get. eapply approx_restrict.
           exploit LA; try eapply H11; eauto using approx_drop.
        -- setoid_rewrite drop_map at 2.
           rewrite <- drop_zip.
           eapply restrict_ifFstR; eauto.
           eapply PIR2_drop; eauto.
      * eapply sim_lock_simc.
        rewrite drop_map in *.
        eapply liveSimI_sim; try rewrite !drop_map; try rewrite block_Z_strip; eauto.
        -- eapply (sawtooth_drop'); eauto.
        -- intros; inv_get. sawtooth.
           exploit LA; eauto. invc H16. eauto.
        -- rewrite H12. eapply update_with_list_agree; eauto with len.
           symmetry. eapply agree_on_incl; eauto.
           clear_all. cset_tac.
    + cno_step.
    + cno_step.
  - cone_step. erewrite mkBlock_strip.
    eapply H; try rewrite ZL_mapi; try rewrite ZL_mapi_F;
      eauto using agree_on_incl, PIR2_app, rd_agree_extend.
    * intros; inv_get. sawtooth.
      -- econstructor; simpl; eauto; try rewrite ZL_mapi_F; try reflexivity.
         sawtooth. eauto. intros. invc H4.
         split. clear_all; cset_tac; intuition.
         split.
         exploit H13; eauto; dcr; simpl in *; eauto with cset.
         exploit H1; eauto. sawtooth. eauto.
      -- eapply get_app_ge in H5; eauto; len_simpl; try omega.
         rewrite <- H0 in *. inv_get.
         exploit LA; eauto.
         eapply approx_extend; eauto with len.
    * rewrite zip_app; eauto with len.
      eapply PIR2_app; eauto using PIR2_ifFstR_refl.
    * eauto with len.
Qed.

(** ** Coherence implies invariance *)

Lemma srd_implies_invariance s a
: live_sound Imperative nil nil s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros.
  eapply simc_sim.
  eapply srdSim_sim with (L:=nil); eauto.
  isabsurd. econstructor. isabsurd. econstructor.
Qed.
