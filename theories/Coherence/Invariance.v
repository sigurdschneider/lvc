Require Import Util IL InRel4 RenamedApart LabelsDefined OptionR.
Require Import Annotation Liveness Restrict SetOperations Coherence.
Require Import Sim SimTactics.

Set Implicit Arguments.
Unset Printing Records.


(** ** Definition of invariance *)

Definition invariant (s:stmt) :=
  forall (E:onv val), sim Bisim (nil:list F.block,E,s) (nil:list I.block,E,s).

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

(** ** Context coherence for IL/F contexts: [approxF] *)

Inductive approx
  : list params -> list params -> list (؟ (set var)) -> list (set var) -> list F.block -> list I.block ->
    params -> params -> option (set var) -> set var -> F.block -> I.block -> Prop :=
  approxI ZL AL Lv o Z E s n lv L1 L2
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restr G ⊝ AL) s a
                /\ live_sound Imperative ZL Lv s a)
     -> length AL = length ZL
     -> length ZL = length Lv
     -> approx ZL ZL AL Lv L1 L2 Z Z o lv (F.blockI E Z s n) (I.blockI Z s n).

(** Stability under restriction *)

Lemma approx_restrict G
  : forall (AL1 AL2 : 〔params〕) (AL3 : 〔؟ ⦃var⦄〕) (AL4 : 〔⦃var⦄〕) (L1 : 〔F.block〕)
     (L2 : 〔I.block〕) (a1 a2 : params) (a3 : ؟ ⦃var⦄) (a4 : ⦃var⦄) (b1 : F.block)
     (b2 : I.block),
   approx AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b1 b2 ->
   approx AL1 AL2 (restr G ⊝ AL3) AL4 L1 L2 a1 a2 (restr G a3) a4 b1 b2.
Proof.
  intros. inv H. econstructor; eauto with len.
  intros. destruct a3; simpl in *; isabsurd.
  cases in H3; [| inv H3].
  exploit H0; eauto.
  rewrite restrict_idem; eauto.
Qed.

(** ** Main Theorem about Coherence *)

(** [strip] removes the environment from a closure  *)

Definition strip (b:F.block) : I.block :=
  match b with
    | F.blockI E Z s n => I.blockI Z s n
  end.

(** The Bisimulation candidate. *)

Hint Extern 5 =>
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

Lemma srdSim_sim ZL AL Lv L L'
      (E EI:onv val) s a
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: inRel approx ZL ZL AL Lv L L')
  (AG:agree_on eq (getAnn a) E EI)
  (LV:live_sound Imperative ZL Lv s a)
  (ER:PIR2 (ifFstR Equal) AL (Lv \\ ZL))
  : sim Bisim (L, E, s) (L', EI,s).
Proof.
  revert_all. cofix; intros.
  inv SRD; inv LV; simpl in *.
  - invt live_exp_sound.
    + case_eq (op_eval E e0); intros.
      *  one_step.
         instantiate (1:=v). erewrite <- op_eval_live; eauto.
         eapply srdSim_sim; eauto using rd_agree_update.
         -- eapply inRel_map_A3; eauto using approx_restrict.
         -- eapply agree_on_update_same; eauto with cset.
         -- eauto using restrict_ifFstR.
      * no_step.
        erewrite <- op_eval_live in def; eauto. congruence.
    + case_eq (omap (op_eval E) Y); intros;
        exploit omap_op_eval_live_agree; try eassumption.
      * extern_step; assert (vl = l) by congruence; subst; eauto.
        -- eapply srdSim_sim; eauto using rd_agree_update, PIR2_length.
           ++ eapply inRel_map_A3; eauto. eapply approx_restrict; eauto.
           ++ eapply agree_on_update_same. reflexivity.
           eapply agree_on_incl; eauto.
           ++ eauto using restrict_ifFstR; eauto.
        -- symmetry in AG.
           exploit omap_op_eval_live_agree; eauto.
           eapply srdSim_sim; eauto using rd_agree_update, PIR2_length.
           ++ eapply inRel_map_A3; eauto. eapply approx_restrict; eauto.
           ++ eapply agree_on_update_same. reflexivity.
             eapply agree_on_incl; eauto. symmetry; eauto.
           ++ eauto using restrict_ifFstR; eauto.
      * no_step.
  - case_eq (op_eval E e); intros;
      exploit op_eval_live_agree; try eassumption.
    + case_eq (val2bool v); intros.
      one_step.
      eapply srdSim_sim; eauto using agree_on_incl.
      one_step.
      eapply srdSim_sim; eauto using agree_on_incl.
    + no_step.
  - no_step. simpl. eapply op_eval_live; eauto.
  - decide (length Z = length Y).
    case_eq (omap (op_eval E) Y); intros;
      exploit omap_op_eval_live_agree; try eassumption.
    + inRel_invs. inv H11. simpl in *.
      exploit H2; try reflexivity; dcr.
      one_step; simpl.
      exploit RA; eauto; simpl in *.
      eapply srdSim_sim; eauto.
      * eapply rd_agree_update_list; eauto with len.
      * eapply inRel_map_A3; eauto using approx_restrict.
      * rewrite H15. eapply update_with_list_agree; eauto with len.
        etransitivity; eapply agree_on_incl; eauto.
        symmetry; eauto. clear_all; cset_tac.
        PIR2_inv. inv_get. rewrite H21. rewrite <- H7.
        clear_all; cset_tac.
      * rewrite <- drop_zip.
        eapply restrict_ifFstR; eauto.
        eapply PIR2_drop; eauto.
    + exploit omap_op_eval_live_agree; try eassumption.
      no_step.
    + no_step.
  - one_step.
    eapply srdSim_sim;
      eauto using agree_on_incl, PIR2_app, rd_agree_extend.
    * econstructor; eauto.
      eapply mutual_approx; simpl;
        eauto 30 using mkBlock_I_i, mkBlock_F_i with len.
      intros; inv_get.
      edestruct @inRel_length; eauto; dcr.
      econstructor; eauto 20 with len.
      intros ? EQ. invc EQ. simpl.
      split. clear_all; cset_tac; intuition.
      eexists x. split.
      exploit H12; eauto; dcr; simpl in *; eauto with cset.
      split. exploit H0; eauto.
      exploit H11; eauto.
    * rewrite zip_app; eauto with len.
      eapply PIR2_app; eauto using PIR2_ifFstR_refl.
Qed.

(** ** Coherence implies invariance *)

Lemma srd_implies_invariance s a
: live_sound Imperative nil nil s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim; eauto.
  isabsurd. econstructor. econstructor.
Qed.
