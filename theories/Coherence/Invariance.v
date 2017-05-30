Require Import Util IL InRel4 RenamedApart LabelsDefined OptionR.
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

(** ** Context coherence for IL/F contexts: [approxF] *)

Inductive approx
  : list params -> list params -> list (؟ (set var)) -> list (set var) -> list F.block -> list I.block ->
    params -> params -> option (set var) -> set var -> F.block -> I.block -> Prop :=
  approxI ZL AL Lv o Z E s n lv L1 L2 a
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
                        getAnn a [=] (G ∪ of_list Z)
                        /\ srd (restr G ⊝ AL) s a)
     -> live_sound Imperative ZL Lv s a
     -> getAnn a = lv
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
  cases in H2; [| inv H2].
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

Smpl Add
     match goal with
     | [ H : ❬nil❭ = ❬?L❭ |- _ ] => destruct L; [|exfalso; inv H]
     | [ H : ❬_ :: _❭ = ❬?L❭ |- _ ] => is_var L; destruct L; [ inv H|]
     end : inv_trivial.

Lemma mutual_block_impl {A1 A2 A3 A4} {A1' A2' A3' A4'}
      {B} `{BlockType B} {C} `{BlockType C}
      {B'} `{BlockType B'} {C'} `{BlockType C'}
      (R:A1->A2->A3->A4->B->C->Prop)
      (R':A1'->A2'->A3'->A4'->B'->C'->Prop)
      n AL1 AL2 AL3 AL4 L1 L2
(MB:mutual_block R n AL1 AL2 AL3 AL4 L1 L2)
      AL1' AL2' AL3' AL4' L1' L2'
      (Len1:❬AL1❭ = ❬AL1'❭)
      (Len2:❬AL2❭ = ❬AL2'❭)
      (Len3:❬AL3❭ = ❬AL3'❭)
      (Len4:❬AL4❭ = ❬AL4'❭)
      (Len5:❬L1❭ = ❬L1'❭)
      (Len6:❬L2❭ = ❬L2'❭)
:  (forall n a1 a2 a3 a4 b c a1' a2' a3' a4' b' c',
         get AL1 n a1 ->
         get AL2 n a2 ->
         get AL3 n a3 ->
         get AL4 n a4 ->
         get L1 n b ->
         get L2 n c ->
         get AL1' n a1' ->
         get AL2' n a2' ->
         get AL3' n a3' ->
         get AL4' n a4' ->
         get L1' n b' ->
         get L2' n c' ->
         R a1 a2 a3 a4 b c -> R' a1' a2' a3' a4' b' c' /\ block_n b = block_n b' /\ block_n c = block_n c')
  ->  mutual_block R' n AL1' AL2' AL3' AL4' L1' L2'.
Proof.
  intros. general induction MB.
  - repeat match goal with
    | [ H : ❬nil❭ = ❬?L❭ |- _ ] => is_var L; destruct L; [ |exfalso; inv H]
           end. econstructor.
  - repeat match goal with
    | [ H : ❬_ :: _❭ = ❬?L❭ |- _ ] => is_var L; destruct L; [ inv H|]
           end.
    exploit H6; eauto using get; dcr.
    econstructor; eauto.
    eapply IHMB; eauto 200 using get. omega.
Qed.

Lemma length_app_inv X Y (A B: list X) (C:list Y)
  : ❬A ++ B❭ = ❬C❭
    -> exists C1 C2, C1 ++ C2 = C /\ ❬C1❭ = ❬A❭ /\ ❬C2❭ = ❬B❭.
Proof.
  intros.
  general induction A; simpl in *; eauto.
  - eexists nil, C; simpl; eauto.
  - destruct C; isabsurd. simpl in *.
    exploit (IHA Y B C); eauto; dcr; subst.
    eexists (y::x), x0. simpl; eauto.
Qed.




Lemma srdSim_sim ZL AL Lv L L'
      (E:onv val) s a
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: inRel approx ZL ZL AL Lv L L')
  (LV:live_sound Imperative ZL Lv s a)
  (ER:PIR2 (ifFstR Equal) AL (Lv \\ ZL))
  : simc bot3 Bisim (L, E, s) (L', E, s).
Proof.
  unfold simc.
  revert_all. eapply Tower3.tower_ind3.
  hnf; intros. hnf; intros. eauto.
  intros.
  inv SRD; inv LV; simpl in *.
  - invt live_exp_sound.
    + case_eq (op_eval E e0); intros.
      * cone_step.
        eapply H; eauto using rd_agree_update.
        -- eapply inRel_map_A3; eauto using approx_restrict.
        -- eauto using restrict_ifFstR.
      * cno_step.
    + case_eq (omap (op_eval E) Y); intros.
      * cextern_step; assert (vl = l) by congruence; subst; eauto.
        -- eapply H; eauto using rd_agree_update, PIR2_length.
           ++ eapply inRel_map_A3; eauto. eapply approx_restrict; eauto.
           ++ eauto using restrict_ifFstR; eauto.
        -- eapply H; eauto using rd_agree_update, PIR2_length.
           ++ eapply inRel_map_A3; eauto. eapply approx_restrict; eauto.
           ++ eauto using restrict_ifFstR; eauto.
      * cno_step.
  - case_eq (op_eval E e); intros.
    + case_eq (val2bool v); intros;
      cone_step; eauto using agree_on_incl.
    + cno_step.
  - cno_step.
  - decide (length Z = length Y).
    case_eq (omap (op_eval E) Y); intros.
    + inRel_invs. inv H11. simpl in *.
      exploit H2; try reflexivity; dcr.
      cone_step; simpl.
      exploit RA; eauto; simpl in *.
      eapply simc_trans_r_left; swap 1 2.
      * eapply H; eauto.
        -- eapply rd_agree_update_list; eauto with len.
        -- eapply inRel_map_A3; eauto using approx_restrict.
        -- rewrite <- drop_zip.
           eapply restrict_ifFstR; eauto.
           eapply PIR2_drop; eauto.
      * eapply sim_lock_simc.
        eapply liveSimI_sim; eauto.
        -- rewrite map_drop.
          eapply inRel_drop with (R:=approxI) in H7. eapply H7.
           revert A. clear_all. intros.
           general induction A; eauto using @inRel.
           econstructor; eauto.
           eapply (mutual_block_impl _ H); eauto with len.
           admit. admit. admit. intros. inv H12.
           simpl. inv_get. simpl. repeat split; eauto.
        -- rewrite H15. eapply update_with_list_agree; eauto with len.
           symmetry. eapply agree_on_incl; eauto.
           clear_all. cset_tac.
    + cno_step.
    + cno_step.
  - cone_step.
    eapply H;
      eauto using agree_on_incl, PIR2_app, rd_agree_extend.
    * econstructor; eauto.
      eapply mutual_approx; simpl;
        eauto 30 using mkBlock_I_i, mkBlock_F_i with len.
      intros; inv_get.
      edestruct @inRel_length; eauto; dcr.
      econstructor; eauto 20 with len.
      intros ? EQ. invc EQ. simpl.
      split. clear_all; cset_tac; intuition.
      eexists x0. split.
      exploit H13; eauto; dcr; simpl in *; eauto with cset.
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
