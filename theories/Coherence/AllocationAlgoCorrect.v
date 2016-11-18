Require Import CMap MapNotations CSet Le Arith.Compare_dec.

Require Import Plus Util Status Take Subset1.
Require Import Val Var Env IL Annotation Liveness Fresh MoreList SetOperations.
Require Import Coherence Allocation RenamedApart AllocationAlgo.

Set Implicit Arguments.

Lemma least_fresh_P_spec c G x
  : (~ x <= c -> x ∉ G)
    -> least_fresh_P c G x ∉ G.
Proof.
  unfold least_fresh_P; cases; eauto using least_fresh_spec.
Qed.

Lemma least_fresh_P_gt c G x
  : ~ x <= c
    -> least_fresh_P c G x = x.
Proof.
  intros; unfold least_fresh_P; cases; try omega; eauto.
Qed.

Lemma least_fresh_P_le c G x
  : x <= c
    -> least_fresh_P c G x = least_fresh G.
Proof.
  intros; unfold least_fresh_P; cases; try omega; eauto.
Qed.

Definition sep (c:var) (G:set var) (ϱ:Map [var,var]) :=
  (forall x, x ∈ G -> ~ x <= c -> findt ϱ 0 x === x)
  /\ (forall x, x ∈ G -> x <= c -> findt ϱ 0 x <= c).

Instance sep_morphism_impl
  : Proper (eq ==> Equal ==> eq ==> impl) sep.
Proof.
  unfold Proper, respectful, impl; intros; subst.
  destruct H2; split; intros.
  eapply H; eauto. rewrite H0; eauto.
  eapply H1; eauto. rewrite H0; eauto.
Qed.

Instance sep_morphism_iff
  : Proper (eq ==> Equal ==> eq ==> iff) sep.
Proof.
  unfold Proper, respectful; intros; subst.
  split; rewrite H0; eauto.
Qed.

Instance sep_morphism_Subset_impl
  : Proper (eq ==> Subset ==> eq ==> flip impl) sep.
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H2; split; intros; eauto.
Qed.

Instance sep_morphism_Subset_impl'
  : Proper (eq ==> flip Subset ==> eq ==> impl) sep.
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H2; split; intros; eauto.
Qed.

Lemma sep_incl c lv lv' ϱ
  : sep c lv ϱ
    -> lv' ⊆ lv
    -> sep c lv' ϱ.
Proof.
  intros A B. rewrite B; eauto.
Qed.

Lemma sep_agree c D ϱ ϱ'
  : agree_on eq D (findt ϱ 0) (findt ϱ' 0)
    -> sep c D ϱ
    -> sep c D ϱ'.
Proof.
  intros AGR [GT LE]; split; intros.
  - rewrite <- AGR; eauto.
  - rewrite <- AGR; eauto.
Qed.

Hint Resolve sep_incl sep_agree.

Lemma sep_lookup_set c (G:set var) (ϱ:Map [var,var]) x
      (SEP:sep c G ϱ) (NotIn:x ∉ G)
  : ~ x <= c -> x ∉ lookup_set (findt ϱ 0) G.
Proof.
  destruct SEP as [GT LE].
  intros Gt. unfold lookup_set; intro In.
  eapply map_iff in In; eauto.
  destruct In as [y [In EQ]]. hnf in EQ; subst.
  decide (y <= c).
  - exfalso. eauto.
  - exploit GT; eauto.
Qed.

Lemma sep_update c lv x ϱ
      (SEP : sep c (lv \ singleton x) ϱ)
      (CARD : cardinal (map (findt ϱ 0) (lv \ singleton x)) <= c)
  : sep c lv (ϱ [-x <- least_fresh_P c (map (findt ϱ 0) (lv \ singleton x)) x -]).
Proof.
  destruct SEP as [GT LE].
  split; intros.
  - unfold findt.
    decide (x === x0).
    + rewrite MapFacts.add_eq_o; eauto.
      rewrite least_fresh_P_gt. eauto.
      hnf in e; congruence.
    + rewrite MapFacts.add_neq_o; eauto.
      exploit GT; eauto. cset_tac.
  - unfold findt.
    decide (x === x0).
    + rewrite MapFacts.add_eq_o; eauto.
      rewrite least_fresh_P_le.
      * rewrite least_fresh_small.
        eapply CARD.
      * hnf in e; congruence.
    + rewrite MapFacts.add_neq_o; eauto.
      cases; try omega.
      rewrite <- LE; eauto.
      unfold findt. rewrite <- Heq; eauto.
      cset_tac.
Qed.

Lemma sep_nd c G ϱ G'
      (SEP:sep c G ϱ) (Disj: disj G' G)
  : forall x : nat, x > c -> x ∈ G' -> x ∈ map (findt ϱ 0) G -> False.
Proof.
  intros. cset_tac. destruct SEP as [GT LE].
  decide (x0 <= c).
  - exploit LE; eauto; try omega.
  - exploit GT; eauto. cset_tac.
    eapply Disj; eauto; congruence.
Qed.

(** ** the algorithm produces a locally injective renaming *)

Lemma regAssign_correct c (ϱ:Map [var,var]) ZL Lv s alv ϱ' al
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (SEP:sep c (getAnn alv) ϱ)
      (allocOK:regAssign c s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
: locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  general induction LS; simpl in *; try monadS_inv allocOK; invt renamedApart;
  pe_rewrite; eauto 10 using locally_inj, injective_on_incl.
  - exploit IHLS; try eapply allocOK; pe_rewrite; eauto with cset.
    + eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_incl.
      eapply injective_on_fresh; eauto using injective_on_incl.
      eapply least_fresh_P_spec; eauto.
      eapply sep_lookup_set; eauto.
      eauto with cset.
    + eapply sep_update; eauto.
      admit.
    + pe_rewrite. eauto with cset.
    + exploit regAssign_renamedApart_agree;
      try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *; simpl in *.
      econstructor; eauto using injective_on_incl.
      * eapply injective_on_agree; try eapply inj.
        eapply agree_on_incl.
        eapply agree_on_update_inv.
        rewrite map_update_update_agree; eauto.
        pe_rewrite.
        revert H5 incl; clear_all; cset_tac; intuition.
  - exploit regAssign_renamedApart_agree;
    try eapply EQ; simpl; eauto using live_sound.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    pe_rewrite.
    simpl in *.
    exploit IHLS1; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
    eapply injective_on_incl; eauto.
    eapply injective_on_agree; eauto using agree_on_incl.
    eapply sep_agree; eauto using agree_on_incl.
    rewrite H12; simpl. rewrite <- incl; eauto.
    econstructor; eauto.
    assert (agree_on eq D (findt ϱ 0) (findt ϱ' 0)). etransitivity; eauto.
    eapply injective_on_agree; eauto. eauto using agree_on_incl.
    eapply locally_inj_live_agree. eauto. eauto. eauto.
    rewrite H11; simpl; eauto.
    exploit regAssign_renamedApart_agree'; try eapply EQ0; simpl; eauto using live_sound.
    pe_rewrite.
    eapply agree_on_incl. eapply H13. instantiate (1:=D ∪ Ds).
    pose proof (renamedApart_disj H9).
    pe_rewrite.
    revert H6 H14; clear_all; cset_tac; intuition; eauto.
    rewrite H11; simpl. rewrite <- incl; eauto.

  - exploit regAssign_renamedApart_agreeF;
    eauto using regAssign_renamedApart_agree'. reflexivity.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    instantiate (1:=D) in H4.
    assert (AGR:agree_on _eq lv (findt ϱ 0) (findt x 0)). {
      eapply agree_on_incl; eauto.
      rewrite disj_minus_eq; eauto. simpl in *.
      symmetry. rewrite <- list_union_disjunct.
      intros; inv_get. edestruct H8; eauto; dcr.
      unfold defVars. symmetry. eapply disj_app; split; eauto.
      symmetry; eauto.
      exploit H7; eauto. eapply renamedApart_disj in H17.
      eapply disj_1_incl; eauto. rewrite H16. eauto with cset.
    }
    exploit IHLS; try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
    + pe_rewrite. etransitivity; eauto.
    + assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                              disj D (defVars Zs DD')).
      {
        eapply renamedApart_disj in sd. eauto using defVars_disj_D.
      }

      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          edestruct (regAssignF_get c (fst (getAnn x0) ∪ snd (getAnn x0) ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H21; eauto.
          exploit H1; try eapply H19; eauto.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H17; clear_all; cset_tac; intuition.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply renamedApart_disj in sd.
            simpl in *.
            rewrite <- H17. symmetry. rewrite disj_app. split; symmetry.
            eapply disj_1_incl. eapply disj_2_incl. eapply sd.
            rewrite <- H13. eapply incl_union_left.
            hnf; intros ? A. eapply list_union_get in A. destruct A. dcr.
            inv_get.
            eapply incl_list_union; eauto using zip_get.
            reflexivity. cset_tac.
            edestruct H2; eauto; dcr. rewrite <- incl. eauto.
            eapply disj_1_incl.
            eapply defVars_take_disj; eauto. unfold defVars.
            eauto with cset.
            setoid_rewrite <- H17 at 1.
            eapply injective_on_fresh_list; eauto with len.
            eapply injective_on_incl; eauto.
            eapply H2; eauto.
            eapply disj_intersection.
            eapply disj_2_incl. eapply fresh_list_P_spec.
            eapply sep_nd; eauto.
            edestruct H2; eauto. clear; hnf; intros; cset_tac.
            edestruct H8; eauto.
            admit.
            reflexivity.
            edestruct H8; eauto.
            eapply fresh_list_nodup; eauto.
            eapply sep_nd; eauto.
            edestruct H2; eauto. clear; hnf; intros; cset_tac.
            edestruct H8; eauto.
            admit.
          - edestruct H2; eauto.
            rewrite map_update_list_update_agree' in H21; eauto with len.
            admit.
          - edestruct H8; eauto; dcr. rewrite H17.
            exploit H2; eauto; dcr. rewrite incl in H26; simpl in *.
            rewrite <- H26. clear_all; cset_tac; intuition.
          - eapply locally_inj_live_agree; try eapply H17; eauto.
            eapply regAssign_renamedApart_agreeF in H18;
              eauto using get_drop, drop_length_stable; try reflexivity.
            + eapply regAssign_renamedApart_agree' in EQ0; simpl; eauto using live_sound.
              etransitivity; eapply agree_on_incl; try eassumption.
              * rewrite disj_minus_eq. reflexivity.
                {
                  edestruct H8; eauto; dcr. rewrite H20.
                  rewrite union_comm. rewrite <- union_assoc.
                  symmetry; rewrite disj_app; split; symmetry.
                  - eapply disj_1_incl. eapply defVars_drop_disj; eauto.
                    unfold defVars. eauto with cset.
                  - eapply renamedApart_disj in sd; simpl in sd.
                    eapply disj_2_incl; eauto.
                    rewrite <- H13. eapply incl_union_left.
                    rewrite <- drop_zip; eauto.
                    eapply list_union_drop_incl; eauto.
                }
              * pe_rewrite.
                rewrite disj_minus_eq. reflexivity.
                {
                  edestruct H8; eauto; dcr. rewrite H20.
                  rewrite union_comm. rewrite <- union_assoc.
                  symmetry; rewrite disj_app; split; symmetry.
                  rewrite union_comm; eauto.
                  eapply renamedApart_disj in H10. pe_rewrite. eapply H10.
                }
            + intros.
              eapply regAssign_renamedApart_agree'; eauto using get_drop, drop_get.
            + intros. edestruct H8; eauto; dcr. rewrite H20.
              exploit H2; eauto; dcr. rewrite incl in H27. simpl in *.
              revert H27; clear_all; cset_tac; intuition.
              decide (a ∈ of_list (fst Zs)); intuition.
          - eauto with len.
        }
      * eapply injective_on_agree; try eapply inj; eauto.
        etransitivity; eapply agree_on_incl; eauto. pe_rewrite. eauto.
Qed.


Require Import Restrict RenamedApart_Liveness LabelsDefined.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_correct]
    above, which we did prove by induction. *)

Lemma regAssign_correct' s ang ϱ ϱ' (alv:ann (set var)) ZL Lv
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> noUnreachableCode isCalled s
  -> injective_on (getAnn alv) (findt ϱ 0)
  -> regAssign s alv ϱ = Success ϱ'
  -> locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply regAssign_correct; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac.
Qed.u
