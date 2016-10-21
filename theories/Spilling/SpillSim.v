Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel MapDefined.
Require Import IL Annotation LabelsDefined Liveness TrueLiveness SimI.
Require Import RenamedApart.
Require Import SetUtil Spilling ReconstrLive DoSpill ReconstrLiveUtil.

Set Implicit Arguments.
Unset Printing Records.

Section Correctness.

  Variable slot : var -> var.


Instance SR : PointwiseProofRelationI (((set var) * (set var)) * params) := {
   ParamRelIP RMZ Z Z' := Z' = slot_lift_params slot (fst RMZ) Z /\ Z = snd RMZ;
   ArgRelIP V V' RMZ VL VL' :=
     VL' = extend_args VL' (mark_elements (snd RMZ) (fst (fst RMZ) ∩ snd (fst RMZ)))
}.

Smpl Add match goal with
         | [ |- context [ ❬@lookup_list ?X ?Y ?f ?L❭ ] ] =>
           rewrite (@lookup_list_length X Y f L)
         end : len.

Lemma lookup_list_map X Y (f:X->Y) L
  : lookup_list f L = f ⊝ L.
Proof.
  induction L; simpl; f_equal; eauto.
Qed.


Lemma injective_unique X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{ Proper _ (_eq ==> _eq) f} xl
  : injective_on (of_list xl) f
    -> unique xl -> unique (lookup_list f xl).
Proof.
  intros Inj Uniq.
  general induction xl; simpl in *; dcr; eauto.
  - split; eauto using injective_on_incl with cset.
    rewrite InA_in. rewrite InA_in in H2.
    intro.
    rewrite of_list_lookup_list in H4; eauto.
    eapply lookup_set_spec in H4; eauto; dcr.
    exploit Inj; eauto; cset_tac.
Qed.

Lemma injective_unique_map X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{ Proper _ (_eq ==> _eq) f} xl
  : injective_on (of_list xl) f
    -> unique xl -> unique (f ⊝ xl).
Proof.
  rewrite <- lookup_list_map; eauto using injective_unique.
Qed.


Lemma sim_write_moves r L V s L' V' s' xl yl (Len:❬xl❭ = ❬yl❭)
  : (forall D (V'':onv val), agree_on eq D (V'[xl <-- lookup_list V' yl]) V''
                        -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s) (L', V'', s'))
    -> defined_on (of_list yl) V'
    -> disj (of_list xl) (of_list yl)
    -> unique xl
    -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s)
            (L', V', write_moves xl yl s').
Proof.
  intros SIM Def Disj Uniq.
  length_equify. general induction Len.
  - simpl in *. eapply (SIM ∅); eauto.
  - simpl in *; dcr.
    edestruct Def; [cset_tac|].
    pone_step_right; simpl. rewrite <- H1.
    eapply IHLen; intros; eauto using injective_on_incl with cset.
    eapply (SIM D).
    rewrite <- update_unique_commute_eq; simpl; eauto with len.
    erewrite lookup_list_agree; eauto.
    symmetry. eapply agree_on_update_dead; eauto.
    eapply disj_not_in.
    eapply disj_1_incl. eapply disj_2_incl; eauto with cset.
    eauto with cset.
    rewrite H1; eapply defined_on_update_some;
      eauto using defined_on_incl with cset.
Qed.

Lemma sim_I k Λ ZL LV VD r L L' V V' G R M s lv sl ib
  : let nlv := reconstr_live_do_spill slot Λ ZL G s sl in
    agree_on eq (getAnn nlv ∩ R) V V'
    -> agree_on eq (getAnn nlv ∩ M) V (fun x => V' (slot x))
  -> live_sound Imperative ZL LV s lv
  -> spill_sound k ZL Λ (R,M) s sl
  -> spill_live VD sl lv
  -> injective_on VD slot
  -> defined_on (R ∪ map slot M) V'
  -> getSp sl ∪ getL sl ⊆ VD
  -> labenv_sim Sim (sim r) SR (zip pair Λ ZL) L L'
  -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ib).
Proof.
  simpl. unfold reconstr_live_do_spill. unfold sim. revert_except s.
  time (sind s).
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Agr1 Agr2 LS SLS SL Inj Def Incl LSim.
  rewrite do_spill_extract_writes.
  exploit L_sub_SpM; eauto.
  exploit Sp_sub_R; eauto.
  eapply sim_write_moves; try rewrite of_list_elements; eauto with len.
  intros ? ? Agr3.
  eapply sim_write_moves; try rewrite of_list_elements; eauto with len.
  intros ? ? Agr4.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto using defined_on_incl with cset.
  - admit.
  - eapply injective_unique_map; eauto.
    rewrite of_list_elements. eauto using injective_on_incl with cset.
    admit.
Qed.



      pose proof (@update_unique_commute+ var _ (option val) _ (slot ⊝ xl) (lookup_list V xl) V' D
                 (slot a) (V a)).
      unfold _eq in H4. simpl in *.
      instantiate (1:=D). hnf; intros.
      exploit H4; eauto with len. len_simpl. rewrite lookup_list_length. eauto.
      exploit H6; eauto.
      Lemma option_eq_eq A
        : forall x y, @option_eq A eq x y <-> x = y.
      Proof.
        split; intros; subst.
        inv H; eauto. reflexivity.
      Qed.
      intros.
      etrans

      eapply H4.

  Qed.
  destruct s; simpl; intros; invt live_sound; invt spill_sound;
        invt spill_live; simpl in * |- *).
  - destruct e.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_op il_statetype_I);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H10. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_I); intros; eauto 20 using op_eval_live, agree_on_incl.
  - eapply labenv_sim_app; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z0 H7);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros. eapply argsLive_liveSound; eauto.
        erewrite get_nth; eauto using zip_get; simpl.
        rewrite H12. eexists; split; eauto.
        repeat split; eauto using filter_filter_by_length.
        eapply agree_on_incl; eauto.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_fun_ptw; eauto.
    + intros. left. rewrite <- zip_app; eauto with len. eapply IH; eauto using agree_on_incl.
    + intros. hnf; intros; simpl in *; dcr; subst.
      inv_get.
      rewrite <- zip_app; eauto with len.
      eapply IH; eauto.
      eapply agree_on_update_filter'; eauto.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.
