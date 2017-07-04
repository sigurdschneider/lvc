Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel MapDefined MapUpdate Position.
Require Import IL Annotation LabelsDefined.
Require Import Liveness.Liveness TrueLiveness SimI.
Require Import RenamedApart.
Require Import SetUtil SpillSound ReconstrLive DoSpill ReconstrLiveUtil.
Require Export SpillMovesAgree.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint extend_list X (L:list X) (Z:params) (RM : ⦃var⦄ * ⦃var⦄)
  : list X
  :=
    match L, Z with
    | l::L, z::Z => if [z ∈ fst RM ∩ snd RM]
             then l::l::extend_list L Z RM
             else l::extend_list L Z RM
    | _, _ => nil
    end.

(** * SpillSim *)

Lemma extend_list_length X (L:list X) (RM : ⦃var⦄ * ⦃var⦄) (Z : params)
      (NoDup:NoDupA eq Z) (Len:❬L❭ = ❬Z❭)
  : ❬extend_list L Z RM❭ = ❬Z❭ + cardinal (of_list Z ∩ (fst RM ∩ snd RM)).
Proof.
  general induction Len; simpl; eauto.
  inv NoDup.
  repeat cases; simpl; rewrite IHLen; eauto.
  - rewrite cap_special_in; eauto.
    rewrite add_cardinal_2; eauto. cset_tac.
  - rewrite cap_special_notin; eauto.
Qed.


Lemma slot_lift_params_extend_list_length X slot RM Z (L:list X)
      (Len:❬Z❭ = ❬L❭)
  : ❬slot_lift_params slot RM Z❭ = ❬extend_list L Z RM❭.
Proof.
  general induction Len; simpl; eauto.
  repeat cases; eauto; simpl; eauto.
Qed.

Lemma omap_slotlift (slot : var -> var) (V V'':onv val) Yv (xl Z:params) (Len:❬xl❭=❬Z❭) RM RMapp
      (Agr4 : agree_on eq (fst RMapp) V V'')
      (Agr5 : agree_on eq (snd RMapp) V (fun x : var => V'' (slot x)))
      (FVincl: of_list xl [<=] fst RMapp ∪ snd RMapp)
  : omap (op_eval V) (Var ⊝ xl) = Some Yv
    -> omap (op_eval V'') (slot_lift_args slot RM RMapp (Var ⊝ xl) Z)
      = Some (extend_list Yv Z RM).
Proof.
  intros.
  general induction Len; simpl in *; eauto;
    monad_inv H; simpl in *. unfold choose_y.
  cases; simpl.
  - assert (y ∈ fst RM /\ y ∈ snd RM) by (revert COND; clear_all; cset_tac).
    destruct H. repeat (cases; simpl).
    + rewrite <- Agr4; eauto. rewrite EQ. simpl.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    + rewrite <- Agr5; eauto.
      * rewrite EQ; eauto; simpl.
        erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
      * revert FVincl NOTCOND. clear_all. cset_tac.
  - assert ((y ∈ fst RM -> y ∈ snd RM -> False))
      by (revert NOTCOND; clear_all; cset_tac).
    unfold choose_y; repeat cases; simpl; eauto.
    + rewrite <- Agr4; [ rewrite EQ | ]; simpl; eauto.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    + rewrite <- Agr5; [ rewrite EQ | eauto]; simpl.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
      cset_tac.
    + rewrite <- Agr4; [ rewrite EQ | ]; simpl; eauto.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    + rewrite <- Agr5; [ rewrite EQ | eauto]; simpl.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
      cset_tac.
    + rewrite <- Agr5; [ rewrite EQ | eauto]; simpl.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    + rewrite <- Agr4; [ rewrite EQ | ]; simpl; eauto.
      erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
      cset_tac.
Qed.




Lemma update_with_list_lookup_in_list_first_slot (slot:var->var)
      A (E:onv A) n (R M:set var)
      Z (Y:list A) z
: length Z = length Y
  -> get Z n z
  -> z ∈ R
  -> disj (of_list Z) (map slot (of_list Z))
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> exists y, get Y n y
         /\ E [slot_lift_params slot (R, M) Z <--
                               Some ⊝ extend_list Y Z (R, M)] z = Some y.
Proof.
  intros Len Get In Disj First. length_equify.
  general induction Len; simpl in *; isabsurd.
  inv Get.
  - exists y; repeat split; eauto using get.
    cases; simpl.
    + lud; eauto using get.
    + cases; simpl.
      * lud; eauto using get.
  - edestruct (IHLen slot E n0) as [? [? ]]; eauto using get; dcr.
    + eapply disj_incl; eauto with cset.
    + intros. eapply (First (S n')); eauto using get. omega.
    + exists x0. eexists; repeat split; eauto using get.
      exploit (First 0); eauto using get; try omega.
      cases; simpl.
      * rewrite lookup_nequiv; eauto.
        rewrite lookup_nequiv; eauto.
        intro.
        eapply (Disj z). eapply get_in_of_list in H3.
        cset_tac. rewrite <- H2.
        eapply map_iff; eauto. eexists x; split; eauto with cset.
      * cases; simpl; lud.
        -- rewrite lookup_nequiv; eauto.
        -- exfalso.
           eapply (Disj (slot x)). eapply get_in_of_list in H3.
           rewrite <- H5. cset_tac.
           eapply map_iff; eauto. eexists x; split; eauto with cset.
        -- eauto.
Qed.


Lemma slot_lift_params_agree (slot : var -> var) X (E:onv X) E' R M Z VL (Len:❬Z❭=❬VL❭)
      (Agr2:agree_on eq (R \ of_list Z) E E')
      (Disj:disj (R ∪ of_list Z) (map slot (R ∪ of_list Z)))
      (Incl:of_list Z [<=] R ∪ M)
  : agree_on eq R (E [Z <-- Some ⊝ VL])
             (E' [slot_lift_params slot (R, M) Z <-- Some ⊝ extend_list VL Z (R, M)]).
Proof.
  hnf; intros.
  decide (x ∈ of_list Z).
  - assert (❬Z❭=❬Some ⊝ VL❭) by eauto with len.
    edestruct (of_list_get_first _ i) as [n]; eauto; dcr.
    edestruct update_with_list_lookup_in_list_first; eauto; dcr.
    + intros; rewrite <- H2. eauto.
    + rewrite H2. rewrite H6. inv_get. hnf in H2; subst.
      edestruct update_with_list_lookup_in_list_first_slot;
        try eapply Len; try eapply H3; try eapply H; dcr.
      Focus 3.
      erewrite H6. get_functional. eauto.
      eapply disj_incl; eauto with cset.
      intros. eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    rewrite lookup_set_update_not_in_Z; eauto.
    eapply Agr2. cset_tac.
    rewrite of_list_slot_lift_params; eauto.
    intro. eapply (Disj x);
    eauto with cset.
    revert n H0; clear; cset_tac.
Qed.

Lemma update_with_list_lookup_in_list_first_slot' (slot : var -> var) A (E:onv A) n (R M:set var)
      Z (Y:list A) z
: length Z = length Y
  -> get Z n z
  -> z ∈ M
  -> disj (of_list Z ∪ R ∪ M) (map slot (of_list Z ∪ R ∪ M))
  -> injective_on (of_list Z ∪ R ∪ M) slot
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> exists y, get Y n y /\ E [slot_lift_params slot (R, M) Z <--
                  Some ⊝ extend_list Y Z (R, M)] (slot z) = Some y.
Proof.
  intros Len Get In Disj Inj First. length_equify.
  general induction Len; simpl in *; isabsurd.
  inv Get.
  - exists y; repeat split; eauto using get.
    cases; simpl.
    + lud; eauto using get.
    + cases; simpl.
      * exfalso. cset_tac.
      * lud; eauto using get.
  - edestruct (IHLen slot E n0 R M) as [? [? ]]; eauto using get; dcr.
    + eapply disj_incl; eauto.
      clear; cset_tac.
      clear; cset_tac'; eauto 20.
    + eapply injective_on_incl; eauto.
      clear; cset_tac.
    + intros. eapply (First (S n')); eauto using get. omega.
    + exists x0. eexists; repeat split; eauto using get.
      exploit (First 0); eauto using get; try omega.
      cases; simpl.
      * rewrite lookup_nequiv; eauto.
        rewrite lookup_nequiv; eauto.
        -- intro. eapply Inj in H2; eauto with cset.
        -- intro. hnf in H2; subst.
           eapply (Disj (slot z)); eauto with cset.
      * cases; simpl; lud; eauto.
        -- exfalso. hnf in e; subst.
           eapply (Disj (slot z)); eauto with cset.
        -- exfalso. eapply H2. eapply Inj; eauto with cset.
Qed.



Lemma slot_lift_params_agree_slot (slot : var -> var) X (E:onv X) E' R M Z VL (Len:❬Z❭=❬VL❭)
      (Agr2:agree_on eq (M \ of_list Z) E (fun x => E' (slot x)))
      (Disj:disj (of_list Z ∪ R ∪ M) (map slot (of_list Z ∪ R ∪ M)))
      (Inj:injective_on (of_list Z ∪ R ∪ M) slot)
      (Incl:of_list Z [<=] R ∪ M)
        : agree_on eq M (E [Z <-- Some ⊝ VL])
             (fun x => E' [slot_lift_params slot (R, M) Z <--
                        Some ⊝ extend_list VL Z (R, M)] (slot x)).
Proof.
  hnf; intros.
  decide (x ∈ of_list Z).
  - assert (❬Z❭=❬Some ⊝ VL❭) by eauto with len.
    edestruct (of_list_get_first _ i) as [n]; eauto; dcr. hnf in H2; subst.
    edestruct update_with_list_lookup_in_list_first; eauto; dcr.
    rewrite H4. inv_get.
    edestruct update_with_list_lookup_in_list_first_slot'; try eapply Len; eauto; dcr.
    rewrite H6. get_functional. eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    rewrite lookup_set_update_not_in_Z; eauto.
    eapply Agr2. cset_tac.
    rewrite of_list_slot_lift_params; eauto.
    intro. eapply union_iff in H0; destruct H0.
    + eapply (Disj (slot x)). cset_tac. cset_tac.
    + eapply (Disj x). cset_tac.
      eapply map_iff in H0; eauto. dcr.
      eapply Inj in H3; eauto with cset.
      exfalso; cset_tac.
      cset_tac.
Qed.


Instance SR (slot : var -> var) (VD:set var)
  : PointwiseProofRelationI (((set var) * (set var)) * params) := {
   ParamRelIP RMZ Z Z' := Z' = slot_lift_params slot (fst RMZ) Z /\ Z = snd RMZ;
   ArgRelIP V V' RMZ VL VL' :=
     VL' = extend_list VL (snd RMZ) (fst RMZ) /\
     agree_on eq (fst (fst RMZ) \ of_list (snd RMZ)) V V' /\
     agree_on eq (snd (fst RMZ) \ of_list (snd RMZ)) V (fun x => V' (slot x)) /\
     ❬VL❭ = ❬snd RMZ❭ /\
     defined_on (fst (fst RMZ) \ of_list (snd RMZ)
                     ∪ map slot (snd (fst RMZ) \ of_list (snd RMZ))) V'
}.

Require Import AppExpFree Subset1.

Lemma sim_I (slot : var -> var) k Λ ZL LV VD r L L' V V' R M s lv sl ra
  : agree_on eq R V V'
    -> agree_on eq M V (fun x => V' (slot x))
    -> live_sound Imperative ZL LV s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl lv
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> defined_on (R ∪ map slot M) V'
    -> R ∪ M ⊆ fst (getAnn ra)
    -> labenv_sim Sim (sim r) (SR slot VD) (zip pair Λ ZL) L L'
    -> (fst (getAnn ra) ∪ snd (getAnn ra)) ⊆ VD
    -> renamedApart s ra
    -> app_expfree s
    -> ann_R Subset1 lv ra
    -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ZL Λ).
Proof.
  simpl. unfold reconstr_live_do_spill. unfold sim.
  move VD before k. move s before VD. revert_until s.
  sind s.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ?
         Agr1 Agr2 LS SLS SL Inj Disj Def Incl' LSim RAincl RA AEF Sub1.
  assert (Incl:R ∪ M [<=] VD). {
    rewrite <- RAincl, <- Incl'. eauto with cset.
  }
  exploit L_sub_SpM as LSpM; eauto.
  exploit Sp_sub_R as SpR; eauto.
  assert (VDincl:getSp sl ∪ getL sl [<=] VD). {
    rewrite LSpM, SpR.
    rewrite <- Incl.
    clear; cset_tac.
  }
  eapply sim_I_moves; eauto.
  eapply injective_on_incl; eauto with cset.
  eapply disj_incl; eauto with cset.
  eapply defined_on_incl; eauto.
  rewrite SpR at 1. rewrite LSpM.
  rewrite map_union; eauto. clear; cset_tac.
  rewrite !lookup_list_map. intros ? Agr3.
  time (destruct s; invt spill_sound; invt spill_live; invt live_sound;
        invt renamedApart; invt app_expfree; try invtc (@ann_R _ _ Subset1);
    (exploit regs_agree_after_spill_load as Agr4); try eassumption;
      exploit mem_agrees_after_spill_load as Agr5; try eassumption;
        simpl in *; rewrite !elements_empty; simpl).
  - destruct e; simpl in *.
    + eapply (sim_let_op il_statetype_I); eauto.
      * symmetry; eapply op_eval_agree; eauto using agree_on_incl.
      * intros. left.
        eapply (IH s); try eassumption.
        -- eauto.
        -- eapply agree_on_update_same; eauto.
           eapply agree_on_incl; eauto.
           clear; cset_tac.
        -- eapply mem_agrees_after_spill_load_update; eauto.
           rewrite SpR, Incl'; eauto.
           rewrite H18 in RAincl.
           revert RAincl; clear; cset_tac.
        -- eapply defined_on_update_some.
           eapply defined_on_incl.
           eapply defined_on_after_spill_load; eauto.
           instantiate (1:=K). clear; cset_tac.
        -- pe_rewrite.
           rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
        -- pe_rewrite. rewrite <- RAincl.
           rewrite H18. clear; cset_tac.
    + eapply (sim_let_call il_statetype_I).
      * symmetry; eapply omap_op_eval_agree; eauto using agree_on_incl.
      * intros. left. eapply (IH s); try eassumption.
        -- eauto.
        -- eapply agree_on_update_same; eauto.
           eapply agree_on_incl; eauto.
           clear; cset_tac.
        -- eapply mem_agrees_after_spill_load_update; eauto.
           rewrite SpR, Incl'; eauto.
           rewrite H18 in RAincl.
           revert RAincl; clear; cset_tac.
        -- eapply defined_on_update_some.
           eapply defined_on_incl.
           eapply defined_on_after_spill_load; eauto.
           instantiate (1:=K). clear; cset_tac.
        -- pe_rewrite. rewrite LSpM, SpR, <- Incl'.
           clear; cset_tac.
        -- pe_rewrite. rewrite <- RAincl.
           rewrite H18. clear; cset_tac.
  - simpl in *.
    eapply (sim_cond il_statetype_I).
    + symmetry; eapply op_eval_agree; eauto using agree_on_incl.
    + intros; left. eapply IH; try eassumption.
      * eauto.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H9. clear; cset_tac.
    + intros; left. eapply IH; try eassumption.
      * eauto.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H9. clear; cset_tac.
  - eapply labenv_sim_app; eauto using zip_get.
    intros; simpl in *. dcr; subst; repeat get_functional.
    split; eauto; intros.
    erewrite !get_nth; eauto using zip_get.
    edestruct op_eval_var; eauto; subst.
    erewrite omap_slotlift; only 6: eauto.
    eexists; split; eauto. split; eauto.
    eapply slot_lift_params_extend_list_length; eauto.
    split; eauto.
    split; eauto using agree_on_incl.
    split; eauto using agree_on_incl.
    split; eauto.
    eapply defined_on_incl.
    eapply defined_on_after_spill_load; eauto. instantiate (1:=K).
    rewrite H8, H11. reflexivity.
    unfold mark_elements. len_simpl. rewrite <- H17. eauto with len.
    simpl. eapply agree_on_incl; eauto.
    simpl. eapply agree_on_incl; eauto. simpl.
    rewrite <- H12. eapply of_list_freeVars_vars.
  - pno_step. simpl.
    erewrite op_eval_agree; [reflexivity| |reflexivity]. symmetry.
    eapply agree_on_incl; eauto using regs_agree_after_spill_load; eauto.
  - eapply sim_fun_ptw; try eapply LSim; try eassumption.
    + intros. left.
      eapply (IH s); eauto.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H25. clear; cset_tac.
    + intros. hnf; intros; simpl in *; dcr. subst.
      inv_get.
      exploit H12 as SPS'; try eassumption.
      exploit H20 as LS'; try eassumption.
      exploit H15 as SL'; try eassumption. destruct x as (R_f,M_f).
      exploit H14 as In'; try eassumption; simpl in *; destruct In' as [In1 In2].
      exploit H2 as RA'; try eassumption.
      exploit (get_PIR2 H7) as EQ; only 1-2: eauto.
      exploit H21 as In3; try eassumption.
      destruct In3 as [In3 _].
      unfold merge in EQ. simpl in *.
      eapply IH; eauto.
      * eapply slot_lift_params_agree; only 1-2: eauto.
        -- eapply disj_incl; eauto.
           ++ rewrite In3, <- EQ, In1, In2.
             clear; eauto with cset.
           ++ rewrite In3, <- EQ, In1, In2.
             clear; eauto with cset.
        -- rewrite EQ; eauto.
      * eapply slot_lift_params_agree_slot; only 1-2: eauto.
        -- eapply disj_incl; eauto.
           rewrite In3, <- EQ, In1, In2. clear; cset_tac.
           eapply map_incl; eauto.
           rewrite In3, <- EQ, In1, In2. clear; cset_tac.
        -- eapply injective_on_incl; eauto.
           rewrite In3, <- EQ, In1, In2. clear; cset_tac.
        -- rewrite EQ; eauto.
      * eapply defined_on_update_list'.
        -- len_simpl.
           edestruct H8; eauto; dcr. simpl in *.
           eapply slot_lift_params_extend_list_length; eauto.
        -- rewrite of_list_slot_lift_params; eauto.
           eapply defined_on_incl; eauto.
           rewrite <- EQ in In3; revert In3; clear.
           ++ cset_tac'.
             ** eexists x. cset_tac.
             ** eexists x; eauto.
           ++ rewrite EQ; eauto.
        -- eapply get_defined; intros; inv_get; eauto.
      * edestruct H8; eauto; dcr.
        simpl in *. rewrite EQ.
        exploit H33; eauto. eapply ann_R_get in H4. eauto.
      * edestruct H8; eauto; dcr.
        rewrite H3. simpl. rewrite union_comm. rewrite <- union_assoc.
        eapply union_incl_split.
        -- rewrite <- RAincl. eapply incl_union_right.
           rewrite <- H25. eapply incl_union_left.
           eapply incl_list_union; eauto using zip_get.
           unfold defVars. simpl. clear; eauto with cset.
        -- rewrite <- RAincl. eauto with cset.
      * exploit H24; eauto.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.
