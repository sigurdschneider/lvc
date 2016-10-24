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
     VL' = extend_args VL (mark_elements (snd RMZ) (fst (fst RMZ) ∩ snd (fst RMZ)))
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


Lemma injective_nodup X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{ Proper _ (_eq ==> _eq) f} xl
  : injective_on (of_list xl) f
    -> NoDupA _eq xl -> NoDupA _eq (lookup_list f xl).
Proof.
  intros Inj Uniq.
  general induction xl; simpl in *; dcr; eauto.
  - econstructor; eauto using injective_on_incl with cset.
    rewrite InA_in. invt NoDupA. rewrite InA_in in H4.
    intro.
    rewrite of_list_lookup_list in H2; eauto.
    eapply lookup_set_spec in H2; eauto; dcr.
    exploit Inj; eauto; cset_tac.
Qed.

Lemma injective_nodup_map X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{ Proper _ (_eq ==> _eq) f} xl
  : injective_on (of_list xl) f
    -> NoDupA _eq xl -> NoDupA _eq (f ⊝ xl).
Proof.
  rewrite <- lookup_list_map; eauto using injective_nodup.
Qed.

Lemma sim_write_moves D r L V s L' V' s' xl yl (Len:❬xl❭ = ❬yl❭)
  : (forall (V'':onv val), agree_on eq D (V'[xl <-- lookup_list V' yl]) V''
                        -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s) (L', V'', s'))
    -> defined_on (of_list yl) V'
    -> disj (of_list xl) (of_list yl)
    -> NoDupA _eq xl
    -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s)
            (L', V', write_moves xl yl s').
Proof.
  intros SIM Def Disj Uniq.
  length_equify. general induction Len.
  - simpl in *. eapply SIM; eauto.
  - simpl in *; dcr; invt NoDupA.
    edestruct Def; [cset_tac|].
    pone_step_right; simpl. rewrite <- H.
    eapply IHLen; intros; eauto using injective_on_incl with cset.
    eapply SIM.
    rewrite <- update_nodup_commute_eq; simpl; eauto with len.
    erewrite lookup_list_agree; eauto.
    symmetry. eapply agree_on_update_dead; eauto.
    eapply disj_not_in.
    eapply disj_1_incl. eapply disj_2_incl; eauto with cset.
    eauto with cset.
    rewrite H; eapply defined_on_update_some;
      eauto using defined_on_incl with cset.
Qed.

Lemma of_list_map X `{OrderedType X} Y `{OrderedType Y}
      (f:X->Y) `{Proper _ (_eq ==> _eq) f} L
  : of_list (f ⊝ L) [=] map f (of_list L).
Proof.
  general induction L; simpl; eauto.
  - rewrite SetOperations.map_add; eauto.
    rewrite IHL; eauto; reflexivity.
Qed.

Lemma map_union X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) `{Proper _ (_eq ==> _eq) f} s t
  : map f (s ∪ t) [=] map f s ∪ map f t.
Proof.
  cset_tac; rewrite !map_iff in *; eauto.
  - rewrite map_iff in H2; eauto.
    cset_tac.
  - rewrite map_iff in H3; eauto.
    cset_tac.
  - rewrite map_iff in H3; eauto.
    cset_tac.
Qed.

Lemma union_exclusive X `{OrderedType X} s t
  : s ∪ t [=] s ∪ (t \ s).
Proof.
  cset_tac.
Qed.

Lemma get_InA_OT X `{OrderedType X} (L:list X) n x
  :  get L n x
     -> InA _eq x L.
Proof.
  intros Get. general induction Get; eauto using InA.
Qed.

Lemma get_InA X (L:list X) n x
  :  get L n x
     -> InA eq x L.
Proof.
  intros Get. general induction Get; eauto using InA.
Qed.

Lemma get_elements_in X `{OrderedType X} s n x
  :  get (elements s) n x
     -> x ∈ s.
Proof.
  intros Get. eapply get_InA_OT in Get.
  rewrite (@InA_in X H) in Get.
  rewrite of_list_elements in Get. eauto.
Qed.

Lemma defined_on_agree X `{OrderedType X} Y R D (f g:X->option Y)
  : defined_on D f
    -> agree_on (option_eq R) D f g
    -> defined_on D g.
Proof.
  intros; hnf; intros.
  edestruct H0; eauto.
  exploit H1; eauto.
  rewrite H3 in H4. inv H4. eauto.
Qed.

Lemma defined_on_agree_eq X `{OrderedType X} Y D (f g:X->option Y)
  : defined_on D f
    -> agree_on eq D f g
    -> defined_on D g.
Proof.
  intros; hnf; intros.
  edestruct H0; eauto.
  exploit H1; eauto.
  rewrite H3 in H4. inv H4. eauto.
Qed.

Lemma defined_on_union X `{OrderedType X} Y (f:X -> option Y) s t
  : defined_on s f
    -> defined_on t f
    -> defined_on (s ∪ t) f.
Proof.
  intros; hnf; intros. cset_tac.
Qed.

Lemma sim_I_moves k Λ ZL r L L' V V' R M s sl ib
  : spill_sound k ZL Λ (R,M) s sl
    -> injective_on (getSp sl ∪ getL sl) slot
    -> disj (getSp sl ∪ getL sl) (map slot (getSp sl ∪ getL sl))
    -> defined_on (getSp sl ∪ (map slot (getL sl) \ map slot (getSp sl))) V'
    -> (forall V'', agree_on eq (R ∪ map slot M ∪ map slot (getSp sl) ∪ getL sl)
                       (V' [slot ⊝ elements (getSp sl) <-- lookup_list V' (elements (getSp sl))]
                           [elements (getL sl) <-- lookup_list (V'[slot ⊝ elements (getSp sl) <-- lookup_list V' (elements (getSp sl))]) (slot ⊝ elements (getL sl))]) V''
              -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s)
                      (L', V'', do_spill slot s (setTopAnn sl ({}, {}, snd (getAnn sl))) ib))
    -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ib).
Proof.
  simpl. unfold reconstr_live_do_spill. unfold sim. revert_except s.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? SPS Inj Disj Def SIM.
  rewrite do_spill_extract_writes.
  exploit L_sub_SpM; eauto.
  exploit Sp_sub_R; eauto.
  eapply (@sim_write_moves (R ∪ map slot M ∪ map slot (getSp sl) ∪ map slot (getL sl))); try rewrite ?of_list_map, of_list_elements;
    eauto with len.
  intros ? Agr3.
  eapply (@sim_write_moves (R ∪ map slot M ∪ map slot (getSp sl) ∪ getL sl)); try rewrite ?of_list_map, of_list_elements;
    eauto with len.
  intros ? Agr4.
  - rewrite update_with_list_agree in Agr4; eauto with len;
      [| symmetry; eapply agree_on_incl; eauto; clear; rewrite of_list_elements; cset_tac].
    erewrite <- (lookup_list_agree) in Agr4.
    eapply SIM; eauto.
    rewrite of_list_map, of_list_elements; eauto.
    eapply agree_on_incl; eauto with cset.
  - eapply defined_on_agree_eq; eauto using agree_on_incl with cset.
    rewrite (incl_union_minus _ _ (map slot (getSp sl))).
    eapply defined_on_union.
    + hnf; intros.
      rewrite <- (of_list_elements (getSp sl)) in H1.
      rewrite <- of_list_map in H1; eauto.
      edestruct update_with_list_lookup_in_list; try eapply H1; dcr.
      Focus 2. rewrite H5. inv_get. eapply get_elements_in in H3.
      rewrite lookup_list_map in H4; inv_get.
      eapply get_elements_in in H4.
      eauto with cset.
      eauto with len.
    + hnf; intros.
      rewrite lookup_set_update_not_in_Z; eauto.
      eapply Def; eauto with cset.
      rewrite of_list_map, of_list_elements; eauto.
      cset_tac.
  - eapply disj_1_incl. eapply disj_2_incl. eauto.
    rewrite map_union; eauto with cset.
    eauto with cset.
  - eapply elements_3w.
  - eauto using defined_on_incl with cset.
  - symmetry.
    eapply disj_1_incl. eapply disj_2_incl; eauto with cset.
    rewrite map_union; eauto with cset.
    eauto with cset.
  - eapply injective_nodup_map; eauto.
    rewrite of_list_elements. eauto using injective_on_incl with cset.
    eapply elements_3w.
Qed.

Lemma sim_I k Λ ZL LV VD r L L' V V' R M s lv sl ib
  : agree_on eq R V V'
    -> agree_on eq M V (fun x => V' (slot x))
  -> live_sound Imperative ZL LV s lv
  -> spill_sound k ZL Λ (R,M) s sl
  -> spill_live VD sl lv
  -> injective_on VD slot
  -> disj VD (map slot VD)
  -> defined_on (R ∪ map slot M) V'
  -> R ∪ M ⊆ VD
  -> labenv_sim Sim (sim r) SR (zip pair Λ ZL) L L'
  -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ib).
Proof.
  simpl. unfold reconstr_live_do_spill. unfold sim. revert_except s.
  time (sind s).
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Agr1 Agr2 LS SLS SL Inj Disj Def Incl LSim.
  exploit L_sub_SpM; eauto.
  exploit Sp_sub_R; eauto.
  assert (VDincl:getSp sl ∪ getL sl [<=] VD). {
    rewrite H, H0. rewrite <- Incl. eauto with cset.
  }
  eapply sim_I_moves; eauto.
  eapply injective_on_incl; eauto with cset.
  eapply disj_1_incl. eapply disj_2_incl. eauto. rewrite VDincl; eauto. eauto.
  eapply defined_on_incl; eauto.
   rewrite H0 at 1. rewrite H.
  rewrite map_union; eauto. clear; cset_tac.
  intros.
  time (destruct s; invt spill_sound; invt spill_live; invt live_sound).
  - simpl in *. simpl. rewrite elements_empty; simpl.
    destruct e.
    + eapply (sim_let_op il_statetype_I); eauto.
      * eapply op_eval_live; eauto. eapply Op.live_freeVars.
        simpl in *. admit.
      * intros. left. eapply IH; eauto.
        eapply agree_on_update_same; eauto.
        admit. admit.
        eapply defined_on_update_some.
        admit.
        exploit L_sub_SpM; try eapply H9; eauto.
        exploit Sp_sub_R; try eapply H9; eauto.
        admit.
    + eapply (sim_let_call il_statetype_I); eauto.
      * admit.
      * intros. left. eapply IH; eauto.
        eapply agree_on_update_same; eauto.
        admit. admit.
        eapply defined_on_update_some.
        admit.
        exploit L_sub_SpM; try eapply H9; eauto.
        exploit Sp_sub_R; try eapply H9; eauto.
        admit.
  - simpl in *. rewrite elements_empty; simpl.
    eapply (sim_cond il_statetype_I); eauto.
    + eapply op_eval_live; eauto.
      admit.
    + intros; left. eapply IH; eauto.
      * etransitivity; [| eapply agree_on_incl; [eapply H1| clear; cset_tac]].
        rewrite union_comm, union_exclusive.
        eapply agree_on_union.
        -- admit.
        -- etransitivity; [eapply agree_on_incl; [eapply Agr1| clear; cset_tac]|].
           admit.
      * rewrite union_exclusive.
        eapply agree_on_union.
        -- etransitivity; [ eapply agree_on_incl; [ eapply Agr1 | eauto with cset]|].
           admit.
        -- etransitivity; [ eapply agree_on_incl; [ eapply Agr2 | eauto with cset]|].
           admit.
      * admit.
      * rewrite H10, H0. rewrite <- Incl. clear; cset_tac.
    + intros; left. eapply IH; eauto.
      admit. admit. admit. admit.
  - simpl in *. rewrite elements_empty; simpl.
    eapply labenv_sim_app; eauto using zip_get.
    intros; simpl in *; dcr; subst.
    split; eauto; intros.
    admit.
  - simpl in *. rewrite elements_empty; simpl.
    pno_step. simpl.
    admit.
  - simpl in *. rewrite elements_empty; simpl.
    eapply sim_fun_ptw; eauto.
    + intros. left.
      eapply IH; eauto using agree_on_incl.
      admit.
      admit.
      admit.
      admit.
    + intros. hnf; intros; simpl in *; dcr. subst.
      inv_get. simpl.
      exploit H23; eauto.
      exploit H15; eauto.
      exploit H18; eauto. destruct x.
      eapply IH; eauto.
      admit.
      admit.
      admit.
      admit.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.
