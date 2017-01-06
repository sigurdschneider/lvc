Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel MapDefined MapUpdate Position.
Require Import IL Annotation LabelsDefined.
Require Import Liveness.Liveness TrueLiveness SimI.
Require Import RenamedApart.
Require Import SetUtil SpillSound ReconstrLive DoSpill ReconstrLiveUtil.

Set Implicit Arguments.
Unset Printing Records.

Lemma agree_on_eq_oval (D:set var) (f g: var -> option val)
  : agree_on _eq D f g
    -> agree_on eq D f g.
Proof.
  intros; hnf; intros.
  eapply H in H0. inv H0; eauto; simpl in *; congruence.
Qed.

Section Correctness.

  Variable slot : var -> var.

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
    eapply IHLen; intros; eauto using injective_on_incl.
    eapply SIM.
    + rewrite <- update_nodup_commute_eq; simpl; eauto with len.
      erewrite lookup_list_agree; eauto.
      symmetry. eapply agree_on_update_dead; eauto.
      eapply disj_not_in.
      eapply disj_incl; eauto with cset.
    + rewrite H; eapply defined_on_update_some;
        eauto using defined_on_incl with cset.
    + eapply disj_incl; eauto with cset.
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
      rewrite <- (of_list_elements _ (getSp sl)) in H1.
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
  - eapply disj_incl; eauto with cset.
  - eapply elements_3w.
  - eauto using defined_on_incl with cset.
  - symmetry.
    eapply disj_incl; eauto with cset.
  - eapply injective_nodup_map; eauto.
    rewrite of_list_elements. eauto using injective_on_incl with cset.
    eapply elements_3w.
Qed.

Instance proper_onv (ϱ:var -> option val)
  : (@Proper (forall _ : var, option val)
             (@respectful var (option val) (@_eq var (@SOT_as_OT var (@eq nat) nat_OrderedType))
                          (@eq (option val))) ϱ) | 0.
Proof.
  intuition.
Qed.

Instance proper_onv' (ϱ:var -> option val)
  : @Proper (forall _ : var, option val)
            (@respectful var (option val) (@_eq var (@SOT_as_OT var (@eq nat) nat_OrderedType))
                         (@_eq (option val) (@option_OrderedType val OrderedType_int))) ϱ | 0.
Proof.
  intuition.
Qed.

Lemma load_agree_after_spill_load (V V':var->option val) VD R M Sp L0
      (Inj : injective_on VD slot)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
  : agree_on eq L0 V
             (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                 [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           ⊝ slot ⊝ elements L0]).
Proof.
  eapply agree_on_update_list; try eapply proper_onv; eauto with len.
  rewrite of_list_elements. eapply agree_on_empty; eauto with cset.
  rewrite !lookup_list_map. rewrite map_map. rewrite <- !lookup_list_map.
  eapply lookup_list_agree. rewrite lookup_list_map.
  rewrite of_list_elements.
  etransitivity; [| eapply agree_on_eq_oval, agree_on_update_list_map];
    [ | eauto with len | eapply proper_var | eapply proper_onv'
      | eapply injective_on_incl; eauto; rewrite <- VDincl, of_list_elements; clear; cset_tac ].
  rewrite (set_decomp Sp).
  eapply agree_on_union.
  ++ rewrite lookup_list_map.
    etransitivity; [eapply agree_on_incl; [ eapply Agr1| rewrite <- SpR; clear; cset_tac]|].
    eapply agree_on_update_list; [ eapply proper_onv | eauto with len |
                                   | rewrite lookup_list_map; reflexivity ].
    rewrite of_list_elements. eapply agree_on_empty; clear; cset_tac.
  ++ rewrite lookup_list_map.
    eapply agree_on_update_list_dead.
    eapply agree_on_incl; eauto. rewrite LSpM. clear; cset_tac.
    rewrite of_list_elements. hnf; intros; cset_tac.
Qed.

Lemma regs_untouched_after_spill_load (V V' V'':var->option val) VD R M K Sp L0
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
      (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V')
      (VDincl:Sp ∪ L0 [<=] VD)
  :  agree_on eq ((R \ K) \ L0) V V''.
Proof.
  etransitivity; [eapply agree_on_incl; [eapply Agr1| clear; cset_tac]|].
  etransitivity; [|eapply agree_on_incl; [eapply Agr3| clear; cset_tac]].
  eapply agree_on_update_list_dead.
  eapply agree_on_update_list_dead. reflexivity.
  rewrite of_list_map, of_list_elements; eauto.
  symmetry. eapply disj_incl; eauto with cset.
  rewrite <- Incl. clear; cset_tac.
  rewrite of_list_elements. clear; hnf; intros; cset_tac.
Qed.

Lemma regs_agree_after_spill_load (V V' V'':var -> option val) VD R M K Sp L0
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
      (Inj : injective_on VD slot) (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
  : agree_on eq (R \ K ∪ L0) V V''.
Proof.
  etransitivity; [|eapply agree_on_incl; [eapply Agr3| clear; cset_tac]].
  rewrite union_comm, union_exclusive.
  eapply agree_on_union.
  -- eapply load_agree_after_spill_load; eauto.
  -- eapply regs_untouched_after_spill_load; eauto.
     reflexivity.
Qed.

Lemma spills_agree_after_spill_load (V V' V'':var->option val) VD R M Sp L0
      (Inj : injective_on VD slot) (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
  : agree_on eq Sp V (fun x : var => V'' (slot x)).
Proof.
  eapply agree_on_comp; eauto; [ symmetry; eapply agree_on_incl; eauto with cset | ].
  etransitivity; [eapply agree_on_incl; [eapply Agr1| eauto with cset]|].
  eapply agree_on_update_list_dead_slot; eauto.
  etransitivity; [| eapply agree_on_eq_oval, agree_on_update_list_map];
    [ | eauto with len | eapply proper_var | eapply proper_onv'
      | eapply injective_on_incl; eauto; rewrite <- VDincl, of_list_elements;
        clear; cset_tac ].
  eapply agree_on_update_list; [ eapply proper_onv | eauto with len |
                                 | rewrite lookup_list_map; reflexivity ].
  eapply agree_on_empty. rewrite of_list_elements. cset_tac.
  eapply disj_incl; eauto with cset.
  rewrite of_list_elements, <- Incl, LSpM, <- SpR; reflexivity.
Qed.

Lemma mem_untouched_after_spill_load (V V' V'':var->option val) VD R M Sp L0
      (Inj : injective_on VD slot) (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
  : agree_on eq (M \ Sp) V (fun x : var => V'' (slot x)).
Proof.
  etransitivity; [eapply agree_on_incl; [eapply Agr2| eauto with cset ]|].
  eapply agree_on_comp_both; eauto using proper_onv.
  etransitivity; [| eapply agree_on_incl; [eapply Agr3| eauto with cset]].
  eapply agree_on_update_list_dead.
  eapply agree_on_update_list_dead. reflexivity.
  rewrite of_list_map, of_list_elements; eauto.
  intros.
  eapply injective_disj; eauto.
  hnf; intros; cset_tac.
  eapply injective_on_incl; eauto. rewrite <- Incl. cset_tac.
  rewrite of_list_elements.
  eapply disj_incl; eauto with cset.
  rewrite <- Incl, LSpM, <- SpR. eauto.
Qed.

Lemma mem_agrees_after_spill_load (V V' V'':var->option val) VD R M Sp L0
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
      (Inj : injective_on VD slot) (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
  : agree_on eq (Sp ∪ M) V (fun x : var => V'' (slot x)).
Proof.
  rewrite union_exclusive.
  eapply agree_on_union.
  -- eapply spills_agree_after_spill_load; try eapply Agr3; eauto.
  -- eapply mem_untouched_after_spill_load; try eapply Agr3; eauto.
Qed.


Lemma mem_agrees_after_spill_load_update (V V' V'':var->option val) VD R M Sp L0 x v
      (Agr5 : agree_on eq (Sp ∪ M) V (fun x : var => V'' (slot x)))
      (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD) (NotIn: x ∉ Sp ∪ M)
      (xIn:x ∈ VD)
      (Agr1 : agree_on eq R V V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
  : agree_on eq (Sp ∪ M) (V [x <- ⎣ v ⎦]) (fun x0 : var => (V'' [x <- ⎣ v ⎦]) (slot x0)).
Proof.
  eapply agree_on_update_dead_both_comp_right; eauto.
  eapply disj_incl; eauto with cset.
  rewrite SpR, Incl. cset_tac.
Qed.

Lemma RKL_incl X `{OrderedType X} (R K L D D':set X)
  :  R \ K ∪ L ⊆ R ∪ D ∪ D' ∪ L.
Proof.
  cset_tac.
Qed.

Hint Resolve RKL_incl | 0: cset.

Lemma defined_on_after_spill_load (V V' V'':var->option val) VD R M Sp L0  K
      (Agr5 : agree_on eq (Sp ∪ M) V (fun x : var => V'' (slot x)))
      (Disj : disj VD (map slot VD)) (Incl : R ∪ M [<=] VD)
      (Agr1 : agree_on eq R V V') (Def : defined_on (R ∪ map slot M) V')
      (Agr2 : agree_on eq M V (fun x : var => V' (slot x)))
      (VDincl:Sp ∪ L0 [<=] VD) (SpR:Sp [<=] R) (LSpM:L0 [<=] Sp ∪ M)
      (Agr3 : agree_on eq (R ∪ map slot M ∪ map slot Sp ∪ L0)
                       (V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                           [elements L0 <-- V' [slot ⊝ elements Sp <-- V' ⊝ elements Sp]
                                     ⊝ slot ⊝ elements L0]) V'')
  : defined_on (R \ K ∪ L0 ∪ map slot (Sp ∪ M)) V''.
Proof.
  assert (defined_on Sp V') as DefSp by eauto using defined_on_incl with cset.
  rewrite union_exclusive.
  eapply defined_on_union.
  -- eapply defined_on_agree_eq; [|eapply agree_on_incl;[eapply Agr3|eauto with cset]].
     rewrite union_comm, union_exclusive. eapply defined_on_union.
     ++ eapply defined_on_update_list'; eauto with len.
       rewrite of_list_elements. clear; hnf; intros; cset_tac.
       eapply defined_on_defined. clear; intuition.
       rewrite of_list_map, of_list_elements; eauto.
       eapply defined_on_update_list'; eauto with len.
       rewrite of_list_map, of_list_elements; eauto.
       rewrite LSpM. eapply (defined_on_incl Def); eauto.
       rewrite map_union; eauto. clear; cset_tac.
       eapply defined_on_defined. clear; intuition. eauto.
       rewrite of_list_elements. eauto.
     ++ eapply defined_on_agree_eq; [| eapply agree_on_update_list_dead; try reflexivity].
       eapply defined_on_update_list'; eauto with len.
       rewrite of_list_map, of_list_elements; eauto.
       eapply (defined_on_incl Def). clear; cset_tac.
       eapply defined_on_defined. clear; intuition. eauto.
       rewrite of_list_elements. eauto.
       rewrite of_list_elements. eauto. clear; hnf; intros; cset_tac.
  -- rewrite map_union; eauto.
     eapply defined_on_agree_eq; [ | eapply agree_on_incl; [ eapply Agr3| clear; cset_tac]];
       eauto.
     eapply defined_on_agree_eq; [| eapply agree_on_update_list_dead; try reflexivity].
     eapply defined_on_update_list'; eauto with len.
     rewrite of_list_map, of_list_elements; eauto.
     eapply (defined_on_incl Def). clear; cset_tac.
     eapply defined_on_defined. clear; intuition. eauto.
     rewrite of_list_elements. eauto.
     rewrite of_list_elements. clear; hnf; intros; cset_tac.
Qed.

Lemma omap_slotlift (V V'':onv val) xl Yv ib (Len:❬xl❭=❬ib❭) Sl R K L0 Sp M
      (Agr4 : agree_on eq (R \ K ∪ L0) V V'')
      (Agr5 : agree_on eq (Sp ∪ M) V (fun x : var => V'' (slot x)))
      (FVincl: of_list xl [<=] Sl ∪ (R \ K ∪ L0))
      (Slincl:Sl [<=] Sp ∪ M)
  : omap (op_eval V) (Var ⊝ xl) = Some Yv
    -> omap (op_eval V'') (slot_lift_args slot Sl ⊝ extend_args (Var ⊝ xl) ib)
      = Some (extend_args Yv ib).
Proof.
  intros.
  length_equify.
  general induction Len; simpl in *; eauto;
    monad_inv H; simpl in *.
  repeat (cases; simpl).
  - rewrite <- Agr5; [ rewrite EQ | rewrite <- Slincl; eauto]; simpl.
    erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
  - rewrite <- Agr4; [ rewrite EQ | ]; simpl.
    erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    assert (x ∈ Sl ∪ (R \ K ∪ L0)) by (rewrite <- FVincl; cset_tac).
    revert NOTCOND H. clear; cset_tac.
  - rewrite <- Agr5; [ rewrite EQ | rewrite <- Slincl; eauto]; simpl.
    erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
  - rewrite <- Agr4; [ rewrite EQ | ]; simpl.
    erewrite IHLen; eauto; [ | rewrite <- FVincl; eauto with cset ]; eauto.
    assert (x ∈ Sl ∪ (R \ K ∪ L0)) by (rewrite <- FVincl; cset_tac).
    revert NOTCOND H. clear; cset_tac.
Qed.

Lemma slot_lift_params_agree X (E:onv X) E' R M Z VL (Len:❬Z❭=❬VL❭)
      (Agr2:agree_on eq (R \ of_list Z) E E')
      (Disj:disj (R ∪ of_list Z) (map slot (R ∪ of_list Z)))
      (Incl:of_list Z [<=] R ∪ M)
  : agree_on eq R (E [Z <-- Some ⊝ VL])
             (E' [slot_lift_params slot (R, M) Z <--
                  Some ⊝ extend_args VL (mark_elements Z (R ∩ M))]).
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

Lemma update_with_list_lookup_in_list_first_slot' A (E:onv A) n (R M:set var)
      Z (Y:list A) z
: length Z = length Y
  -> get Z n z
  -> z ∈ M
  -> disj (of_list Z ∪ R ∪ M) (map slot (of_list Z ∪ R ∪ M))
  -> injective_on (of_list Z ∪ R ∪ M) slot
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> exists y, get Y n y /\ E [slot_lift_params slot (R, M) Z <--
                  Some ⊝ extend_args Y (mark_elements Z (R ∩ M))] (slot z) = Some y.
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
      * cases; simpl; lud.
        -- exfalso. hnf in e; subst.
           eapply (Disj (slot z)); eauto with cset.
        -- exfalso. eapply H2. eapply Inj; eauto with cset.
        -- eauto.
Qed.

Lemma slot_lift_params_agree_slot X (E:onv X) E' R M Z VL (Len:❬Z❭=❬VL❭)
      (Agr2:agree_on eq (M \ of_list Z) E (fun x => E' (slot x)))
      (Disj:disj (of_list Z ∪ R ∪ M) (map slot (of_list Z ∪ R ∪ M)))
      (Inj:injective_on (of_list Z ∪ R ∪ M) slot)
      (Incl:of_list Z [<=] R ∪ M)
        : agree_on eq M (E [Z <-- Some ⊝ VL])
             (fun x => E' [slot_lift_params slot (R, M) Z <--
                        Some ⊝ extend_args VL (mark_elements Z (R ∩ M))] (slot x)).
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

Instance SR (VD:set var) : PointwiseProofRelationI (((set var) * (set var)) * params) := {
   ParamRelIP RMZ Z Z' := Z' = slot_lift_params slot (fst RMZ) Z /\ Z = snd RMZ;
   ArgRelIP V V' RMZ VL VL' :=
     VL' = extend_args VL (mark_elements (snd RMZ) (fst (fst RMZ) ∩ snd (fst RMZ))) /\
     agree_on eq (fst (fst RMZ) \ of_list (snd RMZ)) V V' /\
     agree_on eq (snd (fst RMZ) \ of_list (snd RMZ)) V (fun x => V' (slot x)) /\
     ❬VL❭ = ❬snd RMZ❭ /\
     defined_on (fst (fst RMZ) \ of_list (snd RMZ)
                     ∪ map slot (snd (fst RMZ) \ of_list (snd RMZ))) V'
}.

Require Import AppExpFree Subset1.


Lemma sim_I k Λ ZL LV VD r L L' V V' R M s lv sl ra
  : agree_on eq R V V'
    -> agree_on eq M V (fun x => V' (slot x))
    -> live_sound Imperative ZL LV s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl lv
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> defined_on (R ∪ map slot M) V'
    -> R ∪ M ⊆ fst (getAnn ra)
    -> labenv_sim Sim (sim r) (SR VD) (zip pair Λ ZL) L L'
    -> (fst (getAnn ra) ∪ snd (getAnn ra)) ⊆ VD
    -> renamedApart s ra
    -> app_expfree s
    -> ann_R Subset1 lv ra
    -> sim r Sim (L, V, s) (L', V', do_spill slot s sl (compute_ib ⊜ ZL Λ)).
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
        invt renamedApart; invt app_expfree; try invt (@ann_R _ _ Subset1));
    exploit regs_agree_after_spill_load as Agr4; eauto;
      exploit mem_agrees_after_spill_load as Agr5; eauto;
        simpl in *; rewrite !elements_empty; simpl.
  - destruct e; simpl in *.
    + eapply (sim_let_op il_statetype_I); eauto.
      * symmetry; eapply op_eval_agree; eauto using agree_on_incl.
      * intros. left.
        eapply IH; eauto.
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
    + eapply (sim_let_call il_statetype_I); eauto.
      * symmetry; eapply omap_op_eval_agree; eauto using agree_on_incl.
      * intros. left. eapply IH; eauto.
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
    eapply (sim_cond il_statetype_I); eauto.
    + symmetry; eapply op_eval_agree; eauto using agree_on_incl.
    + intros; left. eapply IH; eauto.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H9. clear; cset_tac.
    + intros; left. eapply IH; eauto.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H9. clear; cset_tac.
  - eapply labenv_sim_app; eauto using zip_get.
    intros; simpl in *. dcr; subst; repeat get_functional.
    split; eauto; intros.
    erewrite get_nth; eauto using zip_get. unfold compute_ib. simpl.
    edestruct op_eval_var; eauto; subst.
    erewrite omap_slotlift; eauto.
    eexists; split; eauto. split; eauto.
    erewrite <- sla_extargs_slp_length; eauto. instantiate (1:=M').
    simpl. eauto with len.
    split; eauto.
    split; eauto using agree_on_incl.
    split; eauto using agree_on_incl.
    split; eauto.
    eapply defined_on_incl.
    eapply defined_on_after_spill_load; eauto. instantiate (1:=K).
    rewrite H8, H11. reflexivity.
    unfold mark_elements. len_simpl. rewrite <- H17. eauto with len.
    rewrite union_comm.
    rewrite <- H12. eapply of_list_freeVars_vars.
  - pno_step. simpl.
    erewrite op_eval_agree; [reflexivity| |reflexivity]. symmetry.
    eapply agree_on_incl; eauto using regs_agree_after_spill_load; eauto.
  - eapply sim_fun_ptw; try eapply LSim; eauto.
    + intros. left. rewrite <- zip_app; [| eauto with len].
      eapply (IH s); eauto using agree_on_incl.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * rewrite !zip_app; eauto with len.
      * pe_rewrite. rewrite <- RAincl, <- H25. clear; cset_tac.
    + intros. hnf; intros; simpl in *; dcr. subst.
      inv_get.
      exploit H12 as SPS'; eauto.
      exploit H20 as LS'; eauto.
      exploit H15 as SL'; eauto. destruct x as (R_f,M_f).
      exploit H14 as In'; eauto; simpl in *; destruct In' as [In1 In2].
      exploit H2 as RA'; eauto.
      exploit (get_PIR2 H7) as EQ; eauto.
      exploit H21 as In3; eauto. destruct In3 as [In3 _].
      unfold merge in EQ. simpl in *.
      rewrite <- zip_app; [| eauto with len].
      eapply IH; eauto.
      * eapply slot_lift_params_agree; eauto.
        -- eapply disj_incl; eauto.
           ++ rewrite In3, <- EQ, In1, In2.
             clear; eauto with cset.
           ++ rewrite In3, <- EQ, In1, In2.
             clear; eauto with cset.
        -- rewrite EQ; eauto.
      * eapply slot_lift_params_agree_slot; eauto.
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
           rewrite countTrue_mark_elements; eauto.
           rewrite slot_lift_params_length; eauto.
           unfold mark_elements. eauto with len.
        -- rewrite of_list_slot_lift_params; eauto.
           eapply defined_on_incl; eauto.
           rewrite <- EQ in In3; revert In3; clear.
           intros.
           cset_tac'.
           ++ right. eexists x. cset_tac.
           ++ right. eexists x; eauto.
           ++ rewrite EQ; eauto.
        -- eapply get_defined; intros; inv_get; eauto.
      * edestruct H8; eauto; dcr.
        simpl in *. rewrite EQ.
        exploit H33; eauto. eapply ann_R_get in H4. eauto.
      * rewrite !zip_app; eauto with len.
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
      Grab Existential Variables. eapply 0.
Qed.

End Correctness.