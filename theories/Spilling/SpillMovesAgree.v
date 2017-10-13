Require Import CSet Util Filter Take MoreList OUnion AllInRel MapDefined MapUpdate Position.
Require Import IL Annotation LabelsDefined.
Require Import Liveness.Liveness TrueLiveness SimI.
Require Import RenamedApart.
Require Import SpillSound ReconstrLive DoSpill.

Set Implicit Arguments.
Unset Printing Records.

Lemma agree_on_eq_oval (D:set var) (f g: var -> option val)
  : agree_on _eq D f g
    -> agree_on eq D f g.
Proof.
  intros; hnf; intros.
  eapply H in H0. inv H0; eauto; simpl in *; congruence.
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

Lemma sim_I_moves (slot : var -> var) k Λ ZL r L L' V V' R M s sl RML
  : spill_sound k ZL Λ (R,M) s sl
    -> injective_on (getSp sl ∪ getL sl) slot
    -> disj (getSp sl ∪ getL sl) (map slot (getSp sl ∪ getL sl))
    -> defined_on (getSp sl ∪ (map slot (getL sl) \ map slot (getSp sl))) V'
    -> (forall V'', agree_on eq (R ∪ map slot M ∪ map slot (getSp sl) ∪ getL sl)
                       (V' [slot ⊝ elements (getSp sl) <-- lookup_list V' (elements (getSp sl))]
                           [elements (getL sl) <-- lookup_list (V'[slot ⊝ elements (getSp sl) <-- lookup_list V' (elements (getSp sl))]) (slot ⊝ elements (getL sl))]) V''
              -> paco3 (sim_gen (S':=I.state)) r Sim (L, V, s)
                      (L', V'', do_spill slot s (setTopAnn sl ({}, {}, snd (getAnn sl))) ZL RML))
    -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ZL RML).
Proof.
  simpl. unfold sim. revert_except s.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? SPS Inj Disj Def SIM.
  rewrite do_spill_extract_writes.
  exploit L_sub_SpM; eauto.
  exploit Sp_sub_R; eauto.
  eapply (@sim_write_moves (R ∪ map slot M ∪ map slot (getSp sl) ∪ map slot (getL sl)));
    try rewrite ?of_list_map, of_list_elements; eauto. eauto with len.
  intros ? Agr3.
  eapply (@sim_write_moves (R ∪ map slot M ∪ map slot (getSp sl) ∪ getL sl)); try rewrite ?of_list_map, of_list_elements; eauto. eauto with len.
  intros ? Agr4.
  - rewrite update_with_list_agree in Agr4; eauto;
      [| symmetry; eapply agree_on_incl; eauto; clear; rewrite of_list_elements; cset_tac
       |eauto with len].
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
      revert H1; clear_all; cset_tac.
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
             (@respectful var (option val) (@_eq var (@SOT_as_OT var (@eq var) _))
                          (@eq (option val))) ϱ) | 0.
Proof.
  intuition.
Qed.

Instance proper_onv' (ϱ:var -> option val)
  : @Proper (forall _ : var, option val)
            (@respectful var (option val) (@_eq var (@SOT_as_OT var (@eq var) _))
                         (@_eq (option val) (@option_OrderedType val OrderedType_int))) ϱ | 0.
Proof.
  intuition.
Qed.

Lemma load_agree_after_spill_load (slot : var -> var) (V V':var->option val) VD R M Sp L0
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

Lemma regs_untouched_after_spill_load (slot : var -> var) (V V' V'':var->option val) VD R M K Sp L0
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
  symmetry. eapply disj_incl; eauto; only 2: eauto with cset.
  rewrite <- Incl. clear; cset_tac.
  rewrite of_list_elements. clear; hnf; intros; cset_tac.
Qed.

Lemma regs_agree_after_spill_load (slot : var -> var) (V V' V'':var -> option val) VD R M K Sp L0
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

Lemma spills_agree_after_spill_load (slot : var -> var) (V V' V'':var->option val) VD R M Sp L0
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
  eapply agree_on_comp; eauto; [ symmetry; eapply agree_on_incl; eauto; clear_all; cset_tac | ].
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

Lemma mem_untouched_after_spill_load (slot : var -> var) (V V' V'':var->option val) VD R M Sp L0
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
  etransitivity; [| eapply agree_on_incl; [eapply Agr3| eauto]].
  - eapply agree_on_update_list_dead.
    eapply agree_on_update_list_dead. reflexivity.
    rewrite of_list_map, of_list_elements; eauto.
    intros.
    eapply injective_disj; eauto.
    hnf; intros; cset_tac.
    eapply injective_on_incl; eauto. rewrite <- Incl. rewrite SpR at 1.
    cset_tac.
    rewrite of_list_elements.
    eapply disj_incl; eauto.
    rewrite <- Incl, LSpM, <- SpR. eauto. eauto with cset.
  - rewrite minus_incl. clear. cset_tac.
Qed.

Lemma mem_agrees_after_spill_load (slot : var -> var) (V V' V'':var->option val) VD R M Sp L0
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


Lemma mem_agrees_after_spill_load_update (slot : var -> var) (V V' V'':var->option val) VD R M Sp L0 x v
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
  eapply disj_incl; eauto. rewrite SpR, Incl. revert xIn; clear. cset_tac.
  rewrite SpR, Incl. cset_tac.
Qed.

Lemma RKL_incl X `{OrderedType X} (R K L D D':set X)
  :  R \ K ∪ L ⊆ R ∪ D ∪ D' ∪ L.
Proof.
  cset_tac.
Qed.

Hint Resolve RKL_incl | 0: cset.

Lemma defined_on_after_spill_load (slot : var -> var) (V V' V'':var->option val) VD R M Sp L0  K
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
