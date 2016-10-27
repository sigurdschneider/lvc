Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel MapDefined MapUpdate Position.
Require Import IL Annotation LabelsDefined Liveness TrueLiveness SimI.
Require Import RenamedApart.
Require Import SetUtil Spilling ReconstrLive DoSpill ReconstrLiveUtil.

Set Implicit Arguments.
Unset Printing Records.

Section Correctness.

  Variable slot : var -> var.

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

Lemma in_add_right X `{OrderedType X} s x x'
  : x ∈ s -> x ∈ {x'; s}.
Proof.
  cset_tac; intuition.
Qed.

Hint Resolve in_add_right : cset.

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

Lemma set_decomp X `{OrderedType X} t s
  : s [=] s ∩ t ∪ (s \ t).
Proof.
  cset_tac. decide (a ∈ t); eauto.
Qed.

Lemma agree_on_update_list X `{OrderedType X} Y (L:list X) (L':list Y) (V:X->Y)
      `{Proper _ (_eq ==> eq) V} V' D (Len:❬L❭= ❬L'❭)
  :  agree_on eq (D \ of_list L) V V'
     -> lookup_list V L = L'
     -> agree_on eq D V (V'[L <-- L']).
Proof.
  intros. hnf; intros.
  decide (x ∈ of_list L).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2. rewrite H7.
    rewrite lookup_list_map in H2. subst. inv_get.
    eapply H0; eauto. eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply H1; cset_tac.
Qed.

Lemma agree_on_update_list_dead X `{OrderedType X} Y (L:list X) (L':list Y) (V:X->Y)
      V' D
  :  agree_on eq D V V'
     -> disj (of_list L) D
     -> agree_on eq D V (V'[L <-- L']).
Proof.
  intros. hnf; intros.
  rewrite lookup_set_update_not_in_Z; eauto.
Qed.

Lemma agree_on_update_list_dead_slot X `{OrderedType X} Y (L:list X) (L':list Y) (V:X->Y) (f:X->X)
      `{Proper _ (_eq ==> _eq) f} V' D
  :  agree_on eq D V (fun x => V' (f x))
     -> disj (of_list L) (map f D)
     -> agree_on eq D V (fun x => V'[L <-- L'] (f x)).
Proof.
  intros. hnf; intros.
  rewrite lookup_set_update_not_in_Z; eauto.
  intro. eapply H2; eauto. eapply map_iff; eauto.
Qed.

Lemma get_map_first X `{OrderedType X} Y `{OrderedType Y} (L:list X) (f:X->Y) n x
  : injective_on (of_list L) f
    -> get L n x
    -> (forall n' z', n' < n -> get L n' z' -> z' =/= x)
    -> get (f ⊝ L) n (f x) /\
      (forall n' z', n' < n -> get (f ⊝ L) n' z' -> z' =/= f x).
Proof.
  intros. general induction H2; simpl.
  - split; eauto using get.
    intros. invt get; omega.
  - split; eauto using get.
    intros. invt get.
    + intro A.
      eapply H1 in A; simpl; eauto with cset.
      eapply H3; eauto using get.
      cset_tac. right. eapply get_in_of_list; eauto.
    + simpl in *.
      exploit IHget; intros; eauto using injective_on_incl, get with cset.
      eapply H3;[| eauto using get]. omega. dcr.
      eapply H8; eauto. omega.
Qed.

Lemma injective_on_not_in_map X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) L x
      `{Proper _ (_eq ==> _eq) f}
  : x ∉ of_list L
    -> injective_on ({x; of_list L}) f
    -> f x ∉ of_list (f ⊝ L).
Proof.
  intros. lset_tac.
  rewrite of_list_map in H4; eauto.
  eapply map_iff in H4; eauto; dcr.
  eapply H3 in H7; eauto with cset.
Qed.


Lemma agree_on_update_map X `{OrderedType X} Y `{OrderedType Y} (V:X->Y) (x:X) (v:Y)
      (f:X->X) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) V}
  : injective_on {x; D} f
    -> agree_on _eq D ((f ∘ V)[x <- v])  (fun y => V[f x <- v] (f y)).
Proof.
  intros Inj.
  hnf; intros. lud; eauto.
  - exfalso. rewrite H4 in *. eauto.
  - exfalso. eapply Inj in e; eauto with cset.
Qed.

Lemma agree_on_update_list_map X `{OrderedType X} Y `{OrderedType Y} (V:X->Y)
      (L:list X) (L':list Y)
      (Len:❬L❭=❬L'❭) (f:X->X) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) V}
  : injective_on (D ∪ of_list L) f
    -> agree_on _eq D ((f ∘ V)[L <-- L'])  (fun x => V[f ⊝ L <-- L'] (f x)).
Proof.
  intros Inj.
  hnf; intros.
  decide (x ∈ of_list L).
  - edestruct (of_list_get_first _ i) as [n]; eauto. dcr.
    edestruct update_with_list_lookup_in_list_first; eauto; dcr.
    intros; intro. eapply H8; eauto. rewrite H9; eauto.
    instantiate (1:=f ∘ V) in H9.
    pose proof (proper_update_with_list _ _ (f ∘ V) L L') as PEQ.
    unfold respectful, Proper, feq in PEQ.
    rewrite PEQ; [| intros; unfold comp; rewrite H4; reflexivity | eapply H5]; clear PEQ.
    rewrite H9.
    setoid_rewrite H5 in H8.
    eapply injective_on_incl in Inj; [| eapply incl_right].
    edestruct (get_map_first Inj H6 H8); dcr.
    edestruct update_with_list_lookup_in_list_first; try eapply H4; dcr.
    Focus 3. rewrite H5. rewrite H13. inv_get.
    rewrite EQ. reflexivity. eauto with len.
    eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    exploit (@injective_on_not_in_map _ _ _ _ f _ _ H1 n); eauto.
    eapply injective_on_incl; eauto.
    cset_tac.
    rewrite lookup_set_update_not_in_Z; eauto.
Qed.

Lemma agree_on_eq_oval (D:set var) (f g: var -> option val)
  : agree_on _eq D f g
    -> agree_on eq D f g.
Proof.
  intros; hnf; intros.
  eapply H in H0. inv H0; eauto; simpl in *; congruence.
Qed.

Lemma agree_on_empty X `{OrderedType X} Y D (f g:X->Y) R
  : D ⊆ ∅
    -> agree_on R D f g.
Proof.
  unfold agree_on; intros; exfalso; cset_tac.
Qed.

Lemma map_incl X `{OrderedType X} Y `{OrderedType Y} D D' (f:X->Y)
      `{Proper _ (_eq ==> _eq) f}
  : D ⊆ D'
    -> map f D ⊆ map f D'.
Proof.
  intros; hnf; intros.
  eapply map_iff in H3; dcr; eauto.
  eapply map_iff; eauto.
Qed.

Hint Resolve map_incl.

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
  symmetry. eapply disj_1_incl. eapply disj_2_incl; eauto.
  eapply map_incl; eauto. rewrite <- VDincl; eauto with cset.
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


Lemma agree_on_comp X `{OrderedType X} Y
      (V V' V'':X->Y) (f:X->X) D `{Proper _ (_eq ==> _eq) f}
  : agree_on eq (map f D) V' V''
    -> agree_on eq D V (fun x => V'' (f x))
    -> agree_on eq D V (fun x => V' (f x)).
Proof.
  intros.
  hnf; intros. rewrite H1; eauto.
  eapply map_iff; eauto.
Qed.

Lemma agree_on_comp_both X `{OrderedType X} Y
      (V V':X->Y) (f:X->X) D `{Proper _ (_eq ==> _eq) f}
      `{Proper _ (_eq ==> eq) V}
      `{Proper _ (_eq ==> eq) V'}
  : agree_on eq (map f D) V V'
    <-> agree_on eq D (fun x => V (f x)) (fun x => V' (f x)).
Proof.
  split; intros Agr; hnf; intros.
  + rewrite Agr; eauto.
    eapply map_iff; eauto.
  + eapply map_iff in H3; eauto; dcr.
    exploit (Agr x0); eauto.
    rewrite <- H6 in H3. eauto.
Qed.

Lemma injective_disj X `{OrderedType X} s t (f:X->X) `{Proper _ (_eq ==> _eq) f}
  : disj s t
    -> injective_on (s ∪ t) f
    -> disj (map f s) (map f t).
Proof.
  intros Disj Inj; hnf; intros.
  eapply map_iff in H1; eauto; dcr.
  eapply map_iff in H2; eauto; dcr.
  rewrite H6 in H5. eapply Inj in H5; cset_tac.
  eapply Disj; eauto. cset_tac.
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
  eapply disj_1_incl. eapply disj_2_incl. eauto.
  eapply map_incl; eauto. rewrite <- Incl, <- SpR. eauto with cset.
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
  eapply disj_1_incl. eapply disj_2_incl. eauto.
  eapply map_incl; eauto. rewrite <- Incl. clear; cset_tac.
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

Inductive defined X : list (option X) -> Prop :=
| NilDefined : defined nil
| ConsDefined x xs: defined xs -> defined (Some x::xs).

Lemma defined_get X (L:list (option X)) n x
  : defined L
    -> get L n x
    -> exists y, x = Some y.
Proof.
  intros. general induction H0; invt defined; eauto.
Qed.

Lemma defined_on_update_list' X `{OrderedType X} Y (E:X -> option Y) L L' (Len:❬L❭=❬L'❭) s
  : defined_on (s \ of_list L) E
    -> defined L'
    -> defined_on s (E [L <-- L']).
Proof.
  intros.
  hnf; intros. decide (x ∈ of_list L).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr; eauto.
    rewrite H6. exploit defined_get; eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply H0; cset_tac.
Qed.

Lemma get_defined X (L:list (option X))
  : (forall n x, get L n x -> exists y, x = Some y)
    -> defined L.
Proof.
  intros. general induction L; eauto using defined, get.
  edestruct H; dcr; eauto using get. subst.
  eauto using defined, get.
Qed.

Lemma defined_on_defined X `{OrderedType X} Y (V:X->option Y) L
      `{Proper _ (_eq ==> eq) V}
  : defined_on (of_list L) V
    <-> defined (V ⊝ L).
Proof.
  split; intros.
  - eapply get_defined; intros; inv_get.
    eapply get_in_of_list in H2. eauto.
  - hnf; intros.
    edestruct of_list_get_first; eauto; dcr.
    eapply defined_get; eauto.
    rewrite H4. eapply map_get_1; eauto.
Qed.

Lemma defined_on_comp X `{OrderedType X} Y (f:X->X) D (V:X -> option Y)
      `{Proper _ (_eq ==> _eq) f}  `{Proper _ (_eq ==> eq) V}
  : defined_on (map f D) V <-> defined_on D (f ∘ V).
Proof.
  split; intros; hnf; intros.
  - exploit H2; eauto. eapply map_iff; eauto.
  - eapply map_iff in H3; dcr; eauto.
    setoid_rewrite H6; eauto.
Qed.

Lemma agree_on_update_dead_both_comp_right X `{OrderedType X} Y R
      (lv:set X) (E E':X -> Y) (f:X->X) `{Proper _ (_eq ==> _eq) f} x v v'
  : ~x ∈ lv
    -> disj {x; lv} (map f lv)
    -> agree_on R lv E (f ∘ E')
    -> agree_on R lv (E [x <- v]) (f ∘ (E'[x <- v'])).
Proof.
  intros NotIn Disj Agr; unfold comp.
  hnf; intros. lud; eauto.
  exfalso. eapply (Disj x); eauto. cset_tac.
  eapply map_iff; eauto.
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
  eapply disj_1_incl. eapply disj_2_incl; eauto.
  eapply map_incl; eauto. rewrite <- Incl, SpR; reflexivity.
  rewrite SpR, Incl. cset_tac.
Qed.

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
  -- eapply defined_on_agree_eq; [|eapply agree_on_incl;[eapply Agr3| eauto with cset]].
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


Instance SR (VD:set var) : PointwiseProofRelationI (((set var) * (set var)) * params) := {
   ParamRelIP RMZ Z Z' := Z' = slot_lift_params slot (fst RMZ) Z /\ Z = snd RMZ;
   ArgRelIP V V' RMZ VL VL' :=
     VL' = extend_args VL (mark_elements (snd RMZ) (fst (fst RMZ) ∩ snd (fst RMZ))) /\
     agree_on eq (fst (fst RMZ)) V V' /\
     agree_on eq (snd (fst RMZ)) V (fun x => V' (slot x)) /\
     (fst (fst RMZ) ∪ snd (fst RMZ)) ⊆ VD
}.


Lemma sim_I k Λ ZL LV VD r L L' V V' R M s lv sl ib ra
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
    -> sim r Sim (L, V, s) (L', V', do_spill slot s sl ib).
Proof.
  simpl. unfold reconstr_live_do_spill. unfold sim.
  move VD before k. move s before VD. revert_until s.
  time (sind s).
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Agr1 Agr2 LS SLS SL Inj Disj Def Incl' LSim RAincl RA.
  assert (Incl:R ∪ M [<=] VD). {
    rewrite <- RAincl, <- Incl'. eauto with cset.
  }
  exploit L_sub_SpM as LSpM; eauto.
  exploit Sp_sub_R as SpR; eauto.
  assert (VDincl:getSp sl ∪ getL sl [<=] VD). {
    rewrite LSpM, SpR. rewrite <- Incl. eauto with cset.
  }
  eapply sim_I_moves; eauto.
  eapply injective_on_incl; eauto with cset.
  eapply disj_1_incl. eapply disj_2_incl. eauto. rewrite VDincl; eauto. eauto.
  eapply defined_on_incl; eauto.
  rewrite SpR at 1. rewrite LSpM.
  rewrite map_union; eauto. clear; cset_tac.
  rewrite !lookup_list_map. intros ? Agr3.
  time (destruct s; invt spill_sound; invt spill_live; invt live_sound; invt renamedApart);
    exploit regs_agree_after_spill_load as Agr4; eauto;
      exploit mem_agrees_after_spill_load as Agr5; eauto;
        simpl in *; rewrite !elements_empty; simpl.
  - destruct e; simpl in *.
    + eapply (sim_let_op il_statetype_I); eauto.
      * symmetry; eapply op_eval_agree; eauto using agree_on_incl.
      * intros. left. eapply IH; eauto.
        -- eapply agree_on_update_same; eauto.
           eapply agree_on_incl; eauto.
           clear; cset_tac.
        -- eapply mem_agrees_after_spill_load_update; eauto.
           rewrite SpR, Incl'; eauto.
           rewrite H17 in RAincl.
           revert RAincl; clear; cset_tac. eapply RAincl; cset_tac.
        -- eapply defined_on_update_some.
           eapply defined_on_incl.
           eapply defined_on_after_spill_load;  eauto.
           clear; cset_tac.
        -- pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
        -- pe_rewrite. rewrite <- RAincl. rewrite H17. clear; cset_tac.
    + eapply (sim_let_call il_statetype_I); eauto.
      * symmetry; eapply omap_op_eval_agree; eauto using agree_on_incl.
      * intros. left. eapply IH; eauto.
        -- eapply agree_on_update_same; eauto.
           eapply agree_on_incl; eauto.
           clear; cset_tac.
        -- eapply mem_agrees_after_spill_load_update; eauto.
           rewrite SpR, Incl'; eauto.
           rewrite H17 in RAincl.
           revert RAincl; clear; cset_tac. eapply RAincl; cset_tac.
        -- eapply defined_on_update_some. admit.
        -- pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
        -- pe_rewrite. rewrite <- RAincl. rewrite H17. clear; cset_tac.
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
    intros; simpl in *; dcr; subst.
    split; eauto; intros.
    exploit omap_op_eval_agree; eauto using agree_on_incl.
    admit.
  - pno_step. simpl.
    erewrite op_eval_agree; [reflexivity| |reflexivity]. symmetry.
    eapply agree_on_incl; eauto using regs_agree_after_spill_load; eauto.
  - eapply sim_fun_ptw; try eapply LSim; eauto.
    + intros. left.
      eapply (IH s); eauto using agree_on_incl.
      * eapply defined_on_after_spill_load; eauto.
      * pe_rewrite. rewrite LSpM, SpR, <- Incl'. clear; cset_tac.
      * pe_rewrite. rewrite <- RAincl, <- H25. clear; cset_tac.
    + intros. hnf; intros; simpl in *; dcr. subst.
      inv_get. simpl.
      exploit H12; eauto.
      exploit H20; eauto.
      exploit H15; eauto. destruct x.
      exploit H14; eauto; simpl in *; dcr.
      exploit H2; eauto.
      exploit al_sub_RfMf; eauto.
      eapply IH; eauto.
      * admit.
      * admit.
      * admit.
      * edestruct H8; eauto; dcr.
        rewrite H39. simpl. simpl in *.
        admit.
      * edestruct H8; eauto; dcr.
        rewrite H39. simpl. rewrite union_comm. rewrite <- union_assoc.
        eapply union_incl_split.
        -- rewrite <- RAincl. eapply incl_union_right.
           rewrite <- H25. eapply incl_union_left.
           eapply incl_list_union; eauto using zip_get.
           unfold defVars. simpl. clear; eauto with cset.
        -- rewrite <- RAincl. eauto with cset.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.
