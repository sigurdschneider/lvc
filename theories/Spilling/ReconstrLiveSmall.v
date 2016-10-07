Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm SpillUtil ReconstrLive.

Set Implicit Arguments.


Lemma reconstr_live_remove_G
      Lv ZL G s sl G'
  :
    getAnn (reconstr_live Lv ZL G s sl) \ G
           ⊆ getAnn (reconstr_live Lv ZL G' s sl)
.
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.




Lemma reconstr_live_small_L'
      (sl : spilling)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (slot : var -> var)
      (ys : list var)
      (R M R' G : ⦃var⦄)
      (IB : list (list bool))
  :
    getL sl ⊆ getSp sl ∪ M
    -> of_list ys ⊆ getL sl
    -> R' [=] R ∪ getL sl \ of_list ys
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ Λ ZL) G'
                (do_spill slot s (clear_SpL sl) IB)
                (do_spill_rm slot (clear_SpL sl))
             )
             ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G'
       )
    -> getAnn
         (reconstr_live
            (slot_merge slot Λ)
            (slot_lift_params slot ⊜ Λ ZL) G
            (write_loads slot ys
                         (do_spill slot s (clear_SpL sl) IB)
            )
            (add_anns ⎣⎦ (length ys)
                      (do_spill_rm slot (clear_SpL sl))
            )
         )
            ⊆ R' ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
intros L_SpM ys_L RR base.
  rewrite RR.
  general induction ys;
    simpl; eauto.
  - rewrite add_anns_zero.
    rewrite base.
    clear; cset_tac.
  - rewrite add_anns_S.
    simpl.
    rewrite IHys; eauto.
    + enough (singleton (slot a) ⊆ map slot (getSp sl ∪ M))
        as a_in_SpM
          by (rewrite a_in_SpM; clear; cset_tac).
      rewrite <- map_singleton.
      apply lookup_set_morphism.
      rewrite <- L_SpM.
      rewrite <- ys_L.
      clear; eauto with cset.
    + rewrite <- ys_L.
      clear; eauto with cset.
    + eauto with cset.
Qed.

Lemma reconstr_live_small_L
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl) IB)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s (clear_Sp sl) IB)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
  intros L_sub base.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  rewrite count_clearSp.
  rewrite getSp_clearSp.
  rewrite getL_clearSp.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  rewrite setTopAnn_setTopAnn.
  rewrite elements_empty.
  simpl.
  rewrite <- elements_length.
  eapply reconstr_live_small_L'; eauto.
  - rewrite of_list_elements.
    reflexivity.
  - rewrite of_list_elements.
    clear; cset_tac.
Qed.


Lemma reconstr_live_small_Sp'
      (sl : spilling)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (slot : var -> var)
      (xs : list var)
      (R M M' G : ⦃var⦄)
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> of_list xs ⊆ getSp sl
    -> M' [=] getSp sl \ of_list xs ∪ M
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ Λ ZL) G'
                (write_loads slot (elements (getL sl))
                             (do_spill slot s (clear_SpL sl) IB)
                )
                (add_anns ⎣⎦ (cardinal (getL sl))
                          (do_spill_rm slot (clear_SpL sl))
                )
             )
             ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G'
       )
    -> getAnn
         (reconstr_live
            (slot_merge slot Λ)
            (slot_lift_params slot ⊜ Λ ZL) G
            (write_spills slot xs
                          (write_loads slot (elements (getL sl))
                                       (do_spill slot s (clear_SpL sl) IB)
                          )
            )
            (add_anns ⎣⎦ (length xs + cardinal (getL sl))
                      (do_spill_rm slot (clear_SpL sl))
            )
         )
            ⊆ R ∪ map slot M' ∪ G
.
Proof.
  intros inj_slot Sp_R xs_Sp MM base.
  rewrite MM.
  general induction xs;
    simpl; eauto.
  - rewrite SetOperations.map_app; eauto.
    assert (getSp sl \ ∅ [=] getSp sl)
      as minus_empty by (clear; cset_tac).
    rewrite minus_empty.
    rewrite <- SetOperations.map_app; eauto.
  - rewrite add_anns_S.
    simpl.
    rewrite IHxs; eauto.
    + rewrite -> !SetOperations.map_app; eauto.
      rewrite -> !lookup_set_minus_eq; eauto.
      rewrite lookup_set_add; eauto.
      * enough (singleton a ⊆ R)
          as a_in_R
            by (rewrite a_in_R; clear; cset_tac).
        rewrite <- Sp_R.
        rewrite <- xs_Sp.
        clear; eauto with cset.
      * eapply injective_on_incl; eauto.
        apply union_incl_split.
        -- reflexivity.
        -- rewrite <- xs_Sp.
           clear; eauto with cset.
      * eapply injective_on_incl; eauto.
        apply union_incl_split.
        -- reflexivity.
        -- rewrite <- xs_Sp.
           clear; eauto with cset.
    + rewrite <- xs_Sp.
      clear; eauto with cset.
    + eauto with cset.
Qed.


Lemma reconstr_live_small_Sp
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_Sp sl) IB)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl IB)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros inj_slot Sp_R base.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  unfold count.
  rewrite <- elements_length.
  eapply reconstr_live_small_Sp' with (M:=M); eauto.
  - rewrite of_list_elements.
    reflexivity.
  - rewrite of_list_elements.
    clear; cset_tac.
  - rewrite do_spill_extract_writes in base.
    rewrite do_spill_rm_s in base.
    rewrite getSp_clearSp in base.
    rewrite getL_clearSp in base.
    rewrite elements_empty in base.
    rewrite count_clearSp in base.
    unfold clear_Sp in base.
    rewrite setTopAnn_setTopAnn in base.
    rewrite getAnn_setTopAnn in base.
    simpl in base.
    apply base.
Qed.


Lemma reconstr_live_small_s
      (sl : spilling)
      (ZL : list (params))
      (R M G : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl) IB)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl IB)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros slot_inj Sp_sub L_sub base.
  apply reconstr_live_small_Sp; eauto.
  intros G''.
  apply reconstr_live_small_L; eauto.
Qed.


Lemma extend_args_elem_eq_ext
      (Y : args)
      (ib : list bool)
  :
    elem_eq Y (extend_args Y ib)
.
Proof.
  general induction Y;
    destruct ib;
    unfold elem_eq;
    simpl; eauto.
  unfold elem_eq in IHY.
  destruct b; simpl; eauto with cset.
  rewrite <- IHY.
  rewrite !add_union_singleton.
  cset_tac.
Qed.


Lemma of_list_empty
      (X : Type)
      `{OrderedType X}
      (L : list X)
  :
    of_list L [=] ∅ <-> L = nil
.
Proof.
  destruct L; simpl; eauto.
  - split; eauto.
  - split; intros; isabsurd.
    exfalso.
    cset_tac.
Qed.




Lemma elem_eq_sym_proof
      (X Y : Type)
      `{OrderedType X}
      `{OrderedType Y}
      (f : list X -> list Y)
  :
    (forall (xl xl' : list X),
      of_list xl ⊆ of_list xl' -> of_list (f xl) ⊆ of_list (f xl'))
    -> (forall (xl xl' : list X),
          elem_eq xl xl' -> elem_eq (f xl)  (f xl'))
.
Proof.
  intros.
  unfold elem_eq in H2.
  unfold elem_eq.
  apply eq_incl in H2 as [incl1 incl2].
  eapply H1 in incl1.
  eapply H1 in incl2.
  apply incl_eq; eauto.
Qed.



Lemma slot_lift_args_elem_eq_ext
      (slot : var -> var)
      (Sl : ⦃var⦄)
      (Y Y' : args)
  :
    elem_eq Y Y'
    -> elem_eq (slot_lift_args slot Sl ⊝ Y)
               (slot_lift_args slot Sl ⊝ Y')
.
Proof.
  apply elem_eq_sym_proof.
  intros.
  unfold elem_eq.
  general induction xl;
    simpl in *; eauto.
  - cset_tac.
  - rewrite IHxl with (xl':=xl');
      simpl; eauto.
    + assert (a ∈ of_list xl') as a_in.
      {
        rewrite <- H.
        clear; cset_tac.
      }
      enough (slot_lift_args slot Sl a ∈ of_list (slot_lift_args slot Sl ⊝ xl')) as sla_in.
      {
        apply incl_singleton in sla_in.
        rewrite add_union_singleton.
        rewrite sla_in.
        clear; cset_tac.
      }
      apply of_list_1.
      apply of_list_1 in a_in.
      clear H.
      general induction a_in;
        simpl; eauto.
      rewrite H.
      econstructor; eauto.
    + rewrite <- H.
      eauto with cset.
Qed.


Lemma op_freeVars_elem_eq_ext
      (Y Y' : args)
  :
    elem_eq Y Y'
    -> elem_eq (Op.freeVars ⊝ Y) (Op.freeVars ⊝ Y')
.
Proof.
  apply elem_eq_sym_proof.
  intros.
  unfold elem_eq.
  general induction xl;
    simpl in *; eauto.
  - cset_tac.
  - rewrite IHxl with (xl':=xl');
      simpl; eauto.
    + assert (a ∈ of_list xl') as a_in.
      {
        rewrite <- H.
        clear; cset_tac.
      }
      enough (Op.freeVars a ∈ of_list (Op.freeVars ⊝ xl')) as sla_in.
      {
        apply incl_singleton in sla_in.
        rewrite add_union_singleton.
        rewrite sla_in.
        clear; cset_tac.
      }
      apply of_list_1.
      apply of_list_1 in a_in.
      clear H.
      general induction a_in;
        simpl; eauto.
      rewrite H.
      econstructor; eauto.
      econstructor; eauto.
    + rewrite <- H.
      eauto with cset.
Qed.

Lemma of_list_list_union
      (X : Type)
      `{OrderedType X}
      (s : ⦃X⦄)
      (L : list ⦃X⦄)
  :
    s ∈ of_list L -> s ⊆ list_union L
.
Proof.
  intro s_in.
  apply of_list_1 in s_in.
  induction s_in;
    simpl in *; eauto.
  - rewrite H0.
    apply list_union_start.
    cset_tac.
  - rewrite list_union_start_swap, IHs_in.
    cset_tac.
Qed.




Lemma union_incl_split2
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    s ∪ t ⊆ u -> s ⊆ u /\ t ⊆ u
.
Proof.
  intros uni.
  split;
    rewrite <- uni;
    cset_tac.
Qed.

Lemma in_singleton
      (X : Type)
      `{OrderedType X}
      (x : X)
      (s : ⦃X⦄)
  :
    singleton x ⊆ s -> x ∈ s
.
Proof.
  intros.
  hnf in H0; eauto.
Qed.


Lemma list_union_elem_eq_ext
      (X : Type)
      `{OrderedType X}
      (L L' : list ⦃X⦄)
  :
    elem_eq L L'
    -> list_union L [=] list_union L'
.
Proof.
  enough (forall (l l' : list ⦃X⦄),
                    of_list l ⊆ of_list l'
                    -> list_union l ⊆ list_union l') as enouf.
  {
    unfold elem_eq.
    intros.
    apply eq_incl in H0 as [incl1 incl2].
    apply incl_eq; eauto.
  }
  intros.
  clear L L'.
  general induction l;
    simpl in *; eauto.
  - cset_tac.
  - rewrite list_union_start_swap.
    rewrite add_union_singleton in H0.
    apply union_incl_split2 in H0 as [a_ofl l_ofl].
    assert (a ⊆ list_union l') as a_sub.
    {
      apply in_singleton in a_ofl.
      apply of_list_list_union; eauto.
    }
    rewrite a_sub.
    rewrite IHl with (l':=l'); eauto.
    clear; cset_tac.
Qed.


Lemma sla_list_union_EQ_extended_args
      (slot : var -> var)
      (Sl : ⦃var⦄)
      (Y : args)
      (ib : list bool)

  :
    list_union (Op.freeVars ⊝ slot_lift_args slot Sl ⊝ Y)
               [=] list_union (Op.freeVars ⊝ slot_lift_args slot Sl
                                           ⊝ (extend_args Y ib))
.
Proof.
  apply list_union_elem_eq_ext.
  apply op_freeVars_elem_eq_ext.
  apply slot_lift_args_elem_eq_ext.
  apply extend_args_elem_eq_ext.
Qed.


Lemma lifted_args_in_RL_slot_SpM
      (Y : args)
      (R M : ⦃var⦄)
      (slot : var -> var)
      (H5 : forall (n : nat) (y : op), get Y n y -> isVar y)
      (Sp L K Sl : ⦃var⦄)
      (H21 : list_union (Op.freeVars ⊝ Y) ⊆ Sl ∪ (R \ K ∪ L))
      (H22 : Sl ⊆ Sp ∪ M)
  :
    list_union (Op.freeVars ⊝ slot_lift_args slot Sl ⊝ Y)
               ⊆ R ∪ L ∪ map slot (Sp ∪ M)
.
Proof.
  apply list_union_incl.
  intros; inv_get.
  unfold slot_lift_args.
  exploit H5; eauto.
  destruct x0;
    isabsurd.
  * decide (v ∈ Sl); simpl.
    -- rewrite <- map_singleton.
       apply incl_union_right.
       apply lookup_set_incl; eauto.
       revert H22. revert i.
       clear; cset_tac.
    -- apply incl_singleton.
       eapply get_live_op_sound in H21; eauto.
       inv H21.
       revert H2. revert n0.
       clear; cset_tac.
  * clear; cset_tac.
Qed.


Lemma nth_rfmf
      (l : lab)
      (Λ : 〔⦃var⦄ * ⦃var⦄〕)
      (slot : var -> var)
      (R_f M_f : ⦃var⦄)
      (H15 : get Λ (counted l) (R_f, M_f))
  :
    nth (counted l) (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f
.
Proof.
  eapply get_nth with (d:=(∅,∅)) in H15 as H15'.
  simpl in H15'.
  assert ((fun RM
           => fst RM ∪ map slot (snd RM)) (nth l Λ (∅,∅))
          = (fun RM
             => fst RM ∪ map slot (snd RM)) (R_f,M_f))
    as H_sms.
  {
    f_equal; simpl; [ | f_equal];
      rewrite H15'; simpl; eauto.
  }
  unfold slot_merge.
  rewrite <- map_nth in H_sms.
  simpl in H_sms.
  assert (l < length ((fun RM : ⦃var⦄ * ⦃var⦄
                       => fst RM ∪ map slot (snd RM)) ⊝ Λ))
    as l_len.
  {
    apply get_length in H15.
    clear - H15; eauto with len.
  }
  assert (nth l ((fun RM : ⦃var⦄ * ⦃var⦄
                  => fst RM ∪ map slot (snd RM)) ⊝ Λ) ∅
          = R_f ∪ map slot M_f)
    as H_sms'.
  {
    rewrite nth_indep with (d':=∅ ∪ map slot ∅).
    * exact H_sms.
    * eauto with len.
  }
  simpl.
  rewrite H_sms'.
  reflexivity.
Qed.

Inductive ann_P
           (A : Type)
           (P : A -> Prop)
  : ann A -> Prop
  :=
  | annP0
      (a : A)
    : P a
      -> ann_P P (ann0 a)
  | annP1
      (a : A)
      (an : ann A)
    : P a
      -> ann_P P an
      -> ann_P P (ann1 a an)
  | annP2
      (a : A)
      (an1 an2 : ann A)
    : P a
      -> ann_P P an1
      -> ann_P P an2
      -> ann_P P (ann2 a an1 an2)
  | ann_PF
      (a : A)
      (anF : list (ann A))
      (an2 : ann A)
    : P a
      -> (forall (an1 : ann A) n,
             get anF n an1
             -> ann_P P an1)
      -> ann_P P an2
      -> ann_P P (annF a anF an2)
.



Lemma ann_P_get
      (A : Type)
      (P : A -> Prop)
      (a : ann A)
  :
    ann_P P a -> P (getAnn a)
.
Proof.
  intro annP.
  induction annP; eauto.
Qed.


Definition union_fs
           (a : ⦃var⦄ * ⦃var⦄)
  : ⦃var⦄
  :=
    fst a ∪ snd a
.


(*

*)


Lemma disj_renamedApart_ann_P
      (ra : ann (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (f : var -> var)
  :
    renamedApart s ra
    -> disj (union_fs (getAnn ra))
            (map f (union_fs (getAnn ra)))
    -> ann_P (fun a => disj (union_fs a) (map f (union_fs a))) ra
.
Proof.
  intros rena disj.
  general induction rena;
    simpl in *; eauto.
  - econstructor; eauto.
    apply IHrena; eauto.
    assert (union_fs (getAnn an) ⊆ union_fs (D, D')) as scd.
    {
      invc H2.
      unfold union_fs.
      simpl.
      rewrite H1.
      rewrite H6.
      rewrite H7.
      clear; cset_tac.
    }
    eapply disj_1_incl;
      [ eapply disj_2_incl | ];
      eauto.
    apply incl_lookup_set_morphism; eauto.
    econstructor; econstructor; eauto.
  - invc H2; invc H3.
    econstructor; eauto.
    + apply IHrena1; eauto.
      assert (union_fs (getAnn ans)
                       ⊆ union_fs (D, D')) as scd.
      {
        unfold union_fs.
        rewrite <- H4.
        simpl.
        rewrite <- H1.
        rewrite H7.
        rewrite H8.
        clear; cset_tac.
      }
      eapply disj_1_incl;
        [ eapply disj_2_incl | ];
        eauto.
      apply incl_lookup_set_morphism; eauto.
      econstructor; econstructor; eauto.
    + apply IHrena2; eauto.
      assert (union_fs (getAnn ant)
                       ⊆ union_fs (D, D')) as scd.
      {
        unfold union_fs.
        rewrite <- H2.
        rewrite <- H1.
        rewrite H9.
        rewrite H10.
        simpl.
        clear; cset_tac.
      }
      eapply disj_1_incl;
        [ eapply disj_2_incl | ];
        eauto.
      apply incl_lookup_set_morphism; eauto.
      econstructor; econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    intros; inv_get.
    + eapply H1; eauto.
      assert (union_fs (getAnn an1) ⊆ union_fs (D, D')) as scd.
      {
        unfold union_fs.
        rewrite <- H5.
        exploit H2; eauto.
        destruct H8 as [fst_of [ uni [ disj_D disj_Dt]]].
        rewrite fst_of.
        simpl.
        enough (snd (getAnn an1) ∪ of_list (fst x)
                    ⊆ list_union (defVars ⊜ F ans)) as enouf.
        {
          rewrite union_assoc.
          rewrite union_comm.
          rewrite union_assoc.
          rewrite enouf.
          clear; cset_tac.
        }
        eapply incl_list_union.
        apply zip_get; eauto.
        rewrite union_comm.
        reflexivity.
      }
      eapply disj_1_incl;
        [ eapply disj_2_incl | ];
        eauto.
      apply incl_lookup_set_morphism; eauto.
      econstructor; econstructor; eauto.
    + eapply IHrena; eauto.
      assert (union_fs (getAnn ant) ⊆ union_fs (D, D')) as scd.
      {
        unfold union_fs.
        rewrite <- H5.
        invc H4.
        rewrite H9.
        rewrite H10.
        simpl.
        clear; cset_tac.
      }
      eapply disj_1_incl;
        [ eapply disj_2_incl | ];
        eauto.
      apply incl_lookup_set_morphism; eauto.
      econstructor; econstructor; eauto.
Qed.
(*
*)



Lemma Sp_sub_RM
      (ZL : list params)
      (k : nat)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    spill_sound k ZL Λ (R,M) s sl
    -> getSp sl ⊆ R ∪ M
.
Proof.
  intros spillSnd.
  invc spillSnd;
    cset_tac.
Qed.


(*
*)

(*

 *)
(*

*)

Lemma injective_on_map_inter
      (X : Type)
      `{OrderedType X}
      (D s t : ⦃X⦄)
      (f : X -> X)
  :
    Proper (_eq ==> _eq) f
    -> injective_on D f
    -> s ⊆ D
    -> t ⊆ D
    -> map f (s ∩ t) [=] map f s ∩ map f t
.
Proof.
  intros.
  apply incl_eq.
  - hnf; intros.
    apply inter_iff in H4 as [a_s a_t].
    apply map_iff in a_s as [b [b_s b_eq]]; eauto.
    apply map_iff in a_t as [c [c_s c_eq]]; eauto.
    unfold injective_on in H1.
    rewrite b_eq in c_eq.
    assert (b ∈ D) as b_D by cset_tac.
    assert (c ∈ D) as c_D by cset_tac.
    apply (H1 b c) in b_D; eauto.
    apply map_iff; eauto.
    exists b.
    rewrite <- b_D in c_s.
    split; eauto.
    cset_tac.
  - hnf; intros.
    apply map_iff in H4 as [b [b_s b_eq]]; eauto.
    apply inter_iff in b_s as [b_s b_t].
    apply inter_iff; split; eauto.
    + eapply map_iff; eauto.
    + eapply map_iff; eauto.
Qed.




Lemma add_incl
      (X : Type)
      `{OrderedType X}
      (x : X)
      (s t : ⦃X⦄)
  :
    {x; s} ⊆ t
    -> x ∈ t /\ s ⊆ t
.
Proof.
  intros.
  hnf; intros;
    split; rewrite <- H0;
      cset_tac.
Qed.



Lemma slp_union_incl
      (s t VD : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  :
    injective_on VD slot
    -> s ⊆ VD
    -> t ⊆ VD
    -> of_list Z ⊆ VD
    -> (s ∩ of_list Z) ∪ (map slot t ∩ map slot (of_list Z))
                      ⊆ of_list (slot_lift_params slot (s,t) Z)
.
Proof.
  intros inj_VD s_VD t_VD Z_VD.
  induction Z; simpl in *; eauto.
  - rewrite SetOperations.map_empty; eauto.
    cset_tac.
  - apply add_incl in Z_VD as [a_VD Z_VD].
    specialize (IHZ Z_VD).
    decide (a ∈ s ∩ t).
    + apply inter_iff in i as [a_s a_t].
      apply union_incl_split; simpl; eauto.
      * rewrite <- IHZ.
        clear; cset_tac.
      * rewrite lookup_set_add; eauto.
        rewrite <- IHZ.
        clear; cset_tac.
    + decide (a ∈ s).
      * assert (a ∉ t ∩ {a; of_list Z}) as an_tZ by cset_tac.
        assert (map slot t ∩ map slot {a; of_list Z}
                    ⊆ map slot t ∩ map slot (of_list Z)) as elim_a.
        {
          rewrite lookup_set_add; eauto.
          unfold lookup_set.
          assert (forall (u v : ⦃var⦄) (x : var),
                     u ∩ {x; v} ⊆ (u ∩ v) ∪ (u ∩ singleton x))
            as demo by (clear; cset_tac).
          rewrite demo.
          apply union_incl_split.
          - reflexivity.
          - rewrite <- map_singleton.
            rewrite <- injective_on_map_inter; eauto.
            + assert (t ∩ singleton a [=] ∅) as ta_empty by cset_tac.
              rewrite ta_empty.
              rewrite SetOperations.map_empty; eauto.
              clear; cset_tac.
            + clear - a_VD; cset_tac.
        }
        rewrite elim_a.
        simpl.
        rewrite <- IHZ.
        clear; cset_tac.
      * assert (a ∉ s ∩ {a; of_list Z}) as an_sZ by cset_tac.
        assert (s ∩ {a; of_list Z} ⊆ s ∩ (of_list Z)) as elim_a.
        {
          hnf; intros.
          decide (a0 = a).
          + subst a0. contradiction.
          + cset_tac.
        }
        rewrite elim_a; simpl.
        rewrite <- IHZ.
        rewrite lookup_set_add; eauto.
        clear; cset_tac.
Qed.


Lemma slp_union_minus_incl
      (s t VD : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  :
    injective_on VD slot
    -> s ⊆ VD
    -> t ⊆ VD
    -> of_list Z ⊆ VD
    -> (s ∪ map slot t) \ of_list (slot_lift_params slot (s,t) Z)
               ⊆ s \ of_list Z ∪ map slot t \ map slot (of_list Z)
.
Proof.
  intros.
  rewrite <- slp_union_incl with (s:=s); eauto.
  cset_tac.
Qed.



Lemma disj_incl
      (X : Type)
      `{OrderedType X}
      (D1 D1' D2 D2' : ⦃X⦄)
  :
    disj D1 D2
    -> D1' ⊆ D1
    -> D2' ⊆ D2
    -> disj D1' D2'
.
Proof.
  intros.
  eapply disj_1_incl; eauto.
  eapply disj_2_incl; eauto.
Qed.


Lemma renamedApart_incl
      (s : stmt)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    renamedApart s ra
    -> match ra with
      | ann1 (D, D') an
        => union_fs (getAnn an) ⊆ D ∪ D'
      | ann2 (D, D') ans ant
        => union_fs (getAnn ans) ⊆ D ∪ D'
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | annF (D, D') anF ant
        => (forall (ans : ann (⦃var⦄ * ⦃var⦄)) n,
              get anF n ans
              -> union_fs (getAnn ans) ⊆ D ∪ D')
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | _ => True
      end
.
Proof.
  intros.
  invc H; simpl; unfold union_fs; eauto.
  - invc H4.
    simpl.
    rewrite H7.
    rewrite H8.
    rewrite H3.
    clear; cset_tac.
  - invc H5; invc H6.
    simpl.
    rewrite H9.
    rewrite H10.
    rewrite H11.
    rewrite H12.
    rewrite <- H2.
    split; clear; cset_tac.
  - invc H5.
    split.
    + intros; inv_get.
      exploit H2; eauto.
      destruct H8 as [A [B [C E]]].
      rewrite A.
      rewrite <- H6.
      enough (snd (getAnn ans0) ∪ of_list (fst x) ⊆ list_union (defVars ⊜ F ans))
        as enouf.
      {
        rewrite union_assoc.
        rewrite union_comm.
        rewrite union_assoc.
        rewrite enouf.
        simpl.
        clear; cset_tac.
      }
      eapply incl_list_union.
      apply zip_get; eauto.
      rewrite union_comm.
      reflexivity.
    + rewrite H9.
      rewrite H10.
      rewrite <- H6.
      simpl.
      clear; cset_tac.
Qed.





Lemma x_VD
      (x : var)
      (VD D Ds D' : ⦃var⦄)
      (H9 : D' [=] {x; Ds})
      (ra_VD : D ∪ D' ⊆ VD)
  :
    x ∈ VD
.
Proof.
  rewrite H9 in ra_VD.
  rewrite <- incl_right in ra_VD.
  apply add_incl in ra_VD as [x_VD _].
  eauto.
Qed.


Lemma Rx_VD
      (x : var)
      (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD)
      (M_VD : M ⊆ VD)
      (Sp L K Kx : ⦃var⦄)
      (H13 : Sp ⊆ R)
      (H16 : L ⊆ Sp ∪ M)
      (x_VD : x ∈ VD)
  :
    {x; (R \ K ∪ L) \ Kx} ⊆ VD
.
Proof.
  apply incl_add_eq.
  split; eauto.
  rewrite H16.
  rewrite H13.
  cset_tac.
Qed.


Lemma R'_VD
      (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD)
      (M_VD : M ⊆ VD)
      (Sp L K : ⦃var⦄)
      (H16 : Sp ⊆ R)
      (H19 : L ⊆ Sp ∪ M)
  :
    R \ K ∪ L ⊆ VD
.
Proof.
  rewrite H19.
  rewrite H16.
  cset_tac.
Qed.




Lemma M'_VD
      (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD)
      (M_VD : M ⊆ VD)
      (Sp : ⦃var⦄)
      (H13 : Sp ⊆ R)
  :
    Sp ∪ M ⊆ VD
.
Proof.
  cset_tac.
Qed.



Lemma Rf_VD
      (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD)
      (M_VD : M ⊆ VD)
      (Sp L K R_f : ⦃var⦄)
      (Z0 : params)
      (H11 : Sp ⊆ R)
      (H12 : L ⊆ Sp ∪ M)
      (H18 : R_f \ of_list Z0 ⊆ R \ K ∪ L)
      (Z_VD : of_list Z0 ⊆ VD)
  :
    R_f ⊆ VD
.
Proof.
  assert (R_f ⊆ R \ K ∪ L ∪ of_list Z0) as H18'.
  {
    rewrite <- H18.
    clear; cset_tac.
  }
  rewrite H18'.
  rewrite H12.
  rewrite H11.
  cset_tac.
Qed.



Lemma Mf_VD
      (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD)
      (M_VD : M ⊆ VD)
      (Sp M_f : ⦃var⦄)
      (Z0 : params)
      (H11 : Sp ⊆ R)
      (H19 : M_f \ of_list Z0 ⊆ Sp ∪ M)
      (Z_VD : of_list Z0 ⊆ VD)
  :
    M_f ⊆ VD
.
Proof.
  assert (M_f ⊆ Sp ∪ M ∪ of_list Z0) as H19'.
  {
    rewrite <- H19.
    clear; cset_tac.
  }
  rewrite H19'.
  rewrite H11.
  clear - R_VD M_VD Z_VD; cset_tac.
Qed.


Lemma merge_app
      (ll1 ll2 : list (⦃var⦄ * ⦃var⦄))
       :
         merge (ll1 ++ ll2) = merge ll1 ++ merge ll2
.
Proof.
  unfold merge.
  rewrite map_app.
  reflexivity.
Qed.



Lemma getAnn_als_EQ_merge_rms
      (Lv : 〔⦃var⦄〕)
      (als : 〔ann ⦃var⦄〕)
      (Λ : 〔⦃var⦄ * ⦃var⦄〕)
      (pir2 : PIR2 Equal (merge Λ) Lv)
      (rms : 〔⦃var⦄ * ⦃var⦄〕)
      (H23 : merge rms = getAnn ⊝ als)
  :
    PIR2 Equal (merge rms ++ merge Λ) (getAnn ⊝ als ++ Lv)
.
Proof.
  rewrite H23.
  apply PIR2_app.
  -- apply PIR2_refl; eauto.
  -- eauto.
Qed.



Lemma get_ofl_VD
      (ZL : 〔params〕)
      (F : 〔params * stmt〕)
      (VD : ⦃var⦄)
      (Z_VD : forall (Z : params) (n : nat), get ZL n Z -> of_list Z ⊆ VD)
      (D D' Dt : ⦃var⦄)
      (ans : 〔ann (⦃var⦄ * ⦃var⦄)〕)
      (H6 : ❬F❭ = ❬ans❭)
      (H8 : Indexwise.indexwise_R (funConstr D Dt) F ans)
      (H13 : list_union (defVars ⊜ F ans) ∪ Dt [=] D')
      (ra_VD : D ∪ D' ⊆ VD)
  :
    forall (Z : params) (n : nat), get (fst ⊝ F ++ ZL) n Z -> of_list Z ⊆ VD
.
Proof.
  intros.
  decide (n < length F).
  -- apply get_in_range in l as [Zs get_Zs].
     assert (get_a := get_Zs).
     eapply get_length_eq in get_a as [a get_a];
       [ | apply H6].
     exploit H8 as fnCnstr; eauto.
     destruct fnCnstr as [fnCnstr _].

     assert (of_list (fst Zs) ⊆ fst (getAnn a)) as ofl.
     {
       clear - fnCnstr.
       apply eq_incl in fnCnstr as [fnCnstr _].
       rewrite <- fnCnstr.
       cset_tac.
     }
     assert (get_Zs' := get_Zs).
     eapply map_get_1 with (f:=fst) in get_Zs; eauto.
     eapply get_app with (L':=ZL) in get_Zs; eauto.
     eapply get_get_eq with (x':=Z) in get_Zs; eauto.
     subst Z.
     rewrite ofl, fnCnstr.
     rewrite <- ra_VD, <- H13.
     assert (of_list (fst Zs) ⊆ of_list (fst Zs) ∪ fst (getAnn a))
       as ofl' by (clear - ofl; cset_tac).
     assert (of_list (fst Zs) ⊆ list_union (defVars ⊜ F ans)) as ofl_def.
     {
       eapply incl_list_union.
       apply zip_get; eauto.
       unfold defVars.
       clear; cset_tac.
     }
     rewrite ofl_def.
     clear; cset_tac.
  -- apply not_lt in n0.
     rewrite <- map_length with (f:=fst) in n0.
     eapply get_app_right_ge with (L':=ZL) in n0; eauto.
Qed.


Lemma reconstr_live_small
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Lv : list ⦃var⦄)
      (s : stmt)
      (G R M VD: ⦃var⦄)
      (k : nat)
      (sl : spilling)
      (slot : var -> var)
      (al : ann ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    R ⊆ VD
    -> M ⊆ VD
    -> union_fs (getAnn ra) ⊆ VD
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> renamedApart s ra
    -> PIR2 Equal (merge Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> app_expfree s
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl al
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
            (do_spill slot s sl (mark_elements ⊜ ZL ((fun RM => fst RM ∩ snd RM) ⊝ Λ)))
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros R_VD M_VD ra_VD inj_VD VD_disj rena pir2 Z_VD aeFree lvSnd spillSnd spilli.

  unfold union_fs in ra_VD.
  assert (injective_on (getSp sl) slot)
    as inj_Sp.
  {
    eapply injective_on_incl; eauto.
    rewrite Sp_sub_RM; [ | eauto].
    clear - R_VD M_VD; cset_tac.
  }
  general induction lvSnd;
    inv rena;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    apply reconstr_live_small_s;
    eauto;
      intros G'; simpl;
        rewrite elements_empty;
        unfold clear_SpL;
        unfold setTopAnn;
        unfold count;
        simpl;
        rewrite empty_cardinal;
        simpl in *.
  - assert (x ∈ VD) as x_VD by (eapply x_VD; eauto).
    assert ({x; (R \ K ∪ L) \ Kx} ⊆ VD) as Rx_VD
        by (eapply Rx_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    erewrite IHlvSnd with (R:={x; (R \K ∪ L) \Kx})
                          (M:=Sp ∪ M)
                          (ra:=an)
                          (VD:=VD);
      eauto.
    + rewrite H19.
      clear; cset_tac.
    + apply renamedApart_incl in rena.
      rewrite rena.
      eauto.
    + eapply injective_on_incl with (D:=VD) ; eauto.
      rewrite Sp_sub_RM; [ | eauto].
      rewrite Rx_VD, M'_VD.
      clear; cset_tac.
  - assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    apply renamedApart_incl in rena as [rena1 rena2].
    rewrite IHlvSnd1 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M)
                          (ra:=ans)
                          (VD:=VD);
      eauto.
    + rewrite IHlvSnd2 with (R:=R \ K ∪ L)
                            (M:=Sp ∪ M)
                            (ra:=ant)
                            (VD:=VD);
        eauto.
      * rewrite H20.
        clear; cset_tac.
      * rewrite rena2. eauto.
      * eapply injective_on_incl with (D:=VD); eauto.
        rewrite Sp_sub_RM; [| eauto].
        rewrite R'_VD, M'_VD.
        clear; cset_tac.
    + rewrite rena1. eauto.
    + eapply injective_on_incl with (D:=VD); eauto.
      rewrite Sp_sub_RM; [| eauto].
      rewrite R'_VD, M'_VD.
      clear; cset_tac.
  - repeat apply union_incl_split.
    + apply incl_union_left.
      rewrite <- sla_list_union_EQ_extended_args.
      eapply lifted_args_in_RL_slot_SpM; eauto.
    + rewrite nth_rfmf; eauto.
      erewrite nth_zip; eauto.
      exploit Z_VD as Z_VD'; eauto.
      assert (R_f ⊆ VD) as Rf_VD
          by (eapply Rf_VD with (R:=R) (M:=M) (L:=L); eauto).
      assert (M_f ⊆ VD) as Mf_VD
          by (eapply Mf_VD with (R:=R) (M:=M); eauto).
      erewrite slp_union_minus_incl with (VD:=VD); eauto.
      rewrite H18.
      rewrite <- lookup_set_minus_eq; eauto; swap 1 2.
      {
        eapply injective_on_incl with (D:=VD); eauto.
        rewrite Z_VD', Mf_VD.
        clear; cset_tac.
      }
      rewrite lookup_set_incl; eauto.
      clear; cset_tac.
    + clear; cset_tac.
  - rewrite H9.
    clear; cset_tac.
  - rewrite fst_zip_pair; eauto with len.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    rewrite <- zip_app; eauto with len.
    apply union_incl_split.
    assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    + apply renamedApart_incl in rena as [renaF rena2].
      rewrite <- map_app.
      rewrite IHlvSnd with (R:=R\K ∪ L)
                           (M:=Sp ∪ M)
                           (ra:=ant)
                           (VD:=VD); eauto with len.
      * clear; cset_tac.
      * rewrite rena2.
        clear - ra_VD; cset_tac.
      * rewrite merge_app.
        apply getAnn_als_EQ_merge_rms; eauto.
      * clear - ra_VD H6 H8 H13 Z_VD.
        eapply get_ofl_VD; eauto.
      * eapply injective_on_incl with (D:=VD); eauto.
        rewrite Sp_sub_RM; [| eauto].
        rewrite R'_VD, M'_VD.
        clear; cset_tac.
    + clear; cset_tac.
Qed.
