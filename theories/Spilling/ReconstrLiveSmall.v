Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
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
  :
    getL sl ⊆ getSp sl ∪ M
    -> of_list ys ⊆ getL sl
    -> R' [=] R ∪ getL sl \ of_list ys
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live 
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) G'
                (do_spill slot s (clear_SpL sl))
                (do_spill_rm slot (clear_SpL sl))
             )
             ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G'
       )
    -> getAnn
         (reconstr_live 
            (slot_merge slot Λ)
            (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) G
            (write_loads slot ys
                         (do_spill slot s (clear_SpL sl))
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
  :
    getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_SpL sl))
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s (clear_Sp sl))
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
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> of_list xs ⊆ getSp sl
    -> M' [=] getSp sl \ of_list xs ∪ M
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live 
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) G'
                (write_loads slot (elements (getL sl))
                             (do_spill slot s (clear_SpL sl))
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
            (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) G
            (write_spills slot xs 
                          (write_loads slot (elements (getL sl))
                                       (do_spill slot s (clear_SpL sl))
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
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_Sp sl))
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s sl)
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
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_SpL sl))
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s sl)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros slot_inj Sp_sub L_sub base.
  apply reconstr_live_small_Sp; eauto.
  intros G''.
  apply reconstr_live_small_L; eauto.
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


Lemma inj_renamedApart_ann_P
      (s : stmt)
      (ra : ann (⦃var⦄ * ⦃var⦄))
      (f : var -> var)
  :
      renamedApart s ra
      -> injective_on (fst (getAnn ra) ∪ snd (getAnn ra)) f
      -> ann_P (fun (a : ⦃var⦄ * ⦃var⦄) 
                => injective_on (fst a ∪ snd a) f) ra
. 
Proof.
  intros rena inj.
  induction rena;
    simpl in *; eauto.
  - econstructor; eauto.
    apply IHrena.
    eapply injective_on_incl; eauto.
    rewrite H1.
    unfold pe in H2.
    invc H2. 
    rewrite H6.
    rewrite H7.
    simpl.
    clear; cset_tac.
  - econstructor; eauto.
    + apply IHrena1; eauto.
      eapply injective_on_incl; eauto.
      invc H2.
      simpl.
      rewrite H7.
      rewrite H8.
      rewrite <- H1.
      clear; cset_tac.
    + apply IHrena2; eauto.
      eapply injective_on_incl; eauto.
      invc H3.
      simpl.
      rewrite H7.
      rewrite H8.
      rewrite <- H1.
      clear; cset_tac.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    + intros; inv_get.
      eapply H1; eauto.
      eapply injective_on_incl; eauto.
      unfold Indexwise.indexwise_R in H2.
      exploit H2; eauto.
      unfold funConstr in H8.
      destruct H8 as [fst_of [ uni [ disj_D disj_Dt]]].
      rewrite fst_of.
      rewrite <- H5.
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
    + invc H4.
      apply IHrena.
      eapply injective_on_incl; eauto.
      rewrite <- H6.
      rewrite H9.
      rewrite H10.
      simpl.
      rewrite <- H5.
      clear; cset_tac.
Qed.

Definition union_fs
           (a : ⦃var⦄ * ⦃var⦄)
  : ⦃var⦄
  :=
    fst a ∪ snd a
.

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
    eapply disj_1_incl;
      [ eapply disj_2_incl | ];
      eauto.
    Focus 2.
    unfold union_fs.
    simpl.
Admitted.
(*
Lemma inj_substmt
      (ra : ann (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (f : var -> var)
:
  let getDD := fun ra' => fst (getAnn ra') ∪ snd (getAnn ra') in
  renamedApart s ra
  -> injective_on (getDD ra) f
  -> match ra with 
     | (ann1 _ ra')
       => injective_on (getDD ra') f
     | (ann2 _ ra1 ra2)
       => injective_on (getDD ra1) f /\ injective_on (getDD ra2) f
     | (annF _ raF ra2)
       => injective_on (getDD ra2) f
       /\ forall n ra', get raF n ra' 
                        -> injective_on (getDD ra') f
     | _ => True
     end
.


Proof.
  intros getDD rena inj_f.
  induction rena; eauto.
  - apply injective_on_incl with (D:=getDD (ann1 (D,D') an)); eauto.
    unfold getDD.
    simpl.
*)




Lemma reconstr_live_small
      ZL Λ Lv s G k R M sl slot al ra
  :
    let DD := fst (getAnn ra) ∪ snd (getAnn ra) in
    injective_on DD slot
    -> disj DD (map slot DD)
    -> renamedApart s ra
    -> PIR2 Equal Lv (merge Λ)
    -> app_expfree s
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live sl al
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s sl)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros DD inj_slot DD_disj rena pir2 aeFree lvSnd spillSnd spilli.
  eapply inj_renamedApart_ann_P in inj_slot; eauto.
  eapply disj_renamedApart_ann_P in DD_disj; eauto.
  assert (injective_on (getSp sl) slot) 
    as inj_R by admit.
  (*eapply inj_substmt in rena as inj_sub; eauto.*)
  general induction lvSnd;
    invc rena;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    invc inj_slot;
    invc DD_disj;
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
  - erewrite IHlvSnd with (R:={x; (R \K ∪ L) \Kx}) 
                          (M:=Sp ∪ M)
                          (ra:=an);
      eauto.
    + rewrite H19.
      clear; cset_tac.
    + eapply injective_on_incl with (D:=DD); eauto.
      subst DD.
      admit.
  - rewrite IHlvSnd1 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M)
                          (ra:=ans);
      eauto.
    + rewrite IHlvSnd2 with (R:=R \ K ∪ L)
                            (M:=Sp ∪ M)
                            (ra:=ant);
        eauto.
      rewrite H20.
      clear; cset_tac.
      * admit.
    + admit.
  - repeat apply union_incl_split.
    + apply incl_union_left.
      eapply lifted_args_in_RL_slot_SpM; eauto.
    + rewrite nth_rfmf; eauto.
      assert (of_list 
                (nth l (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) nil)
                [=] of_list (slot_lift_params slot M_f Z0)).
      {
        erewrite nth_zip; eauto.
        reflexivity.
      }
      rewrite H4.
(*
      assert ((R_f ∪ map slot M_f) 
                \ of_list (slot_lift_params slot M_f Z0)
           ⊆ R_f \ of_list Z0 ∪ map slot M_f \ map slot (of_list Z0)).
      { 


assert (of_list Z0 \ M_f ∪ map slot (of_list Z0 ∩ M_f)
        ⊆ of_list (slot_lift_params slot M_f Z0)).
      { clear - inj_slot.
        - apply union_incl_split.
          + hnf.
            intros a a_in.
            apply diff_iff in a_in as [a_in a_out].
            apply of_list_1 in a_in.
            induction a_in; simpl.
            * rewrite H.
              rewrite H in a_out.
              decide (y ∈ M_f); simpl; eauto with cset.
            * cset_tac.
          + hnf.
            intros a a_in.
            assert (forall s t : ⦃var⦄,
                       map slot (s ∩ t) [=] map slot s ∩ map slot t)
                   as injective_set_inter.
            {
              clear - inj_slot.
              intros s t a.
              split; intros a_in.
              - apply map_iff in a_in as [b [b_in b_eq]]; eauto.
                rewrite b_eq.
                apply inter_iff.
                apply inter_iff in b_in as [bs bt].
                split; apply map_1; eauto.
              - apply inter_iff in a_in.
                destruct a_in as [a_s a_t].
                apply map_iff in a_s as [b [b_in b_eq]]; eauto.
                apply map_iff in a_t as [b' [b'_in b'_eq]]; eauto.
                rewrite b_eq in b'_eq.
                apply inj_slot in b'_eq; [ | admit | admit].
                rewrite <- b'_eq in b'_in.
                rewrite b_eq.
                apply map_1; eauto.
                cset_tac.
            }   
            apply injective_set_inter in a_in.
            unfold slot_lift_params.
            general induction Z0; simpl; eauto.
            admit. 
        }
      rewrite <- H7.
      assert (forall s t u : ⦃var⦄,
                 (s ∪ t) \ u [=] s \ u ∪ t \ u) by cset_tac.
      rewrite H9.
      apply union_incl_split.
      + clear; cset_tac.
        admit. 
      + admit.
      }
      rewrite H7.
      rewrite H18.
      eapply lookup_set_incl with (m:=slot) in H19; eauto.
      unfold lookup_set in H19.
      rewrite injective_map_minus in H19; eauto; [ | admit | admit ].
      rewrite H19.
      clear; cset_tac.*)
      admit.
    + clear; cset_tac.
  - rewrite H9.
    clear; cset_tac.
  - rewrite fst_zip_pair; eauto with len.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    rewrite <- map_app.
    apply union_incl_split.
    + rewrite IHlvSnd with (ra:=ant); eauto with len.
      * clear; cset_tac.
      * admit.
      * admit.
    + clear; cset_tac.

Qed.
    + c
      assert (of_list (slot_lift_params slot M_f Z0)
              [=] of_list Z0 \ M_f ∪ map slot (of_list Z0 ∩ M_f)).
      { clear - inj_slot.
        apply set_incl.
        - apply union_incl_split.
          + hnf.
            intros a a_in.
            apply diff_iff in a_in as [a_in a_out].
            apply of_list_1 in a_in.
            induction a_in; simpl.
            * rewrite H.
              rewrite H in a_out.
              decide (y ∈ M_f); simpl; eauto with cset.
            * cset_tac.
          + hnf.
            intros a a_in.
            assert (forall s t : ⦃var⦄,
                       map slot (s ∩ t) [=] map slot s ∩ map slot t)
                   as injective_set_inter.
            {
              clear - inj_slot.
              intros s t a.
              split; intros a_in.
              - apply map_iff in a_in as [b [b_in b_eq]]; eauto.
                rewrite b_eq.
                apply inter_iff.
                apply inter_iff in b_in as [bs bt].
                split; apply map_1; eauto.
              - apply inter_iff in a_in.
                destruct a_in as [a_s a_t].
                apply map_iff in a_s as [b [b_in b_eq]]; eauto.
                apply map_iff in a_t as [b' [b'_in b'_eq]]; eauto.
                rewrite b_eq in b'_eq.
                apply inj_slot in b'_eq; [ | admit | admit].
                rewrite <- b'_eq in b'_in.
                rewrite b_eq.
                apply map_1; eauto.
                cset_tac.
            }   
            apply injective_set_inter in a_in.
            unfold slot_lift_params.
            general induction Z0; simpl; eauto.
            admit. 
        - admit.
      }
      rewrite H7.

      assert (forall s t : ⦃var⦄,
                       map slot (s ∩ t) [=] map slot s ∩ map slot t)
                   as injective_set_inter by admit.
      rewrite injective_set_inter.
      assert ((R_f ∪ map slot M_f)
        \ (of_list Z0 \ M_f ∪ (map slot (of_list Z0) ∩ map slot M_f))
        ⊆ R_f \ of_list Z0 ∪ map slot M_f \ map slot (of_list Z0)).
      {
        clear; cset_tac.
      }

            apply of_list_1 in a_in.
            inv a_in.
            * isabsurd.
            * decide (a0 ∈ M_f); simpl.
              -- isabsurd.
              -- 
            unfold slot_lift_params.
          
      rewrite SetOperations.map_app; eauto.
      clear - H18 H19.
      eapply lookup_set_incl with (m:=slot) in H19; eauto.
      rewrite lookup_set_minus_eq in H19; eauto.
      rewrite <- SetOperations.map_app; eauto.
      rewrite <- H19.
      assert ((R_f ∪ map slot M_f) 
                \ of_list (slot_lift_params slot M_f Z0)
                ⊆ R_f \ of_list Z0 
                ∪ map slot M_f \ map slot (of_list Z0)).
      { 
        clear.
        unfold slot_lift_params.
        hnf.
        intros a a_in.
        apply diff_iff in a_in as [a_in a_out].
        assert (forall b, 
                   b ∈ of_list ((fun z => if [z ∈ M_f] 
                                          then slot z
                                          else z) ⊝ Z0)
                   -> b <> a).
        {
          intros b b_in N.
          apply a_out.
          rewrite <- N.
          exact b_in.
        }
        apply union_iff.
        apply union_iff in a_in as [a_in | a_in].
        - left.
          apply diff_iff.
          split; eauto.
          intro N; apply a_out.
          
        
        rewrite of_list_elements.
        rewrite map_slot_cut.
        simpl.
        cset_tac. }
      rewrite H.
      rewrite H16.
      rewrite H17.
      rewrite SetOperations.map_app; eauto.
      clear.
      cset_tac.
    + clear. cset_tac.
  - rewrite H7.
    cset_tac.
  - rewrite fst_F; eauto.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    rewrite IHlvSnd with (R:=R \ K ∪ L) (M:=Sp ∪ M); eauto.
    + clear. cset_tac.
    + unfold merge.
      unfold merge in H7.
      rewrite <- H7.
      rewrite map_app.
      apply PIR2_app.
      * apply PIR2_refl; eauto.
      * unfold merge in pir2.
        eauto.

Admitted.
