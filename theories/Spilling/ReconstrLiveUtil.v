Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.
Require Import SpillSound DoSpill DoSpillRm SpillUtil ReconstrLive AnnP InVD SetUtil.
Require Import ToBeOutsourced.


Set Implicit Arguments.

(** * ReconstrLiveUtil *)

Definition reconstr_live_do_spill
           (slot : var -> var)
           (Λ : list (⦃var⦄ * ⦃var⦄))
           (ZL : list params)
           (G : ⦃var⦄)
           (s : stmt)
           (sl : spilling)
  : ann ⦃var⦄
  :=
    reconstr_live (slot_merge slot Λ)
                  ((slot_lift_params slot) ⊜ Λ ZL)
                  G
                  (do_spill slot s sl (compute_ib ⊜ ZL Λ))
                  (do_spill_rm slot sl)
.

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
  - rewrite map_empty; eauto. cset_tac.
  - apply add_incl in Z_VD as [a_VD Z_VD].
    specialize (IHZ Z_VD).
    decide (a ∈ s ∩ t).
    + apply inter_iff in i as [a_s a_t].
      apply union_incl_split; simpl; eauto.
      * rewrite <- IHZ.
        clear; cset_tac.
      * rewrite lookup_set_add; eauto.
        rewrite <- IHZ. unfold lookup_set.
        clear; cset_tac.
    + decide (a ∈ s).
      * assert (a ∉ t ∩ {a; of_list Z}) as an_tZ by cset_tac.
        assert (map slot t ∩ map slot {a; of_list Z}
                    ⊆ map slot t ∩ map slot (of_list Z)) as elim_a. {
          rewrite lookup_set_add; eauto.
          unfold lookup_set.
          assert (forall (u v : ⦃var⦄) (x : var),
                     u ∩ {x; v} ⊆ (u ∩ v) ∪ (u ∩ singleton x))
            as demo by (clear; cset_tac).
          rewrite demo. apply union_incl_split.
          - reflexivity.
          - rewrite <- map_singleton.
            rewrite <- injective_on_map_inter; eauto.
            + assert (t ∩ singleton a [=] ∅) as ta_empty by cset_tac.
              rewrite ta_empty.
              rewrite map_empty; eauto.
              clear; cset_tac.
            + clear - a_VD; cset_tac.
        }
        rewrite elim_a.
        simpl.
        rewrite <- IHZ.
        clear; cset_tac.
      * assert (a ∉ s ∩ {a; of_list Z}) as an_sZ by cset_tac.
        assert (s ∩ {a; of_list Z} ⊆ s ∩ (of_list Z)) as elim_a. {
          hnf; intros. decide (a0 = a).
          + subst a0. contradiction.
          + cset_tac'. destruct H1; eauto.
        }
        rewrite elim_a; simpl.
        rewrite <- IHZ.
        rewrite lookup_set_add; eauto. unfold lookup_set.
        clear; cset_tac.
Qed.


Lemma slp_union_minus_incl
      (s t VD : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  : injective_on VD slot
    -> s ⊆ VD
    -> t ⊆ VD
    -> of_list Z ⊆ VD
    -> (s ∪ map slot t) \ of_list (slot_lift_params slot (s,t) Z)
               ⊆ s \ of_list Z ∪ map slot t \ map slot (of_list Z)
.
Proof.
  intros.
  rewrite <- slp_union_incl with (s:=s); eauto.
  unfold lookup_set. cset_tac'; eauto 20 with cset.
Qed.




(* this should be generalized *)
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
  : forall (Z : params) (n : nat), get (fst ⊝ F ++ ZL) n Z -> of_list Z ⊆ VD.
Proof.
  intros.
  decide (n < length F).
  -- apply get_in_range in l as [Zs get_Zs].
     assert (get_a := get_Zs).
     eapply get_length_eq in get_a as [a get_a];
       [ | apply H6].
     exploit H8 as fnCnstr; eauto.
     destruct fnCnstr as [fnCnstr _].

     assert (of_list (fst Zs) ⊆ fst (getAnn a)) as ofl. {
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
     assert (of_list (fst Zs) ⊆ list_union (defVars ⊜ F ans)) as ofl_def. {
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

Lemma lifted_args_in_RL_slot_SpM
      (Y : args)
      (R M : ⦃var⦄)
      (slot : var -> var)
      (H5 : forall (n : nat) (y : op), get Y n y -> isVar y)
      (Sp L K M' : ⦃var⦄)
      (H21 : list_union (Op.freeVars ⊝ Y) ⊆ (R \ K ∪ L) ∪ M')
      (H22 : M' ⊆ Sp ∪ M)
  : list_union (Op.freeVars ⊝ slot_lift_args slot M' ⊝ Y) ⊆ R ∪ L ∪ map slot (Sp ∪ M) .
Proof.
  apply list_union_incl.
  intros; inv_get.
  unfold slot_lift_args.
  exploit H5; eauto.
  destruct x0;
    isabsurd.
  * decide (n0 ∈ M'); simpl.
    -- rewrite <- map_singleton.
       apply incl_union_right.
       apply lookup_set_incl; eauto.
       revert H22. revert i.
       clear; cset_tac.
    -- apply incl_singleton.
       eapply get_live_op_sound in H21; eauto.
       inv H21.
       revert H2. revert n1.
       clear; cset_tac.
  * clear; cset_tac.
Qed.


Lemma nth_rfmf
      (l : lab)
      (Λ : 〔⦃var⦄ * ⦃var⦄〕)
      (slot : var -> var)
      (R_f M_f : ⦃var⦄)
      (H15 : get Λ (counted l) (R_f, M_f))
  : nth (counted l) (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f .
Proof.
  eapply get_nth with (d:=(∅,∅)) in H15 as H15'.
  simpl in H15'.
  assert ((fun RM
           => fst RM ∪ map slot (snd RM)) (nth l Λ (∅,∅))
          = (fun RM
             => fst RM ∪ map slot (snd RM)) (R_f,M_f))
    as H_sms. {
    f_equal; simpl; [ | f_equal];
      rewrite H15'; simpl; eauto.
  }
  unfold slot_merge.
  rewrite <- map_nth in H_sms.
  simpl in H_sms.
  assert (l < length ((fun RM : ⦃var⦄ * ⦃var⦄
                       => fst RM ∪ map slot (snd RM)) ⊝ Λ))
    as l_len. {
    apply get_length in H15.
    clear - H15; eauto with len.
  }
  assert (nth l ((fun RM : ⦃var⦄ * ⦃var⦄
                  => fst RM ∪ map slot (snd RM)) ⊝ Λ) ∅
          = R_f ∪ map slot M_f)
    as H_sms'. {
    rewrite nth_indep with (d':=∅ ∪ map slot ∅).
    * exact H_sms.
    * eauto with len.
  }
  simpl.
  rewrite H_sms'.
  reflexivity.
Qed.

Lemma sla_list_union_EQ_extended_args
      (slot : var -> var)
      (Sl : ⦃var⦄)
      (Y : args)
      (ib : list bool)

  : list_union (Op.freeVars ⊝ slot_lift_args slot Sl ⊝ Y)
               [=] list_union (Op.freeVars ⊝ slot_lift_args slot Sl
                                           ⊝ (extend_args Y ib)).
Proof.
  apply list_union_elem_eq_ext.
  eapply elem_eq_map. intuition.
  apply slot_lift_args_elem_eq_ext.
  apply extend_args_elem_eq_ext.
Qed.



(* utils for reconstr_live_sound *)



Lemma al_sub_RfMf
      (als : list (ann ⦃var⦄))
      (rms : list (⦃var⦄ * ⦃var⦄))
      (al : ann ⦃var⦄)
      (R M : ⦃var⦄)
      (n : nat)
  : get rms n (R,M)
    -> get als n al
    -> PIR2 Equal (merge ⊝ rms) (getAnn ⊝ als)
    -> getAnn al ⊆ R ∪ M.
Proof.
  intros get_rm get_al H16.
  general induction get_rm;
    try invc get_al; invc H16;
      unfold merge in *; simpl in *; eauto.
  rewrite pf; eauto.
Qed.

Lemma al_eq_RfMf

      (als : list (ann ⦃var⦄))
      (rms : list (⦃var⦄ * ⦃var⦄))
      (al : ann ⦃var⦄)
      (R M : ⦃var⦄)
      (n : nat)
  : get rms n (R,M)
    -> get als n al
    -> merge ⊝ rms = getAnn ⊝ als
    -> getAnn al [=] R ∪ M .
Proof.
  intros get_rm get_al H16.
  general induction get_rm;
    try invc get_al; invc H16;
      simpl in *; eauto.
Qed.


Lemma ofl_slp_sub_rm
      (al : ann ⦃var⦄)
      (R M : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  : getAnn al ⊆ R ∪ M
    -> of_list Z ⊆ getAnn al
    -> of_list (slot_lift_params slot (R,M) Z) ⊆ R ∪ map slot M .
Proof.
  intros ofl_in_rm H2'.
  rewrite <- H2' in ofl_in_rm.
  induction Z;
    simpl in *; eauto.
  - clear; cset_tac.
  - assert (of_list Z ⊆ getAnn al) as ofl_al
        by (rewrite <- H2'; clear; cset_tac).
    assert (of_list Z ⊆ R ∪ M) as ofl_rm
        by (rewrite <- ofl_in_rm; clear; cset_tac).
    assert (a ∈ M -> slot a ∈ map slot M)
      as slot_a_in. {
      intro a_in.
      apply in_singleton.
      rewrite <- map_singleton.
      apply lookup_set_incl; eauto.
      apply incl_singleton; eauto.
    }
    specialize (IHZ ofl_rm ofl_al).
    decide (a ∈ R ∩ M); simpl.
    + apply inter_iff in i as [a_fst a_snd].
      rewrite IHZ.
      apply slot_a_in in a_snd.
      clear - a_fst a_snd; cset_tac.
    + decide (a ∈ R); simpl.
      * rewrite IHZ.
        clear - i; cset_tac.
      * rewrite add_union_singleton in ofl_in_rm.
        eapply union_incl_split2 in ofl_in_rm as [ofl_in_rm _].
        eapply in_singleton in ofl_in_rm.
        assert (a ∈ M) as a_in
            by (clear - ofl_in_rm n0; cset_tac).
        apply slot_a_in in a_in.
        rewrite IHZ.
        clear - a_in; cset_tac.
Qed.

Lemma nth_mark_elements
      (l : lab)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (rm : ⦃var⦄ * ⦃var⦄)
      (Z : params)
  :
    get ZL l Z
    -> get Λ l rm
    -> nth l (mark_elements ⊜ ZL ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) ⊝ Λ)) nil
      = mark_elements Z ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) rm)
.
Proof.
  intros get_Z get_rm.
  apply get_nth.
  eapply zip_get; eauto.
  eapply map_get_eq; eauto.
Qed.





Lemma sla_extargs_slp_length
      (slot : var -> var)
      (R_f M_f Sl : ⦃var⦄)
      (ZL : list params)
      (Z : params)
      (l : lab)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Y : args)
  :
    length Y = length Z
    -> ❬slot_lift_args slot Sl
                      ⊝ extend_args Y
                      (mark_elements Z ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) (R_f,M_f)))❭
      = ❬slot_lift_params slot (R_f, M_f) Z❭
.
Proof.
  intros H2.
  unfold slot_lift_params.
  rewrite !map_length.
  general induction Z; inv H2;
    simpl; eauto.
  - apply length_zero_iff_nil in H2.
    rewrite H2.
    eauto with len.
  - fold slot_lift_params.
    fold slot_lift_params in IHZ.
    destruct Y; isabsurd.
    simpl.
    decide (a ∈ R_f ∩ M_f);
      unfold extend_args;
      simpl; eauto.
    decide (a ∈ R_f);
      simpl; eauto.
Qed.


Lemma get_Y_from_extargs
      (Y : args)
      (ib : list bool)
      (y : op)
      (n : nat)
  :
    get (extend_args Y ib) n y
    -> exists n', get Y n' y
.
Proof.
  intros get_ext.

  general induction get_ext;
    destruct Y;
    destruct ib;
    simpl; isabsurd; eauto.
  - exists 0.
    invc Heql.
    econstructor; eauto.
  - exists 0.
    invc Heql.
    destruct b; simpl in H0; invc H0;
      econstructor; eauto.
  - exists (S n).
    invc Heql.
    econstructor; eauto.
  - destruct b; simpl in *.
    + specialize (IHget_ext (o :: Y) (false :: ib)).
      simpl in IHget_ext.
      invc Heql.
      apply IHget_ext; eauto.
    + specialize (IHget_ext Y ib).
      invc Heql.
      assert (extend_args Y ib = extend_args Y ib)
        as refl by reflexivity.
      apply IHget_ext in refl as [n0 get_x].
      exists (S n0).
      econstructor; eauto.
Qed.
