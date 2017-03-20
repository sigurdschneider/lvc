Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.



Set Implicit Arguments.

(** * Register Liveness *)

Fixpoint reg_live 
         (ZL : list params)
         (Lv : list ⦃var⦄)
         (G : ⦃var⦄)
         (s : stmt)
         (sl : spilling)
         {struct s}
  : ann ⦃var⦄
  :=
    match s, sl with
    | stmtLet x e s, ann1 (Sp, L, _) sl'
      => let lv_s := reg_live ZL Lv (singleton x) s sl' in
        (* subtracting L might lead to unnecessary gaps in the liveness, but this is ok:
           variables are killed from the register directly after their last use *)
        ann1 (G ∪ Sp ∪ (((getAnn lv_s) \ singleton x ∪ Exp.freeVars e) \ L)) lv_s

    | stmtReturn e, ann0 (Sp, L, _)
      => ann0 (G ∪ Sp ∪ (Op.freeVars e \ L))

    | stmtIf e s1 s2, ann2 (Sp, L, _) sl1 sl2
      => let lv1 := reg_live ZL Lv ∅ s1 sl1 in
        let lv2 := reg_live ZL Lv ∅ s2 sl2 in
        ann2 (G ∪ Sp ∪ ((getAnn lv1 ∪ getAnn lv2 ∪ Op.freeVars e) \ L)) lv1 lv2

    | stmtApp f Y, ann0 (Sp, L, (_,Sl)::nil)
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (G ∪ Sp ∪ (((list_union (Op.freeVars ⊝ Y) \ Sl) ∪ blv \ of_list Z) \ L))

    | stmtFun F t, annF (Sp, L, rms) sl_F sl_t
      => let lv_t := reg_live (fst ⊝ F ++ ZL) (fst ⊝ rms ++ Lv) ∅ t sl_t in
        let lv_F := (fun ps sl_s => reg_live (fst ⊝ F   ++ ZL)
                                          (fst ⊝ rms ++ Lv)
                                          (of_list (fst ps))
                                          (snd ps)
                                           sl_s
                    ) ⊜ F sl_F in
        annF (G ∪ Sp ∪ ((getAnn lv_t ∪ G) \ L)) lv_F lv_t

    | _,_ => ann0 G
    end
.



Inductive rlive_sound
  : list params -> list (set var) -> stmt -> spilling -> ann (set var) -> Prop :=
| RLiveLet ZL Lv x e s Sp L sl lv (al:ann (set var))
  :  Sp ⊆ lv
     -> rlive_sound ZL Lv s sl al
     -> live_exp_sound e (lv ∪ L)
     -> (getAnn al \ singleton x) ⊆ lv ∪ L
     -> x ∈ getAnn al
     -> rlive_sound ZL Lv (stmtLet x e s) (ann1 (Sp,L,nil) sl) (ann1 lv al)
| RLiveIf Lv ZL e s1 s2 Sp L sl1 sl2 lv al1 al2
  :  Sp ⊆ lv
     -> rlive_sound ZL Lv s1 sl1 al1
     -> rlive_sound ZL Lv s2 sl2 al2
     -> live_op_sound e (lv ∪ L)
     -> getAnn al1 ⊆ lv ∪ L
     -> getAnn al2 ⊆ lv ∪ L
     -> rlive_sound ZL Lv (stmtIf e s1 s2) (ann2 (Sp,L,nil) sl1 sl2) (ann2 lv al1 al2)
| RLiveApp ZL Lv l Y Sp L R' M' lv blv Z
  : Sp ⊆ lv
    -> get ZL (counted l) Z
    -> get Lv (counted l) blv
    -> (blv \ of_list Z) ⊆ lv ∪ L
    -> (forall n y, get Y n y -> live_op_sound y (lv ∪ M' ∪ L))
    -> rlive_sound ZL Lv (stmtApp l Y) (ann0 (Sp,L,(R',M')::nil)) (ann0 lv)
| RLiveReturn ZL Lv e Sp L lv
  : Sp ⊆ lv
    -> live_op_sound e (lv ∪ L)
    -> rlive_sound ZL Lv (stmtReturn e) (ann0 (Sp,L,nil)) (ann0 lv)
| RLiveFun ZL Lv F t lv Sp L rms sl_F sl_t als alb
  : Sp ⊆ lv
    -> rlive_sound (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t sl_t alb
    -> (forall n Zs a sl_s, get F n Zs ->
                 get als n a ->
                 get sl_F n sl_s ->
                 rlive_sound (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) sl_s a)
    -> (forall n Zs a, get F n Zs -> (* do I need this? *)
                 get als n a ->
                 (of_list (fst Zs)) ⊆ getAnn a (* don't add L here *)
                 /\ NoDupA eq (fst Zs))
    -> getAnn alb ⊆ lv ∪ L
    -> rlive_sound ZL Lv (stmtFun F t) (annF (Sp,L,rms) sl_F sl_t) (annF lv als alb)
.


Lemma reg_live_G_eq
      (G : ⦃var⦄)
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (s : stmt)
      (sl : spilling)
  :
    getAnn (reg_live ZL Lv G s sl)
           [=]
           getAnn (reg_live ZL Lv ∅ s sl) ∪ G
.
Proof.
  general induction s;
    destruct sl;
    try destruct a;
    try destruct p;
    simpl; eauto; try cset_tac.
  induction l0; simpl; eauto.
  - cset_tac.
  - destruct a. destruct l0; simpl; cset_tac. 
Qed.



(* remove ? 
Lemma reconstr_live_remove_G
      Lv ZL G s sl G'
  :
    getAnn (reconstr_live Lv ZL G s sl) \ G
           ⊆ getAnn (reconstr_live Lv ZL G' s sl)
.
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.
*)



Lemma reg_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (G : set var)
      (s : stmt)
      (sl : spilling)
  :
    G ⊆ getAnn (reg_live ZL Lv G s sl)
.
Proof.
  induction s,sl; destruct a,p;
    simpl; eauto with cset.
  - simpl. induction l0; simpl; eauto with cset.
    destruct a,l0; simpl; cset_tac.
Qed.

Require Import Subterm.

Inductive subAnno (X:Type) : ann X -> ann X -> Prop :=
    subAnno_refl (a : ann X) : subAnno a a
  | subAnno1 (a b : ann X) (x : X) :
      subAnno a b -> subAnno a (ann1 x b)
  | subAnno21 (a b b' : ann X) (x : X) :
      subAnno a b -> subAnno a (ann2 x b b')
  | subAnno22 (a b b' : ann X) (x : X) :
      subAnno a b'-> subAnno a (ann2 x b b')
  | subAnnoF1 (a b : ann X) (bF : list (ann X)) (x : X) :
      subAnno a b -> subAnno a (annF x bF b)
  | subAnnoF2 (a b b' : ann X) (bF : list (ann X)) (x : X) (n : nat) :
      get bF n b' -> subAnno a b' -> subAnno a (annF x bF b)
.



Lemma reg_live_sound k ZL Λ rlv (R M : ⦃var⦄) G s sl
  : spill_sound k ZL Λ (R,M) s sl
    -> (forall s' sl',
          subTerm s' s
          -> subAnno sl' sl
          -> match s',sl' with
            | stmtFun F t, annF (_,rms) sl_F _ =>
              forall Zs sl_s rm' n, get rlv n rm'
                              -> get F n Zs
                              -> get sl_F n sl_s
                              -> rm' = getAnn (reg_live ZL rlv ∅ (snd Zs) sl_s)
            | _,_ => True
            end)
    -> PIR2 Subset rlv (fst ⊝ Λ) 
    -> rlive_sound ZL rlv s sl (reg_live ZL rlv G s sl)
.
Proof.
  intros spillSnd inR.
  general induction spillSnd.
  - econstructor.
    + apply union_incl_left; clear;cset_tac.
    + eapply IHspillSnd; eauto.
      intros; apply inR; econstructor; eauto.
    + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      * apply live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear;cset_tac.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + apply reg_live_G. clear; cset_tac.
  - econstructor.
    + clear; cset_tac.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.
  - econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + eapply IHspillSnd1; eauto.
      intros; apply inR; econstructor; eauto.
    + eapply IHspillSnd2; eauto.
      intros; apply inR; econstructor 4; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
  - assert (H8' := H8). eapply PIR2_flip in H8'. eapply PIR2_nth in H8'.
    destruct H8', H9.
    econstructor; eauto.
    + clear; cset_tac.
    + simpl. erewrite !get_nth; eauto. clear; cset_tac.
    + intros. inv_get.
      apply live_op_sound_incl with (lv':=Op.freeVars y).
      * apply Op.live_freeVars.
      * erewrite !get_nth; eauto. 
        erewrite <-incl_list_union with (s:=Op.freeVars y); eauto; clear; cset_tac.
    + eauto.
  - econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + admit.
    + intros; inv_get. admit.
    + intros; inv_get. split. admit. (* THIS will most likely need another invariant *) admit.
    + clear; cset_tac.

      
    
11:00 - 17:00 + 18:00 -
      
############################################################################################
############################################################################################
PROOF of reconstrlv:########################################################################
############################################################################################
############################################################################################

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.
    eapply get_get_eq in H; eauto.
    subst Z0.

    econstructor; eauto.
    + eapply zip_get; eauto.
    + simpl.
      unfold slot_merge.
      eapply map_get_eq; eauto.
    + simpl.
      assert (nth (labN l) (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f)
        as nth_EQ.
      {
        unfold slot_merge.
        assert ((fun RM => fst RM ∪ map slot (snd RM)) (R_f,M_f) = R_f ∪ map slot M_f)
          by (simpl; reflexivity).
        eapply map_get_eq in H13; eauto.
        erewrite get_nth; eauto.
        reflexivity.
      }
      rewrite nth_EQ.
      assert (of_list (nth (labN l) (slot_lift_params slot ⊜ Λ ZL) nil)
              [=] of_list (slot_lift_params slot (R_f,M_f) Z))
        as nth_slp by (erewrite nth_zip; eauto; simpl; reflexivity).
      rewrite nth_slp.
      clear; cset_tac.
    + unfold compute_ib.
      erewrite nth_zip; eauto.
      apply sla_extargs_slp_length; eauto.
    + intros; inv_get.
      erewrite nth_zip; eauto.
      erewrite nth_zip in H; eauto.
      assert (get_x := H).
      eapply get_Y_from_extargs in get_x as [n' get_x].
      exploit H5 as is_var; eauto.
      invc is_var.
      apply live_op_sound_incl
      with (lv':= match slot_lift_args slot M' (Var v) with
                  | Var v => singleton v
                  | _ => ∅
                  end
           );
        unfold slot_lift_args;
        simpl.
      * decide (v ∈ M');
          econstructor;
          eauto with cset.
      * repeat apply incl_union_left.
        decide (v ∈ M');
          unfold slot_lift_args;
          simpl;
          [ change (singleton (slot v)) with (Op.freeVars (Var (slot v)))
          | change (singleton v) with (Op.freeVars (Var v)) ];
          eapply get_list_union_map; eauto;
          eapply map_get_eq; eauto;
          simpl;
          decide (v ∈ M'); simpl; eauto.
  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    econstructor; simpl; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    apply renamedApart_incl in renAp as [renaF rena2].
    rewrite fst_zip_pair by eauto with len.
    econstructor; simpl; eauto.
    + rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

      apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- zip_app.
        eapply IHlvSnd with (ra:=ant) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (R:=R) (M:=M); eauto.
        -- eapply M'_VD with (R:=R) (M:=M); eauto.
        -- rewrite rena2; eauto.
        -- eapply getAnn_als_EQ_merge_rms; eauto.
        -- eapply get_ofl_VD; eauto.
        -- eauto with len.
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        -- rewrite <- zip_app.
           intros n x x' H4 H5.
           unfold slot_merge in H5.
           inv_get; simpl.
           rename x into Zs.
           rename x0 into rm.
           rename x4 into sl_s.
           rename x1 into a.
           rename x2 into al.
           rename H32 into get_al.
           rename H31 into get_a.
           rename H26 into get_sls.
           rename H29 into get_Zs.
           rename H5 into get_rm.

           rewrite slot_merge_app.

           exploit H19 as H24'; eauto. (*H31*)
           exploit H23 as H20'; eauto. (*H32*)
           exploit renaF as renaF'; eauto.
           exploit H14 as H15'; eauto. (*H33*)
           exploit H2 as H2'; eauto.
           destruct H2' as [H2' _].
           destruct H15' as [A [B [C E]]].
           assert (rm = (fst rm, snd rm)) as rm_eta by apply pair_eta.
           rewrite rm_eta in H24'.
           erewrite reconstr_live_small with (VD:=VD)
                                             (ra:=a)
                                             (R:=fst rm)
                                             (M:=snd rm); eauto.
           ++ (*clear - pir2_EQ pir3 renaF H24 H20 H15 H2 H16 H20 H8 H13 H14 H H9 H18 ra_VD.*)
             clear - rm_eta H2' get_al get_a get_sls get_rm get_Zs H15.
             rewrite rm_eta in get_rm.
             eapply al_sub_RfMf in get_rm; eauto.
             rewrite rm_eta.
              repeat apply union_incl_split;
                [clear; cset_tac | clear; cset_tac
                 | eapply ofl_slp_sub_rm; eauto ].
           ++ rewrite renaF'; eauto.
           ++ eapply getAnn_als_EQ_merge_rms; eauto.
           ++ eapply get_ofl_VD; eauto.
           ++ eauto with len.

        -- rewrite <- zip_app.
           rewrite map_length.
           ++ rewrite zip_length2.
              ** rewrite zip_length2; eauto with len.
              ** rewrite zip_length2, map_length;
                   eauto with len.
           ++ eauto with len.
    + symmetry.
      apply zip_length2.
      repeat rewrite length_map.
      rewrite zip_length2;
        eauto with len.
    + intros; inv_get.
      simpl.
      rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

      apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- zip_app; eauto with len.
        assert ((fst x2, snd x2) = x2)
          by (destruct x2; simpl; reflexivity).
        rewrite <- H4 in H30.
        exploit H23; eauto.
        eapply H1 with (ra:=x0) (R:=fst x2) (M:=snd x2); eauto.
        -- exploit renaF as renaF'; eauto.
           rewrite renaF'; eauto.
        -- eapply getAnn_als_EQ_merge_rms; eauto.
        -- eapply get_ofl_VD; eauto.
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        -- intros.
           unfold slot_merge in H5.
           inv_get; simpl.
           rewrite slot_merge_app.
           rewrite <- zip_app; eauto with len.
           exploit H19; eauto.
           exploit H23; eauto.
           exploit H9; eauto.
           destruct x5 as [R_f M_f].
           erewrite reconstr_live_small with (ra:=x6)
                                             (VD:=VD)
                                             (R:=R_f)
                                             (M:=M_f); eauto.
           ++ exploit H2 as H2'; eauto; dcr; simpl in *.

             rewrite ofl_slp_sub_rm; eauto. simpl.
             clear; cset_tac.
             eapply al_sub_RfMf; eauto.
           ++ rewrite renaF; eauto.
           ++ eapply getAnn_als_EQ_merge_rms; eauto.
           ++ eapply get_ofl_VD; eauto.
        -- unfold slot_merge. eauto with len.
    + intros.
      inv_get.
      simpl.
      split; [ | auto].
      * apply reconstr_live_G.
      * split; eauto.
        -- exploit H2; eauto; dcr.
           eapply PIR2_nth in H15; eauto; dcr.
           destruct x2. eapply NoDupA_slot_lift_params; eauto.
           unfold merge in H33.
           exploit H23; eauto; dcr. eauto with cset.
           rewrite <- M_VD. unfold union_fs. simpl.
           rewrite <- H27.
           rewrite <- incl_list_union; eauto using zip_get; [|reflexivity].
           unfold defVars. clear; cset_tac.
Qed.
        


      