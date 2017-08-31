Require Import CSet Le.

Require Import Plus Util AllInRel Map LengthEq.
Require Import CSet Val Var Env SimF IL Fresh Annotation RenamedApart.

Require Import SetOperations Liveness.Liveness Eqn OptionR.

Set Implicit Arguments.
Unset Printing Records.

Inductive eqn_sound : list params -> list eqns  (*params*set var*eqns*)
                      -> stmt -> stmt
                      -> eqns
                      -> ann (set var * set var)
                      -> Prop :=
| EqnLet x ZL Δ s s' e Gamma e' G G' ang
  : eqn_sound ZL Δ s s' {EqnEq (Var x) e ; Gamma } ang
    -> entails Gamma {EqnApx e e'}
    -> eqn_sound ZL Δ (stmtLet x (Operation e) s) (stmtLet x (Operation e') s') Gamma
                (ann1 (G,G') ang)
| EqnIf ZL Δ e e' s s' t t' Gamma G G' ang1 ang2
  : eqn_sound ZL Δ s s' {EqnEq (UnOp UnOpToBool e) (Con val_true); Gamma} ang1
  -> eqn_sound ZL Δ t t' {EqnEq (UnOp UnOpToBool e) (Con val_false); Gamma} ang2
  -> entails Gamma {(EqnApx e e')}
  -> eqn_sound ZL Δ (stmtIf e s t) (stmtIf e' s' t') Gamma
              (ann2 (G,G') ang1 ang2)
| EqnApp (l:lab) Y Y' ZL Δ Gamma Z Γf G G'
  : get ZL  l Z -> get Δ l Γf
    -> length Y = length Y'
    -> entails (of_list ((fun y => EqnEq y y) ⊝ Y) ∪ Gamma) (subst_eqns (sid [Z <-- Y']) Γf)
    -> entails Gamma (list_EqnApx Y Y')
    -> eqn_sound ZL Δ (stmtApp l Y) (stmtApp l Y') Gamma (ann0 (G,G'))
| EqnReturn ZL Δ e e' Gamma G G'
  : entails Gamma {(EqnApx e e')}
    -> eqn_sound ZL Δ (stmtReturn e) (stmtReturn e') Gamma (ann0 (G,G'))
| EqnExtern x f ZL Δ s s' Y Y' Gamma G G' ang
  : eqn_sound ZL Δ s s' {EqnEq (Var x) (Var x) ; Gamma} ang
    -> entails Gamma (list_EqnApx Y Y')
    -> list_union (List.map Op.freeVars Y') ⊆ G
    -> length Y = length Y'
    -> eqn_sound ZL Δ (stmtLet x (Call f Y) s) (stmtLet x (Call f Y') s') Gamma
                (ann1 (G,G') ang)
| EqnFun ZL Δ ΓF F F' t t' Gamma G G' angs angb
         (Len1:length(ΓF) = length F)
         (Len2: length F = length F')
         (ParamEq:forall n Z s Z' s' , get F n (Z, s) -> get F' n (Z', s') -> Z = Z')
         (IndF:forall n Z s Z' s' EqS angn , get F n (Z, s) -> get F' n (Z', s')
                                        -> get ΓF n EqS -> get angs n angn
                                        -> eqn_sound (List.map fst F ++ ZL)
                                                    (ΓF ++ Δ) s s' (EqS ∪ Gamma) angn)
         (Indt:eqn_sound (List.map fst F ++ ZL) (ΓF ++ Δ)  t t' Gamma angb)
         (EqnFVF: forall n EqS Zs, get F n Zs -> get ΓF n EqS -> eqns_freeVars EqS ⊆ G ∪ of_list (fst Zs))
  : eqn_sound ZL Δ (stmtFun F t) (stmtFun F' t') Gamma
              (annF (G,G') angs angb)
| EqnUnsat ZL Δ s s' Gamma ang
  : unsatisfiables Gamma
    -> eqn_sound ZL Δ s s' Gamma ang.


Lemma unsat_Equal Γ Γ'
  : unsatisfiables Γ
    -> Γ [=] Γ'
    -> unsatisfiables Γ'.
Proof.
  intros; hnf; intros.
  rewrite <- H0. eauto.
Qed.

Instance eqn_sound_Proper
  : Proper (eq ==> eq ==> eq ==> eq ==> Equal ==> ann_R (@pe var _) ==> impl)
           eqn_sound.
Proof.
  unfold Proper, respectful, impl; intros; subst. symmetry in H4.
  general induction H5; only 1-6:(invt @ann_R; invt @pe).
  - econstructor 1; eauto with cset; try rewrite <- H3; eauto.
  - econstructor 2; eauto with cset; try rewrite <- H3; eauto.
  - econstructor 3; eauto with cset; try rewrite <- H4; eauto.
  - econstructor 4; eauto with cset; try rewrite <- H3; eauto.
  - econstructor 5; eauto with cset; try rewrite <- H3; eauto.
    rewrite H10. eauto.
  - econstructor 6; eauto with cset.
    + intros; inv_get.
      exploit H; eauto; try reflexivity.
      rewrite H3; eauto.
    + intros; inv_get.
      rewrite EqnFVF; eauto. rewrite H7. reflexivity.
  - econstructor.
    rewrite <- H3; eauto.
Qed.


Instance subst_exp_Proper Z Y
  : Proper (_eq ==> _eq) (subst_op (sid [Z <-- Y])).
Proof.
  hnf; intros. inv H. clear H.
  simpl. general induction y; simpl; eauto.
Qed.

Ltac dowith c t :=
  match goal with
    | [ H : c _ _ _ _ |- _ ] => t H
  end.

Lemma eval_op_subst E y Y Z e
: length Z = length Y
  -> omap (op_eval E) Y = ⎣y ⎦
  -> op_eval (E [Z <-- List.map Some y]) e =
    op_eval E (subst_op (sid [Z <-- Y]) e).
Proof.
  intros.
  general induction e; simpl; eauto.
  - eapply length_length_eq in H.
    general induction H; simpl in * |- *; eauto.
    monad_inv H0. simpl.
    lud; eauto.
  - erewrite IHe; eauto.
  - erewrite IHe1; eauto.
    erewrite IHe2; eauto.
Qed.

Lemma satisfies_subst V Z Y y bE gamma
  (EVAL: omap (op_eval V) Y = ⎣ y ⎦)
  (Len1 : ❬Y❭ = ❬y❭)
  (Len2 : ❬Z❭ = ❬Y❭)
  (AGR:agree_on eq (freeVars gamma \ of_list Z) V bE)
  : satisfies V (subst_eqn (sid [Z <-- Y]) gamma) <-> satisfies (bE [Z <-- Some ⊝ y]) gamma.
Proof.
  destruct gamma; simpl in *.
  * do 2 rewrite <- (eval_op_subst _ _ _ _ Len2 EVAL); eauto.
    erewrite op_eval_agree; [| |reflexivity].
    erewrite op_eval_agree with (e:=e'); [| |reflexivity].
    reflexivity.
    -- eapply update_with_list_agree; eauto with len.
       symmetry.
       eapply agree_on_incl; eauto. cset_tac.
    -- eapply update_with_list_agree; eauto with len.
       symmetry.
       eapply agree_on_incl; eauto.
       cset_tac.
  * simpl in * |- *.
    do 2 erewrite <- (eval_op_subst _ _ _ _ Len2 EVAL); eauto.
    erewrite op_eval_agree; [| |reflexivity].
    erewrite op_eval_agree with (e:=e'); [| |reflexivity]; eauto.
    reflexivity.
    -- eapply update_with_list_agree; eauto with len.
       symmetry.
       eapply agree_on_incl; eauto.
       cset_tac.
    -- eapply update_with_list_agree; eauto with len.
       symmetry.
       eapply agree_on_incl; eauto.
       cset_tac.
  * reflexivity.
Qed.

Lemma satisfiesAll_subst V Z EqS Y y bE
:  omap (op_eval V) Y = ⎣y⎦
   -> agree_on eq (eqns_freeVars EqS \ of_list Z) V bE
   -> length Z = length Y
   -> satisfiesAll V (subst_eqns (sid [Z <-- Y]) EqS) <-> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  revert_except EqS. pattern EqS. eapply set_induction; intros.
  - hnf; intros. eapply empty_is_empty_1 in H.
    rewrite H. rewrite subst_eqns_empty.
    unfold satisfiesAll; split; intros; cset_tac.
  - eapply Add_Equal in H1. rewrite H1 in *.
    rewrite subst_eqns_add.
    rewrite !satisfiesAll_add.
    rewrite eqns_freeVars_add in H3.
    rewrite satisfies_subst; eauto with len;[|eauto with cset].
    rewrite H; eauto with cset. reflexivity.
Qed.

Lemma eqn_sound_entails_monotone ZL Δ Γ1 Γ1' s s' ang
  : renamedApart s ang
    -> eqn_sound ZL Δ s s' Γ1 ang
    -> entails Γ1' Γ1
    -> eqn_sound ZL Δ s s' Γ1' ang.
Proof.
  intros. general induction H0;
            (try now (eapply EqnUnsat; eauto using unsatisfiable_entails_monotone));
            invt renamedApart; eauto.
  - econstructor; eauto.
    eapply IHeqn_sound; eauto.
    rewrite <- H2. reflexivity.
    + etransitivity; eauto.
  - econstructor; intros; eauto using entails_transitive.
    + eapply IHeqn_sound1; eauto.
      rewrite H1. reflexivity.
    + eapply IHeqn_sound2; eauto.
      rewrite H1. reflexivity.
  - econstructor; eauto using entails_transitive.
    etransitivity; eauto.
    eapply entails_union; split.
    + eapply entails_subset. cset_tac.
    + etransitivity; eauto.
      eapply entails_subset. cset_tac.
  - econstructor; eauto using entails_transitive.
  - econstructor; eauto using entails_transitive, entails_monotone.
    eapply IHeqn_sound; eauto.
    rewrite H4. reflexivity.
  - econstructor; eauto.
    + intros.
      exploit H10; eauto.
      eapply H; eauto.
      eapply entails_union; eauto; split.
      eapply entails_incl. eauto with cset.
      etransitivity; eauto.
      eapply entails_incl. eauto with cset.
Qed.

Lemma eqn_sound_monotone ZL Δ Γ Γ' s s' ang
  : renamedApart s ang
    -> eqn_sound ZL Δ s s' Γ ang
    -> Γ ⊆ Γ'
    -> eqn_sound ZL Δ s s' Γ' ang.
Proof.
  intros. eapply eqn_sound_entails_monotone; eauto.
  eapply entails_incl; eauto.
Qed.

Hint Resolve satisfies_fstNoneOrR_apx onvLe_fstNoneOrR_apx.

Instance PR : PointwiseProofRelationF (params*eqns):=
  {
    ArgRelFP := fun E E' '(Z,Γf) VL VL'
               => length Z = length VL /\ VL = VL'
                 /\ exists Γ Y V, entails (of_list ((fun y : op => EqnEq y y) ⊝ Y) ∪ Γ)
                                    (subst_eqns (sid [Z <-- Y]) Γf)
                            /\ satisfiesAll V Γ /\ omap (op_eval V) Y = Some VL
                            /\ agree_on eq (eqns_freeVars Γf \ of_list Z) V E;
    ParamRelFP := fun '(Z,_) Z' Zb => Z = Z' /\ Zb = Z'
  }.

(*
Instance prod_eq_fst_morphism X `{OrderedType X}
: Proper (@pe X _ ==> Equal) fst.
Proof.
  unfold Proper, respectful; intros.
  inversion H0; simpl; eauto.
Qed.

Instance prod_eq_snd_morphism X `{OrderedType X}
: Proper (@pe X _ ==> Equal) snd.
Proof.
  unfold Proper, respectful; intros.
  inversion H0; simpl; eauto.
Qed.

Instance add_s_m_flip A `{OrderedType A}
  : Proper (Equal ==> Equal ==> iff) Subset.
Proof.
  unfold Proper, respectful, flip; intros.
  rewrite H0, H1. reflexivity.
Qed.

Instance add_s_m_flip' A `{OrderedType A}
  : Proper (Equal ==> Equal ==> impl) Subset.
Proof.
  unfold Proper, respectful, flip; intros.
  rewrite H0, H1. reflexivity.
Qed.

Instance add_s_m_flip'' A `{OrderedType A}
  : Proper (Equal ==> Equal ==> flip impl) Subset.
Proof.
  unfold Proper, respectful, flip; intros.
  rewrite H0, H1. reflexivity.
Qed.
 *)

Lemma satisfiesAll_EqnEq_omap E Y
  : satisfiesAll E (of_list ((fun y : op => EqnEq y y) ⊝ Y))
    <-> exists vl, omap (op_eval E) Y = Some vl.
Proof.
  general induction Y; simpl.
  - split; hnf; intros; eauto. hnf; intros. cset_tac.
  - rewrite satisfiesAll_add.
    simpl. case_eq (op_eval E a); intros; simpl.
    rewrite IHY.
    + split; intros; dcr. rewrite H3. simpl. eauto.
      split; eauto. econstructor; eauto. monad_inv H1. eauto.
    + split; intros; dcr; clear_trivial_eqs.
Qed.

Lemma satisfiesAll_EqnApx_omap E Y Y' (LEN:❬Y❭=❬Y'❭) vl
  : satisfiesAll E (list_EqnApx Y Y')
    -> omap (op_eval E) Y = Some vl
    -> omap (op_eval E) Y' = Some vl.
Proof.
  unfold list_EqnApx.
  general induction LEN; simpl in *; eauto.
  - monad_inv H0.
    rewrite satisfiesAll_add in H; dcr.
    hnf in H0. rewrite EQ in *. inv H0.
    simpl. eapply IHLEN in H1; eauto.
    rewrite H1. reflexivity.
Qed.

Lemma sim_vopt r L L' V s s' ZL Δ Gamma ang
  : satisfiesAll V Gamma
    -> eqn_sound ZL Δ s s' Gamma ang
    -> labenv_sim Sim (sim r) PR (zip pair ZL Δ) L L'
    -> renamedApart s ang
    -> eqns_freeVars Gamma ⊆ fst (getAnn ang)
    -> (forall n b Γf, get L n b ->
                get Δ n Γf ->
                eqns_freeVars Γf ⊆ fst (getAnn ang) ∪ of_list (block_Z b) /\
                agree_on eq (eqns_freeVars Γf \ of_list (block_Z b)) (F.block_E b) V)
    -> sim r Sim  (L,V, s) (L',V, s').
Proof.
  intros SAT EQN SIML REAPT FV EEQ.
  general induction EQN; (try (now exfalso; eapply H; eauto));
    simpl; invtc renamedApart; simpl in * |- *.
  - exploit H; eauto.
    exploit H0; eauto; [cset_tac|].
    eapply (sim_let_op_apx il_statetype_F).
    + eauto.
    + intros. left. eapply IHEQN; eauto.
      * assert (satisfies (V [x <- ⎣ v ⎦]) (EqnEq (Var x) e)). {
          eauto using satisfies_EqnEq_on_update.
        }
        rewrite !satisfiesAll_add; split; eauto.
         -- eapply satisfiesAll_agree; eauto.
            symmetry.
            eapply agree_on_update_dead; eauto.
      * pe_rewrite. rewrite! eqns_freeVars_add. simpl.
        rewrite H7, FV. clear. cset_tac.
      * intros. exploit EEQ; dcr; eauto.
        pe_rewrite. rewrite H11 at 1. split.
        -- clear_all. cset_tac.
        -- symmetry. eapply agree_on_update_dead; eauto.
           rewrite H11. revert H6; clear_all; cset_tac.
           symmetry. eauto.
  -  exploit H; eauto.  exploit H0; eauto; [cset_tac|].
     eapply (sim_cond_op_apx il_statetype_F).
     + eauto.
     + intros. left. eapply IHEQN1; clear IHEQN1 IHEQN2; eauto.
       * apply satisfiesAll_add. eauto using  op_eval_true_satisfies.
       * rewrite eqns_freeVars_add. simpl. pe_rewrite. intros a0 A. cset_tac.
       * pe_rewrite; eauto with cset.
     + intros. left. eapply IHEQN2; clear IHEQN1 IHEQN2; eauto.
       * apply satisfiesAll_add. eauto using op_eval_false_satisfies.
       * rewrite eqns_freeVars_add . pe_rewrite.  intros gamma A. cset_tac.
       * pe_rewrite. eauto with cset.
  - eapply labenv_sim_app; eauto using zip_get; simpl.
    intros; split; intros; eauto.
    assert (EV:omap (op_eval V) Y' = ⎣ Yv ⎦). {
      eapply omap_satisfies_list_EqnApx; eauto.
    }
    simpl in *; dcr; subst.
    exists Yv; repeat split; eauto using omap_exp_eval_onvLe.
    exists Gamma, Y, V.
    exploit EEQ; eauto; dcr. simpl in *.
    repeat split; eauto.
    + hnf; intros.
      exploit H2; eauto.
      eapply satisfiesAll_union in H6; dcr.
      eapply satisfiesAll_EqnEq_omap in H14; dcr.
      eapply satisfiesAll_subst; eauto. reflexivity. eauto with len.
      exploit satisfiesAll_EqnApx_omap; eauto.
      eapply satisfiesAll_subst; eauto with len.
    + symmetry; eapply agree_on_incl; eauto.
  - eapply (sim_return_apx il_statetype_F).
    exploit H; eauto.
  - exploit H; eauto. eapply (sim_let_call_apx il_statetype_F); eauto; simpl.
    + case_eq (omap (op_eval V) Y); eauto using fstNoneOrR.
      intros.
      rewrite <- H3. eapply satisfies_omap_op_eval_fstNoneOrR; eauto.
    + intros. simpl. left. eapply IHEQN; eauto.
      * eauto using satisfiesAll_EqnEq_on_update.
      * pe_rewrite. rewrite eqns_freeVars_add. simpl.
        rewrite FV.  clear_all. cset_tac.
      * intros. exploit EEQ; dcr; eauto.
        pe_rewrite. split.
        rewrite H6. clear_all; cset_tac.
        symmetry. eapply agree_on_update_dead; try symmetry; eauto.
        rewrite H6. revert H8. clear_all. cset_tac.
  - pone_step. left. eapply IHEQN; eauto.
    + rewrite zip_app; eauto with len.
      eapply labenv_sim_extension_ptw; eauto with len.
      * intros. hnf. intros. simpl in * |- *. destruct a. dcr. subst. inv_get.
        exploit ParamEq; eauto. subst.
        exploit H7; eauto. dcr.
        eapply H; eauto.
        -- rewrite satisfiesAll_union; split.
           ++ exploit EqnFVF; eauto.
             edestruct H8; eauto; dcr. simpl in *.
             rewrite <- satisfiesAll_subst; eauto with len.
             eapply H16.
             eapply satisfiesAll_union; split; eauto.
             hnf; intros.
             eapply of_list_get_first in H20; dcr. invc H25.
             inv_get. simpl.
             eapply omap_inversion in H17; eauto; dcr.
             rewrite H25. econstructor; eauto.
           ++ eapply satisfiesAll_agree; eauto.
             eapply agree_on_update_list_dead; eauto.
             ** edestruct H8; eauto; dcr.
                rewrite FV. eauto.
        -- rewrite eqns_freeVars_union.
           rewrite FV. edestruct H8; eauto; dcr. simpl in *.
           rewrite H15.
           exploit EqnFVF as EQ; eauto.
           rewrite EQ. simpl.
           clear; cset_tac.
        -- intros ? ? ? Get1 Get2. eapply get_app_cases in Get1. destruct Get1.
           ++ inv_get.
             edestruct H8; try eapply H5; eauto; dcr. simpl in *.
             rewrite H18. split.
             ** rewrite EqnFVF; eauto. clear_all; cset_tac.
             ** eapply agree_on_update_list_dead; eauto with len.
                rewrite EqnFVF; eauto.
                eapply disj_2_incl; eauto. clear_all; cset_tac.
           ++ dcr; simpl in *. len_simpl.
             rewrite get_app_ge in Get2; eauto with len.
             rewrite Len1 in *. inv_get.
             exploit EEQ; eauto; dcr.
             edestruct H8; try eapply H5; eauto; dcr.
             rewrite H15. simpl. split. rewrite H21.
             clear_all; cset_tac.
             simpl in *.
             eapply agree_on_update_list_dead; eauto.
             eapply disj_2_incl; eauto. rewrite H21.
             clear_all; cset_tac. omega.
      * hnf. intros. simpl in *. subst. inv_get. exploit ParamEq; dcr; eauto.
    + pe_rewrite. eauto.
    + intros ? ? ? Get1 Get2. eapply get_app_cases in Get1. destruct Get1.
      ++ inv_get. pe_rewrite. split; eauto.
      ++ dcr; simpl in *. len_simpl.
        rewrite get_app_ge in Get2; eauto with len.
        rewrite Len1 in *.
        exploit EEQ; eauto; dcr.
        split; eauto. pe_rewrite. eauto. omega.
Qed.
