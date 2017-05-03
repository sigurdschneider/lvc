Require Import CSet Le.

Require Import Plus Util AllInRel Map LengthEq.
Require Import CSet Val Var Env SimF IL Fresh Annotation RenamedApart.

Require Import SetOperations Liveness.Liveness Eqn OptionR.

Set Implicit Arguments.
Unset Printing Records.
Print Coercions.

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
    -> entails (of_list ((fun y => EqnEq y y) ⊝ Y') ∪ Gamma) (subst_eqns (sid [Z <-- Y']) Γf)
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
  -> ⎣y ⎦ = omap (op_eval E) Y
  -> op_eval (E [Z <-- List.map Some y]) e =
    op_eval E (subst_op (sid [Z <-- Y]) e).
Proof.
  general induction e; simpl; eauto.
  - eapply length_length_eq in H.
    general induction H; simpl in * |- *; eauto.
    symmetry in H0. monad_inv H0. simpl.
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
  (SAT : satisfies V (subst_eqn (sid [Z <-- Y]) gamma))
  : satisfies (bE [Z <-- Some ⊝ y]) gamma.
Proof.
  hnf in SAT. destruct gamma; simpl in *.
  * do 2 erewrite <- eval_op_subst in SAT; eauto.
    erewrite op_eval_agree; [| |reflexivity].
    erewrite op_eval_agree with (e:=e'); [| |reflexivity].
    eapply SAT.
    -- eapply update_with_list_agree; eauto with len.
       eapply agree_on_incl; eauto. cset_tac.
    -- eapply update_with_list_agree; eauto with len.
       eapply agree_on_incl; eauto.
       cset_tac.
  * simpl in * |- *.
    do 2 erewrite <- eval_op_subst in SAT; eauto.
    erewrite op_eval_agree; [| |reflexivity].
    erewrite op_eval_agree with (e:=e'); [| |reflexivity]; eauto.
    -- eapply update_with_list_agree; eauto with len.
       eapply agree_on_incl; eauto.
       cset_tac.
    -- eapply update_with_list_agree; eauto with len.
       eapply agree_on_incl; eauto.
       cset_tac.
  * eauto.
Qed.

Lemma satisfiesAll_subst V Gamma Z EqS Y y bE
:  length Z = length Y
   -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
   -> satisfiesAll V Gamma
   -> agree_on eq (eqns_freeVars EqS \ of_list Z) V bE
   -> omap (op_eval V) Y = ⎣y⎦
   -> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  revert_except EqS. pattern EqS. eapply set_induction; intros.
  - hnf; intros. eapply empty_is_empty_1 in H.
    exfalso. cset_tac.
  - hnf; intros.
    assert (LEN:❬Y❭ = ❬y❭). {
      eapply omap_length; eauto.
    }
    eapply Add_Equal in H1. rewrite H1 in *.
    eapply add_iff in H7. destruct H7.
    + hnf in H7; subst.
      specialize (H3 V H4 (subst_eqn (sid [Z <-- Y]) gamma)).
      exploit H3 as SAT.
      * eapply in_subst_eqns; eauto. cset_tac.
      * eapply satisfies_subst; eauto.
        eapply agree_on_incl; eauto.
        rewrite eqns_freeVars_add.
        clear; cset_tac.
    + eapply H; try eapply H7; eauto.
      * etransitivity; eauto.
        setoid_rewrite <- incl_add'; eauto. reflexivity.
      * setoid_rewrite <- incl_add' in H5; eauto.
Qed.

Lemma eqn_sound_monotone ZL Δ Γ Γ' s s' ang
  : renamedApart s ang
    -> eqn_sound ZL Δ s s' Γ ang
    -> Γ ⊆ Γ'
    -> eqn_sound ZL Δ s s' Γ' ang.
Proof.
  intros. general induction H0;
            (try now (eapply EqnUnsat; eauto using unsatisfiable_monotone)); invt renamedApart; eauto.
  - constructor; eauto.
    eapply IHeqn_sound; eauto.
    + rewrite H2; reflexivity.
    + eapply entails_monotone; eauto.
  - econstructor; intros; eauto using entails_monotone.
    eapply IHeqn_sound1; eauto. rewrite H1; reflexivity.
    eapply IHeqn_sound2; eauto. rewrite H1. reflexivity.
  - econstructor; eauto using entails_monotone.
    eapply entails_monotone; eauto. cset_tac.
  - econstructor; eauto using entails_monotone.
  - econstructor; eauto using entails_monotone.
    eapply IHeqn_sound; eauto.
    cset_tac.
  - econstructor; eauto.
    + intros.
      exploit H10; eauto.
      eapply H; eauto.
      rewrite <- H2; eauto.
Qed.

Lemma entails_incl Γ Γ'
  : Γ' ⊆ Γ
    -> entails Γ Γ'.
Proof.
  intros. rewrite H. reflexivity.
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

Hint Resolve satisfies_fstNoneOrR_apx onvLe_fstNoneOrR_apx.

Instance PR : PointwiseProofRelationF (params*eqns):=
  {
    ArgRelFP := fun E E' '(Z,Γ2) VL VL'
               => length Z = length VL /\ VL = VL'
                 /\ exists Γ Y V, entails (of_list ((fun y : op => EqnEq y y) ⊝ Y) ∪ Γ)
                                    (subst_eqns (sid [Z <-- Y]) Γ2)
                            /\ satisfiesAll V Γ /\ omap (op_eval V) Y = Some VL
                            /\ agree_on eq (eqns_freeVars Γ2 \ of_list Z) V E;
    ParamRelFP := fun '(Z,_) Z' Zb => Z = Z' /\ Zb = Z'
  }.

Lemma sim_vopt r L L' V V' s s' ZL Δ Gamma ang
  : satisfiesAll V Gamma
    -> eqn_sound ZL Δ s s' Gamma ang
    -> labenv_sim Sim (sim r) PR (zip pair ZL Δ) L L'
    -> renamedApart s ang
    -> eqns_freeVars Gamma ⊆ fst (getAnn ang)
    -> onvLe V V'
    -> (forall n b Γf, get L n b ->
                get Δ n Γf ->
                exists G, G ⊆ fst (getAnn ang) /\
                eqns_freeVars Γf ⊆ G ∪ of_list (block_Z b) /\
                agree_on eq G (F.block_E b) V)
    -> sim r Sim  (L,V, s) (L',V', s').
Proof.
  intros SAT EQN SIML REAPT FV OLE EEQ.
  general induction EQN; (try (now exfalso; eapply H; eauto))
  ; simpl; invt renamedApart; simpl in * |- *.
  - exploit H; eauto.
    exploit H0; eauto; [cset_tac|].
    eapply (sim_let_op_apx il_statetype_F).
    + etransitivity; eauto.
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
      * eapply agree_on_onvLe; eauto.
      * intros. exploit EEQ; dcr; eauto.
        pe_rewrite. exists x0. do 2 try split; eauto with cset.
        symmetry. eapply agree_on_update_dead; eauto.
        symmetry; eauto.
  -  exploit H; eauto.  exploit H0; eauto; [cset_tac|].
     eapply (sim_cond_op_apx il_statetype_F).
     + etransitivity; eauto.
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
      exploit H4; eauto. eapply omap_satisfies_list_EqnApx; eauto.
    }
    simpl in *; dcr; subst.
    exists Yv; repeat split; eauto using omap_exp_eval_onvLe.
    exists Gamma, Y', V.
    exploit EEQ; eauto; dcr. simpl in *.
    repeat split; eauto.
    + symmetry; eapply agree_on_incl; eauto.
      rewrite H11; eauto. clear; cset_tac.
  - eapply (sim_return_apx il_statetype_F).
    exploit H; eauto. exploit H0; eauto; [cset_tac|]. etransitivity; eauto.
  - exploit H; eauto. eapply (sim_let_call_apx il_statetype_F); eauto; simpl.
    + case_eq (omap (op_eval V) Y); eauto using fstNoneOrR.
      intros. etransitivity; eauto using  onvLe_omap_op_eval_fstNoneOrEq.
      rewrite <- H3. eapply satisfies_omap_op_eval_fstNoneOrR; eauto.
    + intros. simpl. left. eapply IHEQN; eauto.
      * eauto using satisfiesAll_EqnEq_on_update.
      * pe_rewrite. rewrite eqns_freeVars_add. simpl.
        rewrite FV.  clear_all. cset_tac.
      * eauto using agree_on_onvLe.
      * intros. exploit EEQ; dcr; eauto.
        pe_rewrite. eexists x0. do 2 try split; eauto with cset.
        symmetry. eapply agree_on_update_dead; eauto.
        symmetry; eauto.
  - pone_step. left. eapply IHEQN; eauto.
    + rewrite zip_app; eauto with len.
      eapply labenv_sim_extension_ptw; eauto with len.
      * intros. hnf. intros. simpl in * |- *. dcr. subst. inv_get.
        exploit H7; eauto.
        eapply H; eauto.
        -- rewrite satisfiesAll_union; split.
           ++ exploit EqnFVF; eauto.
             edestruct H8; eauto; dcr. simpl in *.
             eapply satisfiesAll_subst; eauto.
             eauto with len.
             eauto with cset.
             eapply satisfiesAll_union; split; eauto.
             hnf; intros.
             eapply of_list_get_first in H5; dcr. invc H26.
             inv_get. simpl.
             eapply omap_inversion in H23; eauto; dcr.
             rewrite H21. econstructor; eauto.
           ++ eapply satisfiesAll_agree; eauto.
             eapply agree_on_update_list_dead; eauto.
             ** edestruct H8; eauto; dcr.
                rewrite FV. eauto.
        -- rewrite eqns_freeVars_union.
           rewrite FV. edestruct H8; eauto; dcr. simpl in *.
           rewrite H14.
           exploit EqnFVF as EQ; eauto.
           rewrite EQ. simpl.
           clear; cset_tac.
        -- exploit ParamEq; dcr; eauto; subst.
           eapply agree_on_onvLe_update_list. eauto.
        -- intros ? ? ? Get1 Get2. eapply get_app_cases in Get1. destruct Get1.
           ++ inv_get.
             edestruct H8; try eapply H13; eauto; dcr. simpl in *.
             eexists G. rewrite H15. split; eauto with cset.
             exploit EqnFVF; eauto. split; eauto.
             eapply agree_on_update_list_dead; eauto with len.
           ++ dcr; simpl in *. len_simpl.
             rewrite get_app_ge in Get2; eauto with len.
             rewrite Len1 in *. inv_get.
             exploit EEQ; eauto; dcr.
             edestruct H8; try eapply H13; eauto; dcr.
             eexists x4.
             rewrite H5. simpl. split. eauto with cset.
             simpl in *. split; eauto.
             eapply agree_on_update_list_dead; eauto.
             rewrite H21. eauto. omega.
      * hnf. intros. simpl in *. subst. inv_get. exploit ParamEq; dcr; eauto.
    + pe_rewrite. eauto.
    + intros ? ? ? Get1 Get2. eapply get_app_cases in Get1. destruct Get1.
      ++ inv_get. pe_rewrite. eexists G; split; eauto.
      ++ dcr; simpl in *. len_simpl.
        rewrite get_app_ge in Get2; eauto with len.
        rewrite Len1 in *.
        exploit EEQ; eauto; dcr.
        eexists x. split; eauto. pe_rewrite. eauto.
        omega.
Qed.
