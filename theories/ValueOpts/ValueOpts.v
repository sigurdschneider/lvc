Require Import CSet Le.

Require Import Plus Util AllInRel Map LengthEq.
Require Import CSet Val Var Env SimF IL Fresh Annotation RenamedApart.

Require Import SetOperations Liveness.Liveness Eqn OptionR.

Set Implicit Arguments.
Unset Printing Records.
Print Coercions.

Inductive eqn_sound : list params -> list (set var) -> list eqns  (*params*set var*eqns*)
                      -> stmt -> stmt
                      -> eqns
                      -> ann (set var * set var)
                      -> Prop :=
| EqnLet x ZL Δ Γ  s s' e Gamma e' G G' ang
  : eqn_sound ZL Δ Γ s s' {EqnEq (Var x) e ; { EqnEq (Var x) e' ; Gamma } } ang
    (* make sure the rest conforms to the new assignment *)
    -> entails Gamma {EqnApx e e'}
    -> Op.freeVars e' ⊆ G
    -> eqn_sound ZL Δ Γ (stmtLet x (Operation e) s) (stmtLet x (Operation e') s') Gamma
                (ann1 (G,G') ang)
| EqnIf ZL Δ Γ e e' s s' t t' Gamma G G' ang1 ang2
  : eqn_sound ZL Δ Γ s s' {EqnEq (UnOp UnOpToBool e) (Con val_true); Gamma} ang1
  -> eqn_sound ZL Δ Γ t t' {EqnEq (UnOp UnOpToBool e) (Con val_false); Gamma} ang2
  -> entails Gamma {(EqnApx e e')}
  -> eqn_sound ZL Δ Γ (stmtIf e s t) (stmtIf e' s' t') Gamma
              (ann2 (G,G') ang1 ang2)
| EqnApp (l:lab) Y Y' ZL Δ Γ Gamma Z Γf Gf G G'
  : get ZL  l Z -> get Δ l Gf -> get Γ l Γf
    -> length Y = length Y'
    -> entails (of_list ((fun y => EqnEq y y) ⊝ Y') ∪ Gamma) (subst_eqns (sid [Z <-- Y']) Γf)
    -> entails Gamma (list_EqnApx Y Y')
    -> eqn_sound ZL Δ Γ (stmtApp l Y) (stmtApp l Y') Gamma (ann0 (G,G'))
| EqnReturn ZL Δ Γ e e' Gamma G G'
  : entails Gamma {(EqnApx e e')}
    -> eqn_sound ZL Δ Γ (stmtReturn e) (stmtReturn e') Gamma (ann0 (G,G'))
| EqnExtern x f ZL Δ Γ s s' Y Y' Gamma G G' ang
  : eqn_sound ZL Δ Γ s s' {EqnEq (Var x) (Var x) ; Gamma} ang
    -> entails Gamma (list_EqnApx Y Y')
    -> list_union (List.map Op.freeVars Y') ⊆ G
    -> length Y = length Y'
    -> eqn_sound ZL Δ Γ (stmtLet x (Call f Y) s) (stmtLet x (Call f Y') s') Gamma
                (ann1 (G,G') ang)
| EqnFun ZL Δ Γ ΓF F F' t t'  Gamma Γ2 G G' angs angb
         (Len1:length(ΓF) = length F)
         (Len2: length F = length F')
         (ParamEq:forall n Z s Z' s' , get F n (Z, s) -> get F' n (Z', s') -> Z = Z')
         (IndF:forall n Z s Z' s' EqS angn , get F n (Z, s) -> get F' n (Z', s')
                                        -> get ΓF n EqS -> get angs n angn
                                        -> eqn_sound (List.map fst F ++ ZL)
                                                    ((List.map (fun _ => G) F) ++ Δ)
                                                    (ΓF ++Γ)  s s' (EqS ∪ Γ2) angn)
         (Indt:eqn_sound (List.map fst F ++ ZL) ((List.map (fun _ => G) F) ++ Δ) (ΓF ++Γ)  t t' Gamma angb)
         (EqnFVF: forall n EqS Zs, get F n Zs -> get ΓF n EqS -> eqns_freeVars EqS ⊆ G ∪ of_list (fst Zs))
         (EqnFV:eqns_freeVars Γ2  ⊆ G)
         (Ent: entails Gamma Γ2)
  : eqn_sound ZL Δ Γ (stmtFun F t) (stmtFun F' t') Gamma
              (annF (G,G') angs angb)
| EqnUnsat ZL Δ Γ s s' Gamma ang
  : unsatisfiables Gamma
    -> eqn_sound ZL Δ Γ s s' Gamma ang.


Lemma unsat_Equal Γ Γ'
  : unsatisfiables Γ
    -> Γ [=] Γ'
    -> unsatisfiables Γ'.
Proof.
  intros; hnf; intros.
  rewrite <- H0. eauto.
Qed.

Instance eqn_sound_Proper
  : Proper (eq ==> list_eq Equal ==> eq ==> eq ==> eq ==> Equal ==> ann_R (@pe var _) ==> impl) eqn_sound.
Proof.
  unfold Proper, respectful, impl; intros; subst. symmetry in H5.
  general induction H6; only 1-6:(invt @ann_R; invt @pe).
  - econstructor 1; eauto with cset; try rewrite <- H4; eauto.
    rewrite H10; eauto.
  - econstructor 2; eauto with cset; try rewrite <- H4; eauto.
  - edestruct @list_eq_get; eauto; dcr.
    econstructor 3; eauto with cset; try rewrite <- H6; eauto.
  - econstructor 4; eauto with cset; try rewrite <- H4; eauto.
  - econstructor 5; eauto with cset; try rewrite <- H4; eauto.
    rewrite H11. eauto.
  - econstructor 6; eauto with cset.
    + intros; inv_get.
      exploit H; eauto; try reflexivity.
      eapply list_eq_app; eauto.
      revert H8; clear.
      induction F; simpl; eauto using @list_eq.
      intros; econstructor; eauto. symmetry; eauto.
    + eapply IHeqn_sound; eauto.
      eapply list_eq_app; eauto.
      revert H8; clear.
      induction F; simpl; eauto using @list_eq.
      intros; econstructor; eauto. symmetry; eauto.
    + intros; inv_get.
      rewrite EqnFVF; eauto. rewrite H8. reflexivity.
    + rewrite H8; eauto.
    + rewrite <- H4; eauto.
  - econstructor.
    rewrite <- H4; eauto.
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


(*
Lemma satisfies_update_dead_list E gamma Z vl
: length Z = length vl
  -> satisfies E gamma
  -> freeVars gamma ∩ of_list Z [=] ∅
  -> satisfies (E[Z <-- vl]) gamma.
Proof.
  intros. destruct gamma; simpl in * |- *.
  - inv H0. symmetry in H3. symmetry in H2.
    erewrite exp_eval_agree; try eapply H2.
    symmetry.
    erewrite exp_eval_agree; try eapply H3.
    econstructor; reflexivity.
    erewrite <- minus_inane_set. symmetry.
    eapply update_with_list_agree_minus; eauto.
    cset_tac; intuition. eapply (H1 a); cset_tac; intuition.
    erewrite <- minus_inane_set. symmetry.
    eapply update_with_list_agree_minus; eauto.
    cset_tac; intuition. eapply (H1 a); cset_tac; intuition.
  - inv H0.
    + symmetry in H3.
      erewrite exp_eval_agree; try eapply H3. econstructor.
      erewrite <- minus_inane_set. symmetry.
      eapply update_with_list_agree_minus; eauto.
      cset_tac; intuition. eapply (H1 a); cset_tac; intuition.
    + symmetry in H3. symmetry in H2.
      erewrite exp_eval_agree; try eapply H2.
      erewrite exp_eval_agree; try eapply H3.
      econstructor; reflexivity.
      erewrite <- minus_inane_set. symmetry.
      eapply update_with_list_agree_minus; eauto.
      cset_tac; intuition. eapply (H1 a); cset_tac; intuition.
      erewrite <- minus_inane_set. symmetry.
      eapply update_with_list_agree_minus; eauto.
      cset_tac; intuition. eapply (H1 a); cset_tac; intuition.
  - eauto.
Qed.


Lemma satisfiesAll_update_dead E Gamma Z vl
: length Z = length vl
  -> satisfiesAll E Gamma
  -> eqns_freeVars Gamma ∩ of_list Z [=] ∅
  -> satisfiesAll (E[Z <-- vl]) Gamma.
Proof.
  intros. hnf; intros.
  exploit H0; eauto.
  eapply satisfies_update_dead_list; eauto.
  exploit eqns_freeVars_incl; eauto.
  rewrite <- H1.
  revert H1 X0; simpl; clear_all; cset_tac; intuition; exfalso; eauto.
Qed.
*)


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

(*

Lemma simL'_update r A (AR AR':ProofRelation A) LV L L' L1 L2
: AIR5 (simB sim_progeq r AR) L L' LV L1 L2
  -> (forall x b b', @BlockRel _ AR x b b' -> @BlockRel _ AR' x b b')
  -> (forall a Z Z', @ParamRel _ AR a Z Z' -> @ParamRel _ AR' a Z Z')
  -> (forall V V' a VL VL', @ArgRel _ AR V V' a VL VL' <-> @ArgRel _ AR' V V' a VL VL')
  -> L = L1
  -> L' = L2
  -> AIR5 (simB sim_progeq r AR') L L' LV L1 L2.
Proof.
  intros. revert_until H. remember AR. induction H; intros.
  - econstructor.
  - intros. invc H3. invc H4. inv pf.
    econstructor; eauto.
    econstructor; intros; eauto.
    eapply H5; eauto. eapply H2; eauto.
Qed.
*)
(*
Lemma entails_freeVars_incl Gamma Γ' G x e
: entails ({{(Var x, e)}} ∪ Gamma) Γ'
  -> Exp.freeVars e ⊆ G
  -> eqns_freeVars Gamma ⊆ G
  -> eqns_freeVars Γ' ⊆ G ∪ {{x}}.
Proof.
  intros. destruct H.
  rewrite eqns_freeVars_add in H2.
  rewrite H2. unfold freeVars; simpl. rewrite H0. rewrite H1.
  clear_all; cset_tac; intuition.
Qed.
*)



Lemma satisfiesAll_subst V Gamma Z EqS Y y bE G
:  length Z = length Y
   -> eqns_freeVars EqS ⊆ G ∪ of_list Z
   -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
   -> satisfiesAll V Gamma
   -> agree_on eq G V bE
   -> omap (op_eval V) Y = ⎣y⎦
   -> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  revert_except EqS. pattern EqS. eapply set_induction; intros.
  - hnf; intros. eapply empty_is_empty_1 in H.
    exfalso. rewrite H in H6. cset_tac; intuition.
  - hnf; intros.
    assert (LEN:❬Y❭ = ❬y❭). {
      eapply omap_length; eauto.
    }
    eapply Add_Equal in H1. rewrite H1 in H8.
    eapply add_iff in H8. destruct H8.
    + hnf in H8; subst.
      specialize (H4 V H5 (subst_eqn (sid [Z <-- Y]) gamma)).
      exploit H4 as SAT.
      eapply in_subst_eqns; eauto. rewrite H1. cset_tac.
      hnf in SAT. destruct gamma. simpl in *.
      * do 2 erewrite <- eval_op_subst in SAT; eauto.
        erewrite op_eval_agree; [| |reflexivity].
        erewrite op_eval_agree with (e:=e'); [| |reflexivity].
        eapply SAT.
        -- eapply update_with_list_agree; eauto with len.
           eapply agree_on_incl; eauto.
           assert (EqnEq e e' ∈ s') as IN. {
             rewrite H1. cset_tac.
           }
           exploit eqns_freeVars_incl as FVI; eauto. simpl in *.
           rewrite H3 in FVI. revert FVI; clear; cset_tac.
        -- eapply update_with_list_agree; eauto with len.
           eapply agree_on_incl; eauto.
           assert (EqnEq e e' ∈ s') as IN. {
             rewrite H1. cset_tac.
           }
           exploit eqns_freeVars_incl as FVI; eauto.
           rewrite H3 in FVI. simpl in *.
           revert FVI; clear; cset_tac.
      * simpl in * |- *.
        do 2 erewrite <- eval_op_subst in SAT; eauto.
        erewrite op_eval_agree; [| |reflexivity].
        erewrite op_eval_agree with (e:=e'); [| |reflexivity]; eauto.
        -- eapply update_with_list_agree; eauto with len.
           eapply agree_on_incl; eauto.
           assert (EqnApx e e' ∈ s') as IN. {
             rewrite H1. clear; cset_tac.
           }
           exploit eqns_freeVars_incl as FVI; eauto. simpl in *.
           rewrite H3 in FVI.
           revert FVI; clear; cset_tac.
        -- eapply update_with_list_agree; eauto with len.
           eapply agree_on_incl; eauto.
           assert (EqnApx e e' ∈ s') as IN. {
             rewrite H1. cset_tac.
           }
           exploit eqns_freeVars_incl as FVI; eauto.
           rewrite H3 in FVI. simpl in *.
           revert FVI; clear; cset_tac.
      * simpl in *; eauto.
    + rewrite H1 in H4.
      eapply H; try eapply H7; eauto.
      * rewrite <- H3. rewrite H1.
        rewrite eqns_freeVars_add'. cset_tac; intuition.
      * setoid_rewrite <- incl_add' in H4; eauto.
Qed.


(*
Lemma satisfiesAll_update x Gamma V e e' y
: x ∉ eqns_freeVars Gamma
  -> x ∉ Exp.freeVars e
  -> x ∉ Exp.freeVars e'
  -> satisfiesAll V Gamma
  -> ⎣y ⎦ = op_eval V e
  -> ⎣y ⎦ = op_eval V e'
  -> satisfiesAll (V [x <- ⎣y ⎦])
                 ({EqnEq (Var x) e ; {EqnEq (Var x) e'; Gamma } }).
Proof.
  intros. hnf; intros. cset_tac. destruct H5 as [|[|]].
  - invc H5; simpl in * |- *; subst.
    + erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      rewrite <- H3. simpl. lud. econstructor; eauto.
      exfalso; eauto.
      eapply agree_on_update_dead; eauto.
  - invc H5; simpl in * |- *; subst.
    + erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      rewrite <- H4. simpl. lud. econstructor; eauto.
      exfalso; eauto.
      eapply agree_on_update_dead; eauto.
  - hnf in H1. exploit H2; eauto.
    eapply satisfies_update_dead; eauto.
    intro. eapply in_eqns_freeVars in H6; eauto.
Qed.


Lemma satisfiesAll_update_dead_single x Gamma V y
: x ∉ eqns_freeVars Gamma
  -> satisfiesAll V Gamma
  -> satisfiesAll (V [x <- ⎣y ⎦]) Gamma.
Proof.
  intros. hnf; intros.
  - eapply satisfies_update_dead; eauto.
    intro. eapply in_eqns_freeVars in H2; eauto.
Qed.
*)

Lemma eqn_sound_monotone ZL Δ Γ Γ1 Γ1' s s' ang
  : renamedApart s ang
    -> eqn_sound ZL Δ Γ s s' Γ1 ang
    -> Γ1 ⊆ Γ1'
    -> eqn_sound ZL Δ Γ s s' Γ1' ang.
Proof.
  intros. general induction H0;
            (try now (eapply EqnUnsat; eauto using unsatisfiable_monotone)); invt renamedApart; eauto.
  - constructor; eauto.
    eapply IHeqn_sound; eauto.
    + rewrite H3; reflexivity.
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
    + rewrite <- H2; eauto.
Qed.

Lemma eqn_sound_entails_monotone ZL Δ Γ Γ1 Γ1' s s' ang
  : renamedApart s ang
    -> eqn_sound ZL Δ Γ s s' Γ1 ang
    -> entails Γ1' Γ1
    -> eqn_sound ZL Δ Γ s s' Γ1' ang.
Proof.
  intros. general induction H0;
            (try now (eapply EqnUnsat; eauto using unsatisfiable_entails_monotone));
            invt renamedApart; eauto.
  - econstructor; eauto.
    eapply IHeqn_sound; eauto. rewrite <- H3. reflexivity.
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
    + etransitivity; eauto.
Qed.


(*
Definition ArgRel' (Z:params ) (VL VL': list val) : Prop :=

(*  /\ satisfiesAll ([Z <-- List.map Some VL]) (EqS ∪ Gamma)*).

Definition ParamRel' (Zb:params) (Z Z' : list var) : Prop :=
 *)


(*
Lemma satisfies_omap_op_eval_some Gamma Y Y' V vl
  : entails Gamma (list_EqnApx Y Y')
    -> ❬Y❭ = ❬Y'❭
    -> satisfiesAll V Gamma
    -> omap (op_eval V) Y = ⎣ vl ⎦
    -> omap (op_eval V) Y' = ⎣ vl ⎦.
Proof.
  intros.
  exploit H; eauto.
  case_eq (omap (op_eval V) Y); eauto.
  intros. length_equify. general induction H0; simpl in * |- *; eauto using fstNoneOrR.
  monad_inv H2. monad_inv H4. rewrite EQ0, EQ3. simpl. erewrite IHlength_eq; eauto.
  - replace (op_eval V y) with ⎣x2⎦; simpl; eauto.
 *)






(*
  omap_satisfies_list_EqnApx, omap_exp_eval_onvLe
*)



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

Lemma sim_vopt r L L' V V' s s' ZL Δ ΓL Gamma ang
  : satisfiesAll V Gamma
    -> eqn_sound ZL Δ ΓL s s' Gamma ang
    -> labenv_sim Sim (sim r) PR (zip pair ZL ΓL) L L'
    -> renamedApart s ang
    -> eqns_freeVars Gamma ⊆ fst (getAnn ang)
    -> onvLe V V'
    -> (forall n b G Γf, get L n b ->
                get Δ n G ->
                get ΓL n Γf ->
                G ⊆ fst (getAnn ang) /\
                eqns_freeVars Γf ⊆ G ∪ of_list (block_Z b) /\
                agree_on eq G (F.block_E b) V)
    -> sim r Sim  (L,V, s) (L',V', s').
Proof.
  intros SAT EQN SIML REAPT FV OLE EEQ.
  general induction EQN; (try (now exfalso; eapply H; eauto))
  ; simpl; invt renamedApart; simpl in * |- *.
  - exploit H; eauto.
    exploit H1; eauto; [cset_tac|].
    eapply (sim_let_op_apx il_statetype_F).
    + etransitivity; eauto.
    + intros. left. eapply IHEQN; eauto.
      *  unfold satisfiesAll. intros. cset_tac'.
         -- rewrite <- H12. eauto using satisfies_EqnEq_on_update.
         -- rewrite <- H4.
            eapply (@satisfies_EqnEq_on_update x e' V v); eauto.
            eapply satisfies_fstNoneOrR_apx in H2.
            rewrite H3 in H2. inv H2. reflexivity.
         -- exploit SAT; eauto. apply satisfies_update_dead; eauto.
            intros X. apply H7. apply FV. eapply in_eqns_freeVars; eauto.
      * pe_rewrite. rewrite! eqns_freeVars_add. simpl.
        rewrite H0, H8, FV. clear. cset_tac.
      * eapply agree_on_onvLe; eauto.
      * intros. exploit EEQ; dcr; eauto.
        pe_rewrite. do 2 try split; eauto with cset.
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
      rewrite H14; eauto. clear; cset_tac.
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
        pe_rewrite. do 2 try split; eauto with cset.
        symmetry. eapply agree_on_update_dead; eauto.
        symmetry; eauto.
  - pone_step. left. eapply IHEQN; eauto.
    + rewrite zip_app; eauto with len.
      eapply labenv_sim_extension_ptw; eauto with len.
      * intros. hnf. intros. simpl in * |- *. dcr. subst. inv_get.
        exploit H7; eauto.
        eapply H; eauto.
        -- assert (SAT2:satisfiesAll V Γ2). {
             eapply Ent in SAT; eauto.
           }
           rewrite satisfiesAll_union; split.
           ++ exploit EqnFVF; eauto.
             edestruct H8; eauto; dcr. simpl in *.
             eapply satisfiesAll_subst
             with (G:=eqns_freeVars x0 \ of_list Z); eauto.
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
                rewrite EqnFV. eauto.
        -- rewrite eqns_freeVars_union.
           rewrite EqnFV. edestruct H8; eauto; dcr. simpl in *.
           rewrite H14.
           exploit EqnFVF as EQ; eauto.
           rewrite EQ. simpl.
           clear; cset_tac.
        -- exploit ParamEq; dcr; eauto; subst.
           eapply agree_on_onvLe_update_list. eauto.
        -- intros. eapply get_app_cases in H16. destruct H16.
           ++ inv_get. edestruct H8; try eapply H13; eauto; dcr. simpl in *.
             rewrite H15. split; eauto with cset.
             exploit EqnFVF; eauto.
             rewrite get_app_lt in H14; eauto with len. inv_get. simpl in *.
             rewrite H5; split; eauto.
             eapply agree_on_update_list_dead; eauto with len.
           ++ dcr; simpl in *. rewrite Len1 in *.
             rewrite get_app_ge in H14; eauto with len.
             rewrite get_app_ge in H15; eauto with len.
             len_simpl.
             exploit EEQ; eauto; dcr.
             edestruct H8; try eapply H13; eauto; dcr.
             rewrite H5. simpl. split. eauto with cset.
             simpl in *. split; eauto.
             eapply agree_on_update_list_dead; eauto.
             rewrite H23. eauto.
      * hnf. intros. simpl in *. subst. inv_get. exploit ParamEq; dcr; eauto.
    + pe_rewrite. eauto.
    + intros. eapply get_app_cases in H2. destruct H2.
      ++ inv_get. pe_rewrite. split; eauto.
        exploit EqnFVF; eauto.
        rewrite get_app_lt in H0; eauto with len. inv_get. simpl in *.
        rewrite H1; split; eauto.
      ++ dcr; simpl in *. rewrite Len1 in *.
        rewrite get_app_ge in H0; eauto with len.
        rewrite get_app_ge in H1; eauto with len.
        len_simpl.
        exploit EEQ; eauto; dcr.
        pe_rewrite. split; eauto.
Qed.
