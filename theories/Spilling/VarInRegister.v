Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.
Require Import SpillSound DoSpill DoSpillRm SpillUtil ReconstrLive.
Require Import ReconstrLiveSmall ReconstrLiveSound SetUtil InVD.
Require Import ToBeOutsourced.

(** * VarInRegister *)

Inductive var_in_register
          (VD : ⦃var⦄)
  : stmt -> Prop
  :=
  | ViRLoad
      (x y : var)
      (s : stmt)
    : x ∈ VD
      -> y ∉ VD
      -> var_in_register VD s
      -> var_in_register VD (stmtLet x (Operation (Var y)) s)

  | ViRLet
      (x : var)
      (e : exp)
      (s : stmt)
    : Exp.freeVars e ⊆ VD
      -> var_in_register VD s
      -> var_in_register VD (stmtLet x e s)

  | ViRReturn
      (e : op)
    : Op.freeVars e ⊆ VD
      -> var_in_register VD (stmtReturn e)

  | ViRIf
      (e : op)
      (s : stmt)
      (t : stmt)
    : Op.freeVars e ⊆ VD
      -> var_in_register VD s
      -> var_in_register VD t
      -> var_in_register VD (stmtIf e s t)

  | ViRApp
      (f : lab)
      (Y : args)
    : var_in_register VD (stmtApp f Y) (* This can't be correct *)

  | ViRFun
      (F : list (params * stmt))
      (t : stmt)
    : (forall (Zs : params * stmt) n,
          get F n Zs
          -> var_in_register VD (snd Zs))
      -> var_in_register VD t
      -> var_in_register VD (stmtFun F t)
.


Lemma var_in_register_loads
      (VD : ⦃var⦄)
      (slot : var -> var)
      (xs : list var)
      (s : stmt)
  :
    of_list xs ⊆ VD
    -> disj VD (map slot VD)
    -> var_in_register VD s
    -> var_in_register VD (write_moves xs (slot ⊝ xs) s)
.
Proof.
  intros xs_VD disj_VD vir_s.
  general induction xs; simpl in *; eauto.
  rewrite add_union_singleton in xs_VD.
    apply union_incl_split2 in xs_VD as [a_VD xs_VD].
  econstructor; eauto.
  - intros N.
    eapply disj_VD; eauto.
    apply in_singleton.
    rewrite <- map_singleton.
    apply lookup_set_incl; eauto.
Qed.

Lemma var_in_register_spills
      (VD : ⦃var⦄)
      (slot : var -> var)
      (xs : list var)
      (s : stmt)
  :
    of_list xs ⊆ VD
    -> var_in_register VD s
    -> var_in_register VD (write_moves (slot ⊝ xs) xs s)
.
Proof.
  intros xs_VD vir_s.
  general induction xs;
    simpl in *; eauto.
  rewrite add_union_singleton in xs_VD.
  apply union_incl_split2 in xs_VD as [a_VD xs_VD].
  econstructor 2; simpl; eauto.
Qed.


Lemma ofl_el_Sp_VD
  :
    forall (Sp R VD : ⦃var⦄),
      R ⊆ VD
      -> Sp ⊆ R
      -> of_list (elements Sp) ⊆ VD
.
Proof.
  intros Sp R VD R_VD Sp_sub.
  rewrite of_list_elements, Sp_sub; assumption.
Qed.
Lemma ofl_el_L_VD
  :
    forall (L Sp R M VD : ⦃var⦄),
      R ⊆ VD
      -> M ⊆ VD

      -> L ⊆ Sp ∪ M
      -> Sp ⊆ R
      -> of_list (elements L) ⊆ VD
.
Proof.
  intros L Sp R M VD R_VD M_VD L_SpM Sp_R.
  rewrite of_list_elements, L_SpM, Sp_R, R_VD, M_VD.
  clear ; cset_tac.
Qed.



Lemma var_in_register_sound
      (k : nat)
      (slot : var -> var)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (ZL : list params)
      (VD R M G : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (al : ann ⦃var⦄)
      (Lv : list ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))

  : R ⊆ VD
    -> M ⊆ VD
    -> disj VD (map slot VD)
    -> union_fs (getAnn ra) ⊆ VD
    -> renamedApart s ra
    -> live_sound Imperative ZL Lv s al
    -> spill_live VD sl al
    -> spill_sound k ZL Λ (R,M) s sl
    -> var_in_register VD (do_spill slot s sl (compute_ib ⊜ ZL Λ))
.
Proof.
  intros R_VD M_VD disj_VD ra_VD rena lvSnd spilli spillSnd.
  time (general induction lvSnd;
    invc spilli;
    invc spillSnd;
    inv rena;
    apply renamedApart_incl in rena; eauto;
    simpl in *; eauto;
      eapply var_in_register_spills;
      simpl; eauto using ofl_el_Sp_VD;
        eapply var_in_register_loads;
        try   eapply (ofl_el_L_VD _ _ _ _ _ R_VD M_VD); eauto).
  - econstructor 2; eauto.
    + rewrite H15, H13, H12, R_VD, M_VD.
      clear; cset_tac.
    + eapply IHlvSnd with (R:={x; (R\K ∪ L) \Kx}) (M:=Sp ∪ M); eauto.
      * eapply Rx_VD with (VD:=VD) (R:=R) (L:=L) (M:=M); eauto.
        eapply x_VD; eauto.
      * rewrite H12, R_VD, M_VD.
        clear; cset_tac.
      * rewrite rena, <- ra_VD; eauto.

  - destruct rena as [rena1 rena2].
    econstructor; eauto.
    + rewrite H16, H15, H14, R_VD, M_VD; clear; cset_tac.
    + eapply IHlvSnd1 with (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
      * eapply R'_VD with (VD:=VD) (R:=R) (M:=M); eauto.
      * rewrite H14, R_VD, M_VD; clear; cset_tac.
      * rewrite rena1, <- ra_VD; eauto.
    + eapply IHlvSnd2 with (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
      * eapply R'_VD with (VD:=VD) (R:=R) (M:=M); eauto.
      * rewrite H14, R_VD, M_VD; clear; cset_tac.
      * rewrite rena2, <- ra_VD; eauto.
  - econstructor.
  - econstructor; simpl; eauto.
    rewrite H8, H7, H6, R_VD, M_VD; clear; cset_tac.
  - destruct rena as [renaF rena2].
    econstructor; simpl; eauto.
    + intros.
      inv_get.
      simpl.
      rewrite <- zip_app; [| eauto with len].
      exploit H24 as spillSnd'; try eassumption.
      exploit renaF as renaF'; try eassumption.
      exploit H2 as H2'; try eassumption.
      exploit H10 as rm_VD; try eassumption.
      destruct H2' as [H2' _].
      destruct rm_VD as [f_x0_VD s_x0_VD].
      rewrite pair_eta with (p:=x0) in spillSnd'.
      eapply H1 with (R:=fst x0) (M:=snd x0); eauto.
      rewrite renaF', <- ra_VD; eauto.
    + rewrite <- zip_app; [| eauto with len].
      eapply IHlvSnd with (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
      * eapply R'_VD with (VD:=VD) (M:=M); eauto.
      * rewrite H18, R_VD, M_VD; clear; cset_tac.
      * rewrite rena2, <- ra_VD; eauto.
Qed.
