Require Import CSet Le.

Require Import Plus Util AllInRel Map LengthEq.
Require Import CSet Val Var Env Equiv.Sim IL Fresh Annotation Coherence RenamedApart.

Require Import SetOperations Liveness Eqn SimF OptionR.

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
    -> entails Gamma (subst_eqns (sid [Z <-- Y']) Γf)
    -> entails Gamma (list_EqnApx Y Y')
    -> eqn_sound ZL Δ Γ (stmtApp l Y) (stmtApp l Y') Gamma (ann0 (G,G'))
| EqnReturn ZL Δ Γ e e' Gamma G G'
  : entails Gamma {(EqnApx e e')}
    -> eqn_sound ZL Δ Γ (stmtReturn e) (stmtReturn e') Gamma (ann0 (G,G'))
| EqnExtern x f ZL Δ Γ s s' Y Y' Gamma G G' ang
  : eqn_sound ZL Δ Γ s s' Gamma ang
    -> entails Gamma (list_EqnApx Y Y')
    -> list_union (List.map Op.freeVars Y') ⊆ G
    -> length Y = length Y'
    -> eqn_sound ZL Δ Γ (stmtLet x (Call f Y) s) (stmtLet x (Call f Y') s') Gamma
                (ann1 (G,G') ang)
| EqnFun ZL Δ Γ ΓF F F' t t'  Gamma Γ2 G G' angs angb
  : length(ΓF) = length F 
    -> length F = length F'
    -> (forall n Z s Z' s' , get F n (Z, s) -> get F' n (Z', s') -> Z = Z')
    -> (forall n Z s Z' s' EqS angn , get F n (Z, s) -> get F' n (Z', s')  -> get ΓF n EqS -> get angs n angn
                                ->  eqn_sound (List.map fst F ++ ZL) ((List.map (fun _ => G) F) ++ Δ) (ΓF ++Γ)  s s' (EqS ∪ Γ2) angn)
    -> eqn_sound (List.map fst F ++ ZL) ((List.map (fun _ => G) F) ++ Δ) (ΓF ++Γ)  t t' Gamma angb
(*  -> eqns_freeVars EqS ⊆ G ++ of_list Z
  -> eqns_freeVars Γ2  ⊆ G *)
  -> entails Gamma Γ2
  -> eqn_sound ZL Δ Γ (stmtFun F t) (stmtFun F' t') Gamma
              (annF (G,G') angs angb)
| EqnUnsat ZL Δ Γ s s' Gamma ang
  : unsatisfiable Gamma
    -> eqn_sound ZL Δ Γ s s' Gamma ang.



Instance subst_exp_Proper Z Y
  : Proper (_eq ==> _eq) (subst_op (sid [Z <-- Y])).
Proof.
  hnf; intros. inv H. clear H.
  simpl. general induction y; simpl; eauto.
Qed.

Instance subst_eqn_Proper ϱ
  : Proper (_eq ==> _eq) (subst_eqn ϱ).
Proof.
  hnf; intros. invc H. simpl in *; subst. reflexivity.
Qed.

Instance subst_eqns_morphism
: Proper (eq ==> Equal ==> Equal) subst_eqns.
Proof.
  unfold Proper, respectful, subst_eqns; intros; subst.
  eapply map_Proper; eauto.
  hnf; intros; split.
  reflexivity.
  split; eauto using subst_eqn_Proper.
Qed.

Instance subst_eqns_morphism_subset
: Proper (eq ==> Subset ==> Subset) subst_eqns.
Proof.
  unfold Proper, respectful, subst_eqns; intros; subst.
  rewrite H0. reflexivity.
Qed.

Instance subst_eqns_morphism_subset_flip
: Proper (eq ==> flip Subset ==> flip Subset) subst_eqns.
Proof.
  unfold Proper, respectful, subst_eqns; intros; subst.
  rewrite H0. reflexivity.
Qed.

Lemma in_subst_eqns (Gamma:eqns) ϱ gamma
  : gamma ∈ Gamma
    -> subst_eqn ϱ gamma ∈ subst_eqns ϱ Gamma.
Proof.
  intros. unfold subst_eqns.
  eapply map_1; eauto. intuition.
Qed.


Instance exp_freeVars_Proper
  :  Proper (eq ==> Equal) Exp.freeVars.
Proof.
  unfold Proper, respectful; intros.
  inv H. general induction y; simpl; hnf; intuition.
Qed.

Instance freeVars_Proper
  :  Proper (_eq ==> _eq) freeVars.
Proof.
  hnf; intros. inv H. reflexivity.
Qed.

Lemma eqns_freeVars_incl (Gamma:eqns) gamma
  : gamma ∈ Gamma
    -> freeVars gamma ⊆ eqns_freeVars Gamma.
Proof.
  intros. unfold eqns_freeVars.
  hnf; intros. eapply fold_union_incl; eauto.
  eapply map_1; eauto. eapply freeVars_Proper.
Qed.

Lemma eqns_freeVars_union Gamma Γ'
  : eqns_freeVars (Gamma ∪ Γ') [=] eqns_freeVars (Gamma) ∪ eqns_freeVars Γ'.
Proof.
  unfold eqns_freeVars.
  rewrite map_app; eauto using freeVars_Proper.
  rewrite fold_union_app. reflexivity.
Qed.

Lemma fold_union_add X `{OrderedType X} x Γ
: fold union ({x; Γ}) {}[=]
  x ∪ fold union Γ {}.
Proof.
  assert ({x; Γ} [=] {{x}} ∪ Γ).
  cset_tac; intuition. rewrite H0.
  rewrite fold_union_app.
  rewrite fold_single; eauto using Equal_ST, union_m, transpose_union.
  cset_tac; intuition.
Qed.

Lemma eqns_freeVars_add Gamma e
  : eqns_freeVars {e; Gamma} [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars.
  rewrite map_add; eauto using freeVars_Proper.
  rewrite fold_union_add.
  cset_tac; intuition.
Qed.

Lemma eqns_freeVars_add2 Gamma e e'
  : eqns_freeVars ({e; { e'; Gamma } }) [=] eqns_freeVars (Gamma) ∪ freeVars e ∪ freeVars e'.
Proof.
  intros. unfold eqns_freeVars.
  repeat rewrite map_add; eauto using freeVars_Proper.
  repeat rewrite fold_union_add.
  cset_tac; intuition.
Qed.

Lemma eqns_freeVars_add' Gamma e
  : eqns_freeVars ({e ; Gamma}) [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars.
  rewrite map_add, fold_union_add.
  cset_tac; intuition. intuition.
Qed.

Ltac dowith c t :=
  match goal with
    | [ H : c _ _ _ _ |- _ ] => t H
  end.

Lemma satisfiesAll_union E Gamma Γ'
  : satisfiesAll E (Gamma ∪ Γ')
    <-> satisfiesAll E Gamma /\ satisfiesAll E Γ'.
Proof.
  split.
  intros H; split; hnf; intros; eapply H; cset_tac; intuition.
  intros [A B]; hnf; intros. cset_tac.
Qed.

Lemma satisfies_update_dead E gamma x v
: satisfies E gamma
  -> x ∉ freeVars gamma
  -> satisfies (E[x <- v]) gamma.
Admitted.
(*
Proof.
  admit.
Qed.
  intros.
  destruct gamma; simpl in * |- *.
  - inv H. symmetry in H2. symmetry in H1.
    erewrite exp_eval_agree; try eapply H1.
    symmetry.
    erewrite exp_eval_agree; try eapply H2.
    econstructor; reflexivity.
    symmetry. eapply agree_on_update_dead; eauto.
    cset_tac; intuition.
    symmetry. eapply agree_on_update_dead; eauto.
    cset_tac; intuition.
  - inv H.
    + symmetry in H2.
      erewrite exp_eval_agree; try eapply H2. econstructor.
      symmetry. eapply agree_on_update_dead; eauto.
      cset_tac; intuition.
    + symmetry in H1. symmetry in H2.
      erewrite exp_eval_agree; try eapply H1.
      erewrite exp_eval_agree; try eapply H2.
      econstructor; reflexivity.
      symmetry. eapply agree_on_update_dead; eauto.
      cset_tac; intuition.
      symmetry. eapply agree_on_update_dead; eauto.
      cset_tac; intuition.
  - eauto.
Qed.
 *)
Lemma satisfiesAll_add E gamma Gamma
  : satisfiesAll E {gamma ; Gamma}
    <-> satisfies E gamma /\ satisfiesAll E Gamma.
Proof.
  split.
  intros H; split; hnf; intros; eapply H; cset_tac; intuition.
  intros [A B]; hnf; intros. cset_tac; intuition.
  destruct H0; dcr; subst; eauto.
Qed.
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
  decide (v ∈ of_list Z).
  eapply length_length_eq in H.
  general induction H; simpl in * |- *; eauto.
  symmetry in H0. monad_inv H0. simpl.
  lud; eauto. eapply IHlength_eq; eauto.
  cset_tac; intuition.
  repeat rewrite lookup_set_update_not_in_Z; eauto.
  erewrite IHe; eauto.
  erewrite IHe1; eauto.
  erewrite IHe2; eauto.
Qed.


Lemma agree_on_onvLe X (V V': onv X) x v
  :onvLe V V'
         -> onvLe (V [x <- v]) (V' [x <- v]).
Proof.
  intros. hnf. intros.
  decide (x0 = x).
  - subst. lud. eauto.
  - lud. eapply H. eauto.
Qed.


    
Lemma agree_on_onvLe_update_list {X} `{OrderedType.OrderedType X} (V V':onv X) Z vl
: onvLe V V'
  -> onvLe (V [Z <-- vl]) (V' [Z <-- vl]).
Proof.
  intros; hnf; intros.
  decide (x ∈ of_list Z).
  - general induction Z; simpl in * |- *; eauto.
    + cset_tac; intuition.
    + destruct vl.
      * rewrite H1. eapply H0 in H1. eauto.
      * lud. erewrite IHZ; eauto. cset_tac; intuition.
  - rewrite lookup_set_update_not_in_Z; eauto.
    rewrite lookup_set_update_not_in_Z in H1; eauto.
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


Lemma entails_subset Γ Γ'
  : Γ' ⊆ Γ
    -> entails Γ Γ'.
Proof.
  unfold entails, satisfiesAll; intuition.
Qed.


Lemma entails_add Gamma gamma Γ'
: entails Gamma ({{gamma}} ∪ Γ')
  -> entails Gamma Γ'.
Proof.
  unfold entails; intros; dcr; intros.
  - hnf; intros. eapply H; eauto. cset_tac; intuition.
Qed.

Lemma entails_add' Gamma gamma Γ'
: entails Gamma Γ'
  -> entails Gamma {{gamma}}
  -> entails Gamma {gamma; Γ'}.
Proof.
  unfold entails; intros; dcr; intros.
  - hnf; intros. cset_tac; intuition.
    + eapply H0; cset_tac; intuition.
    + eapply H; eauto.
Qed.


Lemma entails_monotonic_add Gamma Γ' gamma
: entails Gamma Γ' -> entails (gamma ∪ Gamma) Γ'.
Proof.
  unfold entails; intros; dcr.
  - hnf; intros. eapply H. hnf; intros. eapply H0. cset_tac; intuition. eauto.
Qed.

Lemma entails_union_split Gamma Γ' Γ''
: entails Gamma (Γ' ∪ Γ'')
-> entails Gamma (Γ')
/\ entails Gamma (Γ'').
Proof.
  unfold entails, satisfiesAll.
  split; intros; dcr.
    + eapply H; eauto. cset_tac; intuition.
    + eapply H; eauto. cset_tac; intuition.
Qed.

Lemma entails_union Gamma Γ' Γ''
: entails Gamma (Γ')
/\ entails Gamma (Γ'')
-> entails Gamma (Γ' ∪ Γ'').
Proof.
  unfold entails, satisfiesAll.
  intros; dcr.
  + intros. cset_tac. 
Qed.

Lemma entails_add_single Gamma gamma Γ'
  : entails Gamma Γ'
    -> entails Gamma {gamma}
    -> entails Gamma {gamma; Γ'}.
Proof.
  unfold entails; intros; dcr; intros.
  - hnf; intros. cset_tac; intuition.
    + eapply H0; cset_tac; intuition.
    + eapply H; eauto.
Qed.

Instance satisfiesAll_Equal_morphism
  : Proper (eq ==> Equal ==> iff) satisfiesAll.
Proof.
  unfold Proper, respectful; intros; subst.
  intuition. hnf; intros. eapply H. eapply H0; eauto.
  hnf; intros. eapply H. eapply H0; eauto.
Qed.


Lemma entails_monotone Γ1 Γ2 Γ1'
: entails Γ1 Γ2
  -> Γ1 ⊆ Γ1'
  -> entails Γ1' Γ2.
Proof.
  unfold entails; intros; dcr.
  - intros. eapply H. hnf; intros. eapply H1; eauto.
Qed.


Instance entails_morphism_add gamma
: Proper (entails ==> entails) (add gamma).
Proof.
  unfold Proper, respectful; intros.
  eapply entails_add'.
  - eapply entails_monotone; cset_tac; eauto.
  - eapply entails_subset; cset_tac; eauto.
Qed.


Instance map_freeVars_morphism
: Proper (Subset ==> Subset) (map freeVars).
Proof.
  unfold Proper, respectful; intros.
  hnf; intros. eapply map_iff; eauto using freeVars_Proper.
  eapply map_iff in H0; eauto using freeVars_Proper.
  destruct H0; dcr. eexists x0; split; eauto.
Qed.

Instance eqns_freeVars_morphism
: Proper (Subset ==> Subset) eqns_freeVars.
Proof.
  unfold Proper, respectful, eqns_freeVars; intros.
  rewrite H. reflexivity.
Qed.

Instance eqns_freeVars_morphism_flip
: Proper (flip Subset ==> flip Subset) eqns_freeVars.
Proof.
  unfold Proper, respectful, eqns_freeVars, flip; intros.
  rewrite H. reflexivity.
Qed.

Instance eqns_freeVars_morphism_equal
: Proper (Equal ==> Equal) eqns_freeVars.
Proof.
  unfold Proper, respectful, eqns_freeVars, flip; intros.
  rewrite H. reflexivity.
Qed.

Instance entails_morphism_impl
: Proper (Subset ==> flip Subset ==> impl) entails.
Proof.
  unfold Proper, respectful, flip, impl, entails, satisfiesAll; intros; dcr; intros.
  eapply H1; eauto.
Qed.

Instance entails_morphism_flip_impl
: Proper (flip Subset ==> Subset ==> flip impl) entails.
Proof.
  unfold Proper, respectful, flip, impl, entails, satisfiesAll; intros; dcr; intros.
  eapply H1; eauto.
Qed.


Instance entails_morphism_impl_iff
: Proper (Equal ==> Equal ==> iff) entails.
Proof.
  unfold Proper, respectful, flip; intros; dcr; split; intros.
  - eapply entails_morphism_impl; eauto.
    + rewrite H; reflexivity.
    + rewrite H0; reflexivity.
  - eapply entails_morphism_impl; eauto.
    + rewrite H; reflexivity.
    + rewrite H0; reflexivity.
Qed.

Lemma entails_union' Gamma Γ' Γ'' Γ'''
  : Γ''' ⊆ Γ' ∪ Γ''
    -> entails Gamma (Γ')
    -> entails Gamma (Γ'')
    -> entails Gamma (Γ''').
Proof.
  intros; hnf; intros; hnf; intros.
  rewrite H in H3. cset_tac.
  - eapply H0; eauto.
  - eapply H1; eauto.
Qed.

Instance entails_refl
  : Reflexive (entails).
Proof.
  hnf; intros. unfold entails; intros; eauto; try reflexivity.
Qed.

Lemma entails_empty s
  : entails s ∅.
Proof.
  hnf; intros. intros.
  - hnf; intros. cset_tac; intuition.
Qed.

Lemma entails_eqns_trans Gamma e e' e''
  : EqnEq e e' ∈ Gamma
    -> EqnEq e' e'' ∈ Gamma
    -> entails Gamma {EqnEq e e''}.
Proof.
  intros. hnf; intros.
  hnf; intros. cset_tac. hnf; intros. rewrite <- H2.
  exploit (H1 _ H); eauto.
  exploit (H1 _ H0); eauto.
  simpl in *. inv H3; inv H4; eauto using OptionR.option_R; try congruence.
Qed.


Lemma entails_eqns_apx_refl e Gamma
  : entails Gamma {EqnApx e e}.
Proof.
  hnf; intros. hnf; intros. hnf; intros. cset_tac. rewrite <- H0.
  reflexivity.
Qed.

(*
Lemma satisfiesAll_subst V Gamma Γf Z EqS Y y bE G
:  length Z = length Y
   -> eqns_freeVars EqS ⊆ G ∪ of_list Z
   -> G ∩ of_list Z [=] ∅
   -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
   -> satisfiesAll V Gamma
   -> agree_on eq G V bE
   -> ⎣y ⎦ = omap (op_eval V) Y
   -> satisfiesAll bE Γf
   -> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  revert_except EqS. pattern EqS. eapply set_induction; intros.
  - hnf; intros. eapply empty_is_empty_1 in H.
    exfalso. rewrite H in H8. cset_tac; intuition.
  - hnf; intros. eapply Add_Equal in H1. rewrite H1 in H10.
    eapply add_iff in H10. destruct H10.
    + hnf in H10; subst.
      specialize (H5 V H6 (subst_eqn (sid [Z <-- Y]) gamma)). exploit H5.
      eapply in_subst_eqns; eauto. rewrite H1. cset_tac; intuition.
      hnf in X. destruct gamma. simpl in *. inv X.
      * do 2 erewrite <- eval_exp_subst in X; eauto.
        erewrite exp_eval_agree; [| |reflexivity].
        erewrite exp_eval_agree with (e:=e'); [| |reflexivity].
        eapply X.
        eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto.
        assert (EqnEq e e' ∈ s'). rewrite H1.
        cset_tac; intuition.
        exploit eqns_freeVars_incl; eauto. simpl in *.
        rewrite H3 in X0.
        rewrite <- (minus_union_set _ _ _ H4); eauto.
        rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
        rewrite map_length. simpl in *.
        exploit omap_length; eauto. congruence.
        eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto.
        assert (EqnEq e e' ∈ s'). rewrite H1.
        cset_tac; intuition.
        exploit eqns_freeVars_incl; eauto.
        rewrite H3 in X0. simpl in X0.
        rewrite <- (minus_union_set _ _ _ H4); eauto.
        rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
        rewrite map_length. simpl in *.
        exploit omap_length; eauto. congruence.
      * simpl in * |- *.
        do 2 erewrite <- eval_exp_subst in X; eauto.
        erewrite exp_eval_agree; [| |reflexivity].
        erewrite exp_eval_agree with (e:=e'); [| |reflexivity].
        eapply X.
        eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto.
        assert (EqnApx e e' ∈ s'). rewrite H1.
        cset_tac; intuition.
        exploit eqns_freeVars_incl; eauto. simpl in *.
        rewrite H3 in X0.
        rewrite <- (minus_union_set _ _ _ H4); eauto.
        rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
        rewrite map_length. simpl in *.
        exploit omap_length; eauto. congruence.
        eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto.
        assert (EqnApx e e' ∈ s'). rewrite H1.
        cset_tac; intuition.
        exploit eqns_freeVars_incl; eauto.
        rewrite H3 in X0. simpl in X0.
        rewrite <- (minus_union_set _ _ _ H4); eauto.
        rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
        rewrite map_length. simpl in *.
        exploit omap_length; eauto. congruence.
      * simpl in *; eauto.
    + rewrite H1 in H5.
      eapply H; try eapply H7; eauto.
      rewrite <- H3. rewrite H1.
      rewrite eqns_freeVars_add'. cset_tac; intuition.
      eapply entails_morphism_impl; eauto. reflexivity.
      unfold flip. eapply subst_eqns_morphism_subset; eauto.
      cset_tac; intuition.
Qed.
 *)
Lemma in_eqns_freeVars x gamma Gamma
  : x \In freeVars gamma
    -> gamma ∈ Gamma
    -> x \In eqns_freeVars Gamma.
Proof. 
  intros. eapply eqns_freeVars_incl; eauto.
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
Lemma satisfiesAll_monotone E Gamma Γ'
: satisfiesAll E Gamma
  -> Γ' ⊆ Gamma
  -> satisfiesAll E Γ'.
Proof.
  intros. hnf; intros. eapply H; eauto.
Qed.

Lemma not_entails_antitone Gamma Γ' gamma
: not_entails Γ' gamma
  -> Gamma ⊆ Γ'
  -> not_entails Gamma gamma.
Proof.
  intros. hnf; intros.
  edestruct H as [E ?]; dcr.
  eexists E; intros; split; eauto using satisfiesAll_monotone; eauto.
Qed.

Lemma unsatisfiable_monotone Gamma Γ'
: unsatisfiable Gamma
  -> Gamma ⊆ Γ'
  -> unsatisfiable Γ'.
Proof.
  intros. hnf; intros. intro. eapply H.
  eapply satisfiesAll_monotone; eauto.
Qed.

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
  - econstructor; intros; eauto using entails_monotone, not_entails_antitone.
    eapply IHeqn_sound1; eauto using not_entails_antitone. rewrite H1; reflexivity.
    eapply IHeqn_sound2; eauto using not_entails_antitone. rewrite H1. reflexivity.
  - econstructor; eauto using entails_monotone.
  - econstructor; eauto using entails_monotone.
  - econstructor; eauto using entails_monotone.
  - econstructor; eauto.
    + rewrite <- H7; eauto.
Qed.


Instance entails_entails_morphism_impl
: Proper (flip entails ==> entails ==> impl) entails.
Proof.
  unfold Proper, respectful, flip, impl, entails; intros; dcr; intros; eauto.
Qed.

Instance entails_entails_morphism_flip_impl
: Proper (entails ==> flip entails ==> flip impl) entails.
Proof.
  unfold Proper, respectful, flip, impl, entails; intros; dcr; intros; eauto.
Qed.

Lemma entails_inert Γ1 Γ2 Γ2'
: entails Γ2 Γ2'
  -> entails (Γ1 ∪ Γ2) (Γ1 ∪ Γ2').
Proof.
  unfold entails; intros; dcr.
  - eapply satisfiesAll_union.
    eapply satisfiesAll_union in H0.
    dcr; split; eauto.
Qed.

Lemma entails_inert_add x Γ2 Γ2'
  : entails Γ2 Γ2'
    -> entails {x ; Γ2} {x ; Γ2'}.
Proof.
  unfold entails; intros; dcr.
  - hnf; intros. cset_tac; intuition.
    eapply H; eauto. hnf; intros; eapply H0.
    cset_tac; intuition.
Qed.

Lemma entails_transitive Γ Γ' Γ''
  : entails Γ Γ' -> entails Γ' Γ'' -> entails Γ Γ''.
Proof.
  intros; hnf; intros.
  - eapply H0; eauto.
Qed.

Instance entails_trans : Transitive entails.
Proof.
  hnf.
  eapply entails_transitive.
Qed.

Lemma not_entails_entails_antitone Gamma Γ' gamma
  : not_entails Γ' gamma
    -> entails Γ' Gamma
    -> not_entails Gamma gamma.
Proof.
  intros. hnf; intros.
  edestruct H as [E ?]; dcr.
  eexists E; intros; split; eauto.
Qed.

Lemma unsatisfiable_entails_monotone Gamma Γ'
  : unsatisfiable Gamma
    -> entails Γ' Gamma
    -> unsatisfiable Γ'.
Proof.
  intros. hnf; intros. intro. exploit (H E); eauto.
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
  - econstructor; intros; eauto using entails_transitive,
                          not_entails_entails_antitone.
    + eapply IHeqn_sound1; eauto using not_entails_entails_antitone.
      rewrite H1. reflexivity.
    + eapply IHeqn_sound2; eauto using not_entails_entails_antitone.
      rewrite H1. reflexivity.
  - econstructor; eauto using entails_transitive.
  - econstructor; eauto using entails_transitive.
  - econstructor; eauto using entails_transitive, entails_monotone.
  - econstructor; eauto.
    + etransitivity; eauto.
Qed.


Lemma omap_exp_eval_onvLe Y E E' v
  : onvLe E E'
    -> omap (op_eval E) Y = Some v
    -> omap (op_eval E') Y = Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  simpl in H0. rewrite H0.
  monad_inv H0.
  erewrite exp_eval_onvLe; try eapply H; eauto. simpl.
  erewrite IHY; eauto; simpl; eauto.
Qed.

Lemma omap_satisfies_list_EqnApx V Y Y' v
  : length Y = length Y'
    -> satisfiesAll V (list_EqnApx Y Y')
    -> omap (op_eval V) Y = ⎣ v ⎦
    -> omap (op_eval V) Y' = ⎣ v ⎦.
Proof.
  intros. length_equify.
  general induction H; simpl in * |- *; eauto.
  monad_inv H1.
  exploit H0. eapply add_1. reflexivity. inv H1. congruence.
  simpl. erewrite IHlength_eq; eauto. rewrite EQ1. reflexivity.
  eapply satisfiesAll_monotone; eauto.
  unfold list_EqnApx; simpl in *.
  cset_tac; intuition.
Qed.
(*
Definition ArgRel' (Z:params ) (VL VL': list val) : Prop :=
  
(*  /\ satisfiesAll ([Z <-- List.map Some VL]) (EqS ∪ Gamma)*).

Definition ParamRel' (Zb:params) (Z Z' : list var) : Prop :=
 *)


Instance AR : PointwiseProofRelationF params:= {
                                                ArgRelFP Z VL VL' := length Z = length VL /\ VL = VL';
                                                ParamRelFP Z Z' Zb := Z = Z' /\ Zb = Z'
                                              }.


Lemma sim_let_op_apx X (IST:ILStateType X) r (L L':X) V V' x x' e e' s s'
      (EQ: fstNoneOrR eq (op_eval V e) (op_eval V' e'))
      (SIM: forall v, op_eval V e = Some v
                 -> (sim r \3/ r) Sim (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim r Sim (L, V, stmtLet x (Operation e) s) (L', V', stmtLet x' (Operation e') s').
Proof.
  inv EQ.
  -  pfold ; eapply SimErr;
       [ | eapply star2_refl | ].
     + apply result_none.  inversion 1.
     + eapply let_op_normal. eauto.
  -  pfold; eapply SimSilent; [ eapply plus2O
                              | eapply plus2O
                              | ].
     eapply step_let_op; eauto. eauto.
     eapply step_let_op.  eauto. eauto.
     eapply SIM; eauto.
Qed.

Lemma satisfies_fstNoneOrR_apx V e e' :
  satisfies V (EqnApx e e') -> fstNoneOrR eq (op_eval V e) (op_eval V e').
Proof.
  intros. eauto.
Qed.

Lemma sim_cond_op_apx X (IST:ILStateType X) r (L L':X) V V' e e' s1 s1' s2 s2'
      (EQ:  fstNoneOrR eq (op_eval V e) (op_eval V' e'))
      (SIM1: forall v, op_eval V e = Some v -> val2bool v = true ->
                  (sim r \3/ r) Sim (L, V, s1) (L', V', s1'))
      (SIM2: forall v, op_eval V e = Some v -> val2bool v = false ->
                  (sim r \3/ r) Sim (L, V, s2) (L', V', s2'))
  : sim r Sim (L, V, stmtIf e s1 s2) (L', V', stmtIf e' s1' s2').
Proof.
  inv EQ.
  - pfold; eapply SimErr;
      [|eapply star2_refl|].
    + apply result_none. inversion 1.
    + eapply cond_normal. eauto.
  -  case_eq (val2bool y); intros.
     + pfold; eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply SIM1; eauto];
       eapply step_cond_true; eauto.    
     + pfold; eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply SIM2; eauto];
       eapply step_cond_false; eauto.
Qed.

Lemma sim_return_apx X (IST:ILStateType X) r (L L':X) V V' e e' 
  :fstNoneOrR eq (op_eval V e) (op_eval V' e') -> sim r Sim (L, V, stmtReturn e) (L', V', stmtReturn e').
Proof.
  intros. inv H.
  - pfold; eapply SimErr; [|eapply star2_refl|].
    + rewrite result_return. eauto.
    + apply return_normal.
  - pfold; eapply SimTerm; [|eapply star2_refl|eapply star2_refl| | ].
    + rewrite! result_return. congruence.
    + apply return_normal.
    + apply return_normal.
Qed.


Lemma sim_let_call_apx X (IST:ILStateType X) r (L L':X) V V' x x' f Y Y' s s'
      (EQ: fstNoneOrR eq  (omap (op_eval V) Y)  (omap (op_eval V') Y'))
      (SIM: forall v, (sim r \3/ r) Sim (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim r Sim (L, V, stmtLet x (Call f Y) s) (L', V', stmtLet x' (Call f Y') s').
Proof.
  inv EQ.
  - pfold. eapply SimErr; [|eapply star2_refl | ]; [ simpl  | ].
    + rewrite !result_none; isabsurd; eauto.
    + eapply let_call_normal; eauto.
  - symmetry in H0, H. 
    pfold; eapply SimExtern;
      [ eapply star2_refl
      | eapply star2_refl
      | step_activated; eauto using step_let_call
      | step_activated; eauto using step_let_call | |];
      intros ? ? STEP; eapply let_call_inversion in STEP; dcr; subst; eexists; split; try eapply step_let_call; eauto; congruence.  
Qed.

Lemma onvLe_op_eval_some V V' e v
  :onvLe V V' -> op_eval V e = ⎣ v ⎦ -> op_eval V' e = ⎣ v ⎦.
Proof.
  intros. general induction e; simpl in * |- * ; eauto using @fstNoneOrR.
  - rewrite H0. exploit H; eauto.
  - monad_inv H0. rewrite EQ. simpl. rewrite (IHe V V' x); eauto.
  - monad_inv H0. rewrite EQ1. rewrite EQ. simpl. erewrite IHe1; eauto. erewrite IHe2; simpl; eauto.
Qed.


Lemma onvLe_fstNoneOrR_apx V V' e :
  onvLe V V' -> fstNoneOrR eq (op_eval V e) (op_eval V' e).
Proof with simpl; eauto using @fstNoneOrR, @onvLe_op_eval_some.
  intros. case_eq (op_eval V e) ...
  intros. erewrite onvLe_op_eval_some... 
Qed.

Lemma satisfies_EqnEq_on_update   (x:var) e V v:
  op_eval V e = ⎣ v ⎦   -> x ∉ Op.freeVars e  ->satisfies (V [x <- ⎣ v ⎦]) (EqnEq(Var x) e).
Proof.
  intros. unfold satisfies. simpl. lud; eauto.
    erewrite op_eval_live.
    -  rewrite <- H. reflexivity.
    - eapply Op.live_freeVars.
    - eapply agree_on_update_dead; eauto.
Qed.



Lemma op_eval_true_satisfies  V e v 
        : op_eval V e = ⎣ v ⎦ -> val2bool v = true -> satisfies V (EqnEq (UnOp UnOpToBool e) (Con val_true)).
Proof.
  intros. unfold satisfies. simpl. rewrite H. simpl. unfold option_lift1. rewrite H0. simpl. reflexivity.
Qed.

Lemma op_eval_false_satisfies V e v
  : op_eval V e = ⎣ v ⎦ -> val2bool v = false -> satisfies V (EqnEq (UnOp UnOpToBool e) (Con val_false)).
Proof.
intros.  unfold satisfies. simpl. rewrite H. simpl. unfold option_lift1. rewrite H0. simpl. reflexivity.
Qed.

Lemma onvLe_omap_op_eval_some V V' Y vl
 : onvLe V V' -> (omap (op_eval V) Y) = ⎣ vl ⎦ -> (omap (op_eval V') Y) = ⎣ vl ⎦.
Proof.  
  intros.
  case_eq (omap (op_eval V) Y); simpl; eauto.
  intros. general induction Y; simpl in * |- *; eauto.
  monad_inv H0. monad_inv H1.
  rewrite EQ,EQ1. simpl. exploit IHY; eauto.
  rewrite H0. erewrite onvLe_op_eval_some; simpl in * |- *; eauto.
  congruence.
Qed.  

Lemma onvLe_omap_op_eval_fstNoneOrEq V V' Y
  : onvLe V V'
    -> fstNoneOrR eq (omap (op_eval V) Y) (omap (op_eval V') Y).
Proof.
  intros.
  case_eq (omap (op_eval V) Y); eauto using @fstNoneOrR.
  intros. exploit onvLe_omap_op_eval_some  ; eauto. rewrite H1.
  reflexivity.
Qed.
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



Lemma satisfies_omap_op_eval_fstNoneOrR V Y Y'
  : ❬Y❭ = ❬Y'❭
    -> satisfiesAll V (list_EqnApx Y Y')
    -> fstNoneOrR eq (omap (op_eval V) Y) (omap (op_eval V) Y').
Proof.
  intros.
  case_eq (omap (op_eval V) Y); eauto using fstNoneOrR.
  intros. length_equify. erewrite (@omap_satisfies_list_EqnApx V Y Y' l ) ; eauto using length_eq_length, fstNoneOrR.
Qed.

Lemma onvLe_op_eval_satisfies V V' e e' v
  : onvLe V V'
    -> op_eval V e = Some v
    -> satisfies V (EqnApx e e')
    -> satisfies V' (EqnApx e e').
Proof.
  intros.
  unfold satisfies in *. rewrite H0 in H1. inv H1.
  symmetry in H3. eapply onvLe_op_eval_some in H3; eauto. eapply onvLe_op_eval_some in H0; eauto.
  rewrite H0,H3. reflexivity.
Qed.            

Lemma onvLe_op_eval_satisfiesAll V V' Y Y' v
  : onvLe V V'
    -> ❬Y❭ = ❬Y'❭
    -> (omap (op_eval V) Y) = Some v
    -> satisfiesAll V (list_EqnApx Y Y')
    -> satisfiesAll V' (list_EqnApx Y Y').
Proof.
  intros.
  unfold satisfiesAll in *. intros.
  length_equify. general induction H0; simpl in * |- *;  eauto.
  - unfold list_EqnApx in H3. simpl in *. cset_tac.
  - unfold list_EqnApx in *. simpl in * |- *.
    cset_tac.
    + monad_inv H1.  rewrite <- H4. eapply onvLe_op_eval_satisfies; eauto.
    + monad_inv H1.  eapply IHlength_eq; eauto. 
Qed.


Lemma satisfiesAll_EqnEq_on_update V v x Gamma
  : satisfiesAll V Gamma
    -> x ∉ eqns_freeVars Gamma
    -> satisfiesAll (V [x <- ⎣ v ⎦] ) Gamma.
Proof.
  intros.
  unfold satisfiesAll in *.
  intros.
  eapply satisfies_update_dead; eauto.
  intros A. eapply H0. eapply in_eqns_freeVars; eauto.
Qed.



  
(*
  omap_satisfies_list_EqnApx, omap_exp_eval_onvLe
*)
  
Hint Resolve satisfies_fstNoneOrR_apx onvLe_fstNoneOrR_apx.

Lemma sim_vopt r L L' V V' s s' ZL Δ Γ Gamma ang
  : satisfiesAll V Gamma
    -> eqn_sound ZL Δ Γ s s' Gamma ang
    -> labenv_sim Sim (sim r) AR ZL L L'
    -> renamedApart s ang
    -> eqns_freeVars Gamma ⊆ fst (getAnn ang)
    -> onvLe V V'
    -> sim r Sim  (L,V, s) (L',V', s').
Proof.
  intros SAT EQN SIML REAPT FV OLE.
  general induction EQN; (try (now exfalso; eapply H; eauto))
  ; simpl; invt renamedApart; simpl in * |- *.
  - exploit H; eauto. exploit H1; eauto; [cset_tac|].  eapply (sim_let_op_apx il_statetype_F). 
    +  etransitivity; eauto.
    + intros. left. eapply IHEQN; eauto.
      *  unfold satisfiesAll.  intros. cset_tac.
         -- rewrite <- H5. eauto using satisfies_EqnEq_on_update.
         -- rewrite <- H4. eapply (@satisfies_EqnEq_on_update x e' V v); eauto. eapply satisfies_fstNoneOrR_apx in H2.
            rewrite H3 in H2.  inv H2. reflexivity.
         --  exploit SAT; eauto. apply satisfies_update_dead; eauto.
             intros X. apply H7. apply FV. eapply in_eqns_freeVars; eauto.
      * pe_rewrite. rewrite! eqns_freeVars_add. simpl. rewrite H0, H8, FV. clear. cset_tac.
      * eapply agree_on_onvLe; eauto.
  -  exploit H; eauto.  exploit H0; eauto; [cset_tac|].  eapply (sim_cond_op_apx il_statetype_F).
     + etransitivity; eauto.
     + intros. left. eapply IHEQN1; clear IHEQN1 IHEQN2; eauto.
       * apply satisfiesAll_add. eauto using  op_eval_true_satisfies.   
       * rewrite eqns_freeVars_add. simpl. pe_rewrite. intros a0 A. cset_tac.
     + intros. left. eapply IHEQN2; clear IHEQN1 IHEQN2; eauto.
       * apply satisfiesAll_add. eauto using op_eval_false_satisfies.
       * rewrite eqns_freeVars_add . pe_rewrite.  intros gamma A. cset_tac.
  - eapply labenv_sim_app; eauto; simpl.
    intros; split; intros; eauto.
    simpl in *.  destruct H7; subst. exists Yv; split; eauto.  eapply omap_exp_eval_onvLe; eauto.
    exploit H4; eauto. eapply omap_satisfies_list_EqnApx; eauto.
  - eapply (sim_return_apx il_statetype_F).
    exploit H; eauto. exploit H0; eauto; [cset_tac|]. etransitivity; eauto.
  -  exploit H; eauto.   eapply (sim_let_call_apx il_statetype_F); eauto; simpl.
     + case_eq (omap (op_eval V) Y); eauto using fstNoneOrR.
       intros. etransitivity; eauto using  onvLe_omap_op_eval_fstNoneOrEq.
       rewrite <- H3. eapply satisfies_omap_op_eval_fstNoneOrR; eauto.
     + intros. simpl. left. eapply IHEQN; eauto.
       * eauto using satisfiesAll_EqnEq_on_update.
       * pe_rewrite. cset_tac.
       * eauto using agree_on_onvLe.
  - pone_step. left. eapply IHEQN; eauto.
    + eapply labenv_sim_extension_ptw; eauto with len. 
      * intros. hnf. intros. simpl in * |- *. dcr. subst. inv_get.  eapply H3; eauto.
        -- clear IHEQN H3 H5 r0. (* indexwise *)
        -- exploit H12; eauto. 
        -- admit.
        -- exploit H1; eauto. subst.
          eapply agree_on_onvLe_update_list. eauto.
      * hnf. intros. simpl in *. subst. inv_get. exploit H1; eauto.
    + pe_rewrite. eauto.

        
        eapply satisfies_omap_op_eval_fstNoneOrR; eauto. eapply onvLe_op_eval_satisfiesAll; eauto.
        
        Lemma onvLe_op_eval_satisfies V V' e e' v
          : onvLe V V'
            -> op_eval V e = Some v
            -> satisfies V (EqnApx e e')
            -> satisfies V' (EqnApx e e').
        Proof.
          intros.
          unfold satisfies in *. rewrite H0 in H1. inv H1.
          symmetry in H3. eapply onvLe_op_eval_some in H3; eauto. eapply onvLe_op_eval_some in H0; eauto.
          rewrite H0,H3. reflexivity.
Qed.            

        Lemma onvLe_op_eval_satisfiesAll V V' Y Y' v
          : onvLe V V'
            -> ❬Y❭ = ❬Y'❭
            -> (omap (op_eval V) Y) = Some v
            -> satisfiesAll V (list_EqnApx Y Y')
            -> satisfiesAll V' (list_EqnApx Y Y').
        Proof.
          intros.
          unfold satisfiesAll in *. intros.
          length_equify. general induction H0; simpl in * |- *;  eauto.
          - unfold list_EqnApx in H3. simpl in *. cset_tac.
          - unfold list_EqnApx in *. simpl in * |- *.
            cset_tac.
            + monad_inv H1.  rewrite <- H4. eapply onvLe_op_eval_satisfies; eauto.
            + monad_inv H1.  eapply IHlength_eq; eauto. 
Qed.



  
                                       
             Lemma tmp V V' A :  onvLe V V' -> satisfiesAll V A -> satisfiesAll V' A.
        Proof.
          intros. unfold satisfiesAll. intros. unfold onvLe in H. exploit H0; eauto. destruct gamma; eauto.
          - simpl. 


          
  - exploit H; eauto. exploit X; eauto. cset_tac; reflexivity. inv X0.
    inv H2.
    + pfold. econstructor 3; try eapply star2_refl; eauto. stuck2.
    + pose proof H2. symmetry in H3. eapply exp_eval_onvLe in H3; eauto.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto using eq_sym. reflexivity.
      econstructor; eauto using eq_sym. reflexivity.
      left. eapply IHEQN; eauto.
      * eapply satisfiesAll_update; eauto.
      * {
          eapply simL'_update; eauto.
          - intros. hnf in H4.
            hnf. destruct x0 as [[[ ?] ?] ?]. dcr.
            repeat (split; eauto).
            rewrite H10, H12. simpl. clear_all; cset_tac; intuition.
            symmetry. eapply agree_on_update_dead.
            intro. eapply H7. eauto.
            symmetry; eauto.
            symmetry. eapply agree_on_update_dead.
            intro. eapply H7. eauto.
            symmetry; eauto.
          - intros; reflexivity.
        }
      * rewrite H10. simpl. rewrite eqns_freeVars_add2.
        rewrite FV. simpl. rewrite H8. rewrite H0.
        clear_all; cset_tac; intuition.
      * hnf; intros. lud; eauto.
  - exploit H; eauto. exploit X; eauto. cset_tac; reflexivity. inv X0.
    inv H1.
    + pfold. econstructor 3; try eapply star2_refl; eauto. stuck2.
    + pose proof H1. symmetry in H2. eapply exp_eval_onvLe in H2; eauto.
      pfold. case_eq (val2bool y); intros.
(*      assert (not_entails Gamma (UnOp 0 e, Con val_false)). {
        hnf; intros. eexists V; split; eauto.
        intro. hnf in H8. simpl in *.
        rewrite <- H4 in H8. inv H8.
        cbv in H7. destruct y. congruence.
        cases in H18. congruence. cbv in H18. congruence.
      } *)
      econstructor; try eapply plus2O.
      econstructor; eauto using eq_sym. reflexivity.
      econstructor; eauto using eq_sym. reflexivity.
      left. eapply IHEQN1; try eapply H9; eauto.
      * eapply satisfiesAll_add; split; eauto.
        hnf; intros.
        simpl. rewrite <- H0. unfold option_lift1. unfold comp; simpl.
        rewrite H3; constructor. reflexivity.
      * eapply simL'_update; eauto.
        unfold BlockRel.
        destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
        repeat (split; eauto).
        rewrite H12; eauto.
        clear_all; reflexivity.
      * rewrite eqns_freeVars_add. rewrite FV, H12.
        simpl. rewrite H7. cset_tac; intuition.
      * (* assert (not_entails Gamma (UnOp 0 e, Con val_true)). {
          hnf; intros. eexists V; split; eauto.
          intro. hnf in H8. simpl in *.
          rewrite <- H4 in H8. inv H8.
          cbv in H7. destruct y.
          cases in H18. cbv in H18. congruence.
          congruence. congruence.
        } *)
        econstructor; try eapply plus2O.
        econstructor 3; eauto using eq_sym. reflexivity.
        econstructor 3; eauto using eq_sym. reflexivity.
        {
          left. eapply IHEQN2; try eapply H13; eauto.
          - eapply satisfiesAll_add; split; eauto.
            hnf; intros. simpl. rewrite <- H0. unfold option_lift1.
            unfold comp; simpl. rewrite H3. constructor. reflexivity.
          - eapply simL'_update; eauto.
            unfold BlockRel.
            destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
            repeat (split; eauto).
            rewrite H13; eauto.
            clear_all; reflexivity.
          - rewrite eqns_freeVars_add; simpl.
            rewrite FV, H7, H13. simpl. cset_tac; intuition.
        }
  - destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length bZ = length Y).
    exploit H2; eauto. case_eq (omap (exp_eval V) Y); intros. Focus 2.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2.
    + pose proof H3.
      eapply omap_satisfies_list_EqnApx in H4; eauto.
      eapply omap_exp_eval_onvLe in H4; eauto.
      pose proof H3.
      eapply omap_satisfies_list_EqnApx in H5; eauto.
      edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H18. hnf in H21; simpl in H23; dcr; subst.
      eapply sim_drop_shift. eapply H24; eauto.
      hnf. simpl; repeat split.
      exploit omap_length; eauto. unfold var in *. congruence.
      eapply satisfiesAll_union; split; eauto.
      symmetry in H5.
      eapply (@satisfiesAll_subst V Gamma Γf); try eapply H5; eauto.
      congruence.
      symmetry; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length.
      exploit omap_length; eauto. congruence.
      rewrite <- H.
      revert H H25; clear_all; cset_tac; intuition; exfalso; eauto.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2; eauto.
      get_functional; subst. simpl in *. congruence.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2; eauto.
  - simpl. exploit H; eauto. exploit X. cset_tac; reflexivity. inv X0; eauto.
    inv H1.
    + pfold. econstructor 3; try eapply star2_refl. simpl. congruence.
      stuck2.
    + pfold. econstructor 4; try eapply star2_refl. simpl.
      erewrite <- exp_eval_onvLe in H0; eauto.
      stuck2. stuck2.
  - case_eq (omap (exp_eval V) Y); intros. Focus 2.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2.
    + pose proof H2.
      eapply omap_satisfies_list_EqnApx in H3; eauto.
      eapply omap_exp_eval_onvLe in H3; eauto.
      pfold. eapply sim'Extern; try eapply star2_refl.
      * exists (ExternI f l 0); eexists; econstructor; eauto.
      * pose proof H2. eapply omap_exp_eval_onvLe in H2; eauto.
        eexists (ExternI f l 0); eexists; econstructor; eauto.
      * { intros. inv H4.
          eexists. econstructor; eauto.
          - econstructor; eauto.
            eapply omap_exp_eval_onvLe; eauto.
            eapply omap_satisfies_list_EqnApx; eauto.
          - left. eapply IHEQN; eauto.
            + eapply satisfiesAll_update_dead_single; eauto.
            + eapply simL'_update; eauto.
              * unfold BlockRel'. intros. simpl in *.
                unfold BlockRel' in *.
                destruct x0 as [[[ ?] ?] ?]; simpl; intros; dcr.
                repeat (split; eauto).
                rewrite H12. rewrite H9. simpl. clear_all; cset_tac; intuition.
                symmetry. eapply agree_on_update_dead. rewrite H9. eauto.
                symmetry; eauto.
                symmetry. eapply agree_on_update_dead. rewrite H9. eauto.
                symmetry; eauto.
              * intros; reflexivity.
            + rewrite H12, FV; simpl. clear_all; cset_tac; intuition.
            + hnf; intros; lud; eauto.
        }
      * { intros. inv H4.
          eexists. econstructor; eauto.
          - econstructor; eauto.
            pose proof H2.
            erewrite <- omap_exp_eval_onvLe in H5; eauto. congruence.
          - left. eapply IHEQN; eauto.
            + eapply satisfiesAll_update_dead_single; eauto.
            + eapply simL'_update; eauto.
              * unfold BlockRel. intros. simpl in *.
                unfold BlockRel' in *.
                destruct x0 as [[[ ?] ?] ?]; simpl; intros; dcr.
                repeat (split; eauto).
                rewrite H9, H12. simpl. clear_all; cset_tac; intuition.
                symmetry. eapply agree_on_update_dead. rewrite H9. eauto.
                symmetry; eauto.
                symmetry. eapply agree_on_update_dead. rewrite H9. eauto.
                symmetry; eauto.
              * intros; reflexivity.
            + rewrite FV, H12; simpl. clear_all; cset_tac; intuition.
            + hnf; intros; lud; eauto.
        }
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IHEQN2; eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * eapply simL'_update; eauto.
        unfold BlockRel.
        destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
        repeat (split; eauto).
        rewrite H5, H15; reflexivity.
        clear_all; reflexivity.
      * hnf; split; intros. hnf; intuition.
        hnf in H2; dcr.
        eapply IHEQN1; try eapply H10; eauto.
        eapply simL'_update; eauto.
        unfold BlockRel. intros.
        destruct x as [[[ ?] ?] ?]; dcr. simpl in H2.
        simpl. dcr.
        assert (sEQ: s0 [=] s0 \ of_list Z). {
          assert (s0 ∩ of_list Z [=] ∅).
          rewrite <- H9. rewrite H15 in H17.
          revert H9 H17; simpl; clear_all; cset_tac; intuition; exfalso; eauto.
          rewrite <- (minus_union_set _ _ _ H2).
          clear_all; cset_tac; intuition.
        }
        repeat (split; eauto).
        rewrite H13. rewrite H17, H15; simpl. eapply incl_right.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto.
        congruence.
        symmetry; eauto.
        reflexivity.
        rewrite H13; simpl. rewrite eqns_freeVars_union.
        rewrite H, H0. clear_all; cset_tac; intuition.
        subst. eapply agree_on_onvLe; eauto.
      * hnf; split; eauto.
      * hnf; intros.
        simpl. split.
        rewrite <- H9. clear_all; cset_tac; intuition.
        split.
        rewrite H15; reflexivity.
        repeat (split; eauto using satisfiesAll_monotone; try reflexivity).
    + rewrite FV, H15; reflexivity.
Qed.

Print Assumptions sim_vopt.
