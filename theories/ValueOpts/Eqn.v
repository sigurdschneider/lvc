Require Import CSet Le.

Require Import Plus Util AllInRel Map OptionR.
Require Import CSet Val Var Env Equiv.Sim IL Fresh Annotation.

Require Import SetOperations.

Set Implicit Arguments.
Unset Printing Records.

Inductive eqn :=
  | EqnEq (e e':op)
  | EqnApx (e e':op)
  | EqnBot.

Definition satisfies (E:onv val) (gamma:eqn) : Prop :=
match gamma with
| EqnEq e e' => option_R eq (op_eval E e) (op_eval E e')
| EqnApx e e' => fstNoneOrR eq (op_eval E e) (op_eval E e')
| EqnBot => False
end.

Inductive eqnLt : eqn -> eqn -> Prop :=
| EqnLtBotEq e e'
  : eqnLt EqnBot (EqnEq e e')
| EqnLtBotApx e e'
  : eqnLt EqnBot (EqnApx e e')
| EqnLtEqApx e1 e1' e2 e2'
  : eqnLt (EqnEq e1 e2) (EqnApx e1' e2')
| EqnLtEqEq1 e1 e1' e2 e2'
  : opLt e1 e1'
    -> eqnLt (EqnEq e1 e2) (EqnEq e1' e2')
| EqnLtEqEq2 e1 e2 e2'
  : opLt e2 e2'
    -> eqnLt (EqnEq e1 e2) (EqnEq e1 e2')
| EqnLtApxApx1 e1 e1' e2 e2'
  : opLt e1 e1'
    -> eqnLt (EqnApx e1 e2) (EqnApx e1' e2')
| EqnLtApxApx2 e1 e2 e2'
  : opLt e2 e2'
    -> eqnLt (EqnApx e1 e2) (EqnApx e1 e2').

Instance eqnLt_irr : Irreflexive eqnLt.
hnf; intros; unfold complement.
- induction x; inversion 1; subst; eauto;
  try now eapply opLt_irr; eauto.
Qed.

Instance eqnLt_trans : Transitive eqnLt.
hnf; intros.
inv H; inv H0; eauto using eqnLt, opLt_trans.
Qed.

Instance StrictOrder_eqnLt : OrderedType.StrictOrder eqnLt eq.
econstructor; intros; eauto using eqnLt_trans.
- intro. rewrite H0 in H. eapply eqnLt_irr; eauto.
Qed.

Local Notation "'Compare' x 'next' y" :=
  (match x with
    | Eq => y
    | z => z
  end) (at level 100).

Fixpoint eqn_cmp (e e':eqn) :=
  match e, e' with
    | EqnBot, EqnBot => Eq
    | EqnBot, _ => Lt
    | EqnEq _ _, EqnBot => Gt
    | EqnEq _ _, EqnApx _ _ => Lt
    | EqnEq e1 e2, EqnEq e1' e2' =>
      Compare _cmp e1 e1' next
      Compare _cmp e2 e2' next Eq
    | EqnApx e1 e2, EqnApx e1' e2' =>
      Compare _cmp e1 e1' next
      Compare _cmp e2 e2' next Eq
    | EqnApx _ _, _ => Gt
  end.

Instance OrderedType_eqn : OrderedType eqn :=
 { _eq := eq;
  _lt := eqnLt;
  _cmp := eqn_cmp}.
intros.
destruct x,y; simpl eqn_cmp; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e e0); unfold _cmp in *; simpl in *.
inv H; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e' e'0); unfold _cmp in *; simpl in *.
inv H1; try now (econstructor; eauto 20 using eqnLt).
pose proof (_compare_spec e e0); unfold _cmp in *; simpl in *.
inv H; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e' e'0); unfold _cmp in *; simpl in *.
inv H1; try now (econstructor; eauto 20 using eqnLt).
Defined.

Definition eqns := set eqn.

Definition satisfiesAll (E:onv val) (Gamma:eqns) :=
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.


Lemma satisfiesAll_monotone E Gamma Γ'
: satisfiesAll E Gamma
  -> Γ' ⊆ Gamma
  -> satisfiesAll E Γ'.
Proof.
  intros. hnf; intros. eapply H; eauto.
Qed.

Definition freeVars (gamma:eqn) :=
  match gamma with
    | EqnEq e e' => Op.freeVars e ∪ Op.freeVars e'
    | EqnApx e e' => Op.freeVars e ∪ Op.freeVars e'
    | EqnBot => ∅
  end.

Definition eqns_freeVars (Gamma:eqns) := fold union (map freeVars Gamma) ∅.

Definition entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'.

Definition not_entails Gamma gamma := exists E, satisfiesAll E Gamma /\ ~ satisfies E gamma.


Lemma not_entails_antitone Gamma Γ' gamma
: not_entails Γ' gamma
  -> Gamma ⊆ Γ'
  -> not_entails Gamma gamma.
Proof.
  intros. hnf; intros.
  edestruct H as [E ?]; dcr.
  eexists E; intros; split; eauto using satisfiesAll_monotone; eauto.
Qed.



Definition onvLe X (E E':onv X)
:= forall x v, E x = Some v -> E' x = Some v.

(*Definition models Gamma gamma := forall E, satisfiesAll E Gamma -> satisfies E gamma.*)

Lemma exp_eval_onvLe e E E' v
: onvLe E E'
  -> op_eval E e = Some v
  -> op_eval E' e = Some v.
Proof.
  intros. general induction e; simpl in * |- *; eauto.
  - monad_inv H0.
    erewrite IHe; eauto.
  - monad_inv H0.
    erewrite IHe1, IHe2; eauto.
Qed.

Definition list_EqnApx Y Y' :=
  of_list (zip (fun e e' => EqnApx e e') Y Y').

Definition subst_eqn (ϱ : env op) (gamma: eqn) :=
  match gamma with
    | EqnEq e e' => EqnEq (subst_op ϱ e) (subst_op ϱ e')
    | EqnApx e e' => EqnApx (subst_op ϱ e) (subst_op ϱ e')
    | EqnBot => EqnBot
  end.

Definition subst_eqns (ϱ : env op) (G:eqns) : eqns :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.


Definition unsatisfiable (gamma:eqn) :=
  forall E, ~ satisfies E gamma.

Definition unsatisfiables (Gamma:eqns) :=
  forall E, ~ satisfiesAll E Gamma.

Lemma satisfiesAll_add E gamma Gamma
  : satisfiesAll E {gamma ; Gamma}
    <-> satisfies E gamma /\ satisfiesAll E Gamma.
Proof.
  split.
  intros H; split; hnf; intros; eapply H; cset_tac; intuition.
  intros [A B]; hnf; intros. cset_tac'.
  destruct H0; dcr; subst; eauto.
Qed.

Lemma unsatisfiable_add_left gamma Gamma
  : (forall E, satisfiesAll E Gamma -> ~ satisfies E gamma)
    -> unsatisfiables {gamma; Gamma}.
Proof.
  intros; hnf; intros.
  intro. eapply satisfiesAll_add in H0; dcr.
  eapply H; eauto with cset.
Qed.

Lemma unsatisfiable_monotone Gamma Γ'
: unsatisfiables Gamma
  -> Gamma ⊆ Γ'
  -> unsatisfiables Γ'.
Proof.
  intros. hnf; intros. intro. eapply H.
  eapply satisfiesAll_monotone; eauto.
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
  - hnf; intros. cset_tac'.
    + eapply H0; cset_tac.
    + eapply H; eauto.
Qed.

Lemma entails_add'' Gamma gamma Γ'
: entails Gamma {gamma ; Γ'}
  -> entails Gamma Γ'.
Proof.
  unfold entails; intros; dcr; intros.
  - hnf; intros. eapply H; eauto. cset_tac; intuition.
Qed.


Lemma entails_monotonic_add Gamma Γ' gamma
: entails Gamma Γ' -> entails (gamma ∪ Gamma) Γ'.
Proof.
  unfold entails; intros; dcr.
  - hnf; intros. eapply H. hnf; intros. eapply H0.
    cset_tac. eauto.
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
  - hnf; intros. cset_tac'.
    + eapply H0; cset_tac.
    + eapply H; eauto.
Qed.

Instance satisfiesAll_Subset_morphism
  : Proper (eq ==> Subset ==> flip impl) satisfiesAll.
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  hnf; intros. eapply H1. cset_tac.
Qed.

Instance satisfiesAll_Equal_morphism
  : Proper (eq ==> Equal ==> iff) satisfiesAll.
Proof.
  unfold Proper, respectful; intros; subst.
  intuition.
  - rewrite <- H0; eauto.
  - rewrite H0; eauto.
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
  rewrite H in H3. cset_tac'.
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
  hnf; intros. cset_tac'. hnf; intros. rewrite <- H2.
  exploit (H1 _ H); eauto.
  exploit (H1 _ H0); eauto.
  etransitivity; eauto.
Qed.


Lemma entails_eqns_apx_refl e Gamma
  : entails Gamma {EqnApx e e}.
Proof.
  hnf; intros. hnf; intros. hnf; intros.
  cset_tac'. rewrite <- H0.
  reflexivity.
Qed.

Lemma satisfiesAll_union E Gamma Γ'
  : satisfiesAll E (Gamma ∪ Γ')
    <-> satisfiesAll E Gamma /\ satisfiesAll E Γ'.
Proof.
  split.
  intros H; split; hnf; intros; eapply H; cset_tac; intuition.
  intros [A B]; hnf; intros. cset_tac.
Qed.

Lemma satisfies_agree E E' gamma
  : satisfies E gamma
    -> agree_on eq (freeVars gamma) E E'
    -> satisfies E' gamma.
Proof.
  intros. general induction gamma; simpl in *.
  - erewrite !op_eval_agree; eauto with cset.
  - erewrite !op_eval_agree; eauto with cset.
  - eauto.
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

Hint Resolve eqns_freeVars_incl : cset.

Lemma satisfiesAll_agree E E' Gamma
  : satisfiesAll E Gamma
    -> agree_on eq (eqns_freeVars Gamma) E E'
    -> satisfiesAll E' Gamma.
Proof.
  intros; hnf; intros.
  eapply satisfies_agree; eauto.
  eapply agree_on_incl; eauto with cset.
Qed.

Lemma satisfies_update_dead E gamma x v
: satisfies E gamma
  -> x ∉ freeVars gamma
  -> satisfies (E[x <- v]) gamma.
Proof.
  intros.
  eapply satisfies_agree; eauto.
  symmetry.
  eapply agree_on_update_dead; eauto.
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
  - hnf; intros. cset_tac'.
    + eapply H0. cset_tac.
    + eapply H; eauto. hnf; intros; eapply H0.
      cset_tac.
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
  : unsatisfiables Gamma
    -> entails Γ' Gamma
    -> unsatisfiables Γ'.
Proof.
  intros. hnf; intros. intro. exploit (H E); eauto.
Qed.


Lemma satisfies_fstNoneOrR_apx V e e' :
  satisfies V (EqnApx e e') -> fstNoneOrR eq (op_eval V e) (op_eval V e').
Proof.
  intros. eauto.
Qed.

Lemma onvLe_op_eval_some V V'
  :onvLe V V' -> forall e v, op_eval V e = ⎣ v ⎦ -> op_eval V' e = ⎣ v ⎦.
Proof.
  intros. general induction e; simpl in * |- * ; eauto using @fstNoneOrR.
  - monad_inv H0. simpl. erewrite (IHe V V' H _ EQ); eauto.
  - monad_inv H0. erewrite IHe1; eauto. erewrite IHe2; simpl; eauto.
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
  general induction Y; simpl in * |- *; eauto.
  monad_inv H0.
 simpl.
  exploit (onvLe_op_eval_some H) as EV; eauto. rewrite EV.
  simpl. erewrite IHY; eauto.
  reflexivity.
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
  simpl. erewrite IHlength_eq; eauto. simpl; congruence.
  eapply satisfiesAll_monotone; eauto.
  unfold list_EqnApx; simpl in *.
  cset_tac; intuition.
Qed.

Lemma satisfies_omap_op_eval_fstNoneOrR V Y Y'
  : ❬Y❭ = ❬Y'❭
    -> satisfiesAll V (list_EqnApx Y Y')
    -> fstNoneOrR eq (omap (op_eval V) Y) (omap (op_eval V) Y').
Proof.
  intros.
  case_eq (omap (op_eval V) Y); eauto using fstNoneOrR.
  intros. length_equify.
  erewrite (@omap_satisfies_list_EqnApx V Y Y' l ) ; eauto using length_eq_length, fstNoneOrR.
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
    cset_tac'.
    + monad_inv H1. rewrite <- H5. eapply onvLe_op_eval_satisfies; eauto.
    + monad_inv H1. eapply IHlength_eq; eauto.
Qed.


Lemma in_eqns_freeVars x gamma Gamma
  : x \In freeVars gamma
    -> gamma ∈ Gamma
    -> x \In eqns_freeVars Gamma.
Proof.
  intros. eapply eqns_freeVars_incl; eauto.
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

Lemma omap_exp_eval_onvLe Y E E' v
  : onvLe E E'
    -> omap (op_eval E) Y = Some v
    -> omap (op_eval E') Y = Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  simpl in H0.
  monad_inv H0.
  erewrite exp_eval_onvLe; try eapply H; eauto. simpl.
  erewrite IHY; eauto; simpl; eauto.
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
  clear; cset_tac.
Qed.

Lemma eqns_freeVars_add Gamma e
  : eqns_freeVars {e; Gamma} [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars.
  rewrite map_add; eauto using freeVars_Proper.
  rewrite fold_union_add.
  cset_tac.
Qed.

Lemma eqns_freeVars_add2 Gamma e e'
  : eqns_freeVars ({e; { e'; Gamma } }) [=] eqns_freeVars (Gamma) ∪ freeVars e ∪ freeVars e'.
Proof.
  intros. unfold eqns_freeVars.
  repeat rewrite map_add; eauto using freeVars_Proper.
  repeat rewrite fold_union_add.
  cset_tac.
Qed.

Lemma eqns_freeVars_add' Gamma e
  : eqns_freeVars ({e ; Gamma}) [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars.
  rewrite map_add, fold_union_add.
  cset_tac; intuition. intuition.
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
  - general induction Z; destruct vl; simpl in * |- *; eauto.
    lud. cset_tac.
  - rewrite lookup_set_update_not_in_Z; eauto.
    rewrite lookup_set_update_not_in_Z in H1; eauto.
Qed.

Instance unsatisfiables_Proper_impl
  : Proper (Subset ==> impl) unsatisfiables.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  hnf; intros. rewrite <- H. eauto.
Qed.

Instance unsatisfiables_Proper_iff
  : Proper (Equal ==> iff) unsatisfiables.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  intuition; eapply unsatisfiables_Proper_impl; eauto;
    rewrite H; eauto.
Qed.

Lemma satisfies_single E gamma
  : satisfies E gamma
    -> satisfiesAll E {gamma}.
Proof.
  intros; hnf; intros.
  cset_tac'. rewrite <- H0; eauto.
Qed.

Lemma satisfies_single' E gamma
  : satisfiesAll E {gamma}
    -> satisfies E gamma.
Proof.
  intros. eapply H. cset_tac.
Qed.

Lemma satisfies_add_extr E gamma Gamma
  : satisfiesAll E {gamma; Gamma}
    -> satisfies E gamma.
Proof.
  intros. eapply H. cset_tac.
Qed.

Lemma satisfies_add_drop E gamma Gamma
  : satisfiesAll E {gamma; Gamma}
    -> satisfiesAll E Gamma.
Proof.
  intros. hnf; intros. eapply H. cset_tac.
Qed.
