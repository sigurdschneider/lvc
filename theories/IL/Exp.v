Require Import Util EqDec DecSolve Val CSet Map Envs Option Get SetOperations IL.Events.
Require Export MoreList Isa.Ops.

Set Implicit Arguments.

(** * Extended Expressions *)

Inductive exp :=
| Operation (e:op)
| Call (f:external) (Y:list op).

Definition isCall e :=
  match e with
  | Operation _ => false
  | Call _ _ => true
  end.


Instance inst_eq_dec_exp : EqDec exp eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
  - eapply inst_eq_dec_op.
  - eapply list_eq_dec.
    intros. eapply inst_eq_dec_op.
  - eapply nat_eq_eqdec.
Defined.

Definition freeVars (e:exp) :=
  match e with
  | Operation e => Ops.freeVars e
  | Call f Y => list_union (List.map Ops.freeVars Y)
  end.

(** ** Renaming *)

Definition rename_exp (ϱ:env var) (e:exp) :=
  match e with
  | Operation e => Operation (rename_op ϱ e)
  | Call f Y => Call f (List.map (rename_op ϱ) Y)
  end.

Lemma rename_exp_comp e ϱ ϱ'
  : rename_exp ϱ (rename_exp ϱ' e) = rename_exp (ϱ' ∘ ϱ) e.
Proof.
  unfold comp. general induction e; simpl; eauto.
  - f_equal; eauto using rename_op_comp.
  - f_equal; eauto.
    rewrite map_map. setoid_rewrite rename_op_comp; eauto.
Qed.

Lemma rename_exp_ext
  : forall e (ϱ ϱ':env var), feq (R:=eq) ϱ ϱ' -> rename_exp ϱ e = rename_exp ϱ' e.
Proof.
  intros. general induction e; simpl; eauto.
  - f_equal; eauto using rename_op_ext.
  - f_equal; eauto.
    abstract (eapply map_ext; eauto using rename_op_ext) using rename_op_list_ext.
Qed exporting.

Lemma rename_exp_agree ϱ ϱ' e
  : agree_on eq (freeVars e) ϱ ϱ'
    -> rename_exp ϱ e = rename_exp ϱ' e.
Proof.
  intros; general induction e; simpl in *; f_equal;
    eauto 30 using agree_on_incl, incl_left, incl_right, rename_op_agree.
  - clear f.
    abstract (eapply MoreList.map_ext_get_eq; intros; inv_get; eauto with len;
    eapply rename_op_agree;
    eapply agree_on_incl; eauto; eapply incl_list_union; eauto using map_get_1) using
        rename_op_list_agree.
Qed exporting.

Lemma rename_exp_freeVars
  : forall e ϱ `{Proper _ (_eq ==> _eq) ϱ},
    freeVars (rename_exp ϱ e) ⊆ lookup_set ϱ (freeVars e).
Proof.
  intros. general induction e; simpl.
  - eapply rename_op_freeVars; eauto.
  - clear f.
    abstract (eapply list_union_incl; eauto with cset;
      intros; inv_get; rewrite lookup_set_list_union; eauto using lookup_set_empty;
      eapply incl_list_union; eauto using map_get_1, rename_op_freeVars)
             using rename_op_list_freeVars.
Qed exporting.

(** ** Liveness *)

Inductive live_exp_sound : exp -> set var -> Prop :=
| OperationLiveSound e lv
  : live_op_sound e lv -> live_exp_sound (Operation e) lv
| CallLiveSound f Y lv
  : (forall n e, get Y n e -> live_op_sound e lv)
    -> live_exp_sound (Call f Y) lv.

Instance live_exp_sound_Subset e
  : Proper (Subset ==> impl) (live_exp_sound e).
Proof.
  unfold Proper, respectful, impl; intros.
  general induction e.
  - invt live_exp_sound. econstructor. eapply live_op_sound_Subset; eauto.
  - inv H0; econstructor; intros. eapply live_op_sound_Subset; eauto.
Qed.

Instance live_op_sound_Equal e
  : Proper (Equal ==> iff) (live_exp_sound e).
Proof.
  unfold Proper, respectful, impl; split; intros.
  - eapply subset_equal in H. rewrite H in H0; eauto.
  - symmetry in H. eapply subset_equal in H.
    rewrite <- H; eauto.
Qed.


Instance live_op_sound_dec e lv
  : Computable (live_exp_sound e lv).
Proof.
  induction e; try dec_solve.
  - decide (live_op_sound e lv); dec_solve.
  - decide ( forall (n : nat) (e : op), get Y n e -> live_op_sound e lv); try dec_solve.
Qed.

Lemma live_exp_sound_incl
  : forall e lv lv', live_exp_sound e lv' -> lv' ⊆ lv -> live_exp_sound e lv.
Proof.
  intros. rewrite <- H0; eauto.
Qed.

Lemma freeVars_live e lv
  : live_exp_sound e lv -> freeVars e ⊆ lv.
Proof.
  intros. general induction H; simpl; eauto using Ops.freeVars_live, Ops.freeVars_live_list.
Qed.

Lemma freeVars_live_list Y lv
  : (forall (n : nat) (y : exp), get Y n y -> live_exp_sound y lv)
    -> list_union (freeVars ⊝ Y) ⊆ lv.
Proof.
  intros H. eapply list_union_incl; intros; inv_get; eauto using freeVars_live with cset.
Qed.

Lemma live_exp_rename_sound e lv (ϱ:env var)
  : live_exp_sound e lv
    -> live_exp_sound (rename_exp ϱ e) (lookup_set ϱ lv).
Proof.
  intros.
  general induction H; simpl; econstructor; intros; inv_get; eauto using live_op_rename_sound.
Qed.

Lemma live_freeVars
  : forall e, live_exp_sound e (freeVars e).
Proof.
  intros. general induction e; simpl; econstructor;
            eauto using Ops.live_freeVars with cset.
  intros. eapply live_op_sound_incl.
  eapply Ops.live_freeVars.
  eapply incl_list_union; eauto using map_get_1.
Qed.

(** ** Alpha Equivalence *)

Inductive alpha_exp : env var -> env var -> exp -> exp -> Prop :=
| AlphaOperation ϱ ϱ' e e' :
    alpha_op ϱ ϱ' e e'
    -> alpha_exp ϱ ϱ' (Operation e) (Operation e')
| AlphaCall ϱ ϱ' f Y Y' :
    length Y = length Y'
  -> (forall n x y, get Y n x -> get Y' n y -> alpha_op ϱ ϱ' x y)
  -> alpha_exp ϱ ϱ' (Call f Y) (Call f Y').

Lemma alpha_exp_rename_injective
  : forall e ϱ ϱ',
    inverse_on (freeVars e) ϱ ϱ'
    -> alpha_exp ϱ ϱ' e (rename_exp ϱ e).
Proof.
  intros. induction e; simpl; eauto using alpha_exp, alpha_op_rename_injective.
  econstructor; eauto with len.
  intros; inv_get. eapply alpha_op_rename_injective.
  eapply inverse_on_incl; eauto; simpl. eapply incl_list_union; eauto using map_get_1.
Qed.

Lemma alpha_exp_refl : forall e, alpha_exp id id e e.
Proof.
  intros; induction e; eauto 20 using alpha_exp, alpha_op_refl.
  econstructor; eauto. intros. get_functional. eapply alpha_op_refl.
Qed.

Lemma alpha_exp_sym : forall ϱ ϱ' e e', alpha_exp ϱ ϱ' e e' -> alpha_exp ϱ' ϱ e' e.
Proof.
  intros. general induction H; eauto using alpha_exp, alpha_op_sym.
Qed.

Set Regular Subst Tactic.

Lemma alpha_exp_trans
  : forall ϱ1 ϱ1' ϱ2 ϱ2' s s' s'',
    alpha_exp ϱ1 ϱ1' s s'
    -> alpha_exp ϱ2 ϱ2' s' s''
    -> alpha_exp (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H; invt alpha_exp; eauto using alpha_exp, alpha_op_trans.
  - econstructor; eauto with len.
    intros. inv_get. eapply alpha_op_trans; eauto.
Qed.

Unset Regular Subst Tactic.

Lemma alpha_exp_inverse_on
  : forall ϱ ϱ' s t, alpha_exp ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros. general induction H; simpl; eauto using alpha_op_inverse_on.
  + eapply inverse_on_list_union; eauto.
    intros; inv_get. eauto using alpha_op_inverse_on.
Qed.

Lemma alpha_exp_agree_on_morph
  : forall f g ϱ ϱ' s t,
    alpha_exp ϱ ϱ' s t
    -> agree_on _eq (lookup_set ϱ (freeVars s)) g ϱ'
    -> agree_on _eq (freeVars s) f ϱ
    -> alpha_exp f g s t.
Proof.
  intros.
  general induction H; simpl in *;
    eauto using alpha_exp, alpha_op_agree_on_morph.
  - econstructor; eauto. clear H f.
    abstract (intros; eapply alpha_op_agree_on_morph; eauto;
      [ eapply agree_on_incl; eauto;
        rewrite SetOperations.lookup_set_list_union; eauto using lookup_set_empty;
        eapply incl_list_union; eauto using map_get_1
      |  eauto with cset ])
    using alpha_op_list_agree_on_morph.
Qed exporting.

Lemma exp_rename_renamedApart_all_alpha e e' ϱ ϱ'
  : alpha_exp ϱ ϱ' e e'
    -> rename_exp ϱ e = e'.
Proof.
  intros. general induction H; simpl; f_equal; eauto using op_rename_renamedApart_all_alpha.
  eapply map_ext_get_eq; intros; eauto using op_rename_renamedApart_all_alpha.
Qed.

Lemma alpha_exp_morph
  : forall (ϱ1 ϱ1' ϱ2 ϱ2':env var) e e',
    @feq _ _ eq ϱ1  ϱ1'
    -> @feq _ _ eq ϱ2 ϱ2'
    -> alpha_exp ϱ1 ϱ2 e e'
    -> alpha_exp ϱ1' ϱ2' e e'.
Proof.
  intros. general induction H1; eauto using alpha_exp, alpha_op_morph.
Qed.

Lemma freeVars_renameExp ϱ e
  : freeVars (rename_exp ϱ e) [=] lookup_set ϱ (freeVars e).
Proof.
  general induction e; simpl;
    eauto using freeVars_rename_op_list, freeVars_renameOp.
Qed.
