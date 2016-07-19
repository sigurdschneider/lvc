Require Import Util EqDec DecSolve Val CSet Map Env Option Get SetOperations.
Require Import Arith.

Set Implicit Arguments.

(** * Expressions *)

Inductive exp :=
  Con : val -> exp
| Var : var -> exp
| UnOp : unop -> exp -> exp
| BinOp : binop -> exp -> exp -> exp.

Instance DoNotRemember_exp : DoNotRemember exp.
eapply (DNR exp exp).
Defined.

Inductive isVar : exp -> Prop :=
  IisVar v : isVar (Var v).

Instance isVar_dec e : Computable (isVar e).
Proof.
  destruct e; try dec_solve.
Defined.

Definition getVar (e:exp) :=
  match e with
  | Var y => y
  | _ => 0
  end.

Instance inst_eq_dec_exp : EqDec exp eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
  - eapply inst_eq_dec_val.
  - eapply nat_eq_eqdec.
  - eapply inst_eq_dec_unop.
  - eapply inst_eq_dec_binop.
Defined.

Fixpoint exp_eval (E:onv val) (e:exp) : option val :=
  match e with
  | Con v => Some v
  | Var x => E x
  | UnOp o e => mdo v <- exp_eval E e;
                 unop_eval o v
  | BinOp o e1 e2 => mdo v1 <- exp_eval E e1;
                      mdo v2 <- exp_eval E e2;
                      binop_eval o v1 v2
  end.

Inductive live_exp_sound : exp -> set var -> Prop :=
| ConLiveSound v lv : live_exp_sound (Con v) lv
| VarLiveSound x lv : x ∈ lv -> live_exp_sound (Var x) lv
| UnopLiveSound o e lv :
    live_exp_sound e lv
    -> live_exp_sound (UnOp o e) lv
| binopLiveSound o e1 e2 lv :
    live_exp_sound e1 lv ->
    live_exp_sound e2 lv ->
    live_exp_sound (BinOp o e1 e2) lv.

Instance live_exp_sound_Subset e
  : Proper (Subset ==> impl) (live_exp_sound e).
Proof.
  unfold Proper, respectful, impl; intros.
  general induction e; invt live_exp_sound; eauto using live_exp_sound.
Qed.

Instance live_exp_sound_Equal e
  : Proper (Equal ==> iff) (live_exp_sound e).
Proof.
  unfold Proper, respectful, impl; split; intros.
  - eapply subset_equal in H. rewrite H in H0; eauto.
  - symmetry in H. eapply subset_equal in H.
    rewrite <- H; eauto.
Qed.

Instance live_exp_sound_dec e lv
  : Computable (live_exp_sound e lv).
Proof.
  induction e; try dec_solve.
  - decide (v ∈ lv); try dec_solve.
  - edestruct IHe; dec_solve.
  - edestruct IHe1, IHe2; dec_solve.
Defined.

Lemma live_exp_sound_incl
  : forall e lv lv', live_exp_sound e lv' -> lv' ⊆ lv -> live_exp_sound e lv.
Proof.
  intros; general induction H; econstructor; eauto.
Qed.

Fixpoint freeVars (e:exp) : set var :=
  match e with
  | Con _ => ∅
  | Var v => {v}
  | UnOp o e => freeVars e
  | BinOp o e1 e2 => freeVars e1 ∪ freeVars e2
  end.

Lemma live_freeVars
  : forall e, live_exp_sound e (freeVars e).
Proof.
  intros. general induction e; simpl; econstructor; eauto using live_exp_sound_incl with cset.
Qed.

Lemma freeVars_live e lv
  : live_exp_sound e lv -> freeVars e ⊆ lv.
Proof.
  intros. general induction H; simpl; cset_tac; intuition.
Qed.

Lemma exp_eval_live
  : forall e lv E E', live_exp_sound e lv -> agree_on eq lv E E' ->
                 exp_eval E e = exp_eval E' e.
Proof.
  intros. general induction e; inv H; simpl; eauto.
  - erewrite IHe; eauto.
  - erewrite IHe1, IHe2; eauto.
Qed.

Global Instance eval_exp_ext
  : Proper (@feq _ _ eq ==> eq ==> eq) exp_eval.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; eauto.
  - erewrite IHy0; eauto.
  - erewrite IHy0_1, IHy0_2; eauto.
Qed.

Lemma get_live_exp_sound Y D n y
  : list_union (freeVars ⊝ Y) ⊆ D
    -> get Y n y
    -> live_exp_sound y D.
Proof.
  intros. eapply live_exp_sound_incl; [eapply live_freeVars |].
  rewrite <- H. eauto using get_list_union_map with cset.
Qed.

Definition var_to_exp : forall x:var, exp := Var.
Lemma var_to_exp_correct : forall M x,
    exp_eval M (var_to_exp x) = M x.
Proof.
  reflexivity.
Qed.

Fixpoint rename_exp (ϱ:env var) (s:exp) : exp :=
  match s with
  | Con v => Con v
  | Var v => Var (ϱ v)
  | UnOp o e => UnOp o (rename_exp ϱ e)
  | BinOp o e1 e2 => BinOp o (rename_exp ϱ e1) (rename_exp ϱ e2)
  end.

Lemma rename_exp_comp e ϱ ϱ'
  : rename_exp ϱ (rename_exp ϱ' e) = rename_exp (ϱ' ∘ ϱ) e.
Proof.
  unfold comp. general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma rename_exp_ext
  : forall e (ϱ ϱ':env var), feq (R:=eq) ϱ ϱ' -> rename_exp ϱ e = rename_exp ϱ' e.
Proof.
  intros. general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma rename_exp_agree ϱ ϱ' e
  : agree_on eq (freeVars e) ϱ ϱ'
    -> rename_exp ϱ e = rename_exp ϱ' e.
Proof.
  intros; general induction e; simpl in *; f_equal;
    eauto 30 using agree_on_incl, incl_left, incl_right.
Qed.

Lemma rename_exp_freeVars
  : forall e ϱ `{Proper _ (_eq ==> _eq) ϱ},
    freeVars (rename_exp ϱ e) ⊆ lookup_set ϱ (freeVars e).
Proof.
  intros. general induction e; simpl; eauto using lookup_set_single_fact,
                                      lookup_set_union_incl, incl_union_lr; eauto.
Qed.

Lemma live_exp_rename_sound e lv (ϱ:env var)
  : live_exp_sound e lv
    -> live_exp_sound (rename_exp ϱ e) (lookup_set ϱ lv).
Proof.
  intros. general induction H; simpl; eauto using live_exp_sound.
  + econstructor. eapply lookup_set_spec; eauto.
Qed.


Fixpoint subst_exp (ϱ:env exp) (s:exp) : exp :=
  match s with
  | Con v => Con v
  | Var v => (ϱ v)
  | UnOp o e => UnOp o (subst_exp ϱ e)
  | BinOp o e1 e2 => BinOp o (subst_exp ϱ e1) (subst_exp ϱ e2)
  end.

Lemma subst_exp_comp e ϱ ϱ'
  : subst_exp ϱ (subst_exp ϱ' e) = subst_exp (fun x => subst_exp ϱ (ϱ' x)) e.
Proof.
  general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma subst_exp_ext
  : forall e (ϱ ϱ':env exp), feq (R:=eq) ϱ ϱ' -> subst_exp ϱ e = subst_exp ϱ' e.
Proof.
  intros. general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Inductive alpha_exp : env var -> env var -> exp -> exp -> Prop :=
| AlphaCon ϱ ϱ' v : alpha_exp ϱ ϱ' (Con v) (Con v)
| AlphaVar ϱ ϱ' x y : ϱ x = y -> ϱ' y = x -> alpha_exp ϱ ϱ' (Var x) (Var y)
| AlphaUnOp ϱ ϱ' o e e' :
    alpha_exp ϱ ϱ' e e'
    -> alpha_exp ϱ ϱ' (UnOp o e) (UnOp o e')
| AlphaBinOp ϱ ϱ' o e1 e1' e2 e2' :
    alpha_exp ϱ ϱ' e1 e1' ->
    alpha_exp ϱ ϱ' e2 e2' ->
    alpha_exp ϱ ϱ' (BinOp o e1 e2) (BinOp o e1' e2').

Lemma alpha_exp_rename_injective
  : forall e ϱ ϱ',
    inverse_on (freeVars e) ϱ ϱ'
    -> alpha_exp ϱ ϱ' e (rename_exp ϱ e).
Proof.
  intros. induction e; simpl; eauto using alpha_exp.
  econstructor; eauto. eapply H; eauto. simpl; cset_tac; eauto.
  simpl in *. econstructor.
  eapply IHe1. eapply inverse_on_incl; eauto. cset_tac; intuition.
  eapply IHe2. eapply inverse_on_incl; eauto. cset_tac; intuition.
Qed.

Lemma alpha_exp_refl : forall e, alpha_exp id id e e.
Proof.
  intros; induction e; eauto using alpha_exp.
Qed.

Lemma alpha_exp_sym : forall ϱ ϱ' e e', alpha_exp ϱ ϱ' e e' -> alpha_exp ϱ' ϱ e' e.
Proof.
  intros. general induction H; eauto using alpha_exp.
Qed.

Lemma alpha_exp_trans
  : forall ϱ1 ϱ1' ϱ2 ϱ2' s s' s'',
    alpha_exp ϱ1 ϱ1' s s'
    -> alpha_exp ϱ2 ϱ2' s' s''
    -> alpha_exp (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H.
  + inversion H0. subst v0 ϱ0 ϱ'0 s''. econstructor.
  + inversion H1. subst x ϱ0 ϱ'0 s''. econstructor; unfold comp; congruence.
  + inversion H0. subst. econstructor; eauto.
  + inversion H1. subst. econstructor; eauto.
Qed.

Lemma alpha_exp_inverse_on
  : forall ϱ ϱ' s t, alpha_exp ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros. general induction H.
  + isabsurd.
  + simpl. hnf; intros; cset_tac.
    rewrite <- H0. rewrite H. rewrite H0. reflexivity.
  + simpl; eauto.
  + simpl. eapply inverse_on_union; eauto.
Qed.

Lemma alpha_exp_agree_on_morph
  : forall f g ϱ ϱ' s t,
    alpha_exp ϱ ϱ' s t
    -> agree_on _eq (lookup_set ϱ (freeVars s)) g ϱ'
    -> agree_on _eq (freeVars s) f ϱ
    -> alpha_exp f g s t.
Proof.
  intros. general induction H; simpl in *;
            eauto 20 using alpha_exp, agree_on_incl, lookup_set_union_incl with cset.
  - econstructor.
    + rewrite H2; eauto.
    + eapply H1. lset_tac.
Qed.

Lemma exp_rename_renamedApart_all_alpha e e' ϱ ϱ'
  : alpha_exp ϱ ϱ' e e'
    -> rename_exp ϱ e = e'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma alpha_exp_morph
  : forall (ϱ1 ϱ1' ϱ2 ϱ2':env var) e e',
    @feq _ _ eq ϱ1  ϱ1'
    -> @feq _ _ eq ϱ2 ϱ2'
    -> alpha_exp ϱ1 ϱ2 e e'
    -> alpha_exp ϱ1' ϱ2' e e'.
Proof.
  intros. general induction H1; eauto using alpha_exp.
  econstructor.
  + rewrite <- H1; eauto.
  + rewrite <- H2; eauto.
Qed.


Inductive expLt : exp -> exp -> Prop :=
| ExpLtCon c c'
  : _lt c c'
    -> expLt (Con c) (Con c')
| ExpLtConVar c v
  : expLt (Con c) (Var v)
| ExpLtConUnOp c o e
  : expLt (Con c) (UnOp o e)
| ExpLtConBinop c o e1 e2
  : expLt (Con c) (BinOp o e1 e2)
| ExpLtVar v v'
  : _lt v v'
    -> expLt (Var v) (Var v')
| ExpLtVarUnOp v o e
  : expLt (Var v) (UnOp o e)
| ExpLtVarBinop v o e1 e2
  : expLt (Var v) (BinOp o e1 e2)
| ExpLtUnOpBinOp o e o' e1 e2
  : expLt (UnOp o e) (BinOp o' e1 e2)
| ExpLtUnOp1 o o' e e'
  : _lt o o'
    -> expLt (UnOp o e) (UnOp o' e')
| ExpLtUnOp2 o e e'
  : expLt e e'
    -> expLt (UnOp o e) (UnOp o e')
| ExpLtBinOp1 o o' e1 e1' e2 e2'
  : _lt o o'
    -> expLt (BinOp o e1 e2) (BinOp o' e1' e2')
| ExpLtBinOp2 o e1 e1' e2 e2'
  : expLt e1 e1'
    -> expLt (BinOp o e1 e2) (BinOp o e1' e2')
| ExpLtBinOp3 o e1 e2 e2'
  : expLt e2 e2'
    -> expLt (BinOp o e1 e2) (BinOp o e1 e2').

Instance expLt_irr : Irreflexive expLt.
hnf; intros; unfold complement.
- induction x; inversion 1; subst;
    try now eauto using StrictOrder_Irreflexive with typeclass_instances.
  * eapply (StrictOrder_Irreflexive _ H2).
  * eapply (StrictOrder_Irreflexive _ H2).
    Grab Existential Variables.
    eauto with typeclass_instances.
Qed.

Instance expLt_trans : Transitive expLt.
hnf; intros.
general induction H; invt expLt; eauto using expLt.
- econstructor. eapply StrictOrder_Transitive. eapply H. eapply H2.
- econstructor. eapply StrictOrder_Transitive.  eapply H. eapply H2.
- econstructor; eauto. eapply StrictOrder_Transitive. eapply H. eapply H4.
- econstructor; eauto. eapply StrictOrder_Transitive. eapply H. eapply H5.
  Grab Existential Variables.
  + eauto with typeclass_instances.
  + eauto with typeclass_instances.
  + eauto with typeclass_instances.
Qed.

Notation "'Compare' x 'next' y" :=
  (match x with
   | Eq => y
   | z => z
   end) (at level 100).

Fixpoint exp_cmp (e e':exp) :=
  match e, e' with
  | Con c, Con c' => _cmp c c'
  | Con _, _ => Lt
  | Var v, Var v' => _cmp v v'
  | Var v, UnOp _ _ => Lt
  | Var v, BinOp _ _ _ => Lt
  | UnOp _ _, BinOp _ _ _ => Lt
  | UnOp o e, UnOp o' e' =>
    Compare _cmp o o' next
            Compare exp_cmp e e' next Eq
  | BinOp o e1 e2, BinOp o' e1' e2' =>
    Compare _cmp o o' next
            Compare exp_cmp e1 e1' next
            Compare exp_cmp e2 e2' next Eq
  | _, _ => Gt
  end.

Instance StrictOrder_expLt : OrderedType.StrictOrder expLt eq.
econstructor.
eapply expLt_trans.
intros. intro. eapply expLt_irr. rewrite H0 in H.
eapply H.
Qed.

Instance OrderedType_exp : OrderedType exp :=
  { _eq := eq;
    _lt := expLt;
    _cmp := exp_cmp}.
intros.
general induction x; destruct y; simpl; try now (econstructor; eauto using expLt).
pose proof (_compare_spec v v0).
- inv H.
  + econstructor. eauto using expLt.
  + econstructor. f_equal. eapply compare_spec_int_eq; eauto.
  + econstructor; eauto using expLt.
- pose proof (_compare_spec v v0).
  inv H; now (econstructor; eauto using expLt).
- pose proof (_compare_spec u u0).
  specialize (IHx y).
  inv H; try now (econstructor; eauto using expLt).
  eapply unop_eq_eq in H1; subst.
  inv IHx; try now (econstructor; eauto using expLt).
- pose proof (_compare_spec b b0).
  specialize (IHx1 y1). specialize (IHx2 y2).
  inv H; try now (econstructor; eauto using expLt).
  eapply binop_eq_eq in H1.
  inv H1.
  inv IHx1; try now (econstructor; eauto using expLt).
  inv IHx2; try now (econstructor; eauto using expLt).
Defined.

Lemma freeVars_renameExp ϱ e
  : freeVars (rename_exp ϱ e) [=] lookup_set ϱ (freeVars e).
Proof.
  general induction e; simpl; try rewrite lookup_set_union; eauto.
  - rewrite IHe1, IHe2; reflexivity.
Qed.

Definition exp2bool (e:exp) : option bool :=
  match e with
  | Con c => Some (val2bool c)
  | _ => None
  end.

Lemma exp2bool_val2bool E e b
  : exp2bool e = Some b
    -> exists v, exp_eval E e = Some v /\ val2bool v = b.
Proof.
  destruct e; simpl; intros; try congruence.
  inv H; eauto.
Qed.