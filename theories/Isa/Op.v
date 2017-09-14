Require Import Util EqDec DecSolve Val CSet Map Envs Option Get MapDefined SetOperations.
Require Import MoreList Option OptionR OptionMap ReplaceIf Filter.

Set Implicit Arguments.

(** * Operations *)

Inductive op :=
  Con : val -> op
| Var : var -> op
| UnOp : unop -> op -> op
| BinOp : binop -> op -> op -> op.

Inductive isVar : op -> Prop :=
  IisVar v : isVar (Var v).

Instance isVar_dec e : Computable (isVar e).
Proof.
  destruct e; try dec_solve.
Defined.

Notation "'IsVar'" := (fun e => B[isVar e]) (at level 0).
Notation "'NotVar'" := (fun e => B[~ isVar e]) (at level 0).

Definition getVar (e:op) :=
  match e with
  | Var y => y
  | _ => default_var
  end.

Instance inst_eq_dec_op : EqDec op eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
  - eapply inst_eq_dec_val.
  - eapply var_dec.
  - eapply inst_eq_dec_unop.
  - eapply inst_eq_dec_binop.
Defined.

Fixpoint op_eval (E:onv val) (e:op) : option val :=
  match e with
  | Con v => Some v
  | Var x => E x
  | UnOp o e => mdo v <- op_eval E e;
                 unop_eval o v
  | BinOp o e1 e2 => mdo v1 <- op_eval E e1;
                      mdo v2 <- op_eval E e2;
                      binop_eval o v1 v2
  end.

Inductive live_op_sound : op -> set var -> Prop :=
| ConLiveSound v lv : live_op_sound (Con v) lv
| VarLiveSound x lv : x ∈ lv -> live_op_sound (Var x) lv
| UnopLiveSound o e lv :
    live_op_sound e lv
    -> live_op_sound (UnOp o e) lv
| binopLiveSound o e1 e2 lv :
    live_op_sound e1 lv ->
    live_op_sound e2 lv ->
    live_op_sound (BinOp o e1 e2) lv.

Instance live_op_sound_Subset e
  : Proper (Subset ==> impl) (live_op_sound e).
Proof.
  unfold Proper, respectful, impl; intros.
  general induction e; invt live_op_sound; eauto using live_op_sound.
Qed.

Instance live_op_sound_Equal e
  : Proper (Equal ==> iff) (live_op_sound e).
Proof.
  unfold Proper, respectful, impl; split; intros.
  - eapply subset_equal in H. rewrite H in H0; eauto.
  - symmetry in H. eapply subset_equal in H.
    rewrite <- H; eauto.
Qed.

Instance live_op_sound_dec e lv
  : Computable (live_op_sound e lv).
Proof.
  induction e as [c|v| |].
  - dec_solve.
  - decide (v ∈ lv); try dec_solve.
  - edestruct IHe; dec_solve.
  - edestruct IHe1, IHe2; dec_solve.
Defined.

Lemma live_op_sound_incl
  : forall e lv lv', live_op_sound e lv' -> lv' ⊆ lv -> live_op_sound e lv.
Proof.
  intros; general induction H; econstructor; eauto.
Qed.

Fixpoint freeVars (e:op) : set var :=
  match e with
  | Con _ => ∅
  | Var v => {v}
  | UnOp o e => freeVars e
  | BinOp o e1 e2 => freeVars e1 ∪ freeVars e2
  end.

Lemma live_freeVars
  : forall e, live_op_sound e (freeVars e).
Proof.
  intros. general induction e; simpl; econstructor; eauto using live_op_sound_incl with cset.
Qed.

Lemma freeVars_live e lv
  : live_op_sound e lv -> freeVars e ⊆ lv.
Proof.
  intros. general induction H; simpl; cset_tac; intuition.
Qed.

Lemma op_eval_live
  : forall e lv E E', live_op_sound e lv -> agree_on eq lv E E' ->
                 op_eval E e = op_eval E' e.
Proof.
  intros. general induction e; inv H; simpl; eauto.
  - erewrite IHe; eauto.
  - erewrite IHe1, IHe2; eauto.
Qed.

Global Instance eval_op_ext
  : Proper (@feq _ _ eq ==> eq ==> eq) op_eval.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; eauto.
  - erewrite IHy0; eauto.
  - erewrite IHy0_1, IHy0_2; eauto.
Qed.

Lemma get_live_op_sound Y D n y
  : list_union (freeVars ⊝ Y) ⊆ D
    -> get Y n y
    -> live_op_sound y D.
Proof.
  intros. eapply live_op_sound_incl; [eapply live_freeVars |].
  rewrite <- H. eauto using get_list_union_map with cset.
Qed.

Definition var_to_op : forall x:var, op := Var.
Lemma var_to_op_correct : forall M x,
    op_eval M (var_to_op x) = M x.
Proof.
  reflexivity.
Qed.

Fixpoint rename_op (ϱ:env var) (s:op) : op :=
  match s with
  | Con v => Con v
  | Var v => Var (ϱ v)
  | UnOp o e => UnOp o (rename_op ϱ e)
  | BinOp o e1 e2 => BinOp o (rename_op ϱ e1) (rename_op ϱ e2)
  end.

Lemma rename_op_comp e ϱ ϱ'
  : rename_op ϱ (rename_op ϱ' e) = rename_op (ϱ' ∘ ϱ) e.
Proof.
  unfold comp. general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma rename_op_ext
  : forall e (ϱ ϱ':env var), feq (R:=eq) ϱ ϱ' -> rename_op ϱ e = rename_op ϱ' e.
Proof.
  intros. general induction e; simpl; f_equal; eauto.
Qed.

Lemma rename_op_agree ϱ ϱ' e
  : agree_on eq (freeVars e) ϱ ϱ'
    -> rename_op ϱ e = rename_op ϱ' e.
Proof.
  intros; general induction e; simpl in *; f_equal;
    eauto 30 using agree_on_incl, incl_left, incl_right.
Qed.

Lemma rename_op_freeVars
  : forall e ϱ `{Proper _ (_eq ==> _eq) ϱ},
    freeVars (rename_op ϱ e) ⊆ lookup_set ϱ (freeVars e).
Proof.
  intros. general induction e; simpl; eauto using lookup_set_single_fact,
                                      lookup_set_union_incl, incl_union_lr; eauto.
Qed.

Lemma live_op_rename_sound e lv (ϱ:env var)
  : live_op_sound e lv
    -> live_op_sound (rename_op ϱ e) (lookup_set ϱ lv).
Proof.
  intros. general induction H; simpl; eauto using live_op_sound with cset.
Qed.

Fixpoint subst_op (ϱ:env op) (s:op) : op :=
  match s with
  | Con v => Con v
  | Var v => (ϱ v)
  | UnOp o e => UnOp o (subst_op ϱ e)
  | BinOp o e1 e2 => BinOp o (subst_op ϱ e1) (subst_op ϱ e2)
  end.

Lemma subst_op_comp e ϱ ϱ'
  : subst_op ϱ (subst_op ϱ' e) = subst_op (fun x => subst_op ϱ (ϱ' x)) e.
Proof.
  general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma subst_op_ext
  : forall e (ϱ ϱ':env op), feq (R:=eq) ϱ ϱ' -> subst_op ϱ e = subst_op ϱ' e.
Proof.
  intros. general induction e; simpl; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Inductive alpha_op : env var -> env var -> op -> op -> Prop :=
| AlphaCon ϱ ϱ' v : alpha_op ϱ ϱ' (Con v) (Con v)
| AlphaVar ϱ ϱ' x y : ϱ x = y -> ϱ' y = x -> alpha_op ϱ ϱ' (Var x) (Var y)
| AlphaUnOp ϱ ϱ' o e e' :
    alpha_op ϱ ϱ' e e'
    -> alpha_op ϱ ϱ' (UnOp o e) (UnOp o e')
| AlphaBinOp ϱ ϱ' o e1 e1' e2 e2' :
    alpha_op ϱ ϱ' e1 e1' ->
    alpha_op ϱ ϱ' e2 e2' ->
    alpha_op ϱ ϱ' (BinOp o e1 e2) (BinOp o e1' e2').

Lemma alpha_op_rename_injective
  : forall e ϱ ϱ',
    inverse_on (freeVars e) ϱ ϱ'
    -> alpha_op ϱ ϱ' e (rename_op ϱ e).
Proof.
  intros. induction e; simpl; eauto using alpha_op.
  econstructor; eauto. eapply H; eauto. simpl; cset_tac; eauto.
  simpl in *. econstructor.
  eapply IHe1. eapply inverse_on_incl; eauto. cset_tac; intuition.
  eapply IHe2. eapply inverse_on_incl; eauto. cset_tac; intuition.
Qed.

Lemma alpha_op_refl : forall e, alpha_op id id e e.
Proof.
  intros; induction e; eauto using alpha_op.
Qed.

Lemma alpha_op_sym : forall ϱ ϱ' e e', alpha_op ϱ ϱ' e e' -> alpha_op ϱ' ϱ e' e.
Proof.
  intros. general induction H; eauto using alpha_op.
Qed.

Lemma alpha_op_trans
  : forall ϱ1 ϱ1' ϱ2 ϱ2' s s' s'',
    alpha_op ϱ1 ϱ1' s s'
    -> alpha_op ϱ2 ϱ2' s' s''
    -> alpha_op (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H.
  + inversion H0. subst v0 ϱ0 ϱ'0 s''. econstructor.
  + inversion H1. subst x ϱ0 ϱ'0 s''. econstructor; unfold comp; congruence.
  + inversion H0. subst. econstructor; eauto.
  + inversion H1. subst. econstructor; eauto.
Qed.

Lemma alpha_op_inverse_on
  : forall ϱ ϱ' s t, alpha_op ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros. general induction H.
  + isabsurd.
  + simpl. hnf; intros.
    eapply In_single in H0.
    rewrite <- H0 at 1. rewrite H. eapply H0.
  + simpl; eauto.
  + simpl. eapply inverse_on_union; eauto.
Qed.

Lemma alpha_op_agree_on_morph
  : forall f g ϱ ϱ' s t,
    alpha_op ϱ ϱ' s t
    -> agree_on _eq (lookup_set ϱ (freeVars s)) g ϱ'
    -> agree_on _eq (freeVars s) f ϱ
    -> alpha_op f g s t.
Proof.
  intros. general induction H; simpl in *;
            eauto 20 using alpha_op, agree_on_incl, lookup_set_union_incl with cset.
  - econstructor.
    + rewrite H2; eauto.
    + eapply H1. lset_tac.
Qed.

Lemma op_rename_renamedApart_all_alpha e e' ϱ ϱ'
  : alpha_op ϱ ϱ' e e'
    -> rename_op ϱ e = e'.
Proof.
  intros. general induction H; simpl; f_equal; eauto.
Qed.

Lemma alpha_op_morph
  : forall (ϱ1 ϱ1' ϱ2 ϱ2':env var) e e',
    @feq _ _ eq ϱ1  ϱ1'
    -> @feq _ _ eq ϱ2 ϱ2'
    -> alpha_op ϱ1 ϱ2 e e'
    -> alpha_op ϱ1' ϱ2' e e'.
Proof.
  intros. general induction H1; eauto using alpha_op.
  econstructor.
  + rewrite <- H1; eauto.
  + rewrite <- H2; eauto.
Qed.

Inductive opLt : op -> op -> Prop :=
| OpLtCon c c'
  : _lt c c'
    -> opLt (Con c) (Con c')
| OpLtConVar c v
  : opLt (Con c) (Var v)
| OpLtConUnOp c o e
  : opLt (Con c) (UnOp o e)
| OpLtConBinop c o e1 e2
  : opLt (Con c) (BinOp o e1 e2)
| OpLtVar v v'
  : _lt v v'
    -> opLt (Var v) (Var v')
| OpLtVarUnOp v o e
  : opLt (Var v) (UnOp o e)
| OpLtVarBinop v o e1 e2
  : opLt (Var v) (BinOp o e1 e2)
| OpLtUnOpBinOp o e o' e1 e2
  : opLt (UnOp o e) (BinOp o' e1 e2)
| OpLtUnOp1 o o' e e'
  : _lt o o'
    -> opLt (UnOp o e) (UnOp o' e')
| OpLtUnOp2 o e e'
  : opLt e e'
    -> opLt (UnOp o e) (UnOp o e')
| OpLtBinOp1 o o' e1 e1' e2 e2'
  : _lt o o'
    -> opLt (BinOp o e1 e2) (BinOp o' e1' e2')
| OpLtBinOp2 o e1 e1' e2 e2'
  : opLt e1 e1'
    -> opLt (BinOp o e1 e2) (BinOp o e1' e2')
| OpLtBinOp3 o e1 e2 e2'
  : opLt e2 e2'
    -> opLt (BinOp o e1 e2) (BinOp o e1 e2').

Lemma _lt_antirefl X `{OrderedType X} x
  : _lt x x -> False.
Proof.
  eapply lt_antirefl.
Qed.

Instance opLt_irr : Irreflexive opLt.
hnf; intros; unfold complement.
- induction x; inversion 1; subst; eauto using @_lt_antirefl.
  eapply lt_antirefl in H2; eauto.
  eapply lt_antirefl in H1; eauto.
  eapply lt_antirefl in H1; eauto.
Qed.

Instance opLt_trans : Transitive opLt.
hnf; intros.
general induction H; invt opLt; eauto using opLt.
- econstructor. eapply StrictOrder_Transitive. eapply H. eapply H2.
- econstructor. eapply StrictOrder_Transitive.  eapply H. eapply H2.
- econstructor; eauto. eapply StrictOrder_Transitive. eapply H. eapply H4.
- econstructor; eauto. eapply StrictOrder_Transitive. eapply H. eapply H5.
Qed.

Notation "'Compare' x 'next' y" :=
  (match x with
   | Eq => y
   | z => z
   end) (at level 100).

Fixpoint op_cmp (e e':op) :=
  match e, e' with
  | Con c, Con c' => _cmp c c'
  | Con _, _ => Lt
  | Var v, Var v' => _cmp v v'
  | Var v, UnOp _ _ => Lt
  | Var v, BinOp _ _ _ => Lt
  | UnOp _ _, BinOp _ _ _ => Lt
  | UnOp o e, UnOp o' e' =>
    Compare _cmp o o' next
            Compare op_cmp e e' next Eq
  | BinOp o e1 e2, BinOp o' e1' e2' =>
    Compare _cmp o o' next
            Compare op_cmp e1 e1' next
            Compare op_cmp e2 e2' next Eq
  | _, _ => Gt
  end.

Instance StrictOrder_opLt : OrderedType.StrictOrder opLt eq.
econstructor.
eapply opLt_trans.
intros. intro. eapply opLt_irr. rewrite H0 in H.
eapply H.
Qed.

Instance OrderedType_op : OrderedType op :=
  { _eq := eq;
    _lt := opLt;
    _cmp := op_cmp}.
Proof.
  intros. revert y.
  induction x as [|v| |]; destruct y as [|v'| |];
    simpl; try now (econstructor; eauto using opLt).
- pose proof (_compare_spec v v0).
  inv H.
  + econstructor. eauto using opLt.
  + econstructor. f_equal. eauto.
  + econstructor; eauto using opLt.
- pose proof (_compare_spec v v').
  inv H; (econstructor; eauto using opLt); f_equal; eauto.
- pose proof (_compare_spec u u0).
  specialize (IHx y).
  inv H; try now (econstructor; eauto using opLt).
  eapply unop_eq_eq in H1; subst.
  inv IHx; try now (econstructor; eauto using opLt).
- pose proof (_compare_spec b b0).
  specialize (IHx1 y1). specialize (IHx2 y2).
  inv H; try now (econstructor; eauto using opLt).
  eapply binop_eq_eq in H1.
  inv H1.
  inv IHx1; try now (econstructor; eauto using opLt).
  inv IHx2; try now (econstructor; eauto using opLt).
Defined.

Lemma freeVars_renameOp ϱ e
  : freeVars (rename_op ϱ e) [=] lookup_set ϱ (freeVars e).
Proof.
  general induction e; simpl; try rewrite lookup_set_union; eauto.
  - rewrite IHe1, IHe2; reflexivity.
Qed.

Definition op2bool (e:op) : option bool :=
  mdo r <- op_eval (fun _ => None) e; Some (val2bool r).

Lemma op_eval_mon (E E':onv val) e
  : agree_on (fstNoneOrR eq) (freeVars e) E E'
    -> fstNoneOrR eq (op_eval E e) (op_eval E' e).
Proof.
  intros. general induction e; simpl in *; eauto using fstNoneOrR.
  - exploit IHe as EQ; eauto. inv EQ; simpl; eauto using fstNoneOrR.
    reflexivity.
  - exploit IHe1 as EQ1; eauto with cset.
    inv EQ1; simpl; eauto using fstNoneOrR.
    exploit IHe2 as EQ2; eauto with cset.
    inv EQ2; simpl; eauto using fstNoneOrR.
    reflexivity.
Qed.

Lemma op_eval_op2bool_true V e v
  : op_eval V e = Some v -> val2bool v = true -> op2bool e <> Some false.
Proof.
  intros. unfold op2bool.
  exploit (@op_eval_mon (fun _ => None) V e).
  hnf; intros; eauto using fstNoneOrR.
  rewrite H in H1. inv H1; simpl; congruence.
Qed.

Lemma op_eval_op2bool_false V e v
  : op_eval V e = Some v -> val2bool v = false -> op2bool e <> Some true.
Proof.
  intros. unfold op2bool.
  exploit (@op_eval_mon (fun _ => None) V e).
  hnf; intros; eauto using fstNoneOrR.
  rewrite H in H1. inv H1; simpl; congruence.
Qed.

Lemma op2bool_val2bool E e b
  : op2bool e = Some b
    -> exists v, op_eval E e = Some v /\ val2bool v = b.
Proof.
  intros. unfold op2bool in H. monad_inv H.
  eexists x; split; eauto.
  exploit (@op_eval_mon (fun _ => None) E e); eauto.
  hnf; intros; econstructor.
  inv H; congruence.
Qed.

Lemma op_eval_agree E E' e v
: agree_on eq (freeVars e) E E'
  -> op_eval E e = v
  -> op_eval E' e = v.
Proof.
  intros.
  erewrite <- op_eval_live; eauto.
  eauto using live_op_sound_incl, live_freeVars.
Qed.

Lemma omap_op_eval_agree E E' Y v
: agree_on eq (list_union (List.map freeVars Y)) E E'
  -> omap (op_eval E) Y = v
  -> omap (op_eval E') Y = v.
Proof.
  intros.
  erewrite omap_agree; eauto.
  intros. eapply op_eval_agree; eauto.
  eapply agree_on_incl; eauto.
  eapply incl_list_union; eauto using map_get_1.
Qed.

Lemma op_eval_live_agree E E' e lv v
: live_op_sound e lv
  -> agree_on eq lv E E'
  -> op_eval E e = v
  -> op_eval E' e = v.
Proof.
  intros. erewrite <- op_eval_live; eauto.
Qed.

Lemma omap_op_eval_live_agree E E' lv Y v
: (forall n y, get Y n y -> live_op_sound y lv)
  -> agree_on eq lv E E'
  -> omap (op_eval E) Y = v
  -> omap (op_eval E') Y = v.
Proof.
  intros.
  erewrite omap_agree; eauto.
  intros. eapply op_eval_agree; eauto.
  eapply agree_on_incl; eauto using freeVars_live.
Qed.

Lemma omap_self_update E Z l
:  omap (op_eval E) (List.map Var Z) = ⎣l ⎦
   -> E [Z <-- List.map Some l] [-] E.
Proof.
  general induction Z; simpl in * |- *.
  - reflexivity.
  - monad_inv H; simpl.
    rewrite IHZ; eauto.
    hnf; intros; lud. congruence.
Qed.

Lemma omap_var_defined_on Za lv E
: of_list Za ⊆ lv
  -> defined_on lv E
  -> exists l, omap (op_eval E) (List.map Var Za) = Some l.
Proof.
  intros. general induction Za; simpl.
  - eauto.
  - simpl in *.
    edestruct H0.
    + instantiate (1:=a). cset_tac; intuition.
    + rewrite H1; simpl. edestruct IHZa; eauto.
      cset_tac; intuition.
      rewrite H2; simpl. eauto.
Qed.

Hint Extern 5 =>
match goal with
| [ LV : live_op_sound ?e ?lv, AG: agree_on eq ?lv ?E ?E',
    H1 : op_eval ?E ?e = _, H2 : op_eval ?E' ?e = _ |- _ ] =>
  rewrite (op_eval_live_agree LV AG H1) in H2; try solve [ exfalso; inv H2 ];
    clear_trivial_eqs
end.

Lemma freeVars_live_list Y lv
  : (forall (n : nat) (y : op), get Y n y -> live_op_sound y lv)
    -> list_union (freeVars ⊝ Y) ⊆ lv.
Proof.
  intros H. eapply list_union_incl; intros; inv_get; eauto using freeVars_live with cset.
Qed.

Lemma freeVars_rename_op_list ϱ Y
  : list_union (List.map freeVars (List.map (rename_op ϱ) Y))[=]
               lookup_set ϱ (list_union (List.map freeVars Y)).
Proof.
  rewrite lookup_set_list_union; eauto using lookup_set_empty.
  repeat rewrite map_map. eapply fold_left_union_morphism; [|reflexivity].
  clear_all. general induction Y; simpl; eauto using AllInRel.PIR2, freeVars_renameOp.
Qed.

Lemma op_eval_var Y
  : (forall (n : nat) (y : op), get Y n y -> isVar y)
    -> { xl : list var | Y = Var ⊝ xl }.
Proof.
  intros. general induction Y.
  - eexists nil; eauto.
  - exploit H; eauto using get.
    destruct a as [|v| |]; try now (exfalso; inv H0).
    edestruct IHY; eauto using get; subst.
    exists (v::x); eauto.
Qed.

Lemma of_list_freeVars_vars xl
  : of_list xl [<=] list_union (freeVars ⊝ Var ⊝ xl).
Proof.
  general induction xl; simpl; eauto. rewrite list_union_start_swap.
  rewrite IHxl; eauto. cset_tac.
Qed.


Lemma omap_lookup_vars V xl vl
  : length xl = length vl
    -> NoDupA _eq xl
    -> omap (op_eval (V[xl <-- List.map Some vl])) (List.map Var xl) = Some vl.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  lud; isabsurd; simpl.
  erewrite omap_op_eval_agree; try eapply IHlength_eq; eauto; simpl in *; intuition.
  instantiate (1:= V [x <- Some y]).
  eapply update_nodup_commute_eq; eauto; simpl; intuition.
Qed.

Lemma omap_replace_if V Y Y' vl0 vl1
  :  omap (op_eval V) (List.filter IsVar Y) = ⎣ vl1 ⎦
     -> omap (op_eval V) Y' = ⎣ vl0 ⎦
     -> omap
         (op_eval V)
         (replace_if NotVar Y Y') = ⎣ merge_cond (IsVar ⊝ Y) vl1 vl0 ⎦.
Proof.
  general induction Y; simpl; eauto.
  simpl in *. cases in H; cases; isabsurd; simpl in *.
  - monad_inv H. rewrite EQ. simpl. erewrite IHY; eauto. eauto.
  - destruct Y'; simpl in *.
    + inv H0; eauto.
    + monad_inv H0. rewrite EQ. simpl.
      erewrite IHY; eauto. simpl; eauto.
Qed.
