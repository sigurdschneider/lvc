Require Import Util EqDec DecSolve Val CSet Map Env EnvTy Option List OrderedType Setoid.
Require Import Arith bitvec orderedBitvec.

Set Implicit Arguments.

(** * Expressions *)

(* Module Type Expressions. *)
(** Assume expressions. We could pack them into a module type, but at the moment
   this would not buy as anything. Packing things in module types only is interesting
   if the module types are instantiated; and expression are not in this development *)

  Definition binop : Set := nat.
  Definition option_lift2 A B C (f:A -> B -> C) := fun x y => Some (f x y).
  Definition binop_eval (o:binop) :=
    match o with
      | 0 => option_lift2 bvAdd
      | 1 => option_lift2 bvSub
      | 2 => option_lift2 bvMult
      | 3 => option_lift2 bvEq
      | 4 => option_lift2 (fun a b => neg (bvEq a b))
      | 5 => bvDiv
      | _ => fun _ _ => None
    end.

  Definition unop : Set := nat.
  Definition option_lift1 A B (f:A -> B) := fun x => Some (f x).

  Definition unop_eval (o:unop) :=
    match o with
      | 0 => option_lift1 (fun a => if toBool a then val_true else val_false)
      | 1 => option_lift1 neg
      | _ => fun _ => None
    end.

  Inductive exp :=
     Con : val -> exp
   | Var : var -> exp
   | UnOp : unop -> exp -> exp
   | BinOp : binop -> exp -> exp -> exp.

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

  Global Instance inst_eq_dec_exp : EqDec exp eq.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
- eapply inst_eq_dec_val.
-  destruct v, v0;firstorder.
- eapply nat_eq_eqdec.
-  eapply nat_eq_eqdec.
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

  Inductive expOfType : onv ty -> exp -> ty -> Prop :=
  | conOfType ET v t : expOfType ET (Con v) t
  | varOfType ET x t : ET x = Some t -> expOfType ET (Var x) t.

  Lemma expOfType_subEnv
    : forall ET ET' e t, subEnv ET' ET -> expOfType ET' e t -> expOfType ET e t.
  Proof.
    intros; destruct e; inv H0; eauto using expOfType.
  Qed.

  Lemma exp_type_soundness :
    forall ET E e t v, expOfType ET e t ->
                       envOfType E ET ->
                       exp_eval E e = Some v ->
                       valOfType v t.
  Proof.
    intros. destruct e,t; eexists; firstorder using valOfType.
  Qed.

  Lemma exp_eval_typed_eq
    : forall ET E E' e t, typed_eq ET E E' -> expOfType ET e t
      -> exp_eval E e = exp_eval E' e.
  Proof.
    intros. destruct e; inv H0; simpl; eauto.
  Qed.

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

  Instance live_exp_sound_dec e lv
  : Computable (live_exp_sound e lv).
  Proof.
    induction e; try dec_solve.
    - decide (v ∈ lv); try dec_solve.
    - edestruct IHe; dec_solve.
    - edestruct IHe1, IHe2; dec_solve.
  Defined.

  Lemma live_exp_sound_incl
    : forall e lv lv', lv' ⊆ lv -> live_exp_sound e lv' -> live_exp_sound e lv.
  Proof.
    intros; general induction H0; econstructor; eauto.
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
    intros. general induction e; simpl; econstructor. cset_tac; eauto.
    - eapply live_exp_sound_incl; eauto. cset_tac; intuition.
    - eapply live_exp_sound_incl; eauto. cset_tac; intuition.
    - eapply live_exp_sound_incl; eauto. cset_tac; intuition.
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


  Lemma rename_exp_freeVars
  : forall e ϱ `{Proper _ (_eq ==> _eq) ϱ},
      freeVars (rename_exp ϱ e) ⊆ lookup_set ϱ (freeVars e).
  Proof.
    intros. general induction e; simpl; cset_tac; intuition.
    hnf in H.
    eapply lookup_set_spec; eauto. eexists v; cset_tac; eauto.
    - eapply Subset_trans; eauto. eapply lookup_set_incl; intuition.
    - eapply Subset_trans; eauto. eapply lookup_set_incl; intuition.
    - eapply Subset_trans; try eapply IHe2; eauto.
      eapply lookup_set_incl; intuition.
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
    + inversion H1. subst x0 ϱ0 ϱ'0 s''. econstructor; unfold comp; congruence.
    + inversion H0. subst. econstructor; eauto.
    + inversion H1. subst. econstructor; eauto.
  Qed.

  Lemma alpha_exp_inverse_on
    : forall ϱ ϱ' s t, alpha_exp ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
  Proof.
    intros. general induction H.
    + isabsurd.
    + simpl. hnf; intros; cset_tac.
      rewrite <- H1. rewrite H. rewrite H0. reflexivity.
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
    intros. general induction H; eauto using alpha_exp.
    econstructor.
    + rewrite <- H. eapply H2; simpl; cset_tac; eauto.
    + rewrite <- H0. eapply H1. set_tac. eexists x; simpl; cset_tac; eauto.
      intuition.
    + simpl in *. econstructor.
      - eapply IHalpha_exp1; eauto.
        eapply agree_on_incl; eauto. eapply lookup_set_incl; intuition.
        eapply agree_on_incl; eauto. eapply union_subset_1; intuition.
      - eapply IHalpha_exp2; eauto.
        eapply agree_on_incl; eauto. eapply lookup_set_incl; intuition.
        eapply agree_on_incl; eauto. eapply union_subset_2; intuition.
  Qed.



  Inductive notOccur : set var -> exp -> Prop :=
  | ConNotOccur D v : notOccur D (Con v)
  | VarNotOccur D x : x ∉ D -> notOccur D (Var x)
  | UnOpNotOccur D o e
    : notOccur D e
      -> notOccur D (UnOp o e)
  | BinopNotOccur D o e1 e2 :
      notOccur D e1 ->
      notOccur D e2 ->
      notOccur D (BinOp o e1 e2).

  Lemma notOccur_freeVars
  : forall D e, notOccur D e <-> D ∩ freeVars e [=] ∅.
  Proof.
    intros. general induction e; simpl; split; intros; eauto using notOccur.
    + cset_tac; intuition.
    + inv H; cset_tac; intuition. rewrite <- H3 in H1; eauto.
    + econstructor. cset_tac; intuition. eapply (H v); cset_tac; intuition.
    + inv H. eapply IHe; eauto.
    + econstructor. eapply IHe; eauto.
    + inv H. eapply IHe1 in H3. eapply IHe2 in H5. cset_tac; intuition.
      eapply H2; eauto. eapply H1; eauto.
    + econstructor. eapply IHe1. cset_tac; intuition. eapply H; eauto.
      eapply IHe2. cset_tac; intuition. eapply H; eauto.
  Qed.

  Lemma notOccur_antitone
  : forall D D' e, D' ⊆ D -> notOccur D e -> notOccur D' e.
  Proof.
    intros. general induction H0; eauto using notOccur.
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
- induction x; inversion 1; subst; try now eauto using StrictOrder_Irreflexive.
  +  eapply (StrictOrder_Irreflexive v H2); eauto.
  + eapply (StrictOrder_Irreflexive v H2); eauto.
  + eapply (StrictOrder_Irreflexive u  H1); eauto.
  + eapply (StrictOrder_Irreflexive b  H1).
Grab Existential Variables. econstructor.
     * exact ltBitvec_irrefl.
     * exact ltBitvec_trans.
Qed.

Instance lt_eq_strict : StrictOrder ltBitvec.
econstructor.
- apply ltBitvec_irrefl.
- eapply ltBitvec_trans.
Defined.


Instance expLt_trans : Transitive expLt.
hnf; intros.
general induction H; invt expLt; eauto using expLt; unfold unop in *.
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
  + econstructor. f_equal. eapply H1.
  + econstructor; eauto using expLt.
- pose proof (_compare_spec v v0).
inv H; now (econstructor; eauto using expLt).
- pose proof (_compare_spec u u0).
specialize (IHx y).
inv H; try now (econstructor; eauto using expLt).
inv H1. inv IHx; now (econstructor; eauto using expLt).
- pose proof (_compare_spec b b0).
specialize (IHx1 y1). specialize (IHx2 y2).
inv H; try now (econstructor; eauto using expLt).
inv H1.
inv IHx1; try now (econstructor; eauto using expLt).
inv IHx2; try now (econstructor; eauto using expLt).
Defined.


(* End Expressions. *)

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
