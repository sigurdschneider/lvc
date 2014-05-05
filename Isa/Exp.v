Require Import Util DecSolve Val CSet Map Env EnvTy Option.
Require Import Arith.

Set Implicit Arguments.

(** * Expressions *)

(* Module Type Expressions. *)
(** Assume expressions. We could pack them into a module type, but at the moment 
   this would not buy as anything. Packing things in module types only is interesting
   if the module types are instantiated; and expression are not in this development *)

  Inductive binop : Set := Add | Sub | Mul.
  Definition binop_eval (o:binop) := 
    match o with
      | Add => Peano.plus
      | Sub => minus
      | Mul => mult
    end.
  

  Inductive exp := 
     Con : val -> exp
   | Var : var -> exp
   | BinOp : binop -> exp -> exp -> exp.

  Fixpoint exp_eval (E:env val) (e:exp) : option val :=
    match e with
      | Con v => Some v
      | Var x => Some (E x)
      | BinOp o e1 e2 => mdo v1 <- exp_eval E e1; 
                         mdo v2 <- exp_eval E e2;
                             Some (binop_eval o v1 v2)
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
  | conLiveSound v lv : live_exp_sound (Con v) lv
  | varLiveSound x lv : x ∈ lv -> live_exp_sound (Var x) lv
  | binopLiveSound o e1 e2 lv : 
      live_exp_sound e1 lv ->
      live_exp_sound e2 lv -> 
      live_exp_sound (BinOp o e1 e2) lv.

  Instance live_exp_sound_dec e lv
  : Computable (live_exp_sound e lv).
  Proof.
    induction e; try dec_solve.
    - decide (v ∈ lv); try dec_solve.
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
      | BinOp o e1 e2 => freeVars e1 ∪ freeVars e2
    end.
    
  Lemma live_freeVars
    : forall e, live_exp_sound e (freeVars e).
  Proof.
    intros. general induction e; simpl; econstructor. cset_tac; eauto. 
    eapply live_exp_sound_incl; eauto. cset_tac; intuition.
    eapply live_exp_sound_incl; eauto. cset_tac; intuition.
  Qed.

  Lemma freeVars_live e lv
     : live_exp_sound e lv -> freeVars e ⊆ lv.
  Proof.
    intros. general induction H; simpl; cset_tac; intuition.
  Qed.

  Lemma exp_eval_live 
    : forall e lv E E', live_exp_sound e lv -> agree_on lv E E' -> 
      exp_eval E e = exp_eval E' e.
  Proof.
    intros. general induction e; inv H; simpl; eauto. f_equal; eapply H0; eauto.
    erewrite IHe1, IHe2; eauto. 
  Qed.

  Global Instance eval_exp_ext 
  : Proper (feq ==> eq ==> eq) exp_eval.
  Proof.
    unfold Proper, respectful; intros; subst.
    general induction y0; simpl; eauto. rewrite H; eauto.
    erewrite IHy0_1, IHy0_2; eauto. 
  Qed.

  Definition var_to_exp : forall x:var, exp := Var.
  Lemma var_to_exp_correct : forall M x,
     exp_eval M (var_to_exp x) = Some (M x).
  Proof.
    reflexivity.
  Qed.  

  Fixpoint rename_exp (ϱ:env var) (s:exp) : exp :=
    match s with
      | Con v => Con v
      | Var v => Var (ϱ v)
      | BinOp o e1 e2 => BinOp o (rename_exp ϱ e1) (rename_exp ϱ e2)
    end.

  Lemma rename_exp_comp e ϱ ϱ' 
  : rename_exp ϱ (rename_exp ϱ' e) = rename_exp (ϱ' ∘ ϱ) e.
  Proof.
    unfold comp. general induction e; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma rename_exp_ext 
    : forall e (ϱ ϱ':env var), feq (R:=eq) ϱ ϱ' -> rename_exp ϱ e = rename_exp ϱ' e.
  Proof.
    intros. general induction e; simpl; eauto. f_equal; eauto.
  Qed.


  Lemma rename_exp_freeVars 
  : forall e ϱ `{Proper _ (_eq ==> _eq) ϱ}, 
      freeVars (rename_exp ϱ e) ⊆ lookup_set ϱ (freeVars e).
  Proof.
    intros. general induction e; simpl; cset_tac; intuition.
    hnf in H.
    eapply lookup_set_spec; eauto. eexists v; cset_tac; eauto.
    eapply Subset_trans; eauto. eapply lookup_set_incl; intuition.
    eapply Subset_trans; try eapply IHe2; eauto. eapply lookup_set_incl; intuition.
  Qed.

  Lemma live_exp_rename_sound e lv (ϱ:env var)
  : live_exp_sound e lv
    -> live_exp_sound (rename_exp ϱ e) (lookup_set ϱ lv).
  Proof.
    intros. general induction H; simpl; eauto using live_exp_sound.
    + econstructor. eapply lookup_set_spec; eauto.
  Qed.

  Inductive alpha_exp : env var -> env var -> exp -> exp -> Prop :=
  | alphaCon ϱ ϱ' v : alpha_exp ϱ ϱ' (Con v) (Con v)
  | alphaVar ϱ ϱ' x y : ϱ x = y -> ϱ' y = x -> alpha_exp ϱ ϱ' (Var x) (Var y)
  | alphaBinOp ϱ ϱ' o e1 e1' e2 e2' :
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
    + inversion H1. subst ϱ0 ϱ'0 o0 e0 e3 s''. econstructor; eauto.
  Qed.
  
  Lemma alpha_exp_inverse_on
    : forall ϱ ϱ' s t, alpha_exp ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
  Proof.
    intros. general induction H.
    + isabsurd.
    + simpl. hnf; intros; cset_tac. rewrite <- H1. rewrite H. rewrite H0. reflexivity.
    + simpl. eapply inverse_on_union; eauto.
  Qed.

  Lemma alpha_exp_agree_on_morph 
  : forall f g ϱ ϱ' s t,
      alpha_exp ϱ ϱ' s t
      -> agree_on (lookup_set ϱ (freeVars s)) g ϱ'
      -> agree_on (freeVars s) f ϱ
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
  | conNotOccur D v : notOccur D (Con v)
  | varNotOccur D x : x ∉ D -> notOccur D (Var x)
  | binopNotOccur D o e1 e2 : 
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
      feq ϱ1  ϱ1' -> feq ϱ2 ϱ2' -> alpha_exp ϱ1 ϱ2 e e' -> alpha_exp ϱ1' ϱ2' e e'.
  Proof.
    intros. general induction H1; eauto using alpha_exp.
    econstructor. 
    + rewrite <- H1; eauto.
    + rewrite <- H2; eauto.
  Qed.


(* End Expressions. *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
