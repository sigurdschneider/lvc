Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL ParamsMatch Sim SimApx Fresh Annotation MoreExp Coherence.

Require Import SetOperations Liveness Filter.

Set Implicit Arguments.
Unset Printing Records.


Definition eqn := (exp * exp)%type.

Inductive expLt : exp -> exp -> Prop :=
| expLtCon c c' 
  : _lt c c'
    -> expLt (Con c) (Con c')
| expLtConVar c v
  : expLt (Con c) (Var v)
| expLtConBinop c o e1 e2
  : expLt (Con c) (BinOp o e1 e2)
| expLtVar v v'
  : _lt v v'
    -> expLt (Var v) (Var v')
| expLtVarBinop v o e1 e2
  : expLt (Var v) (BinOp o e1 e2)
| expLtBinOp1 o o' e1 e1' e2 e2'
  : _lt o o'
    -> expLt (BinOp o e1 e2) (BinOp o' e1' e2')
| expLtBinOp2 o e1 e1' e2 e2'
  : expLt e1 e1'
    -> expLt (BinOp o e1 e2) (BinOp o e1' e2')
| expLtBinOp3 o e1 e2 e2'
  : expLt e2 e2'
    -> expLt (BinOp o e1 e2) (BinOp o e1 e2').


Instance expLt_irr : Irreflexive expLt.
hnf; intros; unfold complement.
- induction x; inversion 1; subst; eauto using StrictOrder_Irreflexive. 
  + eapply (StrictOrder_Irreflexive _ H2).
  + eapply (StrictOrder_Irreflexive _ H2).
  + eapply (StrictOrder_Irreflexive _ H1).
Qed.

Instance expLt_trans : Transitive expLt.
hnf; intros. 
general induction H; invt expLt; eauto using expLt. 
- econstructor. eapply StrictOrder_Transitive; eauto.
- econstructor. eapply StrictOrder_Transitive; eauto.
- econstructor; eauto. transitivity o'; eauto.
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
    | Var v, BinOp _ _ _ => Lt
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
inv H; now (econstructor; eauto using expLt).
pose proof (_compare_spec v v0). 
inv H; now (econstructor; eauto using expLt).
pose proof (_compare_spec b b0).
specialize (IHx1 y1). specialize (IHx2 y2).
inv H; try now (econstructor; eauto using expLt).
inv H1.
inv IHx1; try now (econstructor; eauto using expLt).
inv IHx2; try now (econstructor; eauto using expLt).
Defined.

Inductive option_R (A B : Type) (eqA : A -> B -> Prop)
: option A -> option B -> Prop :=
| option_R_Some a b : eqA a b -> option_R eqA ⎣a⎦ ⎣b⎦.

Lemma option_R_refl A R `{Reflexive A R} : forall x, option_R R ⎣x⎦ ⎣x⎦.
intros; eauto using option_R.
Qed.

Instance option_R_sym A R `{Symmetric A R} : Symmetric (option_R R).
hnf; intros ? [] []; eauto using option_R.
Qed.
                                         
Definition satisfies (E:onv val) (gamma:eqn) := 
  option_R eq (exp_eval E (fst gamma)) (exp_eval E (snd gamma)).

Inductive moreDef {X} : option X -> option X -> Prop :=
  | moreDefSome v v' : moreDef (Some v) (Some v')
  | moreDefNone x : moreDef None x.

Definition eqns := set eqn.

Definition satisfiesAll (E:onv val) (Gamma:eqns) := 
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.

Definition sem_entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'. 

Definition freeVars (gamma:exp * exp) := 
  let (e,e'):= gamma in Exp.freeVars e ∪ Exp.freeVars e'.

Definition domain (gamma:exp * exp) := 
  let (e,e'):= gamma in Exp.freeVars e.

Definition eqns_freeVars (Gamma:eqns) := fold union (map freeVars Gamma) ∅.

Definition entails Gamma Γ' := (forall E, satisfiesAll E Gamma -> satisfiesAll E Γ') 
/\ eqns_freeVars Γ' ⊆ eqns_freeVars Gamma. 

Definition onvLe X (E E':onv X)
:= forall x v, E x = Some v -> E' x = Some v.

Definition moreDefined Gamma Γ' e e' := 
  forall E E', onvLe E E'
          -> satisfiesAll E Gamma 
          -> satisfiesAll E' Γ'
          -> fstNoneOrR eq (exp_eval E e) (exp_eval E' e').

Lemma exp_eval_onvLe e E E' v
: onvLe E E' 
  -> exp_eval E e = Some v
  -> exp_eval E' e = Some v.
Proof.
  intros. general induction e; simpl in * |- *; eauto.
  simpl in H0. rewrite H0. eapply H in H0. eauto.
  monad_inv H0. rewrite EQ, EQ1.
  erewrite IHe1, IHe2; eauto.
Qed.

Instance moreDefined_refl Gamma Γ'
: Reflexive (moreDefined Gamma Γ').
Proof.
  hnf; intros; hnf; intros.
  case_eq (exp_eval E x); intros.
  erewrite exp_eval_onvLe; eauto. constructor; eauto.
  constructor.
Qed.

Definition moreDefinedArgs Gamma Γ' Y Y' := 
  forall E E', onvLe E E'
          -> satisfiesAll E Gamma 
          -> satisfiesAll E' Γ' 
          -> fstNoneOrR eq (omap (exp_eval E) Y) (omap (exp_eval E') Y').

Definition remove (Gamma:eqns) G :=
  filter (fun gamma => B[freeVars gamma ∩ G [=] ∅]) Gamma.

Definition subst_eqn (ϱ : env exp) (e: eqn) :=
  (subst_exp ϱ (fst e), subst_exp ϱ (snd e)).

Definition subst_eqns (ϱ : env exp) (G:eqns) :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.

Inductive eqn_sound : list (params*set var*eqns*eqns*eqns*eqns) 
                      -> stmt 
                      -> ann (eqns) 
                      -> ann (eqns) 
                      -> ann (set var * set var)
                      -> ann (list exp) 
                      -> Prop :=
| EqnOpr x Lv b e Gamma al Γ' (al':ann (eqns)) e' cl G G' ang
  : eqn_sound Lv b al al' ang cl 
    (* make sure the rest conforms to the new assignment *)
    -> entails ({{(Var x,e)}} ∪ Gamma) (getAnn al)
    -> entails ({{(Var x,e')}} ∪ Γ') (getAnn al')
    -> moreDefined Gamma Γ' e e'
    -> Exp.freeVars e' ⊆ G
    -> eqn_sound Lv (stmtExp x e b) (ann1 Gamma al) (ann1 Γ' al')
                (ann1 (G,G') ang) (ann1 (e'::nil) cl)
| EqnIf Lv e e' b1 b2 Gamma Γ' al1 al2 al1' al2' cl1 cl2 G G' ang1 ang2
  : eqn_sound Lv b1 al1 al1' ang1 cl1
  -> eqn_sound Lv b2 al2 al2' ang2 cl2
 (* TODO: include information about condition *)
  -> entails Gamma (getAnn al1)
  -> entails Gamma (getAnn al2)
  -> entails Γ' (getAnn al1')
  -> entails Γ' (getAnn al2')
  -> moreDefined Gamma Γ' e e'
  -> eqn_sound Lv (stmtIf e b1 b2) (ann2 Gamma al1 al2) (ann2 Γ' al1' al2') 
              (ann2 (G,G') ang1 ang2) (ann2 (e'::nil) cl1 cl2)
| EqnGoto l Y Y' Lv Gamma Γ' Z Γf Γf' EqS EqS' Gf G G'
  : get Lv (counted l) (Z,Gf,Γf, EqS, Γf',EqS')
    -> length Y = length Y'
    -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
    -> entails Γ' (subst_eqns (sid [Z <-- Y']) EqS')
    -> moreDefinedArgs Gamma Γ' Y Y'
    -> eqn_sound Lv (stmtGoto l Y) (ann0 Gamma) (ann0 Γ') (ann0 (G,G')) (ann0 Y')
| EqnReturn Lv e e' Gamma Γ' G G'
  : moreDefined Gamma Γ' e e'
    -> eqn_sound Lv (stmtReturn e) (ann0 Gamma) (ann0 Γ') (ann0 (G,G')) (ann0 (e'::nil))
| EqnLet Lv s Z b Gamma Γ' EqS EqS' als alb als' alb' cls clb G G' angs angb
  : eqn_sound ((Z, G, Gamma, EqS, Γ', EqS')::Lv) s als als' angs cls
  -> eqn_sound ((Z, G ,Gamma, EqS, Γ', EqS')::Lv) b alb alb' angb clb
  -> entails (EqS ∪ Gamma) (getAnn als)
  -> entails Gamma (getAnn alb)
  -> entails (EqS' ∪ Γ') (getAnn als')
  -> entails Γ' (getAnn alb')
  -> eqns_freeVars EqS ⊆ G ++ of_list Z
  -> eqns_freeVars EqS' ⊆ G ++ of_list Z
  -> eqn_sound Lv (stmtLet Z s b) (ann2 Gamma als alb) (ann2 Γ' als' alb') 
              (ann2 (G,G') angs angb) (ann2 nil cls clb).

Fixpoint compile (s:stmt) (a:ann (list exp)) :=
  match s, a with
    | stmtExp x _ s, ann1 (e'::nil) an =>
      stmtExp x e' (compile s an)
    | stmtIf _ s t, ann2 (e'::nil) ans ant => 
      stmtIf e' (compile s ans) (compile t ant)
    | stmtGoto f _, ann0 Y' => 
      stmtGoto f Y'
    | stmtReturn _, ann0 (e'::nil) => stmtReturn e'
    | stmtLet Z s t, ann2 nil ans ant => 
      stmtLet Z (compile s ans) (compile t ant)
    | s, _ => s
  end.



Definition ArgRel E E' (a:list var*set var*eqns*eqns*eqns*eqns) (VL VL': list val) : Prop := 
  let '(Z, G, Gamma, EqS, Γ', EqS') := a in
  length Z = length VL 
  /\ VL = VL' 
  /\ satisfiesAll (E[Z <-- List.map Some VL]) (EqS ∪ Gamma)
  /\ satisfiesAll (E'[Z <-- List.map Some VL']) (EqS' ∪ Γ').

Definition ParamRel (a:params*set var*eqns*eqns*eqns*eqns) (Z Z' : list var) : Prop := 
  let '(Zb, G, Gamma, EqS, Γ', EqS') := a in  
  Z = Z' /\ Zb = Z.

Definition BlockRel (G':set var) (V V':onv val) (a:params*set var*eqns*eqns*eqns*eqns) (b b':F.block) : Prop := 
  let '(Zb, G, Gamma, EqS, Γ', EqS') := a in  
  G ∩ of_list Zb [=] {}
  /\ G ⊆ G'
  /\ eqns_freeVars EqS ⊆ G ∪ of_list Zb
  /\ eqns_freeVars EqS' ⊆ G ∪ of_list Zb
  /\ satisfiesAll (F.block_E b) Gamma
  /\ satisfiesAll (F.block_E b') Γ'
  /\ agree_on eq G (F.block_E b) V
  /\ agree_on eq G (F.block_E b') V'
  /\ eqns_freeVars Gamma ⊆ G
  /\ eqns_freeVars Γ' ⊆ G.

Instance AR lv V V' : ApxRelation (params*set var*eqns*eqns*eqns*eqns) := {
  ArgRel := ArgRel;
  ParamRel := ParamRel;
  BlockRel := BlockRel lv V V'
}.
intros. hnf in H. hnf in H0.
destruct a as [[[[[]]]]]; dcr; split; congruence.
Defined.

Instance subst_exp_Proper Z Y
  : Proper (_eq ==> _eq) (subst_exp (sid [Z <-- Y])).
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


Instance exp_freeVars_Proper
  :  Proper (eq ==> Equal) Exp.freeVars.
Proof.
  unfold Proper, respectful; intros.
  inv H. general induction y; simpl; hnf; intuition. 
Qed.

Instance freeVars_Proper
  :  Proper (_eq ==> _eq) freeVars.
Proof.
  hnf; intros. inv H. inv H0. inv H1. reflexivity.
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

Lemma eqns_freeVars_add Gamma e 
  : eqns_freeVars ({{e}} ∪ Gamma) [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars. 
  rewrite map_app; eauto using freeVars_Proper.
  rewrite fold_union_app. rewrite map_single.
  rewrite fold_single. 
  cset_tac; intuition.
  eapply Equal_ST.
  eapply union_m.
  eapply transpose_union.
  eapply freeVars_Proper.
Qed.

Lemma eqns_freeVars_add' Gamma e 
  : eqns_freeVars ({e ; Gamma}) [=] eqns_freeVars (Gamma) ∪ freeVars e.
Proof.
  intros. unfold eqns_freeVars. 
  assert ({e; Gamma} [=] {{e}} ∪ Gamma).
  cset_tac; intuition.
  rewrite H. eapply eqns_freeVars_add.
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
  destruct H; dcr; eauto.
Qed.

Lemma satisfiesAll_update_dead E Gamma Z vl
: length Z = length vl
  -> satisfiesAll E Gamma
  -> eqns_freeVars Gamma ∩ of_list Z [=] ∅
  -> satisfiesAll (E[Z <-- vl]) Gamma.
Proof.
  intros. hnf; intros. hnf; intros.
  hnf in H0; exploit H0; eauto. hnf in X.
  erewrite exp_eval_agree; try eapply X.
  symmetry. 
  erewrite exp_eval_agree; try eapply X.
  symmetry. 
  erewrite <- minus_inane_set.
  eapply update_with_list_agree_minus; eauto. reflexivity.
  exploit eqns_freeVars_incl; eauto.
  destruct gamma; simpl in *. rewrite <- H1. 
  revert H1 X0; clear_all; cset_tac; intuition; exfalso; eauto.
  inv X; eauto.
  erewrite <- minus_inane_set.
  symmetry.
  eapply update_with_list_agree_minus; eauto. reflexivity.
  exploit eqns_freeVars_incl; eauto.
  destruct gamma; simpl in *. rewrite <- H1. 
  revert H1 X0; clear_all; cset_tac; intuition; exfalso; eauto.
  inv X; eauto.
Qed.

Lemma eval_exp_subst E y Y Z e
: length Z = length Y
  -> ⎣y ⎦ = omap (exp_eval E) Y
  -> exp_eval (E [Z <-- List.map Some y]) e = 
    exp_eval E (subst_exp (sid [Z <-- Y]) e). 
Proof.
  general induction e; simpl; eauto.
  decide (v ∈ of_list Z).
  eapply length_length_eq in H.
  general induction H; simpl in * |- *; eauto.
  symmetry in H0. monad_inv H0. simpl.
  lud; eauto. eapply IHlength_eq; eauto.
  cset_tac; intuition.
  remember (sid [Z <-- Y] v); intros. symmetry in Heqy0; eauto.
  eapply update_with_list_lookup_not_in in Heqy0. 
  remember (E [Z <-- List.map Some y] v); intros. 
  symmetry in Heqy1.
  eapply update_with_list_lookup_not_in in Heqy1; eauto.
  subst; simpl; eauto. eauto.
  erewrite IHe1; eauto.
  erewrite IHe2; eauto.
Qed.


Lemma agree_on_onvLe {X} `{OrderedType.OrderedType X} (V V':onv X) Z vl
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
  - eapply update_with_list_lookup_not_in in H1; eauto.
    remember (V' [Z <-- vl] x). eapply eq_sym in Heqy.
    eapply update_with_list_lookup_not_in in Heqy; eauto. 
    eapply H0 in H1. congruence.
Qed.


Lemma simL'_update r A (AR AR':ApxRelation A) LV L L' L1 L2
: AIR5 (simB r AR) L L' LV L1 L2
  -> (forall x b b', @SimApx.BlockRel _ AR x b b' -> @SimApx.BlockRel _ AR' x b b')
  -> (forall a Z Z', @SimApx.ParamRel _ AR a Z Z' -> @SimApx.ParamRel _ AR' a Z Z')
  -> (forall V V' a VL VL', @SimApx.ArgRel _ AR V V' a VL VL' <-> @SimApx.ArgRel _ AR' V V' a VL VL')
  -> L = L1
  -> L' = L2
  -> AIR5 (simB r AR') L L' LV L1 L2.
Proof.
  intros. revert_until H. remember AR. induction H; intros.
  - econstructor. 
  - intros. invc H3. invc H4. inv pf.
    econstructor; eauto.
    econstructor; intros; eauto.
    eapply H5; eauto. eapply H2; eauto. 
Qed.

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

Lemma entails_add Gamma gamma Γ'
: entails Gamma ({{gamma}} ∪ Γ')
  -> entails Gamma Γ'.
Proof.
  unfold entails; intros; dcr; split; intros.
  - hnf; intros. eapply H0; eauto. cset_tac; intuition.
  - rewrite <- H1. rewrite eqns_freeVars_add. cset_tac; intuition.
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
  unfold Proper, respectful, flip, impl, entails, satisfiesAll; intros; dcr; split; intros.
  eapply H2; eauto. 
  rewrite H0, <- H. eauto.
Qed.

Instance entails_morphism_flip_impl
: Proper (flip Subset ==> Subset ==> flip impl) entails.
Proof.
  unfold Proper, respectful, flip, impl, entails, satisfiesAll; intros; dcr; split; intros.
  eapply H2; eauto. 
  rewrite H0, <- H. eauto.
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

Lemma satisfiesAll_subst V Gamma Γf Z EqS Y y bE G
:  length Z = length Y
   -> eqns_freeVars EqS ⊆ G ∪ of_list Z
   -> G ∩ of_list Z [=] ∅
   -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
   -> satisfiesAll V Gamma
   -> agree_on eq G V bE
   -> ⎣y ⎦ = omap (exp_eval V) Y
   -> satisfiesAll bE Γf
   -> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  revert_except EqS. pattern EqS. eapply set_induction; intros.
  - hnf; intros. eapply empty_is_empty_1 in H. 
    exfalso. rewrite H in H8. cset_tac; intuition.
  - hnf; intros. eapply Add_Equal in H1. rewrite H1 in H10.
    eapply add_iff in H10. destruct H10.
    + invc H10.
      hnf in H5; dcr. simpl in *. subst.
      specialize (H10 V H6 (subst_eqn (sid [Z <-- Y]) (c,d))). exploit H10.
      admit.
      hnf in X. simpl in X.
      do 2 erewrite <- eval_exp_subst in X; eauto.
      hnf. simpl.
      erewrite exp_eval_agree; [| |reflexivity].
      erewrite exp_eval_agree with (e:=d); [| |reflexivity].
      eapply X.
      eapply update_with_list_agree; eauto.
      eapply agree_on_incl; eauto. 
      assert ((c, d) ∈ s'). rewrite H1.
      cset_tac; intuition.
      exploit eqns_freeVars_incl; eauto. simpl in *.
      rewrite H3 in X0. 
      rewrite <- (minus_union_set _ _ _ H4); eauto.
      rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
      rewrite map_length. simpl in *.
      exploit omap_length; eauto. congruence.
      eapply update_with_list_agree; eauto.
      eapply agree_on_incl; eauto.
      assert ((c, d) ∈ s'). rewrite H1.
      cset_tac; intuition.
      exploit eqns_freeVars_incl; eauto. 
      rewrite H3 in X0. simpl in X0.
      rewrite <- (minus_union_set _ _ _ H4); eauto.
      rewrite <- X0. eapply incl_minus_lr; cset_tac; intuition.
      rewrite map_length. simpl in *.
      exploit omap_length; eauto. congruence.
    + rewrite H1 in H5.
      eapply H; try eapply H7; eauto.
      rewrite <- H3. rewrite H1. 
      rewrite eqns_freeVars_add'. cset_tac; intuition.
      eapply entails_morphism_impl; eauto. reflexivity.
      unfold flip. eapply subst_eqns_morphism_subset; eauto.
      cset_tac; intuition.
Qed.

Lemma in_eqns_freeVars x gamma Gamma
  : x \In freeVars gamma
    -> gamma ∈ Gamma
    -> x \In eqns_freeVars Gamma.
Proof.
  intros. eapply eqns_freeVars_incl; eauto. 
Qed.

Lemma satisfiesAll_update x Gamma V e y
: x ∉ eqns_freeVars Gamma
  -> x ∉ Exp.freeVars e
  -> satisfiesAll V Gamma
  -> ⎣y ⎦ = exp_eval V e
  -> satisfiesAll (V [x <- ⎣y ⎦]) ({{(Var x, e)}} ∪ Gamma).
Proof.
  intros. hnf; intros. cset_tac. destruct H3.
  - hnf; intros. invc H3; simpl in * |- *; subst.
    + erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      rewrite <- H2. simpl. lud. constructor; reflexivity.
      exfalso; eauto.
      eapply agree_on_update_dead; eauto. reflexivity.
  - hnf in H1. exploit H1; eauto. hnf in X.
    hnf. 
    erewrite <- exp_eval_agree; eauto.
    symmetry.
    erewrite <- exp_eval_agree; eauto. symmetry. eapply X.
    eapply agree_on_update_dead; try reflexivity. 
    intro. eapply H. eapply in_eqns_freeVars; eauto. 
    destruct gamma; simpl; cset_tac; intuition.
    eapply agree_on_update_dead; try reflexivity.
    intro. eapply H. eapply in_eqns_freeVars; eauto. 
    destruct gamma; simpl; cset_tac; intuition.
Qed.

Lemma sim_DVE r L L' V V' s LV eqns eqns' repl ang
:
  satisfiesAll V (getAnn eqns) 
-> satisfiesAll V' (getAnn eqns')
-> eqn_sound LV s eqns eqns' ang repl
-> simL' r (AR (fst (getAnn ang)) V V') LV L L'
-> ssa s ang
-> eqns_freeVars (getAnn eqns) ⊆ fst (getAnn ang)
-> eqns_freeVars (getAnn eqns') ⊆ fst (getAnn ang)
-> onvLe V V'
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s repl).
Proof.
  general induction s; simpl; invt eqn_sound; invt ssa; simpl in * |- *.
  + exploiT moreDefined; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs; eauto.
      * eapply H11. eapply satisfiesAll_update; eauto.
      * eapply H13. eapply satisfiesAll_update; eauto.
      * eapply simL'_update; eauto.
        intros. hnf in H9.
        hnf. destruct x0 as [[[[[] ?] ?] ?] ?]. dcr. repeat (split; eauto).
        rewrite H21. rewrite H16. simpl. clear_all; cset_tac; intuition.
        symmetry. eapply agree_on_update_dead.
        intro. eapply H15. eauto. 
        symmetry; eauto. 
        symmetry. eapply agree_on_update_dead.
        intro. eapply H15. eauto. 
        symmetry; eauto.
        clear_all; reflexivity.
      * rewrite H21. simpl. eauto using entails_freeVars_incl.
      * rewrite H21. eapply entails_freeVars_incl; eauto.
      * hnf; intros. lud; eauto.
  + exploiT moreDefined; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. case_eq (val2bool y); intros. 
      econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs1; eauto.
      * eapply H12; eauto.
      * eapply H15; eauto.
      * eapply simL'_update; eauto.
        unfold SimApx.BlockRel.
        destruct x as [[[[[] ?] ?] ?] ?]; simpl; intros; dcr. 
        repeat (split; eauto).
        rewrite H26; eauto.
        clear_all; reflexivity.
      * inv H12. rewrite H26; eauto; simpl. rewrite H16; eauto. 
      * inv H15. rewrite H26; eauto; simpl. rewrite H16; eauto. 
      * econstructor; try eapply plusO.
        econstructor 3; eauto using eq_sym.
        econstructor 3; eauto using eq_sym.
        left. eapply IHs2; try eapply H10; eauto.
        eapply H13; eauto.
        eapply H20; eauto.
        eapply simL'_update; eauto.
        unfold SimApx.BlockRel.
        destruct x as [[[[[] ?] ?] ?] ?]; simpl; intros; dcr. 
        repeat (split; eauto).
        rewrite H27; eauto.
        clear_all; reflexivity.
        inv H13. rewrite H16; eauto. rewrite H27; eauto.
        inv H20. rewrite H16; eauto. rewrite H27; eauto.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length bZ = length Y).
    exploiT moreDefinedArgs; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck.
    - edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
      simpl in *. repeat get_functional; subst.
      inv H26. hnf in H29; simpl in H29; dcr; subst.
      eapply sim_drop_shift. eapply H32; eauto. hnf. simpl; repeat split. 
      exploit omap_length; eauto. unfold var in *. rewrite e. congruence.
      intros. inv H11.
      intros.       
      hnf in H31; dcr.
      eapply satisfiesAll_union; split; eauto.
      eapply (@satisfiesAll_subst V Gamma Γf); eauto. 
      symmetry; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length.
      exploit omap_length; eauto. congruence.
      rewrite <- H19.
      revert H19 H35; clear_all; cset_tac; intuition; exfalso; eauto.
      simpl in *.
      intros. inv H13.
      intros.       
      hnf in H31; dcr. 
      eapply satisfiesAll_union; split; eauto.
      simpl in *.
      eapply (@satisfiesAll_subst V' Γ' Γf'); 
        try eapply H8; eauto.
      congruence. 
      symmetry; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length. 
      exploit omap_length; eauto. congruence. 
      rewrite <- H19.
      revert H19 H37; clear_all; cset_tac; intuition; exfalso; eauto.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
      get_functional; subst. simpl in *. congruence.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
  + simpl. exploiT moreDefined; eauto. inv X; eauto.
    - pfold. econstructor 3; try eapply star_refl. simpl. congruence.
      stuck.
    - pfold. econstructor 2; try eapply star_refl. simpl. congruence.
      stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto.
    - eapply H13; eauto.
    - eapply H16; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * eapply simL'_update; eauto.
        unfold SimApx.BlockRel.
        destruct x as [[[[[] ?] ?] ?] ?]; simpl; intros; dcr. 
        repeat (split; eauto).
        rewrite H28; eauto.
        clear_all; reflexivity.
      * hnf; intros. hnf in H7; dcr.
        eapply IHs1; eauto.
        eapply H12. eauto. 
        eapply H14. eauto.
        eapply simL'_update; eauto.
        unfold SimApx.BlockRel. intros. 
        destruct x as [[[[[] ?] ?] ?] ?]; dcr. simpl in H7.
        simpl. dcr. 
        assert (sEQ: s [=] s \ of_list Z). {
          assert (s ∩ of_list Z [=] ∅).
          rewrite <- H20. rewrite H28 in H32.
          revert H32 H20; simpl; clear_all; cset_tac; intuition; exfalso; eauto.
          rewrite <- (minus_union_set _ _ _ H7).
          clear_all; cset_tac; intuition.
        }
        repeat (split; eauto).
        rewrite H32. rewrite H26. rewrite H28. simpl. eapply incl_right.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto. 
        reflexivity.
        inv H12. rewrite H26; simpl. rewrite H29. rewrite eqns_freeVars_union.
        rewrite H21. rewrite H4. clear_all; cset_tac; intuition.
        inv H14. rewrite H29. rewrite H26. simpl. rewrite eqns_freeVars_union.
        rewrite H22. rewrite H5. clear_all; cset_tac; intuition.
        subst. eapply agree_on_onvLe; eauto.
      * hnf; split; eauto.
      * unfold entails in *. dcr. hnf; intros.
        simpl. split.
        rewrite <- H20. cset_tac; intuition. 
        split.
        rewrite H28; reflexivity.
        repeat (split; eauto; try reflexivity).
    - inv H13. rewrite H8, H28; eauto.
    - invc H16. rewrite H8, H28; eauto.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
