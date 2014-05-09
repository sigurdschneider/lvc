Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL ParamsMatch Sim SimApx Alpha Coherence Fresh Annotation MoreExp.

Require Import Liveness Filter.

Set Implicit Arguments.
Unset Printing Records.


Definition eqn := (exp * exp)%type.

Instance OrderedType_binop : OrderedType binop.
Admitted.

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
Admitted.

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
assert (b = b0) by admit; subst.
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

Definition satisfiesAll (E:onv val) (Gamma:set eqn) := 
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.

Definition sem_entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'. 

Definition freeVars (gamma:exp * exp) := 
  Exp.freeVars (fst gamma) ∪ Exp.freeVars (snd gamma).

Definition eqns_freeVars (Gamma:set eqn) := fold union (map freeVars Gamma) ∅.

Definition entails Gamma Γ' := (forall E, satisfiesAll E Gamma -> satisfiesAll E Γ') 
/\ eqns_freeVars Γ' ⊆ eqns_freeVars Gamma. 

Definition moreDefined Gamma Γ' e e' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Γ' -> fstNoneOrR eq (exp_eval E e) (exp_eval E' e').

Definition moreDefinedArgs Gamma Γ' Y Y' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Γ' -> 
          fstNoneOrR eq (omap (exp_eval E) Y) (omap (exp_eval E') Y').

(*Definition moreDefined Gamma Γ' e e' := 
  forall E, satisfies E Gamma -> forall E', satisfies E' Γ' -> moreDef (exp_eval E e) (exp_eval E' e').*)


Definition remove (Gamma:set eqn) G :=
  filter (fun gamma => B[freeVars gamma ∩ G [=] ∅]) Gamma.

Definition subst_eqn (ϱ : env exp) (e: eqn) :=
  (subst_exp ϱ (fst e), subst_exp ϱ (snd e)).

Definition subst_eqns (ϱ : env exp) (G:set eqn) :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.


Inductive eqn_sound : list (params*set eqn*set eqn*set eqn*set eqn) 
                      -> stmt 
                      -> ann (set eqn) 
                      -> ann (set eqn) 
                      -> ann (list exp) 
                      -> Prop :=
| EqnOpr x Lv b e Gamma al Γ' (al':ann (set eqn)) e' al' cl
  : eqn_sound Lv b al al' cl
    (* make sure the rest conforms to the new assignment *)
    -> entails (Gamma ∪ {{ (Var x,e) }}) (getAnn al)
    -> entails (Γ' ∪ {{ (Var x,e') }}) (getAnn al')
    -> moreDefined Gamma Γ' e e'
    -> Exp.freeVars e' ⊆ eqns_freeVars Γ'
    -> eqn_sound Lv (stmtExp x e b) (ann1 Gamma al) (ann1 Γ' al') (ann1 (e'::nil) cl)
| EqnIf Lv e e' b1 b2 Gamma Γ' al1 al2 al1' al2' cl1 cl2
  : eqn_sound Lv b1 al1 al1' cl1
  -> eqn_sound Lv b2 al2 al2' cl2
 (* TODO: include information about condition *)
  -> entails Gamma (getAnn al1)
  -> entails Gamma (getAnn al2)
  -> entails Γ' (getAnn al1')
  -> entails Γ' (getAnn al2')
  -> moreDefined Gamma Γ' e e'
  -> eqn_sound Lv (stmtIf e b1 b2) (ann2 Gamma al1 al2) (ann2 Γ' al1' al2') (ann2 (e'::nil) cl1 cl2)
| EqnGoto l Y Y' Lv Gamma Γ' Z Γf Γf' EqS EqS'
  : get Lv (counted l) (Z,Γf, EqS, Γf',EqS')
    -> length Y = length Y'
    -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
    -> entails Γ' (subst_eqns (sid [Z <-- Y']) EqS')
    -> moreDefinedArgs Gamma Γ' Y Y'
    -> eqn_sound Lv (stmtGoto l Y) (ann0 Gamma) (ann0 Γ') (ann0 Y')
| EqnReturn Lv e e' Gamma Γ'
  : moreDefined Gamma Γ' e e'
    -> eqn_sound Lv (stmtReturn e) (ann0 Gamma) (ann0 Γ') (ann0 (e'::nil))
| EqnLet Lv s Z b Gamma Γ' EqS EqS' als alb als' alb' cls clb
  : eqn_sound ((Z,Gamma, EqS, Γ', EqS')::Lv) s als als' cls
  -> eqn_sound ((Z,Gamma, EqS, Γ', EqS')::Lv) b alb alb' clb
  -> entails (Gamma ∪ EqS) (getAnn als)
  -> entails Gamma (getAnn alb)
  -> entails (Γ' ∪ EqS') (getAnn als')
  -> entails Γ' (getAnn alb')
  -> eqns_freeVars EqS ⊆ eqns_freeVars Gamma ++ of_list Z
  -> eqns_freeVars EqS' ⊆ eqns_freeVars Γ' ++ of_list Z
  -> eqn_sound Lv (stmtLet Z s b) (ann2 Gamma als alb) (ann2 Γ' als' alb') (ann2 nil cls clb).

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

Definition ArgRel E E' (G:list var*set eqn*set eqn*set eqn*set eqn) (VL VL': list val) : Prop := 
  let '(Z, Gamma, EqS, Γ', EqS') := G in
  length Z = length VL 
  /\ length VL = length VL' 
  /\ satisfiesAll (E[Z <-- List.map Some VL]) (Gamma ∪ EqS)
  /\ satisfiesAll (E'[Z <-- List.map Some VL']) (Γ' ∪ EqS').


Definition ParamRel (G:params*set eqn*set eqn*set eqn*set eqn) (Z Z' : list var) : Prop := 
  let '(Zb, Gamma, EqS, Γ', EqS') := G in  
  Z = Z' /\ Zb = Z.

Definition onvLe X (E E':onv X)
:= forall x v, E x = Some v -> E' x = Some v.

Definition BlockRel (lv:set var) (V V':onv val) (G:params*set eqn*set eqn*set eqn*set eqn) (b b':F.block) : Prop := 
  let '(Zb, Gamma, EqS, Γ', EqS') := G in  
  eqns_freeVars Gamma ∩ of_list Zb [=] {}
  /\ eqns_freeVars Γ' ∩ of_list Zb [=] {}
  /\ eqns_freeVars EqS ⊆ eqns_freeVars Gamma ∪ of_list Zb
  /\ eqns_freeVars EqS' ⊆ eqns_freeVars Γ' ∪ of_list Zb
  /\ satisfiesAll (F.block_E b) Gamma
  /\ satisfiesAll (F.block_E b') Γ'
  /\ agree_on (eqns_freeVars Gamma) (F.block_E b) V
  /\ agree_on (eqns_freeVars Γ') (F.block_E b') V'
  /\ eqns_freeVars Gamma ⊆ lv
  /\ eqns_freeVars Γ' ⊆ lv.

(* problem is Gamma that satisfies nothing 
Lemma entails_freeVars Gamma Γ'
 : entails Gamma Γ' -> eqns_freeVars Γ' ⊆ eqns_freeVars Gamma.
Proof.
  intros. hnf in H.
  unfold eqns_freeVars in *.
  hnf. intros. 
  assert (exists l, l ∈ (map freeVars Γ') /\ a ∈ l) by .
  destruct H1. dcr. eapply map_2 in H2.
  destruct H2. dcr. decide (a \In fold union (map freeVars Gamma) {}); eauto.
  exfalso. hnf in n.
  (* construct E that maps x to None *).
  
  
  
Qed.
*)


Lemma fold_union_incl X `{OrderedType.OrderedType X} s u (x:X) y
  : x ∈ y
    -> y ∈ s
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - exfalso. eapply H0; eauto.
  - rewrite fold_2; eauto. eapply Add_Equal in H2. rewrite H2 in H4.
    cset_tac. destruct H4.
    left. rewrite H4. eauto.
    right. eapply H0; eauto. eapply Equal_ST. eapply union_m.
    hnf; intros. cset_tac; intuition.
Qed.

Lemma eqn_freeVars_incl Gamma gamma
  : gamma ∈ Gamma
    -> freeVars gamma ⊆ eqns_freeVars Gamma.
Proof.
  intros. unfold eqns_freeVars. 
  hnf; intros.
  eapply fold_union_incl; eauto.
  eapply map_1; eauto. hnf; intros.
  inv H1. inv H2. inv H3. reflexivity.
Qed.

Lemma map_app X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) 
      `{Proper _ (_eq ==> _eq) f} s t 
: map f (s ∪ t) [=] map f s ∪ map f t.
Proof. 
  cset_tac. repeat rewrite map_iff; eauto. 
  split; intros. destruct H2.
  dcr.
  eapply union_cases in H3. firstorder.
  intuition. destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
  intuition. destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
Qed.

Lemma map_empty X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) 
      `{Proper _ (_eq ==> _eq) f}
: map f ∅ [=] ∅.
Proof. 
  cset_tac.
  rewrite map_iff; eauto. 
  firstorder. cset_tac; eauto.
Qed.

Instance map_Proper X `{OrderedType X} Y `{OrderedType Y}
  : Proper (@fpeq X _ Y _ ==> _eq ==> _eq) map.
Proof.
  unfold Proper, respectful; intros. inv H1; dcr.
  hnf; intros. repeat rewrite map_iff; eauto.
  intuition. 
  destruct H4; dcr; eexists; split; eauto.
  rewrite <- H2; eauto. rewrite H8. eapply H3.
  destruct H4; dcr; eexists; split; eauto.
  rewrite H2; eauto. rewrite H8. symmetry. eapply H3.
Qed.

Instance fold_union_Proper X `{OrderedType X}
  : Proper (_eq ==> _eq ==> _eq) (fold union).
Proof.
  unfold Proper, respectful.
  intros. revert_except x. pattern x.
  eapply set_induction; intros.
  - repeat rewrite fold_1; eauto.
    rewrite <- H1; eauto.
  - rewrite fold_2; eauto using union_m.
    eapply Add_Equal in H2.
    rewrite H3 in H2.
    eapply Add_Equal in H2.
    symmetry.
    rewrite fold_2; eauto using union_m. 
    rewrite H0; try reflexivity. symmetry; eauto.
    hnf; intros. hnf. cset_tac; intuition.
    hnf; intros. hnf. cset_tac; intuition.    
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

Lemma eqns_freeVars_union Gamma Γ'
  : eqns_freeVars (Gamma ++ Γ') [=] eqns_freeVars (Gamma) ∪ eqns_freeVars Γ'.
Proof.
  unfold eqns_freeVars.
  rewrite map_app.
  revert Γ'. pattern Gamma.
  eapply set_induction.
  - intros. eapply empty_is_empty_1 in H. 
    assert (fold union (map freeVars s) ∅ [=] ∅).
    assert (fpeq freeVars freeVars). 
    hnf; split. reflexivity. split; eauto using freeVars_Proper.
    rewrite (map_Proper _ _ _ _ H0 _ _ H). reflexivity.
Admitted.

Lemma eqns_freeVars_add Gamma x e
  : eqns_freeVars (Gamma ++ {{(Var x, e)}}) [=] eqns_freeVars (Gamma) ∪ {{ x }} ∪ Exp.freeVars e.
Proof.
  intros.
Admitted.

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
  intros [A B]; hnf; intros. cset_tac. destruct H; auto.
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
  exfalso; admit. inv X; eauto.
  erewrite <- minus_inane_set.
  symmetry.
  eapply update_with_list_agree_minus; eauto. reflexivity.
  exfalso; admit. inv X; eauto.
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

Lemma agree_on_onvLe X `{OrderedType.OrderedType X} (V V':onv X) Z vl
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


Lemma simL'_update r A R R' (RB RB':SimApx.BlockRel A) LV L L' L1 L2
: AIR5 (@simB r A R R' RB) L L' LV L1 L2
  -> (forall x b b', RB x b b' -> RB' x b b')
  -> L = L1
  -> L' = L2
  -> AIR5 (simB r R R' RB') L L' LV L1 L2.
Proof.
  intros. general induction H.
  - econstructor. 
  - inv pf.
    econstructor; eauto.
    econstructor; intros; eauto.
Qed.

Lemma eqns_freeVars_incl Gamma Γ' G x e
: entails (Gamma ++ {{(Var x, e)}}) Γ'
  -> Exp.freeVars e ⊆ G
  -> eqns_freeVars Gamma ⊆ G
  -> eqns_freeVars Γ' ⊆ G ∪ {{x}}.
Proof.
  intros. destruct H.
  rewrite eqns_freeVars_add in H2.
  rewrite H2. rewrite H0. rewrite H1. 
  clear_all; cset_tac; intuition.
Qed.

Instance subst_exp_Proper Z Y
  : Proper (_eq ==> _eq) (subst_exp (sid [Z <-- Y])).
Proof.
  hnf; intros. inv H. clear H.
  simpl. general induction y; simpl; eauto.
Qed.

Instance subst_eqn_Proper Z Y
  : Proper (_eq ==> _eq) (subst_eqn (sid [Z <-- Y])).
Proof.
  hnf; intros. inv H. hnf in H0, H1. subst. clear H.
  simpl. unfold subst_eqn; simpl. 
  rewrite subst_exp_Proper; try reflexivity.
Qed.

Lemma satisfiesAll_subst V Gamma Γf Z EqS Y y bE
:  length Z = length Y
   -> eqns_freeVars EqS ⊆ eqns_freeVars Γf ∪ of_list Z
   -> eqns_freeVars Γf ∩ of_list Z [=] ∅
   -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
   -> satisfiesAll V Gamma
   -> agree_on (eqns_freeVars Γf) V bE
   -> ⎣y ⎦ = omap (exp_eval V) Y
   -> satisfiesAll bE Γf
   -> satisfiesAll (bE [Z <-- List.map Some y]) EqS.
Proof.
  intros.
  revert_except EqS. pattern EqS.
  eapply set_induction; intros. 
  - hnf; intros. exfalso. eapply H. eauto.
  - hnf; intros ? INS. rewrite Add_Equal in H1.
    rewrite H1 in INS. eapply add_iff in INS. destruct INS.
    + inv H10. hnf in H11, H12; subst.
      hnf in H5; dcr.
      specialize (H11 V H6 (subst_eqn (sid [Z <-- Y]) (c,d))). exploit H11.
      unfold subst_eqns.
      eapply map_1; eauto using subst_eqn_Proper. 
      rewrite H1. cset_tac; intuition.
      hnf in X. simpl in X.
      do 2 erewrite <- eval_exp_subst in X; eauto.
      hnf. simpl.
      erewrite exp_eval_agree; [| |reflexivity].
      erewrite exp_eval_agree with (e:=d); [| |reflexivity].
      eapply X.
      eapply update_with_list_agree.
      eapply agree_on_incl; eauto. admit.
      rewrite map_length. simpl in *.
      exploit omap_length; eauto. congruence.
      eapply update_with_list_agree.
      eapply agree_on_incl; eauto. admit.
      rewrite map_length. simpl in *.
      exploit omap_length; eauto. congruence.
    + eapply H; try eapply H8; eauto. admit. 
      admit.
Qed.

Lemma satisfiesAll_update x Gamma V e y
: x ∉ eqns_freeVars Gamma
  -> x ∉ Exp.freeVars e
  -> satisfiesAll V Gamma
  -> ⎣y ⎦ = exp_eval V e
  -> satisfiesAll (V [x <- ⎣y ⎦]) (Gamma ++ {(Var x, e); {}}).
Proof.
  intros. hnf; intros. cset_tac. destruct H3.
  - hnf; intros. admit.
  - assert (gamma = (Var x, e)) by admit. subst gamma.
    hnf; simpl. lud. erewrite exp_eval_agree; eauto.
    instantiate (1:=V). erewrite <- H2. constructor; eauto.
    symmetry. eapply agree_on_update_dead; eauto.
    reflexivity.
    exfalso. eapply H4. reflexivity.
Qed.

Lemma sim_DVE r L L' V V' s LV eqns eqns' repl G G'
:
  satisfiesAll V (getAnn eqns) 
-> satisfiesAll V' (getAnn eqns')
-> eqn_sound LV s eqns eqns' repl
-> simL' r ArgRel ParamRel (BlockRel G V V') LV L L'
-> ssa G s G'
-> eqns_freeVars (getAnn eqns) ⊆ G
-> eqns_freeVars (getAnn eqns') ⊆ G
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s repl).
Proof.
  general induction s; simpl; invt eqn_sound; invt ssa; simpl in * |- *.
  + unfold moreDefined in H16; exploit H16; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs; eauto.
      eapply H10.
      eapply satisfiesAll_update; eauto.
      eapply H12. eapply satisfiesAll_update; eauto.
      eapply simL'_update; eauto.
      intros. hnf in H8.
      hnf. destruct x0 as [[[[] ?] ?] ?]. dcr. repeat (split; eauto).
      symmetry. eapply agree_on_update_dead.
      intro. eapply H13. eauto. eauto using agree_on_sym.
      symmetry. eapply agree_on_update_dead.
      intro. eapply H13. eauto. eauto using agree_on_sym.
      cset_tac; intuition. cset_tac; intuition.
      eauto using eqns_freeVars_incl.
      eapply eqns_freeVars_incl; eauto.
      rewrite H17; eauto.
  + unfold moreDefined in H19; exploit H19; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. case_eq (val2bool y); intros. 
      econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs1; eauto.
      eapply H11; eauto.
      eapply H14; eauto.
      destruct H11. rewrite H16; eauto. 
      destruct H14. rewrite H16; eauto.
      econstructor; try eapply plusO.
      econstructor 3; eauto using eq_sym.
      econstructor 3; eauto using eq_sym.
      left. eapply IHs2; try eapply H10; eauto.
      eapply H12; eauto.
      eapply H18; eauto.
      destruct H12. rewrite H16; eauto.
      destruct H18. rewrite H18; eauto.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length bZ = length Y).
    hnf in H16. exploit H16; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck.
    - edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
      simpl in *. repeat get_functional; subst.
      inv H25. hnf in H28; simpl in H28; dcr; subst.
      eapply sim_drop_shift. eapply H31; eauto. hnf. simpl; repeat split. 
      exploit omap_length; eauto. unfold var in *. rewrite e. congruence.
      intros. inv H10.
      intros.       
      hnf in H30; dcr. eauto. 
      eapply satisfiesAll_union; split; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length.
      exploit omap_length; eauto. congruence. simpl in *.
      intros. 
      eapply (@satisfiesAll_subst V Gamma Γf); eauto using agree_on_sym.
      intros. inv H12.
      intros.       
      hnf in H30; dcr. 
      eapply satisfiesAll_union; split; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length. 
      exploit omap_length; eauto. congruence. 
      simpl in *.
      eapply (@satisfiesAll_subst V' Γ' Γf'); 
        try eapply H7; eauto using agree_on_sym.
      congruence. 
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
      get_functional; subst. simpl in *. congruence.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
  + simpl. hnf in H8; exploit H8; eauto. inv X; eauto.
    - pfold. econstructor 3; try eapply star_refl. simpl. congruence.
      stuck.
    - pfold. econstructor 2; try eapply star_refl. simpl. congruence.
      stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto.
    - eapply H12; eauto.
    - eapply H15; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * hnf; intros. destruct a as [[[[Zb Γb] EqSb] Γb'] EqSb'].
        hnf in H6. hnf in H7. dcr; subst.
        split; eauto. unfold var in *. congruence.
      * hnf; intros. hnf in H6; dcr.
        eapply IHs1; eauto.
        eapply H11. eauto. 
        eapply H13. eauto.
        eapply simL'_update; eauto.
        unfold BlockRel. intros. 
        destruct x as [[[[] ?] ?] ?]; dcr.
        repeat (split; eauto).
        symmetry. 
        assert (eqns_freeVars s [=] eqns_freeVars s \ of_list Z) by admit.
        rewrite H6.
        eapply update_with_list_agree_minus. rewrite map_length; eauto.
        eauto using agree_on_sym; eauto.
        symmetry.
        assert (eqns_freeVars s3 [=] eqns_freeVars s3 \ of_list Z) by admit.
        rewrite H6.
        eapply update_with_list_agree_minus. rewrite map_length; eauto.
        eauto using agree_on_sym; eauto.
        rewrite <- H35. clear_all; cset_tac; intuition. 
        rewrite <- H37. clear_all; cset_tac; intuition.
        destruct H11. rewrite H11. rewrite eqns_freeVars_union.
        rewrite H19. rewrite H4. clear_all; cset_tac; intuition.
        destruct H13. rewrite H13. rewrite eqns_freeVars_union.
        rewrite H20. rewrite H5. clear_all; cset_tac; intuition.
      * hnf; split; eauto.
      * unfold entails in *. dcr. hnf; intros.
        simpl. split.
        rewrite <- H14. cset_tac; intuition. exfalso. eapply H14; eauto.
        split.
        rewrite <- H14. cset_tac; intuition. exfalso. eapply H14; eauto.
        repeat (split; eauto using agree_on_refl).
    - destruct H12. rewrite H7; eauto.
    - destruct H15. rewrite H7; eauto.
Qed.

Print Assumptions sim_DVE.

(*           
Lemma sim_DVE L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> @simapx F.state _ F.state _ (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - eapply simS; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto. 
    - eapply simapx_expansion_closed; 
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - eapply simErr; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto. 
    rewrite <- H; eauto. eapply IHs1; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. eapply IHs2; eauto using agree_on_incl.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
(*    hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length Z = length Y). 
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply simS; try eapply plusO.
    econstructor; eauto. simpl. congruence.
    econstructor; eauto. simpl. hnf in H21. dcr. simpl in *. subst.
    simpl.  
    eapply argsLive_filter_length; eauto.
    simpl in * |- *.
    unfold updE. eapply H21.
    hnf. simpl. 
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto.
    congruence.
    rewrite lookup_list_length; congruence.
    subst. rewrite lookup_list_length.
    eapply argsLive_filter_length; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    simpl in *. repeat get_functional; subst.

  + eapply simE; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
    stuck. stuck.
  + econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. eapply IHs2; eauto. 
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_extension; eauto. hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
