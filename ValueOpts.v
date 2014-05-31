Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy Equiv.Sim IL Fresh Annotation MoreExp Coherence.

Require Import SetOperations Liveness Filter.

Set Implicit Arguments.
Unset Printing Records.


Definition eqn := (exp * exp)%type.

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
  option_eq eq (exp_eval E (fst gamma)) (exp_eval E (snd gamma)).

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
(* /\ eqns_freeVars Γ' ⊆ eqns_freeVars Gamma *).

Definition not_entails Gamma gamma := (exists E, satisfiesAll E Gamma /\ ~ satisfies E gamma).

Definition onvLe X (E E':onv X)
:= forall x v, E x = Some v -> E' x = Some v.

Definition moreDefined Gamma e e' :=
  forall E, satisfiesAll E Gamma
          -> fstNoneOrR eq (exp_eval E e) (exp_eval E e').

Lemma exp_eval_onvLe e E E' v
: onvLe E E'
  -> exp_eval E e = Some v
  -> exp_eval E' e = Some v.
Proof.
  intros. general induction e; simpl in * |- *; eauto.
  simpl in H0. rewrite H0. eapply H in H0. eauto.
  - monad_inv H0. rewrite EQ.
    erewrite IHe; eauto.
  - monad_inv H0. rewrite EQ, EQ1.
    erewrite IHe1, IHe2; eauto.
Qed.

Instance moreDefined_refl Gamma
: Reflexive (moreDefined Gamma).
Proof.
  hnf; intros; hnf; intros.
  case_eq (exp_eval E x); intros.
  constructor; eauto.
  constructor.
Qed.

Definition moreDefinedArgs Gamma Y Y' :=
  forall E,
           satisfiesAll E Gamma

          -> fstNoneOrR eq (omap (exp_eval E) Y) (omap (exp_eval E) Y').

Definition remove (Gamma:eqns) G :=
  filter (fun gamma => B[freeVars gamma ∩ G [=] ∅]) Gamma.

Definition subst_eqn (ϱ : env exp) (e: eqn) :=
  (subst_exp ϱ (fst e), subst_exp ϱ (snd e)).

Definition subst_eqns (ϱ : env exp) (G:eqns) :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.

Inductive eqn_sound : list (params*set var*eqns*eqns)
                      -> stmt
                      -> eqns
                      -> ann (set var * set var)
                      -> ann (list exp)
                      -> Prop :=
| EqnOpr x Lv b e Gamma e' cl G G' ang
  : eqn_sound Lv b ({{(Var x,e)}} ∪ {{(Var x,e')}} ∪ Gamma) ang cl
    (* make sure the rest conforms to the new assignment *)
    -> moreDefined Gamma e e'
    -> Exp.freeVars e' ⊆ G
    -> eqn_sound Lv (stmtExp x e b) Gamma
                (ann1 (G,G') ang) (ann1 (e'::nil) cl)
| EqnIf Lv e e' b1 b2 Gamma cl1 cl2 G G' ang1 ang2
  : (not_entails Gamma (UnOp 0 e, Con val_false) -> eqn_sound Lv b1 ({{(UnOp 0 e,Con val_true)}} ∪ Gamma) ang1 cl1)
  -> (not_entails Gamma (UnOp 0 e, Con val_true) -> eqn_sound Lv b2 ({{(UnOp 0 e,Con val_false)}} ∪ Gamma) ang2 cl2)
  -> moreDefined Gamma e e'
  -> eqn_sound Lv (stmtIf e b1 b2) Gamma
              (ann2 (G,G') ang1 ang2) (ann2 (e'::nil) cl1 cl2)
| EqnGoto l Y Y' Lv Gamma Z Γf EqS Gf G G'
  : get Lv (counted l) (Z,Gf,Γf, EqS)
    -> length Y = length Y'
    -> entails Gamma (subst_eqns (sid [Z <-- Y']) EqS)
    -> moreDefinedArgs Gamma Y Y'
    -> eqn_sound Lv (stmtGoto l Y) Gamma (ann0 (G,G')) (ann0 Y')
| EqnReturn Lv e e' Gamma G G'
  : moreDefined Gamma e e'
    -> eqn_sound Lv (stmtReturn e) Gamma (ann0 (G,G')) (ann0 (e'::nil))
| EqnExtern x f Lv b Y Y' Gamma cl G G' ang
  : eqn_sound Lv b Gamma ang cl
    -> moreDefinedArgs Gamma Y Y'
    -> list_union (List.map Exp.freeVars Y') ⊆ G
    -> eqn_sound Lv (stmtExtern x f Y b) Gamma
                (ann1 (G,G') ang) (ann1 Y' cl)
| EqnLet Lv s Z b Gamma Γ2 EqS cls clb G G' angs angb
  : eqn_sound ((Z, G, Γ2, EqS)::Lv) s (EqS ∪ Γ2) angs cls
  -> eqn_sound ((Z, G ,Γ2, EqS)::Lv) b Gamma angb clb
  -> eqns_freeVars EqS ⊆ G ++ of_list Z
  -> eqns_freeVars Γ2  ⊆ G
  -> entails Gamma Γ2
  -> eqn_sound Lv (stmtLet Z s b) Gamma
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
    | stmtExtern x f _ s, ann1 Y' an =>
      stmtExtern x f Y' (compile s an)
    | stmtLet Z s t, ann2 nil ans ant =>
      stmtLet Z (compile s ans) (compile t ant)
    | s, _ => s
  end.



Definition ArgRel (E E':onv val) (a:list var*set var*eqns*eqns) (VL VL': list val) : Prop :=
  let '(Z, G, Gamma, EqS) := a in
  length Z = length VL
  /\ VL = VL'
  /\ satisfiesAll (E[Z <-- List.map Some VL]) (EqS ∪ Gamma).

Definition ParamRel (a:params*set var*eqns*eqns) (Z Z' : list var) : Prop :=
  let '(Zb, G, Gamma, EqS) := a in
  Z = Z' /\ Zb = Z.

Definition BlockRel (G':set var) (V V':onv val) (a:params*set var*eqns*eqns) (b b':F.block) : Prop :=
  let '(Zb, G, Gamma, EqS) := a in
  G ∩ of_list Zb [=] {}
  /\ G ⊆ G'
  /\ eqns_freeVars EqS ⊆ G ∪ of_list Zb
  /\ satisfiesAll (F.block_E b) Gamma
  /\ agree_on eq G (F.block_E b) V
  /\ agree_on eq G (F.block_E b') V'
  /\ eqns_freeVars Gamma ⊆ G.

Instance AR lv V V' : SimRelation (params*set var*eqns*eqns) := {
  ArgRel := ArgRel;
  ParamRel := ParamRel;
  BlockRel := BlockRel lv V V'
}.
intros. hnf in H. hnf in H0.
destruct a as [[[]]]; dcr; split; congruence.
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

Lemma eqns_freeVars_add2 Gamma e e'
  : eqns_freeVars ({{e}} ∪ {{e'}} ∪ Gamma) [=] eqns_freeVars (Gamma) ∪ freeVars e ∪ freeVars e'.
Proof.
  intros. unfold eqns_freeVars.
  repeat rewrite map_app; eauto using freeVars_Proper.
  repeat rewrite fold_union_app.
  repeat rewrite map_single; eauto using freeVars_Proper.
  repeat rewrite fold_single.
  cset_tac; intuition.
  eapply Equal_ST.
  eapply union_m.
  eapply transpose_union.
  eapply Equal_ST.
  eapply union_m.
  eapply transpose_union.
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
  erewrite IHe; eauto.
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


Lemma simL'_update r A (AR AR':SimRelation A) LV L L' L1 L2
: AIR5 (simB r AR) L L' LV L1 L2
  -> (forall x b b', @Sim.BlockRel _ AR x b b' -> @Sim.BlockRel _ AR' x b b')
  -> (forall a Z Z', @Sim.ParamRel _ AR a Z Z' -> @Sim.ParamRel _ AR' a Z Z')
  -> (forall V V' a VL VL', @Sim.ArgRel _ AR V V' a VL VL' <-> @Sim.ArgRel _ AR' V V' a VL VL')
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

Lemma entails_add Gamma gamma Γ'
: entails Gamma ({{gamma}} ∪ Γ')
  -> entails Gamma Γ'.
Proof.
  unfold entails; intros; dcr; intros.
  - hnf; intros. eapply H; eauto. cset_tac; intuition.
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

Lemma entails_union Gamma Γ' Γ''
: entails Gamma (Γ')
  /\ entails Gamma (Γ'')
  -> entails Gamma (Γ' ∪ Γ'').
Proof.
  unfold entails, satisfiesAll; intros; dcr.
  + intros. cset_tac. destruct H1; eauto.
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
: (e, e') ∈ Gamma
  -> (e', e'') ∈ Gamma
  -> entails Gamma {(e, e''); {}}.
Proof.
  intros. hnf; intros.
  hnf; intros. cset_tac. hnf; intros. rewrite H2.
  simpl. exploit (H1 _ H); eauto.
  exploit (H1 _ H0); eauto.
  simpl in *. inv X; inv X0.
  - econstructor.
  - exfalso. congruence.
  - exfalso. congruence.
  - econstructor. congruence.
Qed.

Lemma entails_eqns_refl e Gamma
: entails Gamma {{ (e, e) }}.
Proof.
  hnf; intros. hnf; intros. hnf; intros. cset_tac. rewrite H0.
  simpl. reflexivity.
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
      hnf in H5; simpl in *. subst.
      specialize (H5 V H6 (subst_eqn (sid [Z <-- Y]) (c,d))). exploit H5.
      eapply in_subst_eqns; eauto. rewrite H1. cset_tac; intuition.
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

Lemma satisfiesAll_update x Gamma V e e' y
: x ∉ eqns_freeVars Gamma
  -> x ∉ Exp.freeVars e
  -> x ∉ Exp.freeVars e'
  -> satisfiesAll V Gamma
  -> ⎣y ⎦ = exp_eval V e
  -> ⎣y ⎦ = exp_eval V e'
  -> satisfiesAll (V [x <- ⎣y ⎦]) ({{(Var x, e)}} ∪ {(Var x, e'); {}} ∪ Gamma).
Proof.
  intros. hnf; intros. cset_tac. destruct H5. destruct H5.
  - hnf; intros. invc H5; simpl in * |- *; subst.
    + erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      rewrite <- H3. simpl. lud.
      exfalso; eauto.
      eapply agree_on_update_dead; eauto. reflexivity.
  - hnf; intros. invc H5; simpl in * |- *; subst.
    + erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      rewrite <- H4. simpl. lud.
      exfalso; eauto.
      eapply agree_on_update_dead; eauto. reflexivity.
  - hnf in H1. exploit H2; eauto. hnf in X.
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


Lemma satisfiesAll_update_dead_single x Gamma V y
: x ∉ eqns_freeVars Gamma
  -> satisfiesAll V Gamma
  -> satisfiesAll (V [x <- ⎣y ⎦]) Gamma.
Proof.
  intros. hnf; intros.
  - hnf; intros.
    assert (agree_on eq (freeVars gamma) (V [x <- ⎣y ⎦]) V). {
      hnf; intros. lud. exfalso; eauto.
      eapply H. eapply in_eqns_freeVars; eauto. rewrite e; eauto.
    }
    + destruct gamma; simpl in *.
      erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      symmetry.
      erewrite <- exp_eval_agree; eauto. instantiate (1:=V).
      symmetry; exploit (H0 _ H1); eauto.
      eapply agree_on_incl; eauto. cset_tac; intuition.
      eapply agree_on_incl; eauto. cset_tac; intuition.
Qed.

Lemma satisfiesAll_monotone E Gamma Γ'
: satisfiesAll E Gamma
  -> Γ' ⊆ Gamma
  -> satisfiesAll E Γ'.
Proof.
  intros. hnf; intros. eapply H; eauto.
Qed.

Lemma moreDefined_monotone Γ1 Γ1' e e'
  : moreDefined Γ1  e e'
    -> Γ1 ⊆ Γ1'
    -> moreDefined Γ1' e e'.
Proof.
  intros. hnf; intros. eapply H; eauto using satisfiesAll_monotone.
Qed.

Lemma moreDefinedArgs_monotone Γ1 Γ1' Y Y'
  : moreDefinedArgs Γ1 Y Y'
    -> Γ1 ⊆ Γ1'
    -> moreDefinedArgs Γ1' Y Y'.
Proof.
  intros. hnf; intros. eapply H; eauto using satisfiesAll_monotone.
Qed.

Lemma entails_monotone Γ1 Γ2 Γ1'
: entails Γ1 Γ2
  -> Γ1 ⊆ Γ1'
  -> entails Γ1' Γ2.
Proof.
  unfold entails; intros; dcr.
  - intros. eapply H. hnf; intros. eapply H1; eauto.
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

Lemma eqn_sound_monotone Es Γ1 Γ1' s ang an
: ssa s ang
  -> eqn_sound Es s Γ1 ang an
  -> Γ1 ⊆ Γ1'
  -> eqn_sound Es s Γ1' ang an.
Proof.
  intros. general induction H0; invt ssa; eauto.
  - econstructor; eauto.
    eapply IHeqn_sound; eauto.
    + rewrite H3; reflexivity.
    + eapply moreDefined_monotone; eauto.
  - econstructor; intros; eauto using moreDefined_monotone, not_entails_antitone.
    eapply H0; eauto using not_entails_antitone. rewrite H5; reflexivity.
    eapply H2; eauto using not_entails_antitone. rewrite H5. reflexivity.
  - econstructor; eauto using entails_monotone, moreDefinedArgs_monotone.
  - econstructor; eauto using moreDefined_monotone.
  - econstructor; eauto using moreDefinedArgs_monotone.
  - econstructor; eauto.
    + rewrite <- H3; eauto.
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

Lemma moreDefined_entails_monotone Γ1 Γ1' e e'
  : moreDefined Γ1 e e'
    -> entails Γ1' Γ1
    -> moreDefined Γ1' e e'.
Proof.
  intros. hnf; intros. eapply H; eauto.
Qed.

Lemma moreDefinedArgs_entails_monotone Γ1 Γ1' Y Y'
  : moreDefinedArgs Γ1 Y Y'
    -> entails Γ1' Γ1
    -> moreDefinedArgs Γ1' Y Y'.
Proof.
  intros. hnf; intros. eapply H; eauto.
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

Lemma eqn_sound_entails_monotone Es Γ1 Γ1' s ang an
: ssa s ang
  -> eqn_sound Es s Γ1 ang an
  -> entails Γ1' Γ1
  -> eqn_sound Es s Γ1' ang an.
Proof.
  intros. general induction H0; invt ssa; eauto.
  - econstructor; eauto.
    eapply IHeqn_sound; eauto using entails_inert.
    + eapply moreDefined_entails_monotone; eauto.
  - econstructor; intros; eauto using moreDefined_entails_monotone,
    not_entails_entails_antitone.
    + eapply H0; eauto using not_entails_entails_antitone.
      eapply entails_union; split.
      eapply entails_monotone. reflexivity. cset_tac; intuition.
      eapply entails_monotone. eauto. cset_tac; intuition.
    + eapply H2; eauto using not_entails_entails_antitone.
      eapply entails_union; split.
      eapply entails_monotone. reflexivity. cset_tac; intuition.
      eapply entails_monotone. eauto. cset_tac; intuition.
  - econstructor; eauto using entails_transitive, moreDefinedArgs_entails_monotone.
  - econstructor; eauto using moreDefined_entails_monotone.
  - econstructor; eauto using moreDefinedArgs_entails_monotone.
  - econstructor; eauto.
    + etransitivity; eauto.
Qed.

Lemma omap_exp_eval_onvLe Y E E' v
: onvLe E E'
  -> omap (exp_eval E) Y = Some v
  -> omap (exp_eval E') Y = Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  simpl in H0. rewrite H0.
  monad_inv H0.
  erewrite exp_eval_onvLe; try eapply H; eauto. simpl.
  erewrite IHY; eauto; simpl; eauto.
Qed.



Lemma sim_DVE r L L' V V' s LV Gamma repl ang
: satisfiesAll V Gamma
-> eqn_sound LV s Gamma ang repl
-> simL' r (AR (fst (getAnn ang)) V V') LV L L'
-> ssa s ang
-> eqns_freeVars Gamma ⊆ fst (getAnn ang)
-> onvLe V V'
-> sim'r r (L,V, s) (L',V', compile s repl).
Proof.
  general induction s; simpl; invt eqn_sound; invt ssa; simpl in * |- *.
  - exploiT moreDefined; eauto. inv X.
    + pfold. econstructor 3; try eapply star2_refl; eauto. stuck2.
    + pose proof H6. symmetry in H7. eapply exp_eval_onvLe in H7; eauto.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto using eq_sym. reflexivity.
      econstructor; eauto using eq_sym. reflexivity.
      left. eapply IHs; eauto.
      * eapply satisfiesAll_update; eauto.
      * {
          eapply simL'_update; eauto.
          - intros. hnf in H8.
            hnf. destruct x0 as [[[ ?] ?] ?]. dcr. repeat (split; eauto).
            rewrite H17, H18. simpl. clear_all; cset_tac; intuition.
            symmetry. eapply agree_on_update_dead.
            intro. eapply H11. eauto.
            symmetry; eauto.
            symmetry. eapply agree_on_update_dead.
            intro. eapply H11. eauto.
            symmetry; eauto.
          - intros; reflexivity.
        }
      * rewrite H17. simpl. rewrite eqns_freeVars_add2.
        rewrite H3. simpl. rewrite H14. rewrite H15.
        clear_all; cset_tac; intuition.
      * hnf; intros. lud; eauto.
  - exploiT moreDefined; eauto. inv X.
    + pfold. econstructor 3; try eapply star2_refl; eauto. stuck2.
    + pose proof H6. symmetry in H7. eapply exp_eval_onvLe in H7; eauto.
      pfold. case_eq (val2bool y); intros.
      assert (not_entails Gamma (UnOp 0 e, Con val_false)). {
        hnf; intros. eexists V; split; eauto.
        intro. hnf in H10. simpl in *.
        rewrite <- H5 in H10. inv H10.
        cbv in H8. destruct y. congruence.
        destruct if in H22. congruence. cbv in H22. congruence.
      }
      econstructor; try eapply plus2O.
      econstructor; eauto using eq_sym. reflexivity.
      econstructor; eauto using eq_sym. reflexivity.
      left. eapply IHs1; try eapply H9; eauto.
      * eapply satisfiesAll_union; split; eauto.
        hnf; intros. cset_tac. inv H11. inv H24. inv H25.
        hnf. simpl. rewrite <- H5. unfold option_lift1. simpl.
        unfold val2bool in H8. destruct y; try congruence.
        destruct if; try congruence. constructor. reflexivity.
      * eapply simL'_update; eauto.
        unfold Sim.BlockRel.
        destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
        repeat (split; eauto).
        rewrite H20; eauto.
        clear_all; reflexivity.
      * rewrite eqns_freeVars_add. rewrite H20, H3.
        simpl. rewrite H15. cset_tac; intuition.
      * assert (not_entails Gamma (UnOp 0 e, Con val_true)). {
          hnf; intros. eexists V; split; eauto.
          intro. hnf in H10. simpl in *.
          rewrite <- H5 in H10. inv H10.
          cbv in H8. destruct y.
          destruct if in H22. cbv in H22. congruence.
          congruence. congruence.
        }
        econstructor; try eapply plus2O.
        econstructor 3; eauto using eq_sym. reflexivity.
        econstructor 3; eauto using eq_sym. reflexivity.
        {
          left. eapply IHs2; try eapply H13; eauto.
          - eapply satisfiesAll_union; split; eauto.
            hnf; intros. cset_tac. inv H11. inv H24. inv H25.
            hnf. simpl. rewrite <- H5. unfold option_lift1. simpl.
            unfold val2bool in H8. destruct y; try congruence.
            destruct if; try congruence. constructor. reflexivity.
          - eapply simL'_update; eauto.
            unfold Sim.BlockRel.
            destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
            repeat (split; eauto).
            rewrite H21; eauto.
            clear_all; reflexivity.
          - rewrite eqns_freeVars_add; simpl.
            rewrite H15, H3, H21. simpl. cset_tac; intuition.
        }
  - destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length bZ = length Y).
    exploiT moreDefinedArgs; eauto. inv X.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2.
    + pose proof H6. symmetry in H9. eapply omap_exp_eval_onvLe in H9; eauto.
      edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H24. hnf in H27; simpl in H27; dcr; subst.
      eapply sim_drop_shift. eapply H30; eauto. hnf. simpl; repeat split.
      exploit omap_length; eauto. unfold var in *. congruence.
      hnf in H29; dcr.
      eapply satisfiesAll_union; split; eauto.
      eapply (@satisfiesAll_subst V Gamma Γf); try eapply H6; eauto.
      congruence.
      symmetry; eauto.
      eapply satisfiesAll_update_dead; eauto. rewrite map_length.
      exploit omap_length; eauto. congruence.
      rewrite <- H7.
      revert H7 H28; clear_all; cset_tac; intuition; exfalso; eauto.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2; eauto.
      get_functional; subst. simpl in *. congruence.
    + pfold. econstructor 3; try eapply star2_refl. eauto. stuck2; eauto.
  - simpl. exploiT moreDefined; eauto. inv X; eauto.
    + pfold. econstructor 3; try eapply star2_refl. simpl. congruence.
      stuck2.
    + pfold. econstructor 4; try eapply star2_refl. simpl.
      erewrite <- exp_eval_onvLe in H5; eauto.
      stuck2. stuck2.
  - exploiT moreDefinedArgs; eauto. inv X.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2.
    + pfold. eapply sim'Extern; try eapply star2_refl.
      * eexists (ExternI f y 0); eexists; econstructor; eauto.
      * pose proof H6. symmetry in H7. eapply omap_exp_eval_onvLe in H7; eauto.
        eexists (ExternI f y 0); eexists; econstructor; eauto.
      * { intros. inv H7.
          eexists. econstructor; eauto.
          - econstructor; eauto.
            eapply omap_exp_eval_onvLe; eauto. congruence.
          - left. eapply IHs; eauto.
            + eapply satisfiesAll_update_dead_single; eauto.
            + eapply simL'_update; eauto.
              * unfold Sim.BlockRel. intros. simpl in *.
                unfold BlockRel in *.
                destruct x0 as [[[ ?] ?] ?]; simpl; intros; dcr.
                repeat (split; eauto).
                rewrite H18. rewrite H12. simpl. clear_all; cset_tac; intuition.
                symmetry. eapply agree_on_update_dead. rewrite H12. eauto.
                symmetry; eauto.
                symmetry. eapply agree_on_update_dead. rewrite H12. eauto.
                symmetry; eauto.
              * intros; reflexivity.
            + rewrite H3, H18; simpl. clear_all; cset_tac; intuition.
            + hnf; intros; lud; eauto.
        }
      * { intros. inv H7.
          eexists. econstructor; eauto.
          - econstructor; eauto.
            pose proof H6.
            erewrite <- omap_exp_eval_onvLe in H6; eauto. congruence.
          - left. eapply IHs; eauto.
            + eapply satisfiesAll_update_dead_single; eauto.
            + eapply simL'_update; eauto.
              * unfold Sim.BlockRel. intros. simpl in *.
                unfold BlockRel in *.
                destruct x0 as [[[ ?] ?] ?]; simpl; intros; dcr.
                repeat (split; eauto).
                rewrite H18. rewrite H12. simpl. clear_all; cset_tac; intuition.
                symmetry. eapply agree_on_update_dead. rewrite H12. eauto.
                symmetry; eauto.
                symmetry. eapply agree_on_update_dead. rewrite H12. eauto.
                symmetry; eauto.
              * intros; reflexivity.
            + rewrite H3, H18; simpl. clear_all; cset_tac; intuition.
            + hnf; intros; lud; eauto.
        }
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IHs2; eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * eapply simL'_update; eauto.
        unfold Sim.BlockRel.
        destruct x as [[[ ?] ?] ?]; simpl; intros; dcr.
        repeat (split; eauto).
        rewrite H10, H23; reflexivity.
        clear_all; reflexivity.
      * hnf; intros. hnf in H5; dcr.
        eapply IHs1; try eapply H10; eauto.
        eapply simL'_update; eauto.
        unfold Sim.BlockRel. intros.
        destruct x as [[[ ?] ?] ?]; dcr. simpl in H5.
        simpl. dcr.
        assert (sEQ: s [=] s \ of_list Z). {
          assert (s ∩ of_list Z [=] ∅).
          rewrite <- H17. rewrite H23 in H26.
          revert H26 H17; simpl; clear_all; cset_tac; intuition; exfalso; eauto.
          rewrite <- (minus_union_set _ _ _ H5).
          clear_all; cset_tac; intuition.
        }
        repeat (split; eauto).
        rewrite H26. rewrite H21,H23; simpl. eapply incl_right.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto.
        rewrite sEQ. symmetry.
        eapply update_with_list_agree_minus; eauto. rewrite map_length; eauto.
        symmetry; eauto.
        reflexivity.
        rewrite H21; simpl. rewrite eqns_freeVars_union.
        rewrite H11, H15. clear_all; cset_tac; intuition.
        subst. eapply agree_on_onvLe; eauto.
      * hnf; split; eauto.
      * hnf; intros.
        simpl. split.
        rewrite <- H17. clear_all; cset_tac; intuition.
        split.
        rewrite H23; reflexivity.
        repeat (split; eauto using satisfiesAll_monotone; try reflexivity).
    + rewrite H3, H23; reflexivity.
Qed.

Print Assumptions sim_DVE.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
