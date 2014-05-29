Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL Sim Fresh Annotation MoreExp Coherence LabelsDefined DecSolve.

Require Import Liveness Filter SetOperations ValueOpts.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)


(* None is top *)
Definition aval := val.

Fixpoint exp_eval (E:onv aval) (e:exp) : option aval :=
  match e with
    | Con v => Some v
    | Var x => E x
    | BinOp o e1 e2 => mdo v1 <- exp_eval E e1;
                      mdo v2 <- exp_eval E e2;
                      Exp.binop_eval o v1 v2
  end.

Inductive le_precise : option aval -> option aval -> Prop :=
  | leTop x : le_precise None x
  | leValVal y : le_precise (Some y) (Some y)
  | leBot  : le_precise None None.

Instance le_precise_computable a b : Computable (le_precise a b).
destruct a, b; try dec_solve.
decide (a = a0); subst; try dec_solve.
Defined.

Lemma PIR2_length X Y (R:X->Y->Prop) L L'
: PIR2 R L L' -> length L = length L'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Instance PIR2_computable X Y (R:X->Y->Prop) `{forall x y, Computable (R x y)}
: forall (L:list X) (L':list Y), Computable (PIR2 R L L').
Proof.
  intros. decide (length L = length L').
  - general induction L; destruct L'; isabsurd; try dec_solve.
    decide (R a y); try dec_solve.
    edestruct IHL with (L':=L'); eauto; subst; try dec_solve.
  - right; intro; subst. exploit PIR2_length; eauto.
Defined.

Inductive cp_sound (AE:onv aval) : list (params)
                      -> stmt
                      -> Prop :=
| CPOpr (x:var) Cp b e
  : cp_sound AE Cp b
    -> exp_eval AE e = AE x
    -> cp_sound AE Cp (stmtExp x e b)
| CPIf Cp e b1 b2
  : (* these conditions make it conditional constant propagation *)
    (exp_eval AE e <> (Some val_false) -> cp_sound AE Cp b1)
    -> (exp_eval AE e <> (Some val_true) -> cp_sound AE Cp b2)
    -> cp_sound AE Cp (stmtIf e b1 b2)
| CPGoto l Y Cp Z
  : get Cp (counted l) Z
    -> length Z = length Y
    -> PIR2 le_precise (lookup_list AE Z) (List.map (exp_eval AE) Y)
    -> cp_sound AE Cp (stmtGoto l Y)
| CPReturn Cp e
  : cp_sound AE Cp (stmtReturn e)
| CPLet Cp s Z b
  : cp_sound AE (Z::Cp) s
  -> cp_sound AE (Z::Cp) b
  -> cp_sound AE Cp (stmtLet Z s b).

Instance cp_sound_dec AE ZL s : Computable (cp_sound AE ZL s).
Proof.
  hnf. general induction s; try dec_solve.
  - edestruct IHs; decide (exp_eval AE e = AE x); dec_solve.
  - decide (exp_eval AE e = Some val_false); decide (exp_eval AE e = Some val_true).
    + unfold val_false, val_true in *. congruence.
    + edestruct IHs2; try dec_solve.
      left; econstructor; intros. rewrite e0 in H; congruence. eauto.
    + edestruct IHs1; try dec_solve.
      left; econstructor; intros. eauto.  rewrite e0 in H; congruence.
    + edestruct IHs1; edestruct IHs2; try dec_solve.
  - destruct (get_dec ZL (counted l)) as [[]|]; try dec_solve.
    decide (length x = length Y); try dec_solve.
    decide (PIR2 le_precise (lookup_list AE x) (List.map (exp_eval AE) Y));
      try dec_solve.
  - edestruct (IHs1 AE (Z::ZL)); edestruct (IHs2 AE (Z::ZL)); try dec_solve.
Defined.

Definition cp_eqn E x :=
  match E x with
    | Some c => {{(Var x, Con c)}}
    | _ => ∅
  end.

Definition cp_eqns (E:onv aval) (lv:set var) : eqns :=
  fold union (map (cp_eqn E) lv) ∅.

Instance cp_eqns_morphism_equal E
: Proper (Equal ==> Equal) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_subset E
: Proper (Subset ==> Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_flip_subset E
: Proper (flip Subset ==> flip Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite <- H. reflexivity.
Qed.

Lemma cp_eqns_union E lv lv'
: cp_eqns E (lv ∪ lv') [=] cp_eqns E lv ∪ cp_eqns E lv'.
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite map_app.
  rewrite fold_union_app. reflexivity.
  intuition.
Qed.

Lemma entails_monotonic_add Gamma Γ' gamma
: entails Gamma Γ' -> entails (gamma ∪ Gamma) Γ'.
Proof.
  unfold entails; intros; dcr.
  - hnf; intros. eapply H. hnf; intros. eapply H0. cset_tac; intuition. eauto.
Qed.

Lemma map_agree X `{OrderedType X} Y `{OrderedType Y}
      lv (f:X->Y) `{Proper _ (_eq ==> _eq) f} (g:X->Y) `{Proper _ (_eq ==> _eq) g}
: agree_on _eq lv f g
  -> map f lv [=] map g lv.
Proof.
  intros. intro.
  repeat rewrite map_iff; eauto.
  split; intros []; intros; dcr; eexists x; split; eauto.
  + specialize (H3 x H5). rewrite <- H3; eauto.
  + specialize (H3 x H5). rewrite H3; eauto.
Qed.

Lemma cp_eqn_agree lv E E'
: agree_on eq lv E E'
-> agree_on _eq lv (cp_eqn E) (cp_eqn E').
Proof.
  unfold agree_on, cp_eqn; intros.
  rewrite H; eauto.
Qed.

Lemma cp_eqns_agree lv E E'
: agree_on eq lv E E'
  -> cp_eqns E lv [=] cp_eqns E' lv.
Proof.
  intros. hnf; intro. unfold cp_eqns.
  rewrite map_agree; eauto using cp_eqn_agree. reflexivity.
  intuition. intuition.
Qed.

Inductive same_shape (A B:Type) : ann B -> ann A -> Prop :=
| SameShape0 a b
  : same_shape (ann0 a) (ann0 b)
| SameShape1 a b an bn
  : same_shape an bn
    -> same_shape (ann1 a an) (ann1 b bn)
| SameShape2 a b an bn an' bn'
  : same_shape an bn
    -> same_shape an' bn'
    -> same_shape (ann2 a an an') (ann2 b bn bn').


Fixpoint zip2Ann X Y Z (f:X->Y->Z) (a:ann X) (b:ann Y) z : ann Z :=
  match a, b with
    | ann1 a an, ann1 a' an' => ann1 (f a a') (zip2Ann f an an' z)
    | ann2 a an1 an2, ann2 a' an1' an2' => ann2 (f a a')
                                               (zip2Ann f an1 an1' z)
                                               (zip2Ann f an2 an2' z)
    | ann0 a, ann0 b => ann0 (f a b)
    | _, _ => z
  end.

(*
Lemma zip2Ann_get X Y Z f a b
: getAnn (zip2Ann f a b) = f (getAnn a) (getAnn b).
*)

Definition cp_eqns_ann (a:ann (onv aval)) (b:ann (set var)) : ann eqns :=
  zip2Ann cp_eqns a b (ann0 ∅).

Definition cp_choose_exp E e :=
  match exp_eval E e with
    | Some c => Con c
    | _ => e
  end.


Fixpoint cp_choose (AE:onv aval) s : ann args :=
  match s with
    | stmtExp x e s =>
      ann1 (cp_choose_exp AE e::nil) (cp_choose AE s)
    | stmtIf e s t =>
        ann2 (cp_choose_exp AE e::nil) (cp_choose AE s) (cp_choose AE t)
    | stmtGoto f Y =>
      ann0 (List.map (cp_choose_exp AE) Y)
    | stmtReturn e => ann0 (cp_choose_exp AE e::nil)
    | stmtLet Z s t =>
      ann2 nil (cp_choose AE s) (cp_choose AE t)
    | _ => ann0 nil
  end.

Lemma zip2Ann_get X Y Z (f:X->Y->Z) a b z
:
  same_shape a b
  -> getAnn (zip2Ann f a b z) = f (getAnn a) (getAnn b).
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma in_or_not X `{OrderedType X} x s
:   { x ∈ s /\ s [=] s \ {{x}} ∪ {{x}} }
  + { x ∉ s /\ s [=] s \ {{x}} }.
Proof.
  decide (x ∈ s); [left|right]; split; eauto.
  - cset_tac; intuition. decide (_eq a x); eauto.
    rewrite H1; eauto.
  - cset_tac; intuition. intro. rewrite H1 in H0; eauto.
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
  + intros. cset_tac. destruct H1; eauto.
Qed.

Instance option_R_trans `{Transitive} : Transitive (option_R R).
Proof.
  hnf; intros. inv H0; inv H1. econstructor; eauto.
Qed.

Lemma in_cp_eqns AE x lv v
  : x \In lv
    -> AE x = ⎣v ⎦
    -> (Var x, Con v) ∈ cp_eqns AE lv.
Proof.
  intros. unfold cp_eqns.
  eapply fold_union_incl.
  instantiate (1:={{ (Var x, Con v) }}). cset_tac; intuition.
  assert (cp_eqn AE x = {{ (Var x, Con v) }}).
  unfold cp_eqn. rewrite H0. reflexivity.
  rewrite <- H1. eapply map_1; eauto.
  intuition.
Qed.

Lemma cp_eqns_satisfies_env AE E x v lv
: x ∈ lv
  -> AE x = ⎣v ⎦
  -> satisfiesAll E (cp_eqns AE lv)
  -> E x = ⎣v ⎦.
Proof.
  intros. exploit H1; eauto.
  instantiate (1:=(Var x, Con v)).
  eapply in_cp_eqns; eauto.
  hnf in X; simpl in *. inv X; eauto.
Qed.

Lemma exp_eval_same e lv AE E v
:   Exp.freeVars e ⊆ lv
    -> exp_eval AE e = ⎣v ⎦
    -> satisfiesAll E (cp_eqns AE lv)
    -> exists v', Exp.exp_eval E e = Some v' /\ option_eq eq ⎣v' ⎦ ⎣v ⎦.
Proof.
  intros. general induction e; simpl in * |- *; eauto 20 using @option_eq.
  - exploit cp_eqns_satisfies_env; eauto.
    + rewrite <- H. cset_tac; eauto.
    + rewrite H0.
      eexists v0; split; eauto using @option_eq.
  - monad_inv H0.
    edestruct IHe1; eauto. cset_tac; intuition.
    edestruct IHe2; eauto. cset_tac; intuition.
    dcr.
    rewrite H3, H2, EQ, EQ1; simpl.
    inv H4; inv H5.
    rewrite EQ2.
    eexists v; split; eauto using @option_eq.
Qed.

Lemma exp_eval_entails AE e v x lv
: Exp.freeVars e ⊆ lv
  -> exp_eval AE e = ⎣v ⎦
  -> entails ({{ (Var x, e) }} ∪ {{ (Var x, cp_choose_exp AE e) }} ∪ cp_eqns AE lv) {{(Var x, Con v)}}.
Proof.
  intros.
  unfold entails; intros. unfold satisfiesAll, satisfies; intros.
  exploit (H1 (Var x, e)); eauto.
  cset_tac; intuition. cset_tac. invc H2; simpl in *; subst; simpl.
  eapply satisfiesAll_union in H1; dcr.
  edestruct exp_eval_same; try eapply H2; eauto; dcr.
  inv X.
  - congruence.
  - econstructor. inv H5; congruence.
Qed.

Lemma cp_eqns_single AE x
: cp_eqns AE {{ x }} [=] cp_eqn AE x.
Proof.
  unfold cp_eqns.
  rewrite map_single; [| intuition].
  erewrite fold_single; eauto.
  cset_tac; intuition.
  eapply Equal_ST.
  eapply union_m.
  eapply transpose_union.
Qed.

Lemma cp_choose_moreDefined AE e lv
: Exp.freeVars e ⊆ lv
  -> moreDefined (cp_eqns AE lv) e (cp_choose_exp AE e).
Proof.
  unfold cp_choose_exp. case_eq (exp_eval AE e); intros.
  - hnf; intros.
      case_eq (Exp.exp_eval E e); intros.
      * edestruct exp_eval_same; try eapply H1; eauto; dcr.
        simpl. inv H5. econstructor. congruence.
      * econstructor.
  - reflexivity.
Qed.

Lemma cp_choose_moreDefinedArgs AE Y lv
: list_union (List.map Exp.freeVars Y) ⊆ lv
  -> moreDefinedArgs (cp_eqns AE lv) Y
                    (List.map (cp_choose_exp AE) Y).
Proof.
  intros. general induction Y; simpl.
  - econstructor; eauto.
  - hnf; intros; simpl.
    unfold cp_choose_exp at 1.
    case_eq (exp_eval AE a); intros.
    + case_eq (Exp.exp_eval E a); intros.
      * simpl.
        exploit (IHY AE lv); eauto using get.
        eapply list_union_incl; intros.
        rewrite <- H. edestruct map_get_4; eauto; dcr; subst.
        eapply get_list_union_map; eauto using get.
        eapply incl_empty.
        exploit X; eauto. inv X0; simpl.
        econstructor.
        exploit (get_list_union_map _ _ Exp.freeVars (a::Y)).
        econstructor. rewrite H in X1.
        edestruct exp_eval_same; try eapply H1; eauto using get; dcr.
        edestruct exp_eval_same; try eapply H1; try eapply H3; eauto using get; dcr.
        inv H8; inv H9.
        econstructor; eauto. congruence.
      * simpl. econstructor.
    + case_eq (Exp.exp_eval E a); intros; simpl; try econstructor; eauto.
      exploit (IHY AE lv); eauto using get.
      eapply list_union_incl; intros.
      rewrite <- H. edestruct map_get_4; eauto; dcr; subst.
      eapply get_list_union_map; eauto using get.
      eapply incl_empty.
      exploit X; eauto. inv X0; simpl.
      * econstructor.
      * econstructor; eauto.
Qed.


Lemma cp_choose_exp_freeVars AE e D
: Exp.freeVars e ⊆ D
  -> Exp.freeVars (cp_choose_exp AE e) ⊆ D.
Proof.
  intros.
  unfold cp_choose_exp. case_eq (exp_eval AE e); intros; eauto using incl_empty.
Qed.

Lemma cp_choose_exp_live_sound_exp AE e lv
:  Exp.freeVars e ⊆ lv
   -> Exp.freeVars (cp_choose_exp AE e) ⊆ lv.
Proof.
  intros. unfold cp_choose_exp.
  destruct (exp_eval AE e); intros; eauto.
  simpl; eapply incl_empty.
Qed.

Lemma cp_choose_exp_eval_exp AE e v
: exp_eval AE e = ⎣v ⎦
  -> exp_eval AE (cp_choose_exp AE e) = ⎣v ⎦.
Proof.
  intros. unfold cp_choose_exp. rewrite H; eauto.
Qed.

Lemma update_with_list_lookup_in_list B E
      (Z:list var) (Y:list B) z
: length Z = length Y
  -> z ∈ of_list Z
  -> exists n y, get Z n z /\ get Y n y /\ E [Z <-- Y] z = y.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in *; isabsurd.
  decide (z = x); subst.
  exists 0, y; repeat split; eauto using get. lud. intuition.
  edestruct (IHlength_eq E z) as [? [? ]]; eauto; dcr.
  cset_tac; intuition. lud; intuition.
  do 2 eexists; repeat split; eauto using get.
Qed.


Lemma subst_eqns_in gamma ϱ Gamma
: gamma \In subst_eqns ϱ Gamma
  -> exists γ', γ' ∈ Gamma /\ gamma = subst_eqn ϱ γ'.
Proof.
  intros. unfold subst_eqns in H.
  eapply map_iff in H; eauto using subst_eqn_Proper.
  destruct H; dcr. eexists x; split; eauto.
  inv H1. hnf in *. subst.
  destruct x; simpl. reflexivity.
Qed.

Lemma cp_eqns_in gamma AE lv
: gamma \In cp_eqns AE lv
  -> exists x, x ∈ lv /\ gamma ∈ cp_eqn AE x.
Proof.
  intros. unfold cp_eqns in H.
  eapply incl_fold_union in H.
  destruct H; isabsurd.
  destruct H; dcr.
  eapply map_iff in H0. destruct H0; dcr.
  eexists x0; split; eauto. rewrite <- H2; eauto.
  intuition.
Qed.

Lemma lookup_list_get (AE:onv aval) Z n x z
: get (lookup_list AE Z) n x
  -> get Z n z
  -> x = AE z.
Proof.
  intros. general induction H0; simpl in *; inv H; eauto.
Qed.

Lemma cp_eqns_freeVars AE lv
: eqns_freeVars (cp_eqns AE lv) ⊆ lv.
Proof.
  hnf; intros.
  eapply incl_fold_union in H; destruct H; isabsurd.
  destruct H; dcr.
  eapply map_iff in H0; destruct H0; dcr; intuition.
  eapply cp_eqns_in in H0. destruct H0; dcr.
  eapply H2 in H1.
  unfold cp_eqn in H3.
  case_eq (AE x1); intros. rewrite H in H3. cset_tac.
  hnf in H3. inv H3; hnf in *; subst. simpl in *.
  cset_tac; intuition. rewrite <- H4. eauto.
  rewrite H in H3. isabsurd.
Qed.

Lemma in_subst_eqns gamma Z Y AE
: length Z = length Y
  -> gamma \In subst_eqns (sid [Z <-- Y]) (cp_eqns AE (of_list Z))
  -> exists n x c,
      gamma = subst_eqn (sid [Z <-- Y]) (Var x, Con c)
      /\ AE x = Some c
      /\ get Z n x
      /\ get Y n ((sid [Z <-- Y]) x).
Proof.
  intros.
  edestruct subst_eqns_in as [γ' ?]; eauto; dcr; subst.
  edestruct cp_eqns_in as [x ?]; eauto; dcr.
  unfold cp_eqn in H4. case_eq (AE x); intros.
  - cset_tac. assert (γ' = (Var x, Con a)).
    destruct γ'. rewrite H1 in H4. cset_tac. inv H4.
    hnf in H8, H10. subst. eauto.
    subst. unfold subst_eqn; simpl.
    edestruct (update_with_list_lookup_in_list sid Z Y) as [? [? ]]; eauto; dcr.
    subst.
    do 2 eexists; eauto.
  - exfalso. rewrite H1 in H4; isabsurd.
Qed.

Lemma entails_cp_eqns_subst AE D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE Z) (List.map (exp_eval AE) Y)
  -> list_union (List.map Exp.freeVars Y)[<=]D
  -> entails (cp_eqns AE D)
            (subst_eqns (sid [Z <-- Y]) (cp_eqns AE (of_list Z))).
Proof.
  intros LEQ le_prec INCL.
  hnf. intros. hnf. intros.

  edestruct in_subst_eqns as [? [? []]]; eauto; dcr.
  edestruct PIR2_nth_2; eauto. eapply map_get_1; eauto. dcr.
  exploit lookup_list_get; eauto. subst.
  inversion H7; try congruence.
  edestruct exp_eval_same; eauto; dcr.
  rewrite <- INCL.
  eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
  hnf; simpl. rewrite H9.
  econstructor. inv H10. congruence.
Qed.


Lemma entails_cp_eqns_subst_choose AE D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE Z) (List.map (exp_eval AE) Y)
  -> list_union (List.map Exp.freeVars Y)[<=]D
  -> entails (cp_eqns AE D)
            (subst_eqns (sid [Z <-- List.map (cp_choose_exp AE) Y]) (cp_eqns AE (of_list Z))).
Proof.
  intros LEQ le_prec INCL.
  hnf. intros. hnf. intros.

  edestruct in_subst_eqns as [? [? []]]; try eapply H0; eauto; dcr.
  rewrite map_length; eauto.
  edestruct map_get_4; eauto; dcr.
  edestruct PIR2_nth_2; eauto. eapply map_get_1; eauto. dcr.
  exploit lookup_list_get; eauto. subst.
  inversion H9; try congruence.
  edestruct exp_eval_same; eauto; dcr.
  rewrite <- INCL.
  eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
  hnf; simpl.
  rewrite <- H5. unfold cp_choose_exp. rewrite <- H10. simpl.
  constructor. inv H12. congruence.
Qed.

Lemma cp_sound_eqn AE Cp Es s (ang:ann (set var * set var))
: let Gamma := (cp_eqns AE (fst (getAnn ang))) in
cp_sound AE Cp s
-> ssa s ang
-> labelsDefined s Es
-> (forall n a Z, get Es n a
              -> get Cp n Z
              -> snd a [=] cp_eqns AE (of_list Z)
                /\ (fst (fst (fst a))) = Z)
-> eqn_sound Es s Gamma ang (cp_choose AE s).
Proof.
  intro. subst Gamma.
  intros CP SSA LD LINV.
  general induction CP; invt ssa; invt labelsDefined; simpl.
  - econstructor.
    eapply eqn_sound_entails_monotone; eauto.
    + rewrite H7; simpl. rewrite cp_eqns_union.
      eapply entails_union; split.
      eapply entails_monotonic_add. reflexivity.

      rewrite cp_eqns_single.
      unfold cp_eqn. case_eq (AE x); intros; eauto using entails_empty.
      eapply exp_eval_entails; eauto. congruence.
    + eapply cp_choose_moreDefined; eauto.
    + eapply cp_choose_exp_freeVars; eauto.
  - econstructor; intros; eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply H0; eauto. intro.
      edestruct H3; dcr.
      eapply H16. hnf; simpl.
      edestruct exp_eval_same; eauto; dcr.
      rewrite H17. eauto.
      * rewrite H12; eauto; reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply H2; eauto. intro.
      exfalso. edestruct H3; dcr.
      eapply H16. hnf; simpl.
      edestruct exp_eval_same; eauto; dcr.
      rewrite H17. eauto.
      * rewrite H13; eauto; reflexivity.
    + eapply cp_choose_moreDefined; eauto.
  - destruct a as [[[Zb G] Γf] EqS].
    exploit LINV; eauto; dcr; simpl in *. subst Zb.
    econstructor; eauto.
    + rewrite map_length; eauto.
    + rewrite H2.
      eapply entails_cp_eqns_subst; eauto.
    + eapply cp_choose_moreDefinedArgs; eauto.
  - econstructor; eauto using cp_choose_moreDefined.
  - eapply EqnLet with (Γ2:=cp_eqns AE D) (EqS:=cp_eqns AE (of_list Z)).
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHCP1; eauto.
      * eapply labelsDefined_any; try eapply H10; eauto.
      * intros; simpl.
        inv H; inv H0; simpl.
        split. reflexivity. reflexivity.
        eapply LINV; eauto.
      * rewrite H6. simpl.
        rewrite cp_eqns_union. reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHCP2; eauto.
      * eapply labelsDefined_any; try eapply H11; eauto.
      * intros; simpl.
        inv H; inv H0; simpl.
        split. reflexivity. reflexivity.
        eapply LINV; eauto.
      * rewrite H9; reflexivity.
    + rewrite cp_eqns_freeVars. eapply incl_right.
    + rewrite cp_eqns_freeVars. reflexivity.
    + reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
