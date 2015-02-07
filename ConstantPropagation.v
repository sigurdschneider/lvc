Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL Sim Fresh Annotation MoreExp Coherence LabelsDefined DecSolve.

Require Import RenamedApart Filter SetOperations Eqn ValueOpts Lattice.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)


(* None is top *)
Definition aval := withTop val.

Fixpoint exp_eval (E:onv aval) (e:exp) : aval :=
  match e with
    | Con v => wTA v
    | Var x => match E x with
                | Some v => v
                | None => Top
              end
    | UnOp o e => match exp_eval E e with
                   | Top => Top
                   | wTA v => match Exp.unop_eval o v with
                               | Some v => wTA v
                               | None => Top
                             end
                 end
    | BinOp o e1 e2 =>
       match exp_eval E e1 with
                   | Top => Top
                   | wTA v1 =>
                     match exp_eval E e2 with
                       | Top => Top
                       | wTA v2 =>
                         match Exp.binop_eval o v1 v2 with
                           | Some v => wTA v
                           | None => Top
                         end
                     end
       end

  end.

Inductive le_precise : option aval -> option aval -> Prop :=
  | leTop x : le_precise (Some Top) x
  | leValVal y : le_precise (Some (wTA y)) (Some (wTA y))
  | leBot  : le_precise None None.

Instance le_precise_computable a b : Computable (le_precise a b).
destruct a, b; try dec_solve.
destruct a, a0; try dec_solve.
decide (a = a0); subst; try dec_solve.
destruct a; try dec_solve.
Defined.

Inductive isEqCmp : exp -> Prop :=
  IisEqCmp x c : isEqCmp (BinOp 3 (Var x) (Con c)).

Instance isEqCmp_dec e : Computable (isEqCmp e).
Proof.
  destruct e; try dec_solve.
  destruct e1, e2; decide (b = 3); subst; try dec_solve.
Defined.

Definition getEqCmpVar (e:exp) :=
  match e with
    | BinOp 3 (Var x) (Con c) => x
    | _ => 0
  end.

Definition getEqCmpCon (e:exp) :=
  match e with
    | BinOp 3 (Var x) (Con c) => c
    | _ => 0
  end.

Definition update_cond (AE:onv aval) (e:exp) (v:bool) :=
  match v with
    | false =>
      if [ isVar e ] then
        AE [getVar e <- Some (wTA 0)]
      else
        AE
    | true =>
      if [ isEqCmp e ] then
        AE [getEqCmpVar e <- Some (wTA (getEqCmpCon e))]
      else
        AE
  end.

Definition aval2bool (v:aval) :=
  match v with
    | wTA v => Some (val2bool v)
    | Top => None
  end.

Lemma oval2bool_some v b
: aval2bool v = Some b ->
  exists v', v = wTA v' /\ val2bool v' = b.
Proof.
  destruct v; simpl; intros; inv H; eauto.
Qed.

Inductive cp_sound : onv aval
                     -> list (params*list (option aval))
                     -> stmt
                     -> Prop :=
| CPOpr AE (x:var) Cp b e
  : cp_sound AE Cp b
    -> Some (exp_eval AE e) = AE x
    -> cp_sound AE Cp (stmtExp x e b)
| CPIf AE Cp e b1 b2
  : (* these conditions make it conditional constant propagation *)
    (aval2bool (exp_eval AE e) <> (Some false) -> cp_sound (update_cond AE e true) Cp b1)
    -> (aval2bool (exp_eval AE e) <> (Some true) -> cp_sound (update_cond AE e false) Cp b2)
    -> cp_sound AE Cp (stmtIf e b1 b2)
| CPGoto AE l Y Cp Z aY
  : get Cp (counted l) (Z,aY)
    -> length Z = length Y
    -> PIR2 le_precise aY (List.map (exp_eval AE ∘ Some) Y)
    -> cp_sound AE Cp (stmtGoto l Y)
| CPReturn AE Cp e
  : cp_sound AE Cp (stmtReturn e)
| CPLet AE Cp s Z b
  : cp_sound AE ((Z,lookup_list AE Z)::Cp) s
  -> cp_sound AE ((Z,lookup_list AE Z)::Cp) b
  -> cp_sound AE Cp (stmtLet Z s b).

Instance cp_sound_dec AE ZL s : Computable (cp_sound AE ZL s).
Proof.
  hnf. general induction s; try dec_solve.
  - edestruct IHs; decide (Some (exp_eval AE e) = AE x); dec_solve.
  - decide (aval2bool (exp_eval AE e) = Some false);
    decide (aval2bool (exp_eval AE e) = Some true).
    + unfold val_false, val_true in *. congruence.
    + edestruct IHs2; try dec_solve.
      left; econstructor; intros. rewrite e0 in H; congruence. eauto.
    + edestruct IHs1; try dec_solve.
      left; econstructor; intros. eauto.  rewrite e0 in H; congruence.
    + edestruct IHs1; edestruct IHs2; try dec_solve.
  - destruct (get_dec ZL (counted l)) as [[[]]|]; try dec_solve.
    decide (length l0 = length Y); try dec_solve.
    decide (PIR2 le_precise l1 (List.map (exp_eval AE ∘ Some) Y));
      try dec_solve.
  - edestruct (IHs1 AE ((Z,lookup_list AE Z)::ZL));
    edestruct (IHs2 AE ((Z,lookup_list AE Z)::ZL)); try dec_solve.
Defined.

Definition cp_eqn (E:onv aval) x :=
  match E x with
    | Some (wTA c) => singleton (EqnEq (Var x) (Con c))
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

Lemma cp_eqns_add E x lv
: cp_eqns E ({x; lv}) [=] cp_eqn E x ∪ cp_eqns E lv.
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite map_add.
  rewrite fold_union_add. reflexivity.
  intuition.
Qed.

Lemma cp_eqns_union E lv lv'
: cp_eqns E (lv ∪ lv') [=] cp_eqns E lv ∪ cp_eqns E lv'.
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite map_app.
  rewrite fold_union_app. reflexivity.
  intuition.
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
    | wTA c => Con c
    | _ => e
  end.


Fixpoint constantPropagate (AE:onv aval) s : stmt :=
  match s with
    | stmtExp x e s =>
      stmtExp x (cp_choose_exp AE e) (constantPropagate AE s)
    | stmtIf e s t =>
      stmtIf (cp_choose_exp AE e)
             (constantPropagate (update_cond AE e true) s)
             (constantPropagate (update_cond AE e false) t)
    | stmtGoto f Y =>
      stmtGoto f (List.map (cp_choose_exp AE) Y)
    | stmtReturn e => stmtReturn (cp_choose_exp AE e)
    | stmtExtern x f Y s =>
      stmtExtern x f (List.map (cp_choose_exp AE) Y)
                 (constantPropagate AE s)
    | stmtLet Z s t =>
      stmtLet Z (constantPropagate AE s) (constantPropagate AE t)
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
    rewrite <- H1; eauto.
  - cset_tac; intuition.
Qed.

Lemma in_cp_eqns AE x lv v
  : x \In lv
    -> AE x = ⎣wTA v ⎦
    -> EqnEq (Var x) (Con v) ∈ cp_eqns AE lv.
Proof.
  intros. unfold cp_eqns.
  eapply fold_union_incl.
  instantiate (1:=singleton (EqnEq (Var x) (Con v))).
  cset_tac; intuition.
  assert (cp_eqn AE x = singleton (EqnEq (Var x) (Con v))).
  unfold cp_eqn. rewrite H0. reflexivity.
  rewrite <- H1. eapply map_1; eauto.
  intuition.
Qed.

Lemma cp_eqns_satisfies_env AE E x v lv
: x ∈ lv
  -> AE x = ⎣wTA v ⎦
  -> satisfiesAll E (cp_eqns AE lv)
  -> E x = ⎣v ⎦.
Proof.
  intros. exploit H1; eauto.
  instantiate (1:=EqnEq (Var x) (Con v)).
  eapply in_cp_eqns; eauto.
  hnf in X; simpl in *. inv X; eauto.
Qed.

Ltac smatch :=
  match goal with
    | [ H : match ?x with
                _ => _
            end = ?y,
            H' : ?x = _ |- _ ] => rewrite H' in H; simpl in H
  end.

Ltac dmatch :=
  match goal with
    | [ H : match ?x with
                _ => _
            end = ?y |- _ ] => case_eq x; intros
  end.

Ltac imatch := dmatch; smatch; isabsurd.

Lemma exp_eval_same e lv AE E v
:   Exp.freeVars e ⊆ lv
    -> exp_eval AE e = wTA v
    -> satisfiesAll E (cp_eqns AE lv)
    -> exists v', Exp.exp_eval E e = Some v' /\ option_eq eq ⎣v' ⎦ ⎣v ⎦.
Proof.
  intros. general induction e; simpl in * |- *; eauto 20 using @option_eq.
  - exploit cp_eqns_satisfies_env; eauto.
    + rewrite <- H. cset_tac; eauto.
    + destruct (AE v). f_equal; eauto. congruence.
    + eexists v0; eauto using @option_eq.
  - repeat imatch.
    edestruct IHe; eauto; dcr.
    rewrite H5; simpl.
    inv H6. inv H0.
    eexists; split; eauto using @option_eq.
  - repeat imatch.
    edestruct IHe1; eauto. cset_tac; intuition.
    edestruct IHe2; eauto. cset_tac; intuition.
    dcr.
    rewrite H6, H7; simpl.
    inv H8; inv H9.
    inv H0.
    eexists v; split; eauto using @option_eq.
Qed.

Lemma exp_eval_entails AE e v x lv
: Exp.freeVars e ⊆ lv
  -> exp_eval AE e = wTA v
  -> entails ({EqnEq (Var x) e ; { EqnEq (Var x) (cp_choose_exp AE e) ;
                                     cp_eqns AE lv } }) (singleton (EqnEq (Var x) (Con v))).
Proof.
  intros.
  unfold entails; intros. unfold satisfiesAll; intros.
  exploit (H1 (EqnEq (Var x) e)); eauto.
  cset_tac; intuition. cset_tac. invc H2; simpl in *; subst; simpl.
  eapply satisfiesAll_add in H1; dcr.
  eapply satisfiesAll_add in H3; dcr.
  edestruct exp_eval_same; try eapply H0; eauto; dcr.
  unfold cp_choose_exp in *; simpl in *.
  rewrite H0 in H1. eauto.
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


Lemma cp_choose_approx AE e lv
: Exp.freeVars e ⊆ lv
  -> entails (cp_eqns AE lv) {EqnApx e (cp_choose_exp AE e)}.
Proof.
  unfold cp_choose_exp. case_eq (exp_eval AE e); intros.
  - eapply entails_eqns_apx_refl.
  - hnf; intros.
    case_eq (Exp.exp_eval E e); intros; simpl.
    + edestruct exp_eval_same; try eapply H1; eauto; dcr.
      hnf; intros. cset_tac. rewrite <- H3; simpl.
      rewrite H4. inv H5. reflexivity.
    + edestruct exp_eval_same; try eapply H1; eauto; dcr. congruence.
Qed.

Lemma cp_choose_approx_list AE Y lv
: list_union (List.map Exp.freeVars Y) ⊆ lv
  ->  entails (cp_eqns AE lv) (list_EqnApx Y (List.map (cp_choose_exp AE) Y)).
Proof.
  intros. general induction Y; simpl.
  - unfold list_EqnApx. simpl. eapply entails_empty.
  - unfold list_EqnApx. simpl. eapply entails_add_single.
    eapply IHY.
    eapply list_union_incl; intros.
    rewrite <- H. edestruct map_get_4; eauto; dcr; subst.
    eapply get_list_union_map; eauto using get. cset_tac; intuition.
    eapply cp_choose_approx.
    rewrite <- H.
    eapply get_list_union_map; eauto using get.
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
: exp_eval AE e = wTA v
  -> exp_eval AE (cp_choose_exp AE e) = wTA v.
Proof.
  intros. unfold cp_choose_exp. rewrite H; eauto.
Qed.

Lemma subst_eqns_in gamma ϱ Gamma
: gamma \In subst_eqns ϱ Gamma
  -> exists γ', γ' ∈ Gamma /\ gamma = subst_eqn ϱ γ'.
Proof.
  intros. unfold subst_eqns in H.
  eapply map_iff in H; eauto using subst_eqn_Proper.
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
  case_eq (AE x1); intros.
  - rewrite H in H3.
    destruct a0.
    + isabsurd.
    + cset_tac. hnf in H3; subst; simpl in *.
      cset_tac; intuition.
  - rewrite H in H3. isabsurd.
Qed.

Lemma in_subst_eqns gamma Z Y AE
: length Z = length Y
  -> gamma \In subst_eqns (sid [Z <-- Y]) (cp_eqns AE (of_list Z))
  -> exists n x c,
      gamma = subst_eqn (sid [Z <-- Y]) (EqnEq (Var x) (Con c))
      /\ AE x = Some (wTA c)
      /\ get Z n x
      /\ get Y n ((sid [Z <-- Y]) x).
Proof.
  intros.
  edestruct subst_eqns_in as [γ' ?]; eauto; dcr; subst.
  edestruct cp_eqns_in as [x ?]; eauto; dcr.
  unfold cp_eqn in H4. case_eq (AE x); intros.
  - rewrite H1 in H4. destruct a; isabsurd.
    cset_tac. invc H4.
    unfold subst_eqn; simpl.
    edestruct (update_with_list_lookup_in_list sid Z Y) as [? [? ]]; eauto; dcr.
    invc H9. invc H7.
    eexists x0, x2, a; repeat split; eauto.
  - exfalso. rewrite H1 in H4; isabsurd.
Qed.

Lemma entails_cp_eqns_subst AE D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE Z) (List.map (exp_eval AE ∘ Some) Y)
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
  simpl. rewrite H9.
  econstructor. inv H10. congruence.
Qed.


Lemma entails_cp_eqns_subst_choose AE AE' D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE' Z) (List.map (exp_eval AE ∘ Some) Y)
  -> list_union (List.map Exp.freeVars Y)[<=]D
  -> entails (cp_eqns AE D)
            (subst_eqns (sid [Z <-- List.map (cp_choose_exp AE) Y]) (cp_eqns AE' (of_list Z))).
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

Lemma cp_eqns_update D x c AE
: x ∈ D
  -> cp_eqns (AE [x <- ⎣ wTA c ⎦]) D [=] singleton (EqnEq (Var x) (Con c)) ∪ cp_eqns AE (D \ {{x}}).
Proof.
  intros.
  assert (D [=] {{x}} ∪ (D \ {{x}})). {
    cset_tac; intuition. decide (a = x); subst; intuition. inv H2; eauto.
  }
  rewrite H0 at 1. rewrite cp_eqns_union. rewrite cp_eqns_single.
  unfold cp_eqn. lud; isabsurd.
  rewrite cp_eqns_agree. reflexivity.
  hnf; intros. lud. inv e0; subst. exfalso; cset_tac; intuition.
Qed.


Lemma cp_sound_eqn AE Cp Es s (ang:ann (set var * set var))
: let Gamma := (cp_eqns AE (fst (getAnn ang))) in
cp_sound AE Cp s
-> renamedApart s ang
-> labelsDefined s (length Es)
-> (forall n a aY Z, get Es n a
              -> get Cp n (Z,aY)
              -> (exists AE', aY = lookup_list AE' Z
                       /\ snd a [=] cp_eqns AE' (of_list Z))
                /\ (fst (fst (fst a))) = Z)
-> eqn_sound Es s (constantPropagate AE s) Gamma ang.
Proof.
  intro. subst Gamma.
  intros CP SSA LD LINV.
  general induction CP; invt renamedApart; invt labelsDefined; simpl.
  - econstructor.
    eapply eqn_sound_entails_monotone; eauto.
    + rewrite H7; simpl. rewrite cp_eqns_add.
      eapply entails_union; split.
      unfold cp_eqn. case_eq (AE x); intros; eauto using entails_empty.
      rewrite H0 in H.
      destruct a; eauto using entails_empty.
      eapply exp_eval_entails; eauto. congruence.
      eapply entails_monotone. reflexivity.
      cset_tac; intuition.
    + eapply cp_choose_approx; eauto.
    + eapply cp_choose_exp_freeVars; eauto.
  - econstructor; intros; eauto.
    + {
        decide (aval2bool (exp_eval AE e) = Some false).
        - eapply EqnUnsat.
          hnf. intros. intro.
          exploit H3. cset_tac. left. reflexivity.
          hnf in X. simpl in *.
          case_eq (exp_eval AE e); intros.
          + rewrite H4 in e0; simpl in *; congruence.
          + edestruct exp_eval_same; eauto; dcr.
            hnf; intros. eapply H3. cset_tac. right; eauto.
            inv H16.
            rewrite H11 in X. rewrite H4 in e0. inv e0.
            simpl in *.
            unfold option_lift1, comp in X. rewrite H17 in X.
            inv X. isabsurd.
        - eapply eqn_sound_entails_monotone; eauto.
          rewrite H12; eauto. simpl.
          hnf. intros. destruct if.
          + inv i; simpl in *.
            rewrite cp_eqns_update.
            * eapply satisfiesAll_union; split.
              hnf; intros. cset_tac. invc H4.
              simpl.
              exploit H3. cset_tac. left; reflexivity.
              case_eq (E x); intros. simpl in *.
              rewrite H4 in X. simpl in *.
              unfold option_lift1, comp in X.
              destruct if in X; subst; try econstructor; eauto.
              simpl in *. inv X. inv H16.
              simpl in *. rewrite H4 in X. isabsurd.
              hnf; intros. eapply H3. cset_tac; right; eauto.
              eapply cp_eqns_morphism_subset; try eapply H4. eapply minus_incl.
            * revert H6; clear_all; intros; cset_tac; intuition.
          + hnf; intros. eapply H3. cset_tac; right; eauto.
      }
    + {
        decide (aval2bool (exp_eval AE e) = Some true).
        - eapply EqnUnsat.
          hnf. intros. intro.
          exploit H3. cset_tac. left; reflexivity.
          simpl in *.
          case_eq (exp_eval AE e); intros.
          + rewrite H4 in e0; simpl in *; congruence.
          + edestruct exp_eval_same; eauto; dcr.
            hnf; intros. eapply H3. cset_tac; right; eauto.
            rewrite H11 in X. inv H16.
            rewrite H4 in e0. simpl in *. inv e0.
            unfold option_lift1, comp in X. rewrite H17 in X.
            inv X. isabsurd.
        - eapply eqn_sound_entails_monotone; eauto.
          + rewrite H13; eauto. simpl.
            destruct if.
            * inv i; simpl in *.
              rewrite cp_eqns_update.
              hnf; intros.
              eapply satisfiesAll_union; split.
              hnf; intros. cset_tac. invc H4.
              simpl. exploit H3. cset_tac. left; reflexivity.
              simpl in *. case_eq (E v); intros.
              rewrite H4 in X. simpl in *.
              unfold option_lift1, comp in X.
              destruct v0; simpl in *. constructor; eauto. inv X; isabsurd.
              rewrite H4 in X. isabsurd.
              hnf; intros. eapply H3. cset_tac; right; eauto.
              eapply cp_eqns_morphism_subset; try eapply H4. eapply minus_incl.
              revert H6; clear_all; intros; cset_tac; intuition.
            * hnf; intros. hnf; intros. eapply H3. cset_tac; right; eauto.
      }
    + eapply cp_choose_approx; eauto.
  - edestruct get_in_range as [a ?]; eauto.
    destruct a as [[[Zb G] Γf] EqS].
    exploit LINV; eauto; dcr; simpl in *. subst Zb.
    econstructor; eauto.
    + rewrite map_length; eauto.
    + subst. rewrite H8.
      eapply entails_cp_eqns_subst_choose; eauto.
    + eapply cp_choose_approx_list; eauto.
  - econstructor; eauto using cp_choose_approx.
  - eapply EqnLet with (Γ2:=cp_eqns AE D) (EqS:=cp_eqns AE (of_list Z)).
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHCP1; eauto.
      * intros; simpl.
        inv H; inv H0; simpl; eauto.
        split. eexists; split; reflexivity. reflexivity.
      * rewrite H6. simpl.
        rewrite cp_eqns_union. reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHCP2; eauto.
      * intros; simpl.
        inv H; inv H0; simpl; eauto.
        split. eexists; split; reflexivity. reflexivity.
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
