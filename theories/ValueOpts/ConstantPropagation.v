Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env IL Sim Fresh Annotation Coherence LabelsDefined DecSolve.

Require Import RenamedApart SetOperations Eqn ValueOpts Infra.Lattice.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)


(* None is top *)
Definition aval := withTop val.

Fixpoint op_eval (E:onv aval) (e:op) : aval :=
  match e with
    | Con v => wTA v
    | Var x => match E x with
                | Some v => v
                | None => Top
              end
    | UnOp o e => match op_eval E e with
                   | Top => Top
                   | wTA v => match Val.unop_eval o v with
                               | Some v => wTA v
                               | None => Top
                             end
                 end
    | BinOp o e1 e2 =>
       match op_eval E e1 with
                   | Top => Top
                   | wTA v1 =>
                     match op_eval E e2 with
                       | Top => Top
                       | wTA v2 =>
                         match Val.binop_eval o v1 v2 with
                           | Some v => wTA v
                           | None => Top
                         end
                     end
       end

  end.

Definition exp_eval (E:onv aval) (e:exp) : aval :=
  match e with
  | Operation e => op_eval E e
  | _ => Top
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

Inductive isEqCmp : op -> Prop :=
  IisEqCmp x c : isEqCmp (BinOp BinOpEq (Var x) (Con c)).

Instance isEqCmp_dec e : Computable (isEqCmp e).
Proof.
  destruct e; try dec_solve.
  destruct e1, e2; decide (b = BinOpEq); subst; try dec_solve.
Defined.

Definition getEqCmpVar (e:op) :=
  match e with
    | BinOp BinOpEq (Var x) (Con c) => x
    | _ => 0
  end.

Definition getEqCmpCon (e:op) :=
  match e with
    | BinOp BinOpEq (Var x) (Con c) => c
    | _ => default_val
  end.

Definition update_cond (AE:onv aval) (e:op) (v:bool) :=
  match v with
    | false =>
      if [ isVar e ] then
        AE [getVar e <- Some (wTA default_val)]
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
    -> cp_sound AE Cp (stmtLet x e b)
| CPIf AE Cp e b1 b2
  : (* these conditions make it conditional constant propagation *)
    (aval2bool (op_eval AE e) <> (Some false) -> cp_sound (update_cond AE e true) Cp b1)
    -> (aval2bool (op_eval AE e) <> (Some true) -> cp_sound (update_cond AE e false) Cp b2)
    -> cp_sound AE Cp (stmtIf e b1 b2)
| CPGoto AE l Y Cp Z aY
  : get Cp (counted l) (Z,aY)
    -> length Z = length Y
    -> PIR2 le_precise aY (List.map (op_eval AE ∘ Some) Y)
    -> cp_sound AE Cp (stmtApp l Y)
| CPReturn AE Cp e
  : cp_sound AE Cp (stmtReturn e)
| CPLet AE Cp F t
  : (forall n Zs, get F n Zs
             -> cp_sound AE (List.map (fun Zs => (fst Zs,lookup_list AE (fst Zs))) F ++ Cp) (snd Zs))
    -> cp_sound AE (List.map (fun Zs => (fst Zs,lookup_list AE (fst Zs))) F ++ Cp) t
    -> cp_sound AE Cp (stmtFun F t).

Definition indexwise_R1 {A} (P:A->Prop) LA :=
forall n a, get LA n a -> P a.

Definition indexwise_R1_dec {A} {P:A->Prop} LA (Rdec:(forall n a, get LA n a -> Computable (P a)))
      : Computable (indexwise_R1 P LA).
unfold Computable. revert LA Rdec. fix 1. intros LA Rdec.
destruct LA; try now left; isabsurd.
intros. destruct (Rdec 0 a).
- eauto using get.
- destruct (indexwise_R1_dec LA); clear indexwise_R1_dec; eauto using get.
  + left. hnf; intros. inv H; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
Defined.

Instance cp_sound_dec AE ZL s : Computable (cp_sound AE ZL s).
Proof.
  hnf. revert AE ZL; sind s; intros; destruct s; try dec_solve.
  - edestruct (IH s); eauto; decide (Some (exp_eval AE e) = AE x); try dec_solve.
  - decide (aval2bool (op_eval AE e) = Some false);
    decide (aval2bool (op_eval AE e) = Some true).
    + unfold val_false, val_true in *. congruence.
    + edestruct (IH s2 ltac:(eauto) (update_cond AE e false) ZL); eauto; try dec_solve.
    + edestruct (IH s1 ltac:(eauto) (update_cond AE e true) ZL); eauto; dec_solve.
    + edestruct (IH s1 ltac:(eauto) (update_cond AE e true) ZL);
        edestruct (IH s2 ltac:(eauto) (update_cond AE e false) ZL); eauto; try dec_solve.
  - destruct (get_dec ZL (counted l)) as [[[]]|]; try dec_solve.
    decide (length l0 = length Y); try dec_solve.
    decide (PIR2 le_precise l1 (List.map (op_eval AE ∘ Some) Y));
      try dec_solve.
  - assert (SZ:size s < size (stmtFun F s)) by eauto.
    edestruct (IH s SZ AE (List.map (fun Zs => (fst Zs,lookup_list AE (fst Zs))) F ++ ZL)).
    exploit (@indexwise_R1_dec _ (fun Zs => cp_sound AE ((fun Zs0 : params * stmt => (fst Zs0, lookup_list AE (fst Zs0))) ⊝ F ++ ZL) (snd Zs)) F); eauto.
    intros. eapply IH; eauto. destruct H.
    dec_solve. dec_solve. dec_solve.
Defined.

Definition cp_eqn (E:onv aval) x :=
  match E x with
    | Some (wTA c) => singleton (EqnEq (Var x) (Con c))
    | _ => ∅
  end.

Instance cp_eqn_eq E
  : Proper (_eq ==> _eq) (cp_eqn E).
Proof.
  unfold Proper, respectful, cp_eqn; intros; subst.
  hnf in H; subst.
  cases; eauto.
Qed.

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
  setoid_rewrite map_agree; try eapply cp_eqn_eq; try reflexivity.
  eapply cp_eqn_agree. symmetry; eauto.
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

Definition cp_choose_op E e :=
  match op_eval E e with
    | wTA c => Con c
    | _ => e
  end.


Fixpoint constantPropagate (AE:onv aval) s {struct s} : stmt :=
  match s with
    | stmtLet x (Operation e) s =>
      stmtLet x (Operation (cp_choose_op AE e)) (constantPropagate AE s)
    | stmtLet x (Call f Y) s =>
      stmtLet x (Call f (List.map (cp_choose_op AE) Y))
              (constantPropagate AE s)
    | stmtIf e s t =>
      stmtIf (cp_choose_op AE e)
             (constantPropagate (update_cond AE e true) s)
             (constantPropagate (update_cond AE e false) t)
    | stmtApp f Y =>
      stmtApp f (List.map (cp_choose_op AE) Y)
    | stmtReturn e => stmtReturn (cp_choose_op AE e)
    | stmtFun F t =>
      stmtFun (List.map (fun Zs => (fst Zs, constantPropagate AE (snd Zs))) F)
              (constantPropagate AE t)
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
  - cset_tac.
  - cset_tac.
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
  intros. exploit H1 as SAT; eauto.
  instantiate (1:=EqnEq (Var x) (Con v)).
  eapply in_cp_eqns; eauto.
  hnf in SAT; simpl in *. inv SAT; eauto.
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

Lemma op_eval_same e lv AE E v
:   Op.freeVars e ⊆ lv
    -> op_eval AE e = wTA v
    -> satisfiesAll E (cp_eqns AE lv)
    -> exists v', Op.op_eval E e = Some v' /\ option_eq eq ⎣v' ⎦ ⎣v ⎦.
Proof.
  intros. general induction e; simpl in * |- *; eauto 20 using @option_eq.
  - exploit cp_eqns_satisfies_env; eauto.
    + rewrite <- H. cset_tac.
    + destruct (AE n). f_equal; eauto. congruence.
    + eexists v; eauto using @option_eq.
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

Lemma op_eval_entails AE e v x lv
: Op.freeVars e ⊆ lv
  -> op_eval AE e = wTA v
  -> entails ({EqnEq (Var x) e ; { EqnEq (Var x) (cp_choose_op AE e) ;
                                     cp_eqns AE lv } }) (singleton (EqnEq (Var x) (Con v))).
Proof.
  intros.
  unfold entails; intros. unfold satisfiesAll; intros.
  exploit (H1 (EqnEq (Var x) e)); eauto.
  - cset_tac.
  - cset_tac'.
    invc H2; simpl in *; subst; simpl.
    eapply satisfiesAll_add in H1; dcr.
    eapply satisfiesAll_add in H4; dcr.
    edestruct op_eval_same; try eapply H0; eauto; dcr.
    unfold cp_choose_op in *; simpl in *.
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
: Op.freeVars e ⊆ lv
  -> entails (cp_eqns AE lv) {EqnApx e (cp_choose_op AE e)}.
Proof.
  unfold cp_choose_op. case_eq (op_eval AE e); intros.
  - eapply entails_eqns_apx_refl.
  - hnf; intros.
    case_eq (Op.op_eval E e); intros; simpl.
    + edestruct op_eval_same; try eapply H1; eauto; dcr.
      hnf; intros. cset_tac'. rewrite <- H3; simpl.
      rewrite H4. inv H5. reflexivity.
    + edestruct op_eval_same; try eapply H1; eauto; dcr. congruence.
Qed.

Lemma cp_choose_approx_list AE Y lv
: list_union (List.map Op.freeVars Y) ⊆ lv
  ->  entails (cp_eqns AE lv) (list_EqnApx Y (List.map (cp_choose_op AE) Y)).
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
: Op.freeVars e ⊆ D
  -> Op.freeVars (cp_choose_op AE e) ⊆ D.
Proof.
  intros.
  unfold cp_choose_op.
  case_eq (op_eval AE e); intros; eauto using incl_empty.
Qed.

Lemma cp_choose_exp_live_sound_exp AE e lv
:  Op.freeVars e ⊆ lv
   -> Op.freeVars (cp_choose_op AE e) ⊆ lv.
Proof.
  intros. unfold cp_choose_op.
  destruct (op_eval AE e); intros; eauto.
  simpl; eapply incl_empty.
Qed.

Lemma cp_choose_exp_eval_exp AE e v
: op_eval AE e = wTA v
  -> op_eval AE (cp_choose_op AE e) = wTA v.
Proof.
  intros. unfold cp_choose_op. rewrite H; eauto.
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
  destruct H; dcr. cset_tac'.
  eapply cp_eqns_in in H. cset_tac'.
  unfold cp_eqn in H4.
  case_eq (AE x1); intros.
  - rewrite H in *.
    destruct a0.
    + isabsurd.
    + cset_tac'. hnf in H4; subst; simpl in *.
      rewrite H0 in H1. cset_tac.
  - rewrite H in H4. isabsurd.
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
    cset_tac'. invc H4.
    unfold subst_eqn; simpl.
    edestruct (update_with_list_lookup_in_list sid Z Y) as [? [? ]]; eauto; dcr.
    invc H9. invc H7.
    eexists x0, x2, a; repeat split; eauto.
  - exfalso. rewrite H1 in H4; isabsurd.
Qed.

Lemma entails_cp_eqns_subst AE D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE Z) (List.map (op_eval AE ∘ Some) Y)
  -> list_union (List.map Op.freeVars Y)[<=]D
  -> entails (cp_eqns AE D)
            (subst_eqns (sid [Z <-- Y]) (cp_eqns AE (of_list Z))).
Proof.
  intros LEQ le_prec INCL.
  hnf. intros. hnf. intros.

  edestruct in_subst_eqns as [? [? []]]; eauto; dcr.
  edestruct PIR2_nth_2; eauto; dcr.
  exploit lookup_list_get; eauto. subst.
  inversion H7; try congruence.
  edestruct op_eval_same; eauto; dcr.
  - rewrite <- INCL.
    eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
  - simpl. rewrite H9.
    econstructor. inv H10. congruence.
Qed.


Lemma entails_cp_eqns_subst_choose AE AE' D Z Y
: length Z = length Y
  -> PIR2 le_precise (lookup_list AE' Z) (List.map (op_eval AE ∘ Some) Y)
  -> list_union (List.map Op.freeVars Y)[<=]D
  -> entails (cp_eqns AE D)
            (subst_eqns (sid [Z <-- List.map (cp_choose_op AE) Y]) (cp_eqns AE' (of_list Z))).
Proof.
  intros LEQ le_prec INCL.
  hnf. intros. hnf. intros.

  edestruct in_subst_eqns as [? [? []]]; try eapply H0; eauto; dcr; subst.
  edestruct map_get_4; eauto; dcr.
  edestruct PIR2_nth_2; eauto; dcr.
  exploit lookup_list_get; eauto. subst.
  inversion H8; try congruence.
  edestruct op_eval_same; eauto; dcr.
  rewrite <- INCL.
  eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
  hnf; simpl. inv_get.
  rewrite H6. unfold cp_choose_op. rewrite <- H10. simpl.
  constructor. inv H12. congruence.
Qed.

Lemma cp_eqns_update D x c AE
: x ∈ D
  -> cp_eqns (AE [x <- ⎣ wTA c ⎦]) D [=] singleton (EqnEq (Var x) (Con c)) ∪ cp_eqns AE (D \ {{x}}).
Proof.
  intros.
  assert (D [=] {{x}} ∪ (D \ {{x}})). {
    cset_tac.
  }
  rewrite H0 at 1. rewrite cp_eqns_union. rewrite cp_eqns_single.
  unfold cp_eqn. lud; isabsurd.
  rewrite cp_eqns_agree. reflexivity.
  hnf; intros. lud. inv e0; subst. exfalso; cset_tac; intuition.
Qed.

Lemma unsat_bool_eq_val E e v
  : (forall w, Op.op_eval E e = Some w -> bool2val (val2bool w) <> v)
    -> ~ satisfies E (EqnEq (UnOp UnOpToBool e) (Con v)).
Proof.
  intros NE SAT. hnf in SAT. simpl in *.
  case_eq (Op.op_eval E e); intros.
  - rewrite H in SAT; simpl in *. inv SAT.
    eapply NE; eauto.
  - rewrite H in SAT; isabsurd.
Qed.

Lemma aval2bool_inv_val b AE e lv (FV:Op.freeVars e [<=] lv)
  : aval2bool (op_eval AE e) = ⎣ b ⎦
    -> forall E, satisfiesAll E (cp_eqns AE lv) -> exists v, Op.op_eval E e = Some v /\
             bool2val (val2bool v) = bool2val b.
Proof.
  intros.
  case_eq (op_eval AE e); intros.
  - rewrite H1 in H; eauto. isabsurd.
  - rewrite H1 in H. inv H.
    edestruct op_eval_same; eauto.
    eexists x; split; eauto; dcr.
    inv H4. reflexivity.
Qed.

Lemma satisfies_BinOpEq_inv_true E e e'
  : satisfies E (EqnEq (UnOp UnOpToBool (BinOp BinOpEq e e')) (Con val_true))
    -> satisfies E (EqnEq e e').
Proof.
  intros. hnf in H. simpl in *.
  destruct (Op.op_eval E e); isabsurd.
  destruct (Op.op_eval E e'); isabsurd.
  simpl in *. inv H.
  pose proof (Integers.Int.eq_spec v v0).
  destruct (Integers.Int.eq v v0); intros; isabsurd.
  subst; eauto. reflexivity.
Qed.

Lemma satisfies_UnOpToBool_inv_false E e
  : satisfies E (EqnEq (UnOp UnOpToBool e) (Con val_false))
    -> satisfies E (EqnEq e (Con default_val)).
Proof.
  intros. hnf in H. simpl in *.
  destruct (Op.op_eval E e); isabsurd.
  simpl in *. inv H.
  unfold val2bool in H2. cases in H2.
  - reflexivity.
  - simpl in *. isabsurd.
Qed.

Lemma satisfies_single E gamma
  : satisfies E gamma
    -> satisfiesAll E {gamma}.
Proof.
  intros; hnf; intros.
  cset_tac'. rewrite <- H0; eauto.
Qed.

Lemma satisfies_single' E gamma
  : satisfiesAll E {gamma}
    -> satisfies E gamma.
Proof.
  intros. eapply H. cset_tac.
Qed.

Lemma satisfies_add_extr E gamma Gamma
  : satisfiesAll E {gamma; Gamma}
    -> satisfies E gamma.
Proof.
  intros. eapply H. cset_tac.
Qed.

Lemma satisfies_add_drop E gamma Gamma
  : satisfiesAll E {gamma; Gamma}
    -> satisfiesAll E Gamma.
Proof.
  intros. hnf; intros. eapply H. cset_tac.
Qed.


Lemma cp_sound_eqn AE Cp ZL GL ΓL s (ang:ann (set var * set var))
 (CP:cp_sound AE Cp s)
 (RA: renamedApart s ang)
 (LD: labelsDefined s (length ZL))
 (Len1: ❬ZL❭ = ❬GL❭)
 (Len2: ❬ZL❭ = ❬ΓL❭)
 (Len3: ❬ZL❭ = ❬Cp❭)
  (LINV:(forall n aY Z G Γ Z', get ZL n Z
                   -> get GL n G
                   -> get ΓL n Γ
                   -> get Cp n (Z',aY)
                   -> (exists AE', aY = lookup_list AE' Z
                             /\ Γ [=] cp_eqns AE' (of_list Z)) /\ Z' = Z))
  :  eqn_sound ZL GL ΓL s (constantPropagate AE s) (cp_eqns AE (fst (getAnn ang))) ang.
Proof.
  general induction CP; invt renamedApart; invt labelsDefined; simpl.
  - simpl in *.
    destruct e.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
        pe_rewrite. rewrite cp_eqns_add.
        eapply entails_union; split.
        -- unfold cp_eqn.
           case_eq (AE x); intros; eauto using entails_empty.
           rewrite H0 in H. inv H.
           cases; eauto using entails_empty.
           eapply op_eval_entails; eauto.
        -- eapply entails_monotone. reflexivity.
           cset_tac.
      * eapply cp_choose_approx; eauto.
      * eapply cp_choose_exp_freeVars; eauto.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
        pe_rewrite. rewrite cp_eqns_add.
        eapply entails_union; split.
        -- unfold cp_eqn.
           case_eq (AE x); intros; eauto using entails_empty.
           rewrite H0 in H. inv H.
           eauto using entails_empty.
        -- reflexivity.
      * eapply cp_choose_approx_list; eauto.
      * simpl in *. rewrite <- H4.
        eapply list_union_incl; eauto with cset.
        intros; inv_get.
        eapply cp_choose_exp_freeVars; eauto.
        eapply incl_list_union; eauto with get.
      * eauto with len.
  - econstructor; intros; eauto.
    + {
        decide (aval2bool (op_eval AE e) = Some false).
        - eapply EqnUnsat.
          eapply unsatisfiable_add_left. intros.
          eapply unsat_bool_eq_val; intros.
          edestruct aval2bool_inv_val; eauto; dcr.
          assert (w = x) by congruence; subst.
          rewrite H16. simpl. intro.
          eapply val_true_false_neq. congruence.
        - eapply eqn_sound_entails_monotone; eauto.
          pe_rewrite.
          hnf. intros. cases.
          + inv COND; simpl in *.
            rewrite cp_eqns_update.
            * eapply satisfiesAll_union; split.
              -- eapply satisfies_single.
                 eapply satisfies_BinOpEq_inv_true.
                 eapply satisfies_add_extr; eauto.
              -- rewrite minus_incl.
                 eapply satisfies_add_drop; eauto.
            * eauto with cset.
          + eapply satisfies_add_drop; eauto.
      }
    + {
        decide (aval2bool (op_eval AE e) = Some true).
        - eapply EqnUnsat.
          eapply unsatisfiable_add_left. intros.
          eapply unsat_bool_eq_val; intros.
          edestruct aval2bool_inv_val; eauto; dcr.
          assert (w = x) by congruence; subst.
          rewrite H16. intro. simpl in *.
          eapply val_true_false_neq. congruence.
        - eapply eqn_sound_entails_monotone; eauto.
          pe_rewrite.
          hnf. intros. cases.
          + inv COND; simpl in *.
            rewrite cp_eqns_update.
            * eapply satisfiesAll_union; split.
              -- eapply satisfies_single.
                 eapply satisfies_UnOpToBool_inv_false.
                 eapply satisfies_add_extr; eauto.
              -- rewrite minus_incl.
                 eapply satisfies_add_drop; eauto.
            * eauto with cset.
          + eapply satisfies_add_drop; eauto.
      }
    + eapply cp_choose_approx; eauto.
  - edestruct get_in_range as [a ?]; eauto.
    inv_get.
    edestruct LINV; eauto; dcr; simpl in *. subst.
    econstructor; eauto with len.
    + rewrite H11.
      eapply entails_cp_eqns_subst_choose; eauto.
    + eapply cp_choose_approx_list; eauto.
  - econstructor; eauto using cp_choose_approx.
  - assert (INV:forall (n : nat) (aY : 〔؟ aval〕) (Z : params) (G : ⦃nat⦄) (Γ : ⦃eqn⦄) Z',
               get (fst ⊝ F ++ ZL) n Z ->
               get (tab D ‖F‖ ++ GL) n G ->
               get ((fun '(Z1, _) => cp_eqns AE (of_list Z1)) ⊝ F ++ ΓL) n Γ ->
               get ((fun Zs : params * stmt => (fst Zs, lookup_list AE (fst Zs))) ⊝ F ++ Cp) n (Z', aY) ->
               (exists AE' : nat -> ؟ aval, aY = lookup_list AE' Z /\ Γ [=] cp_eqns AE' (of_list Z)) /\ Z' = Z). {
      intros.
      eapply get_app_cases in H1. destruct H1; dcr.
      - inv_get. split; eauto. eexists; split; eauto.
        destruct x; reflexivity.
      - len_simpl.
        rewrite get_app_ge in H11; eauto with len.
        rewrite get_app_ge in H13; eauto with len.
        rewrite get_app_ge in H2; eauto with len.
    }
    eapply EqnFun with (Γ2:=cp_eqns AE D) (ΓF:=List.map (fun '(Z,s) => cp_eqns AE (of_list Z)) F);
      eauto with len.
    + intros; inv_get; eauto.
    + intros; inv_get; eauto.
      exploit H0; eauto; eauto with len.
      edestruct H5; eauto; dcr; eauto with len.
      simpl in *.
      rewrite H11 in H2. rewrite cp_eqns_union in H2.
      eapply H2.
    + eapply eqn_sound_entails_monotone; eauto.
      * eapply IHCP; eauto; eauto with len.
      * pe_rewrite. reflexivity.
    + intros; inv_get; destruct Zs; simpl.
      rewrite cp_eqns_freeVars. eapply incl_right.
    + rewrite cp_eqns_freeVars. eauto.
    + reflexivity.
Qed.

Require Import CMap.

Lemma cp_eqns_no_assumption d G
: (forall x : var,
   x \In G -> MapInterface.find x d = ⎣⎦)
   -> cp_eqns (fun x0 : var => MapInterface.find x0 d) G [=] ∅.
Proof.
  intros. revert H. pattern G. eapply set_induction.
  - intros.
    eapply empty_is_empty_1 in H. rewrite H.
    reflexivity.
  - intros. eapply Add_Equal in H1. rewrite H1.
    assert ({x; s} [=] {{x}} ∪ s) by cset_tac.
    rewrite H3. rewrite cp_eqns_union.
    rewrite cp_eqns_single. unfold cp_eqn.
    rewrite H2.
    + rewrite H.
      * cset_tac.
      * intros; eapply H2.
        rewrite H1. cset_tac.
    + rewrite H1. cset_tac.
Qed.
