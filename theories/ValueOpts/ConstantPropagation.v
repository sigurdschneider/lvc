Require Import CSet Le Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Indexwise.
Require Import CSet Val Var Env IL Sim Fresh Annotation LabelsDefined DecSolve OptionR.

Require Import RenamedApart SetOperations Eqn ValueOpts Infra.Lattice WithTop.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)

Require compcert.lib.Integers.


(* None is top *)
Definition aval := option (withTop val).

Coercion option_as_unkown A (a:option A) :=
  match a with
  | Some a => Known a
  | None => Unknown
  end.

Fixpoint op_eval (E:onv (withTop val)) (e:op) : aval :=
  match e with
    | Con v => Some (wTA v)
    | Var x => E x
    | UnOp o e => match op_eval E e with
                 | Some (wTA v) =>
                   match Val.unop_eval o v with
                   | Some v => Some (wTA v)
                   | None => None
                   end
                   | v => v
                 end
    | BinOp o e1 e2 =>
       match op_eval E e1 with
       | Some (wTA v1) =>
         match op_eval E e2 with
         | Some (wTA v2) =>
           match Val.binop_eval o v1 v2 with
           | Some v => Some (wTA v)
           | None => None
           end
         | v => v
         end
       | v => v
       end

  end.

Definition exp_eval (E:onv (withTop val)) (e:exp) : aval :=
  match e with
  | Operation e => op_eval E e
  | _ => Some Top
  end.

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

Definition aval2bool (v:aval) :=
  match v with
    | Some (wTA v) => Some (val2bool v)
    | _ => None
  end.

Lemma oval2bool_some v b
: aval2bool v = Some b ->
  exists v', v = (Some (wTA v')) /\ val2bool v' = b.
Proof.
  destruct v; try destruct w; simpl; intros; inv H; eauto.
Qed.

Inductive cp_sound : onv (withTop val)
                     -> list (params*list aval)
                     -> list bool
                     -> stmt
                     -> ann bool
                     -> Prop :=
| CPOpr AE (x:var) Cp Rch (b:bool) r e s
  : cp_sound AE Cp Rch s r
    -> (b -> exp_eval AE e = AE x)
    -> (b -> getAnn r)
    -> cp_sound AE Cp Rch (stmtLet x e s) (ann1 b r)
| CPIf AE Cp Rch e (b:bool) s1 s2 (r1 r2:ann bool)
       (Cond1:cp_sound AE Cp Rch s1 r1)
       (Cond2:cp_sound AE Cp Rch s2 r2)
       (Reach1:b -> op_eval AE e <> None -> aval2bool (op_eval AE e) <> Some false -> getAnn r1)
       (Reach2:b -> poLe (Some (wTA val_false)) (op_eval AE e) -> getAnn r2)
  : cp_sound AE Cp Rch (stmtIf e s1 s2) (ann2 b r1 r2)
| CPGoto AE l Y Cp Rch Z aY (b bf:bool)
  : get Cp (counted l) (Z,aY)
    -> get Rch (counted l) bf
    -> length Z = length Y
    -> (b -> PIR2 poLe (List.map (op_eval AE) Y) aY)
    -> (b -> bf)
    -> cp_sound AE Cp Rch (stmtApp l Y) (ann0 b)
| CPReturn AE Cp Rch e b
  : cp_sound AE Cp Rch (stmtReturn e) (ann0 b)
| CPLet AE Cp Rch F t (b:bool) (rF:list (ann bool)) (r:ann bool) (rfLen:❬F❭=❬rF❭)
   (Reach1:b -> getAnn r)
  : (forall n Zs r,
        get F n Zs ->
        get rF n r ->
        cp_sound AE (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ Cp)
                 (getAnn ⊝ rF ++ Rch)
                 (snd Zs) r)
    -> cp_sound AE (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ Cp)
               (getAnn ⊝ rF ++ Rch) t r
    -> cp_sound AE Cp Rch (stmtFun F t) (annF b rF r).

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

Instance cp_sound_dec AE Rch ZL s r : Computable (cp_sound AE ZL Rch s r).
Proof.
  hnf. revert AE Rch ZL r; sind s; intros; destruct s; destruct r; try dec_solve.
  - edestruct (IH s); eauto;
      decide (a -> exp_eval AE e = AE x); try dec_solve;
        decide (a -> getAnn r); try dec_solve.
  - edestruct (IH s2 ltac:(eauto) AE Rch ZL); eauto; [| dec_solve];
      edestruct (IH s1 ltac:(eauto) AE Rch ZL); eauto; [| dec_solve];
        decide (op_eval AE e = None);
        decide (aval2bool (op_eval AE e) = Some false);
        (decide (poLe (Some (wTA val_false)) (op_eval AE e)));
        decide (a); decide (getAnn r1); decide (getAnn r2); try dec_solve.
  - destruct (get_dec ZL (counted l)) as [[[]]|]; try dec_solve.
    destruct (get_dec Rch (counted l)) as [[]|]; try dec_solve.
    decide (length l0 = length Y); try dec_solve.
    decide (a -> PIR2 poLe (List.map (op_eval AE) Y) l1);
      try dec_solve.
    decide (a -> x); try dec_solve.
  - assert (SZ:size s < size (stmtFun F s)) by eauto.
    decide (❬F❭=❬sa❭); [|dec_solve].
    edestruct (IH s SZ AE (getAnn ⊝ sa ++ Rch) (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ ZL) r); [|dec_solve].
    exploit (@indexwise_R2_dec _ _ (fun Zs r => cp_sound AE ((fun Zs0 : params * stmt => (fst Zs0,
        lookup_list AE (fst Zs0))) ⊝ F ++ ZL)(getAnn ⊝ sa ++ Rch)  (snd Zs) r) F); eauto.
    intros. eapply IH; eauto. destruct H;[|dec_solve].
    decide (a -> getAnn r); dec_solve.
Defined.

Definition cp_eqn (E:onv (withTop val)) x :=
  match E x with
  | Some (wTA c) => singleton (EqnEq (Var x) (Con c))
  | None => singleton EqnBot
  | _ => ∅
  end.

Instance cp_eqn_eq E
  : Proper (_eq ==> _eq) (cp_eqn E).
Proof.
  unfold Proper, respectful, cp_eqn; intros; subst.
  hnf in H; subst.
  cases; eauto.
Qed.

Definition cp_eqns (E:onv (withTop val)) (lv:set var) : eqns :=
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

Definition cp_eqns_ann (a:ann (onv (withTop val))) (b:ann (set var)) : ann eqns :=
  zip2Ann cp_eqns a b (ann0 ∅).

Definition cp_choose_op E e :=
  match op_eval E e with
    | Some (wTA c) => Con c
    | _ => e
  end.


Fixpoint constantPropagate (AE:onv (withTop val)) s {struct s} : stmt :=
  match s with
    | stmtLet x (Operation e) s =>
      stmtLet x (Operation (cp_choose_op AE e)) (constantPropagate AE s)
    | stmtLet x (Call f Y) s =>
      stmtLet x (Call f (List.map (cp_choose_op AE) Y))
              (constantPropagate AE s)
    | stmtIf e s t =>
      stmtIf (cp_choose_op AE e)
             (constantPropagate AE s)
             (constantPropagate AE t)
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
    -> AE x = ⎣ wTA v ⎦
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

Lemma in_cp_eqns_bot AE x lv
  : x \In lv
    -> AE x = ⎣⎦
    -> EqnBot ∈ cp_eqns AE lv.
Proof.
  intros. unfold cp_eqns.
  eapply fold_union_incl.
  instantiate (1:=singleton EqnBot).
  cset_tac; intuition.
  assert (cp_eqn AE x = singleton EqnBot).
  unfold cp_eqn. rewrite H0. reflexivity.
  rewrite <- H1. eapply map_1; eauto.
  eauto with typeclass_instances.
Qed.

Lemma cp_eqns_satisfies_env_none AE E x lv
: x ∈ lv
  -> AE x = None
  -> satisfiesAll E (cp_eqns AE lv)
  -> E x = None.
Proof.
  intros. exploit H1 as SAT; eauto.
  instantiate (1:=EqnBot).
  eapply in_cp_eqns_bot; eauto.
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

Ltac imatch := try dmatch; try smatch; try clear_trivial_eqs; isabsurd.

Lemma op_eval_same e lv AE E v
:   Op.freeVars e ⊆ lv
    -> op_eval AE e = Some (wTA v)
    -> satisfiesAll E (cp_eqns AE lv)
    -> Op.op_eval E e = Some v.
Proof.
  intros. general induction e; simpl in * |- *; eauto 20 using @option_eq.
  - exploit cp_eqns_satisfies_env; eauto using @option_eq.
    + cset_tac.
  - repeat imatch.
    erewrite IHe; eauto; dcr.
  - repeat imatch.
    erewrite IHe1; eauto.
    erewrite IHe2; eauto.
    cset_tac. cset_tac.
Qed.

Lemma op_eval_None e lv AE E
:   Op.freeVars e ⊆ lv
    -> op_eval AE e = None
    -> satisfiesAll E (cp_eqns AE lv)
    -> Op.op_eval E e = None.
Proof.
  intros. general induction e; simpl in * |- *; eauto 20 using @option_eq.
  - exploit cp_eqns_satisfies_env_none; eauto using @option_eq.
    + cset_tac.
  - repeat imatch.
    + erewrite op_eval_same; eauto; dcr; subst.
    + erewrite IHe; eauto; dcr.
  - repeat imatch.
    + erewrite !op_eval_same; eauto; cset_tac.
    + erewrite op_eval_same; eauto.
      erewrite IHe2; eauto.
      cset_tac. cset_tac.
    + erewrite IHe1; eauto. cset_tac.
Qed.

Lemma op_eval_entails AE e v x lv
: Op.freeVars e ⊆ lv
  -> op_eval AE e = Some (wTA v)
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
  unfold cp_choose_op. case_eq (op_eval AE e); try destruct w; intros.
  - eapply entails_eqns_apx_refl.
  - hnf; intros.
    eapply op_eval_same in H; eauto.
    hnf; intros. cset_tac'. rewrite <- H2; simpl.
    rewrite H.  reflexivity.
  - eapply entails_eqns_apx_refl.
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
  case_eq (op_eval AE e); try destruct w; intros; eauto using incl_empty.
Qed.

Lemma cp_choose_exp_live_sound_exp AE e lv
:  Op.freeVars e ⊆ lv
   -> Op.freeVars (cp_choose_op AE e) ⊆ lv.
Proof.
  intros. unfold cp_choose_op.
  destruct (op_eval AE e); intros; try destruct w; eauto.
  simpl; eapply incl_empty.
Qed.

Lemma cp_choose_exp_eval_exp AE e v
: op_eval AE e = Some (wTA v)
  -> op_eval AE (cp_choose_op AE e) = Some (wTA v).
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
  intros. general induction H0; simpl in *; eauto.
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
    destruct w.
    + isabsurd.
    + destruct a0.
      * cset_tac'. hnf in H4; subst; simpl in *.
        rewrite H0 in H1. cset_tac.
  - rewrite H in H4. cset_tac'.
    rewrite <- H4 in H0. simpl in *.
    exfalso. rewrite H0 in H1. cset_tac.
Qed.

Lemma in_subst_eqns gamma Z Y AE
: length Z = length Y
  -> gamma \In subst_eqns (sid [Z <-- Y]) (cp_eqns AE (of_list Z))
  -> (exists n x c,
      gamma = subst_eqn (sid [Z <-- Y]) (EqnEq (Var x) (Con c))
      /\ AE x = Some (wTA c)
      /\ get Z n x
      /\ get Y n ((sid [Z <-- Y]) x))
    \/ (exists n x,
      gamma = subst_eqn (sid [Z <-- Y]) (EqnBot)
      /\ AE x = None
      /\ EqnBot ∈ cp_eqns AE (of_list Z)
      /\ get Z n x
      /\ get Y n ((sid [Z <-- Y]) x)).
Proof.
  intros.
  edestruct subst_eqns_in as [γ' ?]; eauto; dcr; subst.
  edestruct cp_eqns_in as [x ?]; eauto; dcr.
  unfold cp_eqn in H4. case_eq (AE x); intros.
  - left. rewrite H1 in H4. destruct w; isabsurd.
    destruct a; isabsurd.
    cset_tac'. invc H4.
    unfold subst_eqn; simpl.
    edestruct (update_with_list_lookup_in_list sid Z Y) as [? [? ]]; eauto; dcr.
    invc H9. invc H7.
    eexists x0, x2; repeat split; eauto.
  - right. rewrite H1 in H4.
    cset_tac'. invc H4.
    unfold subst_eqn; simpl.
    edestruct (update_with_list_lookup_in_list sid Z Y) as [? [? ]]; eauto; dcr.
    invc H9. invc H7.
    eexists x0, x2; repeat split; eauto.
Qed.

Lemma entails_cp_eqns_subst_choose AE AE' D Z Y
: length Z = length Y
  -> PIR2 poLe (List.map (op_eval AE) Y) (lookup_list AE' Z)
  -> list_union (List.map Op.freeVars Y)[<=]D
  -> entails (of_list ((fun y => EqnEq y y) ⊝ cp_choose_op AE ⊝ Y) ∪ cp_eqns AE D)
            (subst_eqns (sid [Z <-- List.map (cp_choose_op AE) Y])
                        (cp_eqns AE' (of_list Z))).
Proof.
  intros LEQ le_prec INCL.
  hnf. intros. hnf. intros.

  edestruct in_subst_eqns as [[? [? []]]|]; try eapply H0; eauto with len; dcr; subst.
  - inv_get.
    edestruct PIR2_nth_2; eauto; dcr.
    + rewrite lookup_list_map.
      eapply map_get_1. eauto.
    + rewrite H4 in *; simpl in *.
      clear_trivial_eqs. inv_get.
      exploit H. instantiate (1:=EqnEq (cp_choose_op AE x2) (cp_choose_op AE x2)).
      eapply incl_left. eapply get_in_of_list.
      eapply map_get_eq; eauto. inv H1; subst.
      inv H5; clear_trivial_eqs.
      * exfalso. exploit op_eval_None; eauto.
        instantiate (1:=D).
        erewrite <- INCL.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        hnf; intros. eapply H. cset_tac. unfold cp_choose_op in H2. rewrite <- H9 in H2.
        congruence.
      * exploit op_eval_same; eauto; dcr.
        -- instantiate (1:=D).
           rewrite <- INCL.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        -- hnf; intros. eapply H. cset_tac.
        -- rewrite <- EQ.
           unfold cp_choose_op. rewrite <- H7. simpl.
           econstructor; eauto.
  - simpl. inv_get.
    simpl in *.
    edestruct PIR2_nth_2; eauto; dcr.
    + rewrite lookup_list_map.
      eapply map_get_1. eauto.
    + rewrite H3 in *. inv H6.
      inv_get.
      exploit H.
      instantiate (1:=EqnEq (cp_choose_op AE x1) (cp_choose_op AE x1)).
      eapply incl_left. eapply get_in_of_list.
      eapply map_get_eq; eauto. inv H1; subst.
      exploit op_eval_None; eauto.
      instantiate (1:=D).
      erewrite <- INCL.
      eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      hnf; intros. eapply H. cset_tac. unfold cp_choose_op in H6.
      rewrite <- H2 in *. congruence.
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
  - rewrite H1 in H; eauto.
    simpl in *. destruct w; isabsurd.
    exploit op_eval_same; eauto; dcr.
    clear_trivial_eqs. eauto.
  - rewrite H1 in H. inv H.
Qed.

(*
Lemma aval2bool_none AE e lv (FV:Op.freeVars e [<=] lv)
  : aval2bool (op_eval AE e) = None
    -> forall E, satisfiesAll E (cp_eqns AE lv) -> Op.op_eval E e = None.
Proof.
  intros.
  case_eq (op_eval AE e); intros.
  - rewrite H1 in H; eauto.
    simpl in *. destruct w; isabsurd.
    exploit op_eval_same; eauto; dcr.
    clear_trivial_eqs. eauto.
  - rewrite H1 in H. inv H.
Qed.
 *)

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
  subst; eauto. econstructor; eauto.
Qed.

Lemma satisfies_UnOpToBool_inv_false E e
  : satisfies E (EqnEq (UnOp UnOpToBool e) (Con val_false))
    -> satisfies E (EqnEq e (Con default_val)).
Proof.
  intros. hnf in H. simpl in *.
  destruct (Op.op_eval E e); isabsurd.
  simpl in *. inv H.
  unfold val2bool in H2. cases in H2.
  - econstructor. reflexivity.
  - simpl in *. isabsurd.
Qed.


Lemma entails_bot Γ Γ'
  : EqnBot ∈ Γ
    -> entails Γ Γ'.
Proof.
  intros. hnf; intros.
  exfalso. exploit H0; eauto.
Qed.


Lemma fold_union_singleton X `{OrderedType X} x
: fold union ({x}) {} [=] x.
Proof.
  assert (singleton x [=] {x; ∅ }).
  cset_tac; intuition. rewrite H0.
  rewrite fold_single; eauto using Equal_ST, union_m, transpose_union.
  clear; cset_tac.
Qed.

Lemma map_singleton {X} `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} x
      : map f (singleton x) [=] (singleton (f x)).
Proof.
  hnf; intros. rewrite map_iff; eauto.
  split; intros.
  - destruct H2; dcr. cset_tac'.
  - cset_tac.
Qed.

Lemma eqns_freeVars_singleton e
  : eqns_freeVars {e} [=] freeVars e.
Proof.
  intros. unfold eqns_freeVars.
  rewrite map_singleton; eauto using freeVars_Proper.
  rewrite fold_union_singleton.
  cset_tac.
Qed.

Lemma val_false_true_neq: (val_false <> val_true)%type.
Proof.
  intro. eapply val_true_false_neq. eauto.
Qed.

Lemma cp_sound_eqn AE Cp Rch ZL GL ΓL s r (ang:ann (set var * set var))
 (CP:cp_sound AE Cp Rch s r)
 (RA: renamedApart s ang)
 (LD: labelsDefined s (length ZL))
 (Len1: ❬ZL❭ = ❬GL❭)
 (Len2: ❬ZL❭ = ❬ΓL❭)
 (Len3: ❬ZL❭ = ❬Cp❭)
 (Len4: ❬ZL❭ = ❬Rch❭)
  (LINV:(forall n aY Z G Γ Z' b, get ZL n Z
                   -> get GL n G
                   -> get ΓL n Γ
                   -> get Cp n (Z',aY)
                   -> get Rch n b
                   -> (exists AE', aY = lookup_list AE' Z
                             /\ Γ [=]
                                 if b then cp_eqns AE' (of_list Z)
                                 else singleton EqnBot) /\ Z' = Z))
  :  eqn_sound ZL GL ΓL s (constantPropagate AE s)
               (if getAnn r then cp_eqns AE (fst (getAnn ang)) else singleton EqnBot) ang.
Proof.
  general induction CP; invt renamedApart; invt labelsDefined; simpl.
  - simpl in *.
    destruct e.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
        repeat cases; pe_rewrite; eauto using entails_empty.
        -- rewrite cp_eqns_add.
           eapply entails_union; split.
           unfold cp_eqn.
           case_eq (AE x); intros; eauto using entails_empty.
           ++ rewrite H1 in H. exploit H; eauto. inv H2.
             repeat cases; eauto using entails_empty.
             eapply op_eval_entails; eauto.
           ++ simpl in *. hnf; intros.
             exfalso. exploit H2.
             instantiate (1:=EqnEq (Var x) (cp_choose_op AE e)). cset_tac.
             unfold cp_choose_op in H3.
             rewrite H in H3; eauto. rewrite H1 in H3.
             simpl in H3. rewrite H1 in H.
             erewrite op_eval_None in H3; eauto.
             inv H3. hnf; intros. eapply H2. cset_tac.
           ++ eapply entails_subset. cset_tac.
        -- eapply entails_bot. cset_tac.
        -- eapply entails_bot. cset_tac.
      * cases.
        -- eapply cp_choose_approx; eauto.
        -- eapply entails_bot; eauto.
      * eapply cp_choose_exp_freeVars; eauto.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
         repeat cases; pe_rewrite; eauto using entails_empty.
        rewrite cp_eqns_add.
        eapply entails_union; split.
        -- unfold cp_eqn.
           case_eq (AE x); intros; eauto using entails_empty.
           rewrite H1 in H. exploit H; eauto. inv H2.
           repeat cases; eauto using entails_empty.
           simpl in *. exploit H; eauto. congruence.
        -- eapply entails_subset. cset_tac.
        -- eapply entails_bot. cset_tac.
        -- eapply entails_bot. cset_tac.
      * cases.
        -- eapply cp_choose_approx_list; eauto.
        -- eapply entails_bot; eauto.
      * simpl in *. rewrite <- H5.
        eapply list_union_incl; eauto with cset.
        intros; inv_get.
        eapply cp_choose_exp_freeVars; eauto.
        eapply incl_list_union; eauto with get.
      * eauto with len.
  - econstructor; intros; eauto.
    + {
        cases.
        - decide (aval2bool (op_eval AE e) = Some false).
          + eapply EqnUnsat.
            eapply unsatisfiable_add_left. intros.
            eapply unsat_bool_eq_val; intros.

            edestruct aval2bool_inv_val; eauto; dcr.
            assert (w = x) by congruence; subst.
            rewrite H12. simpl. eapply val_false_true_neq.
          + decide (op_eval AE e = None).
            * decide (getAnn r1).
              -- eapply eqn_sound_entails_monotone; eauto.
                 cases. pe_rewrite. eapply entails_subset. cset_tac.
              -- eapply eqn_sound_entails_monotone; eauto.
                 cases; eauto.
                 hnf; intros. exfalso.
                 exploit H. instantiate (1:=EqnEq (UnOp UnOpToBool e) (Con val_true)).
                 cset_tac. simpl in H0.
                 erewrite op_eval_None in H0; eauto. simpl in *.
                 inv H0.
                 hnf; intros. eapply H. cset_tac.
            * eapply eqn_sound_entails_monotone; eauto.
              exploit Reach1; eauto.
              cases.
              pe_rewrite. eapply entails_add''. reflexivity.
        - eapply eqn_sound_entails_monotone; eauto.
          eapply entails_bot. cset_tac.
      }
    + {
        cases.
        - decide (aval2bool (op_eval AE e) = Some true).
          +eapply EqnUnsat.
           eapply unsatisfiable_add_left. intros.
           eapply unsat_bool_eq_val; intros.
           edestruct aval2bool_inv_val; eauto; dcr.
           assert (w = x) by congruence; subst.
           rewrite H12. eapply val_true_false_neq.
          + decide (op_eval AE e = None).
            * decide (getAnn r2).
              -- eapply eqn_sound_entails_monotone; eauto.
                 cases. pe_rewrite. eapply entails_subset. cset_tac.
              -- eapply eqn_sound_entails_monotone; eauto.
                 cases; eauto.
                 hnf; intros. exfalso.
                 exploit H. instantiate (1:=EqnEq (UnOp UnOpToBool e) (Con val_false)).
                 cset_tac. simpl in H0.
                 erewrite op_eval_None in H0; eauto. simpl in *.
                 inv H0.
                 hnf; intros. eapply H. cset_tac.
            * exploit Reach2; eauto.
              revert n.
              case_eq(op_eval AE e); intros; try congruence.
              simpl in *. destruct w; simpl in *.
              -- econstructor; eauto. econstructor.
              -- unfold val2bool in n. cases in n; isabsurd.
                 econstructor; reflexivity.
              -- eapply eqn_sound_entails_monotone; eauto.
                 cases. pe_rewrite.
                 eapply entails_subset; eauto. cset_tac.
        - eapply eqn_sound_entails_monotone; eauto.
          eapply entails_bot. cset_tac.
      }
    + cases.
      * eapply cp_choose_approx; eauto.
      * eapply entails_bot; eauto.
  - edestruct get_in_range as [a ?]; eauto.
    inv_get.
    edestruct LINV; eauto; dcr; simpl in *. subst.
    econstructor; eauto with len.
    + cases.
      * rewrite H13. cases.
        eapply entails_cp_eqns_subst_choose; eauto.



      * eapply entails_bot; eauto. cset_tac.
    + cases.
      * eapply cp_choose_approx_list; eauto.
      * eapply entails_bot; eauto.
  - econstructor; cases; eauto using cp_choose_approx, entails_bot.
  - assert (INV:forall (n : nat) aY (Z : params) (G : ⦃nat⦄) (Γ : ⦃eqn⦄) Z' b,
               get (fst ⊝ F ++ ZL) n Z ->
               get (tab D ‖F‖ ++ GL) n G ->
               get ((fun '(Z1, _) (x:ann bool) => if getAnn x then cp_eqns AE (of_list Z1) else
                    singleton EqnBot) ⊜ F rF ++ ΓL) n Γ ->
               get ((fun Zs : params * stmt => (fst Zs, lookup_list AE (fst Zs))) ⊝ F ++ Cp) n (Z', aY) ->
               get (getAnn ⊝ rF ++ Rch) n b ->
               (exists AE', aY = lookup_list AE' Z /\
                       Γ [=] if b then cp_eqns AE' (of_list Z) else singleton EqnBot) /\ Z' = Z). {
      intros.
      eapply get_app_cases in H1. destruct H1; dcr.
      - inv_get. split; eauto. eexists; split; eauto.
        rewrite get_app_lt in H11; eauto with len.
        inv_get.
        destruct x; try reflexivity.
      - len_simpl.
        rewrite get_app_ge in H11; eauto with len.
        rewrite get_app_ge in H13; eauto with len.
        rewrite get_app_ge in H14; eauto with len.
        rewrite get_app_ge in H2; eauto with len.
        edestruct LINV; dcr; eauto with len.
        rewrite rfLen. eauto with len.
        len_simpl. rewrite <- rfLen. eauto.
    }
    eapply EqnFun with (Γ2:=if getAnn r then cp_eqns AE D else singleton EqnBot) (ΓF:=(fun '(Z1, _) (x:ann bool) => if getAnn x then cp_eqns AE (of_list Z1) else
                                                                                                                singleton EqnBot) ⊜ F rF); eauto with len.
    + intros; inv_get; eauto.
    + intros; inv_get; eauto.
      exploit H0; eauto; eauto with len.
      repeat cases in H2; pe_rewrite; eauto.
      edestruct H5; eauto; dcr; eauto with len.
      simpl in *.
      rewrite H14 in H2. rewrite cp_eqns_union in H2.
      cases; eauto. destruct b; clear_trivial_eqs.
      exploit H4; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      eapply entails_bot. cset_tac.
      exploit H4; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      eapply entails_bot. cset_tac.

    + eapply eqn_sound_entails_monotone; eauto.
      * eapply IHCP; eauto; eauto with len.
      * cases; eauto.
        -- cases. pe_rewrite. reflexivity.
        -- eapply entails_bot. cset_tac.
    + intros; inv_get; destruct Zs; simpl.
      cases.
      * rewrite cp_eqns_freeVars. eapply incl_right.
      * rewrite eqns_freeVars_singleton. simpl.
        eauto with cset.
    + cases.
      * rewrite cp_eqns_freeVars. reflexivity.
      * rewrite eqns_freeVars_singleton. simpl.
        eauto with cset.
    + cases.
      * cases; reflexivity.
      * eapply entails_bot; eauto.
Qed.

Require Import CMap.

Lemma cp_eqns_no_assumption d G
: (forall x : var,
   x \In G -> MapInterface.find x d = ⎣Top⎦)
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
