Require Import CSet Le Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Indexwise.
Require Import CSet Val Var Envs IL Sim Fresh Annotation LabelsDefined DecSolve OptionR.

Require Import RenamedApart SetOperations Eqn ValueOpts Infra.Lattice WithTop.
Require Import ConstantPropagation ConstantPropagationSound Reachability.

Set Implicit Arguments.
Unset Printing Records.

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
  rewrite <- H1.
  eapply map_1; eauto.
  eauto with typeclass_instances.
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
:   Ops.freeVars e ⊆ lv
    -> op_eval AE e = Some (wTA v)
    -> satisfiesAll E (cp_eqns AE lv)
    -> Ops.op_eval E e = Some v.
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
:   Ops.freeVars e ⊆ lv
    -> op_eval AE e = None
    -> satisfiesAll E (cp_eqns AE lv)
    -> Ops.op_eval E e = None.
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
: Ops.freeVars e ⊆ lv
  -> op_eval AE e = Some (wTA v)
  -> entails ({EqnEq (Var x) e ; cp_eqns AE lv }) (singleton (EqnEq (Var x) (Con v))).
Proof.
  intros.
  unfold entails; intros. unfold satisfiesAll; intros.
  cset_tac'.
  invc H2; simpl in *; subst; simpl.
  eapply satisfiesAll_add in H1; dcr.
  eapply op_eval_same in H0; eauto. simpl in *.
  rewrite H0 in H2. eauto.
Qed.

Lemma op_eval_entails' AE e v x
: op_eval AE e = Some (wTA v)
  -> entails ({EqnEq (Var x) e ; cp_eqns AE (Ops.freeVars e) }) (singleton (EqnEq (Var x) (Con v))).
Proof.
  intros.
  unfold entails; intros.
  eapply satisfies_single.
  eapply satisfiesAll_add in H0; dcr.
  eapply op_eval_same in H; eauto. simpl in *.
  rewrite H in H1. eauto. reflexivity.
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

Lemma cp_eqns_single' AE x
: cp_eqns AE {x} [=] cp_eqn AE x.
Proof.
  unfold cp_eqns. simpl.
  setoid_rewrite map_singleton; [|eapply cp_eqn_eq].
  erewrite fold_union_singleton; eauto.
Qed.

Lemma op_eval_entails_eqns AE e x
: op_eval AE e = AE x
  -> entails {EqnEq (Var x) e; cp_eqns AE (Ops.freeVars e)} (cp_eqns AE {x}).
Proof.
  intros EQ.
  rewrite cp_eqns_single'.
  unfold cp_eqn. rewrite <- EQ.
  case_eq (op_eval AE e); intros.
  - destruct w; eauto using entails_empty.
    eapply op_eval_entails'; eauto.
  - hnf; intros. simpl in *.
    exploit op_eval_None; eauto; [ reflexivity| |].
    eapply satisfiesAll_add; eauto.
    eapply satisfies_add_extr in H0.
    exfalso. hnf in H0. simpl in *.
    inv H0; congruence.
Qed.

Lemma op_eval_entails_eqns_Top AE x Gamma
: AE x = Some Top
  -> entails Gamma (cp_eqns AE {x}).
Proof.
  intros EQ.
  rewrite cp_eqns_single'.
  unfold cp_eqn. rewrite EQ.
  eapply entails_empty.
Qed.

Lemma cp_eqns_single AE x
: cp_eqns AE {{ x }} [=] cp_eqn AE x.
Proof.
  unfold cp_eqns.
  rewrite map_single; [| intuition].
  erewrite fold_single; eauto.
  cset_tac.
  eapply Equal_ST.
  eapply union_m.
  eapply transpose_union.
Qed.

Lemma cp_choose_approx AE e lv
: Ops.freeVars e ⊆ lv
  -> entails (cp_eqns AE lv) {EqnApx e (cp_choose_op AE e)}.
Proof.
  general induction e; simpl in *.
  - eapply entails_eqns_apx_refl.
  - repeat cases; eauto using entails_eqns_apx_refl.
    hnf; intros.
    eapply cp_eqns_satisfies_env in H0; eauto; [|cset_tac].
    eapply satisfies_single.
    hnf; simpl. rewrite H0. reflexivity.
  - exploit (IHe AE); eauto.
    hnf; intros.
    eapply satisfies_single. simpl.
    eapply H0 in H1.
    eapply satisfies_single' in H1. hnf in H1.
    revert H1;
      case_eq (cp_choose_op AE e); intros; simpl in *; clear_trivial_eqs;
        try cases; simpl; invt fstNoneOrR; simpl; eauto using fstNoneOrR;
          try reflexivity.
    + rewrite <- Heq; reflexivity.
    + rewrite <- Heq; constructor.
  - exploit (IHe1 AE lv); eauto; [cset_tac|].
    exploit (IHe2 AE lv); eauto; [cset_tac|].
    hnf; intros.
    pose proof (H0 _ H2). eapply H1 in H2. clear H0 H1 H IHe1 IHe2.
    eapply satisfies_single. simpl.
    eapply satisfies_single' in H2. hnf in H2.
    eapply satisfies_single' in H3. hnf in H3.
    revert H2 H3;
      case_eq (cp_choose_op AE e1); case_eq (cp_choose_op AE e2);
        intros; simpl in *; clear_trivial_eqs;
          try cases; simpl; inv H2; inv H3; simpl; eauto using fstNoneOrR;
            try reflexivity.
    + rewrite <- Heq; reflexivity.
    + rewrite <- Heq; constructor.
Qed.

Lemma cp_choose_approx_list AE Y lv
: list_union (List.map Ops.freeVars Y) ⊆ lv
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
: Ops.freeVars e ⊆ D
  -> Ops.freeVars (cp_choose_op AE e) ⊆ D.
Proof.
  intro.
  induction e; simpl in *.
  - eauto.
  - repeat cases; simpl in *; eauto using incl_empty.
  - specialize (IHe H); clear H.
    repeat cases; eauto.
  - exploit IHe1; eauto. cset_tac.
    exploit IHe2; eauto. cset_tac.
    clear H IHe1 IHe2.
    repeat cases; eauto; simpl in *; cset_tac.
Qed.

Lemma cp_choose_exp_eval_exp AE e v
: op_eval AE e = Some (wTA v)
  -> op_eval AE (cp_choose_op AE e) = Some (wTA v).
Proof.
  revert v. induction e; simpl; intros; eauto.
  - rewrite H. reflexivity.
  - revert H IHe.
    case_eq (op_eval AE e); intro w; simpl in *.
    + destruct w; [intros; isabsurd|].
      cases; intros; clear_trivial_eqs.
      exploit IHe; eauto.
      cases; eauto; simpl in *;
        try rewrite H1; simpl; eauto;
        try rewrite <- Heq; simpl; eauto;
          try rewrite H1; simpl; eauto.
    + isabsurd.
  - revert H IHe1 IHe2.
    case_eq (op_eval AE e1); intro w1; simpl in *.
    + case_eq (op_eval AE e2); intro w2; simpl in *.
      * destruct w1; [intros; isabsurd|].
        destruct w2; [intros; isabsurd|].
        cases; intros; clear_trivial_eqs.
        exploit IHe1; eauto;
          exploit IHe2; eauto.
        repeat cases; eauto; simpl in *;
              try rewrite <- Heq; simpl; eauto;
                clear_trivial_eqs;
                try rewrite H2; simpl; eauto;
                  try rewrite H3; simpl; eauto;
                    try rewrite <- Heq; simpl; eauto;
                    try congruence.
      * destruct w1; [intros; isabsurd|].
        isabsurd.
    + isabsurd.
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
  -> list_union (List.map Ops.freeVars Y)[<=]D
  -> entails (of_list ((fun y => EqnEq y y) ⊝ Y) ∪ cp_eqns AE D)
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
    + rewrite H4 in *.
      inv_get.
      exploit H.
      { eapply incl_left.
        eapply get_in_of_list.
        eapply map_get_eq; eauto. }
      invc H1; clear_trivial_eqs.
      invc H5; clear_trivial_eqs.
      * simpl. rewrite <- EQ.
        exfalso. exploit op_eval_None; eauto.
        -- instantiate (1:=D).
           erewrite <- INCL.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        -- hnf; intros. eapply H. cset_tac.
        -- congruence.
      * exploit op_eval_same; eauto; dcr.
        -- instantiate (1:=D).
           rewrite <- INCL.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        -- hnf; intros. eapply H. cset_tac.
        -- simpl. rewrite <- EQ.
           exploit (@cp_choose_approx AE x2 D).
           ++ rewrite <- INCL.
             eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
           ++ exploit H7.
             ** eapply satisfiesAll_Subset_morphism; try eapply H; try reflexivity.
                eauto with cset.
             ** eapply satisfies_single' in H8. hnf in H8.
                rewrite H5 in *. clear_trivial_eqs.
                econstructor. reflexivity.
  - simpl. inv_get.
    simpl in *.
    edestruct PIR2_nth_2; eauto; dcr.
    + rewrite lookup_list_map.
      eapply map_get_1. eauto.
    + rewrite H3 in *. inv H6.
      inv_get.
      exploit H.
      { eapply incl_left.
        eapply get_in_of_list.
        eapply map_get_eq; eauto. }
      invc H1; clear_trivial_eqs.
      exploit op_eval_None; eauto.
      * instantiate (1:=D).
        erewrite <- INCL.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      * hnf; intros. eapply H. cset_tac.
      * congruence.
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
  : (forall w, Ops.op_eval E e = Some w -> bool2val (val2bool w) <> v)
    -> ~ satisfies E (EqnEq (UnOp UnOpToBool e) (Con v)).
Proof.
  intros NE SAT. hnf in SAT. simpl in *.
  case_eq (Ops.op_eval E e); intros.
  - rewrite H in SAT; simpl in *. inv SAT.
    eapply NE; eauto.
  - rewrite H in SAT; isabsurd.
Qed.

Lemma aval2bool_inv_val b AE e lv (FV:Ops.freeVars e [<=] lv)
  : aval2bool (op_eval AE e) = ⎣ wTA b ⎦
    -> forall E, satisfiesAll E (cp_eqns AE lv) -> exists v, Ops.op_eval E e = Some v /\
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

Lemma satisfies_BinOpEq_inv_true E e e'
  : satisfies E (EqnEq (UnOp UnOpToBool (BinOp BinOpEq e e')) (Con val_true))
    -> satisfies E (EqnEq e e').
Proof.
  intros. hnf in H. simpl in *.
  destruct (Ops.op_eval E e); isabsurd.
  destruct (Ops.op_eval E e'); isabsurd.
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
  destruct (Ops.op_eval E e); isabsurd.
  simpl in *. inv H.
  unfold val2bool in H2. cases in H2.
  - econstructor. reflexivity.
  - simpl in *. isabsurd.
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

Lemma impb_lift (b b':bool)
  : (b -> b')
    -> impb b b'.
Proof.
  unfold impb; cases; eauto.
Qed.

Local Hint Resolve impb_lift.


Lemma eqn_sound_EqnEq ZL ΓL AE s s' e ans Γ v
      (ΓINCL: cp_eqns AE (Ops.freeVars e) ⊆ Γ)
      (HEQ:Some (wTA v) ⊑ op_eval AE e ->
           eqn_sound ZL ΓL s s' {EqnEq e (Con v); Γ} ans)
  : eqn_sound ZL ΓL s s' {EqnEq e (Con v); Γ} ans.
Proof.
  decide (Some (wTA v) ⊑ op_eval AE e); eauto.
  eapply EqnUnsat.
  intros E SAT.
  exploit SAT; [ cset_tac |].
  assert (satisfiesAll E (cp_eqns AE (Ops.freeVars e))). {
    rewrite <- incl_add' in SAT.
    rewrite <- ΓINCL in SAT. eauto.
  }
  invc H. dcr.
  case_eq (op_eval AE e); intros.
  - destruct w.
    + eapply n. rewrite H. eauto.
    + decide (a = v); subst.
      * eapply n. rewrite <- H; eauto.
      * eapply op_eval_same in H0; try eapply H; eauto. congruence.
  - eapply op_eval_None in H; eauto; eauto. congruence.
Qed.

Lemma cp_sound_eqn AE Cp Rch ZL ΓL s r (ang:ann (set var * set var))
      (CP:cp_sound AE Cp s r)
      (RCH: reachability (ConstantPropagationSound.cop2bool AE) Sound Rch s r)
      (RA: renamedApart s ang)
      (LD: labelsDefined s (length ZL))
      (Len2: ❬ZL❭ = ❬ΓL❭)
      (Len3: ❬ZL❭ = ❬Cp❭)
      (Len4: ❬ZL❭ = ❬Rch❭)
      (LINV:(forall n aY Z Γ Z' b, get ZL n Z
                              -> get ΓL n Γ

                              -> get Cp n (Z',aY)
                              -> get Rch n b
                              -> aY = lookup_list AE Z /\ Z' = Z
                                /\ Γ [=]
                                    if b then cp_eqns AE (of_list Z)
                                    else singleton EqnBot))
  :  eqn_sound ZL ΓL s (constantPropagate AE s)
               (if getAnn r then cp_eqns AE (IL.freeVars s)
                else singleton EqnBot) ang.
Proof.
  general induction CP;
    invt renamedApart; invt labelsDefined; invt reachability; simpl.
  - simpl in *.
    destruct e.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
        repeat cases; pe_rewrite; eauto using entails_empty.
        -- assert (IL.freeVars s ⊆ IL.freeVars s \ singleton x ∪ singleton x). {
             clear_all. cset_tac.
           }
           rewrite cp_eqns_union. rewrite H0 at 2.
           rewrite cp_eqns_union.
           eapply entails_union; split.
           ++ eapply entails_subset. clear_all. cset_tac.
           ++ rewrite <- incl_right.
             eapply op_eval_entails_eqns; eauto.
        -- eapply entails_bot. cset_tac.
        -- eapply entails_bot. cset_tac.
      * cases.
        -- eapply cp_choose_approx; eauto.
           clear_all. cset_tac.
        -- eapply entails_bot; eauto.
    + econstructor. set_simpl.
      * eapply eqn_sound_entails_monotone; eauto.
         repeat cases; pe_rewrite; eauto using entails_empty.
        -- assert (IL.freeVars s ⊆ IL.freeVars s \ singleton x ∪ singleton x). {
             clear_all. cset_tac.
           }
           rewrite cp_eqns_union. rewrite H0 at 2.
           rewrite cp_eqns_union.
           eapply entails_union; split.
           ++ eapply entails_subset. cset_tac.
           ++ eapply op_eval_entails_eqns_Top; eauto.
             symmetry; eauto.
        -- eapply entails_bot. cset_tac.
        -- eapply entails_bot. cset_tac.
      * cases.
        -- eapply cp_choose_approx_list; eauto.
           clear_all. cset_tac.
        -- eapply entails_bot; eauto.
      * simpl in *. rewrite <- H4.
        eapply list_union_incl; eauto with cset.
        intros; inv_get.
        eapply cp_choose_exp_freeVars; eauto.
        eapply incl_list_union; eauto with get.
      * eauto with len.
  - econstructor; intros; eauto.
    + {
        cases. simpl_isComplete.
        - eapply eqn_sound_EqnEq.
          + rewrite <- incl_right. reflexivity.
          + unfold ConstantPropagationSound.cop2bool in *.
            rewrite <- op_eval_aval2bool in *.
            intros EQ. rewrite <- EQ in H15. simpl in H15.
            exploit H15. intro. clear_trivial_eqs. inv H.
            repeat cases; intros; clear_trivial_eqs.
            * eapply eqn_sound_entails_monotone; eauto.
              cases.
              pe_rewrite.
              rewrite !cp_eqns_union.
              eapply entails_subset. clear_all. cset_tac.
        - eapply eqn_sound_entails_monotone; eauto.
          eapply entails_bot. cset_tac.
      }
    + {
        cases. simpl_isComplete.
        - eapply eqn_sound_EqnEq.
          + rewrite <- incl_right. reflexivity.
          + unfold ConstantPropagationSound.cop2bool in *.
            rewrite <- op_eval_aval2bool in *.
            intros EQ. rewrite <- EQ in H16. simpl in H16.
            exploit H16. intro. clear_trivial_eqs. inv H.
            repeat cases; intros; clear_trivial_eqs.
            * eapply eqn_sound_entails_monotone; eauto.
              cases.
              pe_rewrite.
              rewrite !cp_eqns_union.
              eapply entails_subset. clear_all. cset_tac.
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
      * rewrite H11. cases.
        eapply entails_cp_eqns_subst_choose; eauto.
      * eapply entails_bot; eauto. cset_tac.
    + cases.
      * eapply cp_choose_approx_list; eauto.
      * eapply entails_bot; eauto.
  - econstructor; cases; eauto using cp_choose_approx, entails_bot.
  - assert (INV:forall (n : nat) aY (Z : params) (Γ : ⦃eqn⦄) Z' b,
               get (fst ⊝ F ++ ZL) n Z ->
               get ((fun '(Z1, _) (x:ann bool) => if getAnn x then cp_eqns AE (of_list Z1) else
                    singleton EqnBot) ⊜ F rF ++ ΓL) n Γ ->
               get ((fun Zs : params * stmt => (fst Zs, lookup_list AE (fst Zs))) ⊝ F ++ Cp) n (Z', aY) ->
               get (getAnn ⊝ rF ++ Rch) n b ->
               (aY = lookup_list AE Z /\ Z' = Z /\
                       Γ [=] if b then cp_eqns AE (of_list Z) else singleton EqnBot)). {
      intros.
      eapply get_app_cases in H1. destruct H1; dcr.
      - inv_get. split; eauto. split; eauto.
        rewrite get_app_lt in H2; eauto with len.
        inv_get.
        destruct x; try reflexivity.
      - len_simpl.
        rewrite get_app_ge in H11;[| eauto with len].
        rewrite get_app_ge in H13;[| eauto with len].
        rewrite get_app_ge in H2;[| eauto with len].
        len_simpl. rewrite rfLen in *.
        edestruct LINV; dcr; eauto.
        len_simpl. rewrite <- rfLen. eauto with len.
    }
    eapply EqnFun with (ΓF:=(fun '(Z1, _) (x:ann bool) => if getAnn x then cp_eqns AE (of_list Z1) else singleton EqnBot) ⊜ F rF).
    + eauto with len.
    + eauto with len.
    + intros; inv_get; eauto.
    + intros; inv_get; eauto.
      exploit H0; eauto.
      * eauto with len.
      * eauto with len.
      * eauto with len.
      * repeat cases in H2; pe_rewrite; eauto.
        -- edestruct H5; eauto; dcr; eauto with len.
           simpl in *.
           (* rewrite H14 in H2. rewrite cp_eqns_union in H2. *)
           cases; eauto.
           ++ exploit H4; eauto.
             eapply eqn_sound_entails_monotone; eauto.
             eapply entails_incl.
             rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
             simpl. rewrite cp_eqns_union.
             assert (IL.freeVars s ⊆ IL.freeVars s \ of_list Z ∪ of_list Z). {
               clear. cset_tac.
             }
             rewrite H20 at 1. rewrite cp_eqns_union.
             clear. cset_tac.
           ++ exploit H4; eauto.
             eapply eqn_sound_entails_monotone; eauto.
             eapply entails_bot.
             clear_all. cset_tac.
        -- edestruct H5; eauto; dcr; eauto with len.
           cases; eauto.
           ++ exploit H4; eauto.
             eapply eqn_sound_entails_monotone; eauto.
             eapply entails_incl.
             rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
           ++ exploit H4; eauto.
             eapply eqn_sound_entails_monotone; eauto.
             eapply entails_bot.
             clear_all. cset_tac.
    + eapply eqn_sound_entails_monotone.
      * eauto.
      * eapply IHCP; eauto with len.
      * cases; eauto.
        -- cases.
           ++ eapply entails_subset.
             rewrite !cp_eqns_union.
             clear. cset_tac.
           ++ simpl in *. invc H18.
        -- eapply entails_bot. cset_tac.
    + intros; inv_get; destruct Zs; simpl.
      cases.
      * rewrite cp_eqns_freeVars. eapply incl_right.
      * rewrite eqns_freeVars_singleton. simpl.
        eauto with cset.
Qed.

Require Import CMap.

Lemma cp_eqns_no_assumption d G
: (forall x : var,
   x \In G -> MapInterface.find x d === ⎣Top⎦)
   -> cp_eqns (fun x0 : var => MapInterface.find x0 d) G [=] ∅.
Proof.
  intros. revert H. pattern G. eapply set_induction.
  - intros.
    eapply empty_is_empty_1 in H. rewrite H.
    reflexivity.
  - intros. eapply Add_Equal in H1. rewrite H1.
    rewrite cp_eqns_add.
    unfold cp_eqn.
    exploit (H2 x).
    + rewrite H1. cset_tac.
    + rewrite H.
      * invc H3. invc H6. cset_tac.
      * intros; eapply H2.
        rewrite H1. cset_tac.
Qed.
