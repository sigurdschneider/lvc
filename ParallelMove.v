Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Sim Fresh Liveness Status MoreExp.

Set Implicit Arguments.

(** * Parallel Moves

   This code is based on the ril-cv-12 repo and the validator
   part its initial version was developed by Tobias Tebbi.
*)

Definition pmov := list (list var * list var).

Definition pmov_source_set (p:pmov) : set var
  := fold_right (fun p s => s \ of_list (fst p) ∪ of_list (snd p)) ∅ p.

Section Parallel_Move.
  Variable X:Type.
  Context `{OrderedType X}.

  Fixpoint upd_list p M : env X :=
    match p with
      | nil => M
      | (l1, l2) :: p' => upd_list p' (M[ l1 <-- lookup_list M l2])
    end.

  Fixpoint par_move (E E': var -> var) (Z : params) (Y : params)
    : var -> var :=
    match Z, Y with
      | nil, nil  => E
      | y::Z', a :: Y' =>
        (fun x => if [ x = y ] then E' a else par_move E E' Z' Y' x)
      | _, _ => E
    end.

  Fixpoint par_list p M :=
    match p with
      | nil => M
      | (l1, l2) :: p' => par_list p' (par_move M M l1 l2)
    end.

Section Translate.

  Definition check_pmove (vars : set var) (p1 p2 : pmov) :=
    let M1 := par_list p1 (fun x => x) in
    let M2 := par_list p2 (fun x => x) in
      for_all
        (fun x => if [M1 x = M2 x] then true else false) vars.
  Hint Unfold check_pmove.

  Lemma par_move_eq (M1 M2 MC:env X) f fC Z Y
    :  (forall y : var, MC y = M1 (fC y))
    -> (forall y : var, M2 y = M1 (f y))
    -> forall y : var, M2 [ Z <-- (lookup_list MC Y) ] y = (M1 (par_move f fC Z Y y)).
  Proof.
    general induction Z; destruct Y; isabsurd; eauto.
    simpl. destruct if; lud; intuition.
  Qed.

  Lemma symb_eval p (M1 M2 : env X) f
    :  (forall y, M2 y = (M1 (f y)))
    -> forall x, upd_list p M2 x = (M1 (par_list p f x)).
  Proof.
    general induction p; simpl; eauto.
    destruct a; simpl; eauto; intros.
    erewrite IHp; eauto.
    intros. erewrite <- par_move_eq; simpl in *; eauto.
  Qed.

  Corollary symb_eval_id : forall p (M : env X) x,
    upd_list p M x = (M (par_list p (fun x => x) x)).
  Proof.
    intros. eapply symb_eval; eauto.
  Qed.

  Lemma check_pmove_correct {vars} {p1} {p2}
    (COK:check_pmove vars p1 p2) (M : env X)
    : agree_on eq vars (upd_list p1 M) (upd_list p2 M).
  Proof.
    assert (check_pmove vars p1 p2 = true) by cbool. clear COK.
    unfold agree_on,check_pmove in *; intros.
    eapply (@for_all_2 var _ _ _ vars) in H0.
    specialize (H0 x H1); simpl in *. destruct if in H; simpl in *.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
    intuition.
    intuition.
  Qed.

  Definition check_source_set (p1 p2 : pmov) :=
    if [ pmov_source_set p1 ⊆ pmov_source_set p2 ] then true else false.

  Lemma check_source_set_correct p1 l1 l2
    (COK:check_source_set p1 ((l1,l2)::nil)) (M : onv X)
    (Src:forall x : var, x \In of_list l2 -> M x <> ⎣⎦)
    : forall x : var, x \In pmov_source_set p1 -> M x <> ⎣⎦.
  Proof.
    unfold check_source_set in COK. destruct if in COK; isabsurd.
    simpl in *.
    intros. eapply Src. rewrite s in H0. cset_tac; intuition.
  Qed.

  End Translate.

End Parallel_Move.

Section GlueCode.
  Function list_to_stmt (p : list (list var * list var)) (s : stmt) {struct p} : stmt :=
    match p with
      | nil => s
      | (x :: nil, y:: nil) :: p' => stmtExp x (var_to_exp y) (list_to_stmt p' s)
      | _ => s
    end.

  Lemma list_to_stmt_correct p s :
    (forall ass, List.In ass p -> exists x, exists y, ass = (x :: nil, y :: nil)) ->
    forall M,
    (forall x, x ∈ pmov_source_set p -> M x <> None) ->
    forall K, star2 I.step (K, M, list_to_stmt p s) nil (K, upd_list p M, s).
  Proof.
    general induction p. firstorder using star2.
    pose proof (H a). assert (List.In a (a :: p)). crush.
    destruct (H1 H2) as [? [? ?]].
    subst. simpl.
    exploit (var_to_exp_correct M x0).
    exploit (H0 x0); eauto. simpl. cset_tac; intuition.
    destruct (M x0); isabsurd.
    refine (S_star2 (yl:=nil) EvtTau _ _ _).
    constructor; eauto. eapply IHp. intros. apply H. crush.
    intros. lud. eauto. eapply H0; try reflexivity.
    simpl. cset_tac; intuition.
  Qed.

  Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).

  Definition linearize_parallel_assignment (vars:set var) (l1 l2:list var) :=
    parallel_move (least_fresh vars) l1 l2.

  Function check_is_simple_ass (p : list(list var * list var)) {struct p} : bool :=
    match p with
      | nil => true
      | (_ :: nil, _ :: nil):: p' => check_is_simple_ass p'
      | _ => false
    end.

  Lemma check_is_simple_ass_correct (p : list (list var * list var)) :
    check_is_simple_ass p ->
    forall ass, List.In ass p -> exists x, exists y, ass = (x :: nil, y :: nil).
  Proof.
    functional induction (check_is_simple_ass p); crush.
  Qed.

  Definition validate_parallel_assignment vars p l1 l2 :=
    check_is_simple_ass p
    /\ check_pmove vars p ((l1, l2) :: nil)
    /\ check_source_set p ((l1, l2) :: nil).


  Lemma validate_parallel_assignment_correct vars p l1 l2
    (VOK:validate_parallel_assignment vars p l1 l2)
    : forall M K cont (Src:forall x : var, x \In of_list l2 -> M x <> ⎣⎦), exists M',
        star2 I.step (K, M, list_to_stmt p cont) nil (K, M', cont) /\
        agree_on eq vars M' (M[ l1 <-- lookup_list M l2]).
  Proof.
    unfold validate_parallel_assignment in *; dcr; intros.
    eexists; split.
    eapply list_to_stmt_correct; eauto.
    eapply check_is_simple_ass_correct; eauto.
    eapply check_source_set_correct; eauto.
    eapply (check_pmove_correct H1 M).
  Qed.

  Definition compile_parallel_assignment
    (vars:set var)  (l1 l2 : list var) (s : stmt) : status stmt :=
    let p := linearize_parallel_assignment vars l1 l2 in
    if [validate_parallel_assignment vars p l1 l2] then
      Success (list_to_stmt p s) else
        Error "compile parallel assignment failed".

  Lemma compile_parallel_assignment_correct
    : forall vars l1 l2 s s',
      compile_parallel_assignment vars l1 l2 s = Success s' ->
      forall M K (Src:forall x : var, x \In (of_list l2) -> M x <> ⎣⎦), exists M',
        star2 I.step (K, M, s') nil (K, M', s) /\
        agree_on eq vars M' (M[ l1 <-- lookup_list M l2]).
  Proof.
    unfold compile_parallel_assignment; intros.
    destruct if in H; try discriminate. inv H.
    eapply validate_parallel_assignment_correct; eauto.
  Qed.

End GlueCode.

Section Implementation.
  Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).

Fixpoint onlyVars (Y:args) : status params :=
  match Y with
    | nil => Success nil
    | (Var x)::Y => sdo Y' <- onlyVars Y; Success (x::Y')
    | _ => Error "onlyVars: argument list contains expressions"
  end.

Lemma onlyVars_defined (E:onv var) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (exp_eval E) Y = Some v
    -> forall x, x ∈ of_list Y' -> E x <> None.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - cset_tac; intuition.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *.
    cset_tac. destruct H1.
    + hnf in H; subst. congruence.
    + eapply IHY; eauto.
Qed.

Lemma onlyVars_lookup (E:onv var) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (exp_eval E) Y = Some v
    -> lookup_list E Y' = List.map Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  destruct a; isabsurd. monadS_inv H. monad_inv H0.
  simpl in * |- *. inv EQ0. f_equal; eauto.
Qed.

Fixpoint lower DL s (an:ann (set var))
  : status stmt :=
  match s, an with
    | stmtExp x e s, ann1 lv ans =>
      sdo sl <- lower DL s ans;
        Success (stmtExp x e sl)
    | stmtIf x s t, ann2 lv ans ant =>
      sdo sl <- lower DL s ans;
        sdo tl <- lower DL t ant;
            Success (stmtIf x sl tl)
    | stmtGoto l Y, ann0 lv  =>
       sdo Lve <- option2status (nth_error DL (counted l)) "lower: No annotation for function";
        sdo Y <- onlyVars Y;
        let '(lv', Z) := Lve in
        compile_parallel_assignment parallel_move lv' Z Y (stmtGoto l nil)

    | stmtReturn x, ann0 lv => Success (stmtReturn x)
    | stmtExtern x f Y s, ann1 _ ans =>
      sdo sl <- lower DL s ans;
        Success (stmtExtern x f Y sl)
    | stmtFun Z s t, ann2 lv ans ant =>
      let DL' := (getAnn ans,Z) in
      sdo s' <- lower (DL' :: DL)%list s ans;
        sdo t' <- lower (DL' :: DL)%list t ant;
        Success (stmtFun nil s' t')
    | s, _ => Error "lower: Annotation mismatch"
  end.

Inductive approx
: list (set var * list var) -> I.block -> I.block -> Prop :=
  approxI Lv s Z lv s'
  (al:ann (set var))
  (LS:live_sound Imperative ((lv,Z)::Lv) s al)
  (AL:(of_list Z) ⊆ lv)
  (EQ:getAnn al \ of_list Z ⊆ lv)
  (spm:lower ((lv,Z)::Lv) s al = Success s')
  : approx ((lv,Z)::Lv) (I.blockI Z s) (I.blockI nil s').

Inductive pmSim : I.state -> I.state -> Prop :=
  pmSimI Lv s (E E':onv val) L L' s'
  (al: ann (set var))
  (LS:live_sound Imperative Lv s al)
  (pmlowerOk:lower Lv s al = Success s')
  (LA:AIR3 approx Lv L L')
  (EEQ:agree_on eq (getAnn al) E E')
  : pmSim (L,E,s) (L', E', s').

Lemma pmSim_sim σ1 σ2
: pmSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H; inv LS; simpl in *; try monadS_inv pmlowerOk.
  - case_eq (exp_eval E e); intros.
    one_step.
    erewrite <- exp_eval_live; eauto.
    eapply pmSim_sim; econstructor; eauto.
    eapply agree_on_update_same; eauto using agree_on_incl.
    no_step. erewrite <- exp_eval_live in def; eauto. congruence.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_live_agree; try eassumption.
    case_eq (val2bool v); intros.
    + one_step.
      eapply pmSim_sim; econstructor; eauto using agree_on_incl.
    + one_step.
      eapply pmSim_sim; econstructor; eauto using agree_on_incl.
    + exploit exp_eval_live_agree; try eassumption.
      no_step.
  - eapply option2status_inv in EQ. eapply nth_error_get in EQ.
    get_functional; subst.
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; try eassumption.
      provide_invariants_3.
      edestruct (compile_parallel_assignment_correct _ _ _ _ _ EQ2 E' L')
        as [M' [X' X'']].
      eapply onlyVars_defined; eauto.
      eapply simSilent.
      * eapply plus2O. econstructor; eauto. reflexivity.
      * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
        eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
      * eapply pmSim_sim; econstructor; try eapply LA1; eauto. simpl.
        assert (getAnn al ⊆ lv0). {
          revert AL EQ0; clear_all. cset_tac; intuition; eauto.
          decide (a ∈ of_list Z0); eauto. cset_tac; intuition.
        }
        eapply agree_on_incl in X''; eauto. symmetry in X''.
        eapply agree_on_trans; eauto. eapply equiv_transitive.
        erewrite onlyVars_lookup; eauto.
        eapply update_with_list_agree.
        eapply eq_equivalence.
        eapply agree_on_incl; eauto. cset_tac; intuition.
        exploit omap_length; eauto. rewrite map_length. congruence.
    + err_step.
  - no_step. simpl. eauto using exp_eval_live.
  - remember (omap (exp_eval E) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; try eassumption.
    destruct o.
    + extern_step.
      * eexists; split. econstructor; eauto. congruence.
        eapply pmSim_sim; econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
      * eexists; split. econstructor; eauto. congruence.
        eapply pmSim_sim; econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
    + no_step.
  - one_step.
    eapply pmSim_sim. econstructor; eauto.
    econstructor; eauto. econstructor; eauto using minus_incl.
    eapply agree_on_incl; eauto.
Qed.

End Implementation.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
