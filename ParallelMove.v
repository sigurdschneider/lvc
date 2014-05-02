Require Import List Compare_dec.
Require Import AllInRel Option Util Var IL Annotation EnvTy EqDec AutoIndTac Sim Fresh Liveness Status.

Set Implicit Arguments.

(** * Parallel Moves

   This code is based from the ril-cv-12 repo and the validator 
   part was initially developed by Tobias Tebbi.
*)

Definition pmov := list (list var * list var).

Section Parallel_Move.
  Fixpoint upd_list p M : env val := 
    match p with
      | nil => M
      | (l1, l2) :: p' => upd_list p' (updE M M l1 l2) 
    end.

  Fixpoint par_move (E E': var -> var) (Z : params) (Y : args)
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

  Lemma par_move_eq (M1 M2 MC:env val) f fC Z Y
    :  (forall y : var, MC y = M1 (fC y))
    -> (forall y : var, M2 y = M1 (f y))
    -> forall y : var, updE M2 MC Z Y y = (M1 (par_move f fC Z Y y)).
  Proof.
    general induction Z; destruct Y; isabsurd; eauto.
    unfold updE. simpl. destruct if; lud; intuition.
    eapply IHZ; eauto.
  Qed.

  Lemma symb_eval p (M1 M2 : env val) f 
    :  (forall y, M2 y = (M1 (f y))) 
    -> forall x, upd_list p M2 x = (M1 (par_list p f x)).
  Proof.
    general induction p; simpl; eauto.
    destruct a; simpl; eauto; intros. 
    erewrite IHp. reflexivity. 
    eapply par_move_eq; simpl in *; firstorder. 
  Qed.

  Corollary symb_eval_id : forall p (M : env val) x,
    upd_list p M x = (M (par_list p (fun x => x) x)).
  Proof.
    intros. eapply symb_eval; eauto. 
  Qed.

  Lemma check_pmove_correct {vars} {p1} {p2}
    (COK:check_pmove vars p1 p2) (M : env val)
    : agree_on vars (upd_list p1 M) (upd_list p2 M).
  Proof.
    assert (check_pmove vars p1 p2 = true) by cbool. clear COK.
    unfold agree_on,check_pmove in *; intros.
    rewrite <- for_all_iff in H; auto; try intuition.
    specialize (H x H0); simpl in *. destruct if in H; firstorder.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
  Qed.

End Translate.

Section GlueCode.
  Function list_to_stmt (p : list (list var * list var)) (s : stmt) {struct p} : stmt :=
    match p with
      | nil => s
      | (x :: nil, y:: nil) :: p' => stmtExp x (var_to_exp y) (list_to_stmt p' s)
      | _ => s
    end.

  Lemma list_to_stmt_correct p s :
    (forall ass, List.In ass p -> exists x, exists y, ass = (x :: nil, y :: nil)) ->
    forall M K, star I.step (K, M, list_to_stmt p s) (K, upd_list p M, s).
  Proof.
    general induction p. firstorder using star.
    pose proof (H a). assert (List.In a (a :: p)). crush.
    specialize (H0 H1). destruct H0. destruct H0.
    subst. simpl. refine (S_star _ _ _ ).
    constructor. eapply var_to_exp_correct. eapply IHp. intros. apply H. crush.
  Qed.

  Definition max a b := if le_dec a b then b else a.
  
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
    check_is_simple_ass p /\ check_pmove vars p ((l1, l2) :: nil).


  Lemma validate_parallel_assignment_correct vars p l1 l2
    (VOK:validate_parallel_assignment vars p l1 l2)
    : forall M K cont, exists M',
        star I.step (K, M, list_to_stmt p cont) (K, M', cont) /\
        agree_on vars M' (updE M M l1 l2).
  Proof.
    unfold validate_parallel_assignment in *; destruct VOK; intros.
    eexists; split.
    eauto using list_to_stmt_correct, check_is_simple_ass_correct.
    eapply (check_pmove_correct H0).
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
      forall M K, exists M',
        star I.step (K, M, s') (K, M', s) /\
        agree_on vars M' (updE M M l1 l2).
  Proof.
    unfold compile_parallel_assignment; intros.
    destruct if in *. inv H.
    eapply validate_parallel_assignment_correct; eauto.
    discriminate.
  Qed.

End GlueCode.

End Parallel_Move.

Section Implementation.
  Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).

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
        let '(lv', Z) := Lve in
        compile_parallel_assignment parallel_move lv' Z Y (stmtGoto l nil)

    | stmtReturn x, ann0 lv => Success (stmtReturn x)
    | stmtLet Z s t, ann2 lv ans ant => 
      let DL' := (getAnn ans,Z) in
      sdo s' <- lower (DL' :: DL)%list s ans;
        sdo t' <- lower (DL' :: DL)%list t ant;
        Success (stmtLet nil s' t')
    | s, _ => Error "lower: Annotation mismatch"
  end.

Inductive approx 
: list (set var * list var) -> I.block -> I.block -> Prop :=
  approxI Lv s Z lv s'
  (al:ann (set var))
  (LS:live_sound ((lv,Z)::Lv) s al)
  (AL:(of_list Z) ⊆ lv)
  (EQ:getAnn al \ of_list Z ⊆ lv)
  (spm:lower ((lv,Z)::Lv) s al = Success s')
  : approx ((lv,Z)::Lv) (I.blockI Z s) (I.blockI nil s').

Inductive pmSim : I.state -> I.state -> Prop :=
  pmSimI Lv s (E E':env var) L L' s'
  (al: ann (set var))
  (LS:live_sound Lv s al) (pmlowerOk:lower Lv s al = Success s')
  (LA:AIR3 approx Lv L L')
  (EEQ:agree_on (getAnn al) E E')
  : pmSim (L,E,s) (L', E', s').

Lemma pmSim_sim σ1 σ2
: pmSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  inv H; inv LS; simpl in *; try monadS_inv pmlowerOk.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. 
    erewrite exp_eval_live; eauto. 
    eapply agree_on_incl; eauto using agree_on_sym. reflexivity.
    eapply pmSim_sim; econstructor; eauto.
    eapply agree_on_update_same; eauto using agree_on_incl.
    eapply simE; try eapply star_refl; eauto; stuck. 
    erewrite <- exp_eval_live in H3; eauto using live_freeVars; simpl in *.
    erewrite H3 in def. congruence. eapply agree_on_incl; eauto using agree_on_sym.
    reflexivity.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto.
    econstructor; eauto. rewrite <- EEQ; eauto.
    eapply pmSim_sim; econstructor; eauto using agree_on_incl.
    eapply simS; try eapply plusO. 
    eapply I.stepIfF; eauto.
    eapply I.stepIfF; eauto. rewrite <- EEQ; eauto.
    eapply pmSim_sim; econstructor; eauto using agree_on_incl.
  + eapply option2status_inv in EQ. eapply nth_error_get in EQ.
    get_functional; subst.
    provide_invariants_3.
    edestruct (compile_parallel_assignment_correct _ _ _ _ _ EQ0 E' L') 
      as [M' [X' X'']].
    eapply simS.
    econstructor. econstructor; eauto. simpl; eauto.
    eapply star_plus_plus; eauto. eapply plusO. econstructor; eauto.
    eauto. 
    eapply pmSim_sim; econstructor; try eapply LA1; eauto.
    unfold updE. simpl.
    erewrite lookup_list_agree; eauto using agree_on_incl.
    eapply agree_on_trans. eapply update_with_list_agree. 
    eapply agree_on_incl; eauto. cset_tac; intuition.
    rewrite lookup_list_length; eauto. 
    unfold updE in X''. eapply agree_on_sym.
    eapply agree_on_incl. eapply X''. cset_tac; intuition.
    decide (a ∈ of_list Z0); cset_tac; intuition.

  + eapply simE; try eapply star_refl; simpl; try stuck.
    rewrite EEQ; eauto.
  + eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. 
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


