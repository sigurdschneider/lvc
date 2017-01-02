Require Import CSet Le.

Require Import Plus Util AllInRel Map MapUpdate MapDefined.
Require Import Val Var Env IL Annotation InRel SimI Fresh.
Require Import Liveness Status.
Require CompCert.Parmov.

Set Implicit Arguments.
Unset Printing Records.


(** * Parallel Moves

   This code is based on the ril-cv-12 repo and the validator
   part its initial version was developed by Tobias Tebbi.
*)

Definition pmov := list (var * var).

Definition pmov_source_set (p:pmov) : set var
  := fold_right (fun p s => s \ singleton (fst p) ∪ singleton (snd p)) ∅ p.

Lemma pmov_source_set_incl p
  : pmov_source_set p ⊆ of_list (snd ⊝ p).
Proof.
  general induction p; simpl.
  - eauto with cset.
  - rewrite IHp; clear. cset_tac.
Qed.

Section Parallel_Move.
  Variable X:Type.
  Context `{OrderedType X}.

  Fixpoint upd_list p M : env X :=
    match p with
      | nil => M
      | (l1, l2) :: p' => upd_list p' (M[ l1 <- M l2])
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

  (*
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
    simpl. cases; lud; intuition.
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
    specialize (H0 x H1); simpl in *.
    cases in H0; simpl in *; try congruence.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
    erewrite symb_eval with (M1:=M) (f:=fun x => x); eauto.
    intuition.
  Qed.

  Definition check_source_set (p1 p2 : pmov) :=
    if [ pmov_source_set p1 ⊆ pmov_source_set p2 ] then true else false.

  Lemma check_source_set_correct p1 l1 l2
    (COK:check_source_set p1 ((l1,l2)::nil)) (M : onv X)
    (Src:forall x : var, x \In of_list l2 -> M x <> ⎣⎦)
    : forall x : var, x \In pmov_source_set p1 -> M x <> ⎣⎦.
  Proof.
    unfold check_source_set in COK. cases in COK; isabsurd.
    simpl in *.
    intros. eapply Src. rewrite COND in H0. cset_tac; intuition.
  Qed.

  End Translate.
*)
End Parallel_Move.

Notation "f [ // p ]" := (upd_list p f) (at level 29, left associativity).

Section GlueCode.
  Fixpoint list_to_stmt (p : list (var * var)) (s : stmt) {struct p} : stmt :=
    match p with
      | nil => s
      | (x, y) :: p' => stmtLet x (Operation (var_to_op y)) (list_to_stmt p' s)
    end.

  Lemma list_to_stmt_correct (p:pmov) s (M:onv val) K
        (Def:defined_on (pmov_source_set p) M)
    : star2 I.step (K, M, list_to_stmt p s) nil
        (K, M [ // p ], s).
  Proof.
    general induction p.
    - firstorder using star2.
    - destruct a as [x y]. simpl in *.
      edestruct (Def y); eauto with cset.
      exploit (var_to_op_correct M y).
      eapply star2_silent.
      + constructor; eauto.
      + rewrite H.
        eapply IHp; eauto using defined_on_update_some,
                    defined_on_incl with cset.
  Qed.

  Hypothesis parallel_move : var -> list var -> list var -> (list(var * var)).

  Definition linearize_parallel_assignment (vars:set var) (l1 l2:list var) :=
    parallel_move (least_fresh vars) l1 l2.

End GlueCode.

Section Implementation.
Fixpoint onlyVars (Y:args) : status params :=
  match Y with
    | nil => Success nil
    | (Var x)::Y => sdo Y' <- onlyVars Y; Success (x::Y')
    | _ => Error "onlyVars: argument list contains expressions"
  end.

Lemma onlyVars_defined (E:onv val) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (op_eval E) Y = Some v
    -> forall x, x ∈ of_list Y' -> E x <> None.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - inv H; simpl in *. cset_tac; intuition.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *.
    cset_tac; congruence.
Qed.

Lemma onlyVars_defined_on (E:onv val) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (op_eval E) Y = Some v
    -> defined_on (of_list Y') E.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - inv H; simpl in *. hnf; cset_tac.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *.
    exploit IHY; eauto.
    hnf; cset_tac.
Qed.

Lemma onlyVars_lookup (E:onv val) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (op_eval E) Y = Some v
    -> lookup_list E Y' = List.map Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - inv H; eauto.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *. inv EQ0. f_equal; eauto.
Qed.

Fixpoint lower (DL:〔⦃nat⦄ * params〕) s (an:ann (set var))
  : status stmt :=
  match s, an with
    | stmtLet x e s, ann1 lv ans =>
      sdo sl <- lower DL s ans;
        Success (stmtLet x e sl)
    | stmtIf x s t, ann2 lv ans ant =>
      sdo sl <- lower DL s ans;
        sdo tl <- lower DL t ant;
            Success (stmtIf x sl tl)
    | stmtApp l Y, ann0 lv  =>
       sdo Lve <- option2status (nth_error DL (counted l)) "lower: No annotation for function";
        sdo Y <- onlyVars Y;
        let '(lv', Z) := Lve in
        let mvs := Parmov.parmove2 var Nat.eq_dec (fun _ => (least_fresh lv')) Z Y in
        Success (list_to_stmt mvs (stmtApp l nil))

    | stmtReturn x, ann0 lv => Success (stmtReturn x)
    | stmtFun F t, annF lv ans ant =>
      let DL' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) in
      sdo s' <- szip (fun Zs a => lower (DL' ++ DL) (snd Zs) a) F ans;
        sdo t' <- lower (DL' ++ DL) t ant;
        Success (stmtFun ((fun s => (nil, s)) ⊝ s') t')
    | s, _ => Error "lower: Annotation mismatch"
  end.

Inductive approx
: list (set var) -> list I.block -> list I.block -> ⦃var⦄ -> I.block -> I.block -> Prop :=
  approxI L L' DL Z s s' lv n
  (al:ann (set var))
  (LS:live_sound Imperative (I.block_Z ⊝ L) DL s al)
  (AL:(of_list Z) ⊆ lv)
  (INCL:getAnn al \ of_list Z ⊆ lv)
  (spm:lower (zip pair DL (I.block_Z ⊝ L)) s al = Success s')
  : approx DL L L' lv (I.blockI Z s n) (I.blockI nil s' n).


Lemma correct Lv s (E E':onv val) L L' s' (al: ann (set var))
 (LS:live_sound Imperative (I.block_Z ⊝ L) Lv s al)
 (pmlowerOk:lower (zip pair Lv (I.block_Z ⊝ L))  s al = Success s')
 (LA:inRel approx Lv L L')
 (EEQ:agree_on eq (getAnn al) E E')
  : sim bot3 Sim (L,E,s) (L', E', s').
Proof.
  revert_all. pcofix pmSim_sim; intros.
  inv LS; simpl in *; try monadS_inv pmlowerOk.
  - invt live_exp_sound.
    + eapply (sim_let_op il_statetype_I);
        eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
    + eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_cond il_statetype_I);
      eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
  - eapply option2status_inv in EQ. eapply nth_error_get in EQ.
    inRel_invs.
    inv_get. simpl in *. invc EQ2.
    case_eq (omap (op_eval E) Y); intros.
    + exploit omap_op_eval_live_agree; try eassumption.
      exploit (@list_to_stmt_correct
                 (Parmov.parmove2 nat Nat.eq_dec (fun _ : nat => least_fresh blv) Z0 x0)
                 (stmtApp l nil) E' L').
      admit.
      pfold. eapply SimSilent.
      * eapply plus2O. econstructor; eauto. simpl. reflexivity.
      * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
        eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
      * right; eapply pmSim_sim; try eapply LA1; eauto; simpl.
        -- eapply (inRel_drop LA H4).
        -- assert (getAnn al ⊆ blv) by eauto with cset.
           admit.
           (*eapply agree_on_incl in X''; eauto. symmetry in X''. simpl.
           eapply agree_on_trans; eauto.
           erewrite onlyVars_lookup; eauto.
           eapply update_with_list_agree; eauto with len.
           eapply agree_on_incl; eauto. eauto with cset.*)
    + perr.
  - pno_step. simpl. eauto using op_eval_live.
  - pone_step.
    right; eapply pmSim_sim; eauto using agree_on_incl.
    econstructor; eauto.
    eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
    intros; inv_get.
    econstructor; eauto.
    + exploit H2; eauto.
    + exploit szip_get; try eapply EQ; eauto.
Admitted.

End Implementation.
