Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Bisim Infra.Status Pos SmallStepCommon.

Set Implicit Arguments.

Inductive bstmt : Type :=
| bstmtLet    (e: exp) (s : bstmt)
| bstmtIf     (e : exp) (s : bstmt) (t : bstmt)
| bstmtApp    (l : lab) (Y:args)
| bstmtReturn (e : exp)
| bstmtExtern (f : external) (Y:args) (s:bstmt)
| bstmtFun    (F : list (nat * bstmt)) (t : bstmt).

Fixpoint exp_eval (E:list val) (e:exp) : option val :=
  match e with
    | Con v => Some v
    | Var x => nth_error E x
    | UnOp o e => mdo v <- exp_eval E e;
        unop_eval o v
    | BinOp o e1 e2 => mdo v1 <- exp_eval E e1;
        mdo v2 <- exp_eval E e2;
        binop_eval o v1 v2
  end.

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
      block_E : list val;
      block_Z : nat;
      block_s : bstmt;
      block_n : nat
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * list val * bstmt)%type.

  Definition mkBlock E n f :=
    blockI E (fst f) (snd f) n.

  Definition mkBlocks E F :=
    mapi (mkBlock E) F.

  Inductive step : state -> event -> state -> Prop :=
  | stepExp L E e b v
    (def:exp_eval E e = Some v)
    : step (L, E, bstmtLet e b) EvtTau (L, v::E, b)

  | stepIfT L E
    e b1 b2 v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, bstmtIf e b1 b2) EvtTau (L, E, b1)

  | stepIfF L E
    e b1 b2 v
    (def:exp_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, bstmtIf e b1 b2) EvtTau (L, E, b2)

  | stepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:block_Z blk = length Y)
    (def:omap (exp_eval E) Y = Some vl) E'
    (updOk:(List.app vl  (block_E blk)) = E')
    : step  (L, E, bstmtApp l Y)
            EvtTau
            (drop (counted l - block_n blk) L, E', block_s blk)

  | stepLet L E
    F t
    : step (L, E, bstmtFun F t) EvtTau ((mkBlocks E F++L)%list, E, t)

  | stepExtern L E f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, bstmtExtern f Y s)
            (EvtExtern (ExternI f vl v))
            (L, v::E, s).

  Lemma step_internally_deterministic
  : internally_deterministic step.
  Proof.
    hnf; intros.
    inv H; inv H0; split; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_externally_determined
  : externally_determined step.
  Proof.
    hnf; intros.
    inv H; inv H0; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_dec
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. do 2 eexists. eauto 20 using step.
      right. stuck.
    - case_eq (exp_eval V e); intros.
      left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?].
      decide (block_Z blk = length Y).
      case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      + left. do 2 eexists. econstructor; eauto.
      + right. stuck2.
      + right. stuck2.
    - right. stuck2.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left; eexists (EvtExtern (ExternI f l 0)). eexists; eauto using step.
    - left. eexists. eauto using step.
  Qed.

End F.

Fixpoint exp_idx (symb:list var) (e:exp) : status exp :=
  match e with
    | Con v => Success (Con v)
    | Var x => sdo x <- option2status (pos symb x 0) "labIndices: Undeclared variable";
        Success (Var x)
    | UnOp o e => sdo e <- exp_idx symb e;
        Success (UnOp o e)
    | BinOp o e1 e2 => sdo e1 <- exp_idx symb e1;
        sdo e2 <- exp_idx symb e2;
        Success (BinOp o e1 e2)
  end.

Fixpoint stmt_idx (symb: list var) (s:stmt) : status bstmt :=
  match s with
    | stmtLet x e s =>
      sdo e <- exp_idx symb e;
      sdo s' <- (stmt_idx (x::symb) s); Success (bstmtLet e s')
    | stmtIf e s1 s2 =>
      sdo e <- exp_idx symb e;
      sdo s1' <- (stmt_idx symb s1);
      sdo s2' <- (stmt_idx symb s2);
      Success (bstmtIf e s1' s2')
    | stmtApp l Y =>
      sdo Y <- smap (exp_idx symb) Y;
      Success (bstmtApp l Y)
    | stmtReturn e =>
      sdo e <- exp_idx symb e;
      Success (bstmtReturn e)
    | stmtExtern x f Y s =>
      sdo Y <- smap (exp_idx symb) Y;
      sdo s' <- (stmt_idx (x::symb) s); Success (bstmtExtern f Y s')
    | stmtFun F s2 =>
      sdo F' <- smap (fun sZ => sdo s <- stmt_idx (fst sZ ++ symb) (snd sZ); Success (length (fst sZ), s)) F;
      sdo s2' <- stmt_idx (symb) s2;
      Success (bstmtFun F' s2')
  end.

Definition state_result X (s:X*list val*bstmt) : option val :=
  match s with
    | (_, E, bstmtReturn e) => exp_eval E e
    | _ => None
  end.

Instance statetype_F : StateType F.state := {
  step := F.step;
  result := (@state_result F.labenv);
  step_dec := F.step_dec;
  step_internally_deterministic := F.step_internally_deterministic;
  step_externally_determined := F.step_externally_determined
}.

Lemma exp_idx_ok E E' e e' (symb:list var)
      (Edef:forall x v, E x = Some v -> exists n, get symb n x)
      (Eagr:forall x n, pos symb x 0 = Some n -> exists v, get E' n v /\ E x = Some v)
      (EQ:exp_idx symb e = Success e')
: Exp.exp_eval E e = exp_eval E' e'.
Proof.
  general induction e; eauto; simpl in * |- *; try monadS_inv EQ.
  - eapply option2status_inv in EQ0. simpl.
    exploit Eagr; eauto. dcr.
    rewrite H2. erewrite get_nth_error; eauto.
  - erewrite IHe; eauto. reflexivity.
  - erewrite IHe1; eauto. erewrite IHe2; eauto. reflexivity.
Qed.

Definition vars_exist (E:onv val) symb := forall x v, E x = Some v -> exists n, get symb n x.
Definition defs_agree symb (E:onv val) E' :=
  forall x n, pos symb x 0 = Some n -> exists v, get E' n v /\ E x = Some v.


Inductive approx : IL.F.block -> F.block -> Prop :=
| Approx E (Z:list var) s E' s' symb n :
    stmt_idx (Z ++ symb) s = Success s'
    -> vars_exist E symb
    -> defs_agree symb E E'
    -> approx (IL.F.blockI E Z s n) (F.blockI E' (length Z) s' n).

Inductive stmtIdxSim : IL.F.state -> F.state -> Prop :=
  | labIndicesSimI (L:IL.F.labenv) L' E E' s s' symb
    (EQ:stmt_idx symb s = Success s')
    (LA:PIR2 approx L L')
    (Edef:vars_exist E symb)
    (Eagr:defs_agree symb E E')
  : stmtIdxSim (L, E, s) (L', E', s').

Lemma vars_exist_update (E:onv val) symb x v
: vars_exist E symb
  -> vars_exist (E [x <- ⎣v ⎦]) (x :: symb).
Proof.
  unfold vars_exist; intros.
  lud. invc H1. eexists; eauto using get.
  edestruct H; eauto using get.
Qed.

Lemma vars_exist_update_list (E:onv val) symb Z vl
: length Z = length vl
  -> vars_exist E symb
  -> vars_exist (E [Z <-- List.map Some vl]) (Z ++ symb).
Proof.
  intros; length_equify.
  general induction H; simpl; eauto using vars_exist_update.
Qed.

Lemma defs_agree_update symb E E' x v
: defs_agree symb E E'
  -> defs_agree (x :: symb) (E [x <- ⎣v ⎦]) (v :: E').
Proof.
  unfold defs_agree; intros.
  simpl in H0. cases in H0.
  - invc COND; invc H0.
    eexists; split; eauto using get. lud; congruence.
  - exploit (pos_ge _ _ _ H0).
    edestruct H; eauto; dcr.
    eapply pos_sub with (k':=1).
    orewrite (n = 1 + (n - 1)) in H0. eauto.
    eexists; split; eauto using get. lud; try congruence.
    orewrite (n = S (n -1)). econstructor; eauto.
    lud; eauto.
Qed.

Lemma defs_agree_update_list (E:onv val) E' symb Z vl
: length Z = length vl
  -> defs_agree symb E E'
  -> defs_agree (Z ++ symb) (E [Z <-- List.map Some vl]) (vl ++ E').
Proof.
  intros. length_equify.
  general induction H; simpl; eauto using defs_agree_update.
Qed.

Lemma stmt_idx_sim σ1 σ2
  : stmtIdxSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl in *; try monadS_inv EQ.
  - case_eq (Exp.exp_eval E e); intros.
    + one_step. erewrite <- exp_idx_ok; eauto.
      eapply stmt_idx_sim; econstructor; eauto using vars_exist_update, defs_agree_update.
    + no_step. erewrite <- exp_idx_ok in def; eauto. congruence.
  - case_eq (Exp.exp_eval E e); intros.
    case_eq (val2bool v); intros; one_step; eauto.
    erewrite <- exp_idx_ok; eauto.
    eapply stmt_idx_sim; econstructor; eauto.
    erewrite <- exp_idx_ok; eauto.
    eapply stmt_idx_sim; econstructor; eauto.
    no_step.
    erewrite <- exp_idx_ok in def; eauto. congruence.
    erewrite <- exp_idx_ok in def; eauto. congruence.
  - destruct (get_dec L (counted l)) as [[blk A]|?].
    edestruct PIR2_nth; eauto; dcr.
    decide (length (IL.F.block_Z blk) = length Y).
    case_eq (omap (Exp.exp_eval E) Y); intros.
    + assert (omap (exp_eval E') x = ⎣l0 ⎦).
      erewrite omap_agree_2; try eapply H; eauto using smap_length.
      intros. exploit (smap_spec _ EQ0); eauto. dcr. get_functional; subst.
      erewrite exp_idx_ok; eauto.
      one_step; eauto. inv H1; eauto; simpl. exploit smap_length; eauto.
      simpl in *. congruence.
      inv H1; simpl in *.
      assert (length Z = length l0).
      exploit omap_length; eauto. exploit smap_length; eauto. congruence.
      eapply stmt_idx_sim; econstructor;
      eauto using PIR2_drop, vars_exist_update_list, defs_agree_update_list.
    + no_step.
      pose proof (smap_spec _ EQ0).
      assert (omap (Exp.exp_eval E) Y = Some vl).
      erewrite omap_agree_2; eauto using smap_length.
      intros. eapply exp_idx_ok; eauto. edestruct H2; eauto; dcr.
      get_functional; subst; eauto. symmetry; eapply smap_length; eauto.
      congruence.
    + no_step.
      invt approx; simpl in *; subst. exploit smap_length; eauto. congruence.
    + no_step; eauto. edestruct PIR2_nth_2; eauto; dcr. eauto.
  - no_step. simpl.
    erewrite <- exp_idx_ok; eauto.
  - case_eq (omap (Exp.exp_eval E) Y); intros.
    assert (omap (exp_eval E') x0 = ⎣l ⎦).
    erewrite omap_agree_2; try eapply H; eauto using smap_length.
    intros. exploit (smap_spec _ EQ0); eauto. dcr. get_functional; subst.
    erewrite exp_idx_ok; eauto.
    + extern_step.
      * eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
      * assert (vl = l) by congruence; subst.
        eexists; split. econstructor; eauto.
        eapply stmt_idx_sim; econstructor; eauto using vars_exist_update, defs_agree_update.
      * assert (vl = l) by congruence; subst.
        eexists; split. econstructor; eauto.
        eapply stmt_idx_sim; econstructor; eauto using vars_exist_update, defs_agree_update.
    + no_step.
      pose proof (smap_spec _ EQ0).
      assert (omap (Exp.exp_eval E) Y = Some vl).
      erewrite omap_agree_2; eauto using smap_length.
      intros. eapply exp_idx_ok; eauto. edestruct H0; eauto; dcr.
      get_functional; subst; eauto. symmetry; eapply smap_length; eauto.
      congruence.
  - one_step. eapply stmt_idx_sim. econstructor; eauto.
    eapply PIR2_app; eauto.
    pose proof (smap_spec _ EQ0). simpl in H.
    eapply smap_length in EQ0.
    unfold IL.F.mkBlocks,F.mkBlocks in *.
    eapply PIR2_get; intros; unfold mapi; repeat rewrite mapi_length; try congruence.
    inv_mapi H0. inv_mapi H1.
    edestruct H; eauto; dcr. monadS_inv H5. get_functional; subst.
    econstructor; eauto.
Qed.
