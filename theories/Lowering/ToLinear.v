Require Import Coqlib Errors AST Integers Linear.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL.
Require Import InfinitePartition.
Require Import SimI.

Section ToLinear.

  Parameter (fe: frame_env).
  Parameter (p:inf_partition var).

  Definition offset_local (x: Z) := fe.(fe_ofs_local) + 4 * x.
  Definition idx_of_slot (x:var) := Zpos (Pos.div2 (x-1)%positive)%positive.
  Definition toReg (x:var) :=
    match Pos.div2 x with
    | (1%positive) => R3
    | (2%positive) => R4
    | (3%positive) => R5
    | (4%positive) => R6
    | (5%positive) => R7
    | (6%positive) => R8
    | (7%positive) => R9
    | (8%positive) => R10
    | (9%positive) => R11
    | (10%positive) => R12
    | (11%positive) => R14
    | (12%positive) => R15
    | (13%positive) => R16
    | (14%positive) => R17
    | (15%positive) => R18
    | (16%positive) => R19
    | (17%positive) => R20
    | (18%positive) => R21
    | (19%positive) => R22
    | (20%positive) => R23
    | (21%positive) => R24
    | (22%positive) => R25
    | (23%positive) => R26
    | (24%positive) => R27
    | (25%positive) => R28
    | (26%positive) => R29
    | (27%positive) => R30
    | _ => R31 (* *)
    end.

  Inductive simplOp : op -> Prop :=
  | SCon v : simplOp (Con v)
  | SVar x : simplOp (Var x)
  | SNeg x : simplOp (UnOp UnOpNeg (Var x))
  | SBinOp bop x y : simplOp (BinOp bop (Var x) (Var y))
  .

  Definition simplExp e := match e with
                              | Operation e' => simplOp e'
                              | _ => True
                              end.

  Definition sop := {e:op | simplOp e}.

  Definition sexp := {e:exp | simplExp e}.

  Inductive letKind :=
  | LetLoad (src:Z) (dst:mreg)
  | LetStore (src:mreg) (dst:Z)
  | LetOpr (o:Op.operation) (srcs:list mreg) (dst:mreg)
  | LetError.

  Definition isReg x := Even.even_pos_fast x.

  Definition getLetOp (r:mreg) (e:op) : letKind :=
    match e with
     | Con v => LetOpr (Op.Ointconst v) nil r
     | UnOp o (Var y) =>
       match o with
       | UnOpToBool => LetError
       | UnOpNeg => LetOpr Op.Onot (toReg y :: nil) r
       end
     | BinOp o (Var y1) (Var y2) =>
       match o with
       | BinOpAdd => LetOpr Op.Oadd
       | BinOpSub => LetOpr Op.Osub
       | BinOpMul => LetOpr Op.Omul
       | BinOpDiv => LetOpr Op.Odiv
       | BinOpEq  => (fun _ _ => LetError) (*PROBLEM! there is only Oxor & Onot: we 2 instructions here.*)
       | BinOpLt  => LetOpr (Op.Ocmp (Op.Ccomp Clt))
       end (toReg y1 :: toReg y2 :: nil) r
     | Var y =>
       if [ isReg y ]
       then LetOpr Op.Omove (toReg y :: nil) r
       else LetError
     | _ => LetError
    end
  .

  Definition getLetKind (x:var) (e:op) : letKind
    := if [ isReg x ]
       then let dst := toReg x in
            match e with
            | Var y => if [ isReg y ]
                      then LetOpr (Op.Omove) (toReg y :: nil) dst
                      else LetLoad (Zpos y) dst
            | _ => getLetOp dst e
            end
       else match e with
            | Var y => if [ isReg y ]
                      then LetStore (toReg y) (Zpos x)
                      else LetError
            | _ => LetError
            end
  .

  Definition dummyinstr := Lop Op.Omove (R3::nil) R3.

  Definition toLinearCond (l:label) (e:op) : instruction :=
    match e with
    | Var y => Lcond (Op.Ccompimm Cne Int.zero) (toReg y :: nil) l
    | BinOp BinOpLt (Var y1) (Var y2) => Lcond (Op.Ccomp Clt) (toReg y1 :: toReg y2 :: nil) l
    | _ => dummyinstr
    end
  .

  Fixpoint toLinear
           (Λ:list label)
           (l:label) (* the biggest label used so far *)
           (s:stmt)
    : code * label :=
    match s with
    | stmtLet x (Operation e) s =>
      let (c', l') := toLinear Λ l s in
      (
        match getLetKind x e with
        | LetLoad  src dst => Lgetstack Local src Tint dst
        | LetStore src dst => Lsetstack src Local dst Tint
        | LetOpr o srcs r => Lop o srcs r
        | _ => dummyinstr
        end :: c',
        l'
      )
    | stmtLet x (Call e Y) s =>
      toLinear Λ l s (* this is incorrect *)
    | stmtIf e s t =>
      let l' := Pos.succ l in
      let (csq, lc) := toLinear Λ l' s in
      let (alt, la) := toLinear Λ lc t in
      (toLinearCond l' e
                    :: alt (* we don't need to jump out,
                              because alt's last intstruction is either Lreturn or Lgoto *)
                    ++ Llabel l' :: csq,
       la) (* missing jump & label *)
    | stmtApp f Y =>
      let l' := nth (counted f) Λ xH in
      (Lgoto l' :: nil, l)
    | stmtReturn (Var x) =>
      (Lreturn::nil, l)
    | stmtReturn _ => (Lreturn :: nil, l)
    | stmtFun F t =>
      let (l', Λ') := fold_left (fun (lΛ:label * list label) ps => let (l, Λ) := lΛ in
                                                       let l' := Pos.succ l in
                                                       (l', Λ ++ l' :: nil))
                                F (l, Λ) in
      let (ct, lt) := toLinear Λ' l' t in
      fold_left (fun (cl : code * label) ps =>
                   let (c, l)  := cl in
                   let l' := Pos.succ l in
                   let (c',l'') := toLinear Λ' l' (snd ps) in
                   (c ++ Llabel l' :: c', l''))
                F (ct, lt)
    end.

End ToLinear.

Require Import Smallstep Globalenvs common.Events.


Inductive linear_step_adapter (G:Globalenvs.Genv.t fundef unit)
  :  Linear.state -> Events.event -> Linear.state -> Prop :=
| StepAdapterTau σ σ'
  : Linear.step G σ nil σ'
    -> linear_step_adapter G σ EvtTau σ'
| StepAdapter σ σ' f arg res fnc
  : Linear.step G σ (Event_syscall f
                               (EVint ⊝ arg)
                               (EVint res)::nil) σ'
    -> linear_step_adapter G σ (EvtExtern (ExternI fnc arg res)) σ'.

Lemma linear_reddec2 G
  : reddec2 (linear_step_adapter G).
Proof.
  hnf; intros.
  unfold normal2.
  eapply Coq.Logic.Classical_Prop.classic.
Defined.

Definition linear_result (σ:Linear.state) :=
  match σ with
  | Returnstate nil rs m =>
    match loc_result signature_main with
    | One r => match rs (R r) with
              | Values.Vint retcode => Some retcode
              | _ => None
              end
    | _ => None
    end
  | _ => None
  end.

Lemma list_forall_det A B (R:A->B->Prop) L L1 L2
      (Rdet: forall x y z, R x y -> R x z -> y = z)
  : list_forall2 R L L1
    -> list_forall2 R L L2
    -> L1 = L2.
Proof.
  intros X Y.
  general induction X; invt list_forall2; eauto.
  f_equal; eauto.
Qed.
(*
Lemma extcall_arg_det rs m sp l v v'
  : extcall_arg rs m sp l v
    -> extcall_arg rs m sp l v'
    -> v = v'.
Proof.
  intros A B.
  general induction A; invt extcall_arg; eauto.
  congruence.
Qed.
 *)
(*
Lemma extcall_arguments_det rs m sp ef a a'
  : extcall_arguments rs m sp ef a
    -> extcall_arguments rs m sp ef a'
    -> a = a'.
Proof.
  eapply list_forall_det.
  intros. general induction H; invt extcall_arg_pair; f_equal; eauto using extcall_arg_det.
Qed.
*)
Local Ltac congr :=
  repeat match goal with
         | [ H : ?t = ?x, H' : ?t = ?y |- _ ] =>
           assert (x = y) by congruence; subst; clear H' || clear H
         | [ H : eval_builtin_args ?G ?rs ?sp ?m ?a ?vargs,
                 H' :  eval_builtin_args ?G ?rs ?sp ?m ?a ?vargs' |- _ ]
           => eapply eval_builtin_args_determ in H; eauto; subst
(*         | [ H : extcall_arguments ?rs ?m ?sp ?ef ?a,
               H' : extcall_arguments ?rs ?m ?sp ?ef ?a' |- _ ]
         => eapply extcall_arguments_det in H; eauto; subst*)

         | [ H :  external_call ?ef ?G ?vargs ?m ?t ?vres ?m',
                  H' :   external_call ?ef ?G ?vargs ?m ?t' ?vres' ?m'' |- _ ]

           =>  let A := fresh "A" in
              let B := fresh "B" in
              edestruct (external_call_determ _ _ _ _ _ _ _ _ _ _ H H') as [A B];
              inv A; try (edestruct B; eauto; subst); clear H || clear H'
         | [ s := _ |- _ ] => subst s
         end.

Definition rel3_functional {A B C} (R:A->B->C->Prop) :=
  forall a b c c', R a b c -> R a b c' -> c = c'.

Lemma linear_int_det G
  : internally_deterministic (linear_step_adapter G).
Proof.
  hnf; intros.
  inv H; inv H0; eauto.
  - inv H1; inv H2; congr; clear_trivial_eqs; try now (split; eauto; congr; try congruence).

  - inv H1; inv H2; exfalso; repeat (congr; clear_trivial_eqs).
Qed.

Lemma linear_ext_det G
  : externally_determined (linear_step_adapter G).
Proof.
  hnf. intros.
  invc H; invc H0; eauto.
  - inv H1; inv H; repeat (congr; clear_trivial_eqs);
      try now (split; eauto; congr; try congruence).
  - inv H1; inv H6; repeat (congr; clear_trivial_eqs); eauto.
Qed.

Instance LinearStateType G : StateType Linear.state :=
  @Build_StateType _ (linear_step_adapter G) linear_result (linear_reddec2 G)
                   (linear_int_det G) (linear_ext_det G).

Lemma toLinear_correct r (L:I.labenv) I l (V:onv val) s bv vv rs m G
  : @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, s)
         ((State nil bv vv (fst (toLinear I l s)) rs m):Linear.state).
Proof.
  revert L I l V s vv rs m r. pcofix CIH; intros.
  destruct s; simpl.
  - assert (SE:simplExp e) by admit.
    hnf in SE.
    destruct e; simpl.
    + let_pair_case_eq. simpl_pair_eqs. subst.
      case_eq (op_eval V e); intros.
      * inv SE; simpl; unfold getLetKind; simpl; cases; simpl.
        -- pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity.
           reflexivity.
           right. eapply CIH.
        -- pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity.
           reflexivity.
           right. eapply CIH.
        -- cases.
           pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity. reflexivity.
           right. eapply CIH.
           pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity.
           right. eapply CIH.
        -- cases.
           pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity.
           right. eapply CIH.
           pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity. reflexivity.
           right. eapply CIH.
        -- pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity. reflexivity.
           right. eapply CIH.
        -- pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity. reflexivity.
           right. eapply CIH.
        -- destruct bop;
           try (pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ econstructor; econstructor; reflexivity | eauto ]
                                    | ];
                right; eapply CIH).
           pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. simpl.
           simpl in *. monad_inv H.
           admit. reflexivity.
           right; eapply CIH.
        -- pfold; eapply SimSilent; [ eapply plus2O; single_step
                                    | eapply plus2O; [ | eauto ]
                                    | ].
           econstructor. econstructor. reflexivity.
           reflexivity.
           right. eapply CIH.
      * admit.
    + admit.
  - repeat (let_pair_case_eq; simpl_pair_eqs); subst. simpl.
    case_eq (op_eval V e); intros.
    + case_eq (val2bool v); intros.
      admit.
      admit.
    + admit.
  - admit.
  - admit.
  - let_pair_case_eq; simpl_pair_eqs; subst.
    let_pair_case_eq; simpl_pair_eqs; subst.
    admit.
Qed.



(*
Definition transf_program (s:stmt) : Linear.program :=
  let sig := mksignature (Tint::Tint::nil) (Some Tint)
                        (mkcallconv false false false) in
  let sz := 0 in
  let fnc := mkfunction sig (fst (toLinear nil xH s nil)) sz (Ptrofs.repr 0) (Ptrofs.repr  0) in
  mkprogram ((xH, Gfun (Internal fnc))::nil) (xH::nil) xH.





Inductive step_adapter {F} {V} (G:Globalenvs.Genv.t F V)
  :  I.state -> Events.trace -> I.state -> Prop :=
| StepAdapterTau σ σ'
  : I.step σ EvtTau σ'
    -> step_adapter G σ nil σ'
| StepAdapter σ σ' fnc arg res
  : I.step σ (EvtExtern (ExternI fnc arg res)) σ'
    -> step_adapter G σ (Event_syscall ""
                                          (EVint ⊝ arg)
                                          (EVint res)::nil) σ'.


Definition semantics (s: stmt) :=
  Semantics step_adapter (fun σ => fst (fst σ) = nil /\ snd σ = s) (fun σ n => result σ = Some n)
            (Genv.empty_genv fundef unit nil).


Lemma transf_initial_states s:
  exists st2, Linear.initial_state (transf_program s) st2.
Proof.
  intros.
  exploit Genv.init_mem_exists; eauto.
  Focus 2.
  destruct H.
  econstructor; split.
  - eapply H.
    intros. isabsurd.
    admit.
Admitted.

Theorem transf_program_correct (s:stmt)
  : forward_simulation (semantics s) (Linear.semantics (fun _ _ _ => False) (transf_program s)).
Proof.
  eapply forward_simulation_plus.
  - simpl. intros. unfold Genv.globalenv, transf_program. simpl.
    admit.
  - intros. admit.
  - admit.
  - admit.
Admitted.

*)