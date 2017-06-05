Require Import Coqlib Errors AST Integers Linear.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL.
Require Import InfinitePartition.
Require Import SimI.

Section ToLinear.

  Parameter (fe: frame_env).
  Parameter (p:inf_partition).

  Definition offset_local (x: Z) := fe.(fe_ofs_local) + 4 * x.
  Definition idx_of_slot (x:var) := Z.of_nat (((x-1)/2)%nat).
  Definition toReg (x:var) :=
    match ((x/2)%nat) with
    | (0%nat) => R3
    | (1%nat) => R4
    | (2%nat) => R5
    | (3%nat) => R6
    | (4%nat) => R7
    | (5%nat) => R8
    | (6%nat) => R9
    | (7%nat) => R10
    | (8%nat) => R11
    | (9%nat) => R12
    | (10%nat) => R14
    | (11%nat) => R15
    | (12%nat) => R16
    | (13%nat) => R17
    | (14%nat) => R18
    | (15%nat) => R19
    | (16%nat) => R20
    | (17%nat) => R21
    | (18%nat) => R22
    | (19%nat) => R23
    | (20%nat) => R24
    | (21%nat) => R25
    | (22%nat) => R26
    | (23%nat) => R27
    | (24%nat) => R28
    | _ => R29 (* reserve R30 & R31 for operations (this is not optimal) *)
    end.

  Inductive letKind :=
  | LetLoad (reg:var) (slot:var)
  | LetStore (slot:var) (reg:var)
  | LetOpr (i:instruction) (srcs:list mreg).

  Definition tmp1 := 26%nat.
  Definition tmp2 := 27%nat.
    
(* TODO to binary *)
  Fixpoint toLinearInstrOp x (e:op) {struct e} : list instruction :=
    match e with
     | Con v => Lop (Op.Ointconst v) nil (toReg x) :: nil
     | UnOp e0 e1 =>
       match e0 with
       | UnOpToBool => toLinearInstrOp x e1 (* this might fail *)
       | UnOpNeg => toLinearInstrOp tmp1 e1 ++ Lop Op.Onot (toReg tmp1 :: nil) (toReg x) :: nil
       end
     | BinOp e0 e1 e2 =>
       toLinearInstrOp tmp1 e1 ++ toLinearInstrOp tmp2 e2 ++
                       match e0 with
                       | BinOpAdd =>  Lop Op.Oadd
                       | BinOpSub => Lop Op.Osub
                       | BinOpMul => Lop Op.Omul
                       | BinOpDiv => Lop Op.Odiv
                       | BinOpEq  => Lop Op.Onxor
                       | BinOpLt => Lop (Op.Ocmp (Op.Ccomp Clt))
                       end (toReg tmp1 :: toReg tmp2 :: nil) (toReg x) :: nil
     | Var y =>
       (*if part_1 p x then
         if part_1 p y then*)
           Lop (Op.Oaddimm Int.zero) (toReg y::nil) (toReg x) :: nil
        (* else
           Lgetstack Local (Ptrofs.repr (offset_local (idx_of_slot y))) Tint (toReg x)
       else
         Lsetstack (toReg y) (Ptrofs.repr (offset_local (idx_of_slot x)))*)
    end.

  Definition toLinearCond (l:label) (e:op) : list instruction :=
    match e with
    | BinOp BinOpLt e1 e2 =>
      toLinearInstrOp tmp1 e1 ++ toLinearInstrOp tmp2 e2 ++
                      Lcond (Op.Ccomp Clt) (toReg tmp1 :: toReg tmp2 :: nil) l :: nil
    | _ => nil
    end
  .

  Fixpoint toLinear
           (l:label) (* the biggest label used so far *)
           (s:stmt)
    : code * label :=
    match s with
    | stmtLet x (Operation e) s =>
      let (c', l') := toLinear l s in
      (toLinearInstrOp x e ++ c', l')
    | stmtLet x (Call e Y) s =>
      toLinear l s (* this is incorrect *)
    | stmtIf e s t =>
      let l' := Pos.succ l in
      let (cs, ls) := toLinear l' s in
      let (ct, lt) := toLinear ls t in
      (toLinearCond l' e ++ ct ++ Llabel l' :: cs, lt) (* missing jump & label *)
    | stmtApp f Y => (* *)
      let l' := Pos.succ l in
      (Lgoto l' :: nil, l')
    | stmtReturn (Var x) =>
      (Lreturn::nil, l)
    | stmtReturn _ => (nil, l) (* why ? *)
    | stmtFun F t =>
      let (ct, lt) := toLinear l t in
      fold_left (fun (cl : code * label) ps => let (c,l)  := cl in
                                            let (c',l'):= toLinear l (snd ps) in
                                            (c ++ c', l'))
                F (nil, lt)
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

  Lemma toLinear_correct r (L:I.labenv) I (V:onv val) s bv vv rs m G
    : @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, s)
           ((State nil bv vv (fst (toLinear I s)) rs m):Linear.state).
  Proof.
    destruct s; simpl.
    - destruct e; simpl.
      + let_pair_case_eq. simpl_pair_eqs. subst.
        case_eq (op_eval V e); intros.
        * pfold; eapply SimSilent; [ eapply plus2O; single_step
                              | 
                              | ].
          

  Qed.




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