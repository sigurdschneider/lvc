Require Import Coqlib Errors AST Integers Mach.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL.
Require Import InfinitePartition.
Require Import SimI.

Section ToMach.

  Parameter (fe: frame_env).
  Parameter (p:inf_partition).

  Definition offset_local (x: Z) := fe.(fe_ofs_local) + 4 * x.
  Definition idx_of_slot (x:var) := Z.of_nat (((x-1)/2)%nat).
  Definition toReg (x:var) :=
    match ((x/2)%nat) with
    | (0%nat) => R0
    | (1%nat) => R1
    | (2%nat) => R2
    | (3%nat) => R3
    | (4%nat) => R4
    | (5%nat) => R5
    | (6%nat) => R6
    | (7%nat) => R7
    | (8%nat) => R8
    | (9%nat) => R9
    | (10%nat) => R10
    | (11%nat) => R11
    | (12%nat) => R12
    | _ => R0
    end.

  Inductive letKind :=
  | LetLoad (reg:var) (slot:var)
  | LetStore (slot:var) (reg:var)
  | LetOpr (i:instruction) (srcs:list mreg).

  Definition toMachInstrOp x (e:op) :=
    match e with
    | Con v => Mop (Ops.Ointconst v) nil (toReg x)
    | Var y =>
      if part_1 p x then
        if part_1 p y then
          Mop (Ops.Oaddimm Int.zero) (toReg y::nil) (toReg x)
        else
          Mgetstack (Ptrofs.repr (offset_local (idx_of_slot y))) Tint (toReg x)
      else
        Msetstack (toReg y) (Ptrofs.repr (offset_local (idx_of_slot x))) Tint
    | _ => Mop (Ops.Ointconst Int.zero) nil (toReg x)
    end.

  Definition toMachCond l (e:op) :=
    match e with
    | _ => Mcond (Ops.Ccomp Ceq) nil l
    end.

  Fixpoint new_labs (l:label) (n:nat) :=
    match n with
    | Init.Datatypes.O => (nil, l)
    | Init.Datatypes.S n =>
      let (L, l') := new_labs l n in
      (Pos.succ l'::L, Pos.succ l')
    end.

  Definition toMachF
           (toMach: forall (L:list label) (l:label) (s:stmt) (k:Mach.code), Mach.code * label) :=
    fix f (L' L:list label) l (F:list (params*stmt)) (k:Mach.code) {struct F} : Mach.code * label :=
    match F, L' with
    | Zs :: F, lf::L' =>
      let (c, l') := f L' L l F k in
      let (cs, ls) := toMach L l' (snd Zs) c in
      (Mlabel lf::cs, ls)
    | _, _ => (nil, l)
    end.

  Fixpoint toMach (L:list label) (l:label) (s:stmt) (k:Mach.code)
    : Mach.code * label :=
    match s with
    | stmtLet x (Operation e) s =>
      let '(c, l') := toMach L l s k in
      (toMachInstrOp x e::c, l')
    | stmtLet x (Call e Y) s =>
      toMach L l s k
    | stmtIf e s t =>
      let l' := Pos.succ (Pos.succ l) in
      let (ct, lt) := toMach L l' t (Mlabel (Pos.succ l)::k) in
      let (cs, ls) := toMach L lt s (Mgoto (Pos.succ l)::Mlabel l::ct) in
      (toMachCond l e::cs, ls)
    | stmtApp f Y =>
      (Mgoto (nth_default (xH) L f)::nil, l)
    | stmtReturn (Var x) =>
      (Mop (Ops.Oaddimm Int.zero) (R0::nil) (toReg x)::Mreturn::nil, l)
    | stmtReturn _ => (nil, l)
    | stmtFun F t =>
      let (L', l') := new_labs l (length F) in
      toMachF toMach L' (L' ++ L) l F k
    end.

End ToMach.

Require Import Smallstep Globalenvs common.Events.


Inductive mach_step_adapter rao (G:Globalenvs.Genv.t fundef unit)
  :  Mach.state -> Events.event -> Mach.state -> Prop :=
| StepAdapterTau σ σ'
  : Mach.step rao G σ nil σ'
    -> mach_step_adapter rao G σ EvtTau σ'
| StepAdapter σ σ' f arg res fnc
  : Mach.step rao G σ (Event_syscall f
                               (EVint ⊝ arg)
                               (EVint res)::nil) σ'
    -> mach_step_adapter rao G σ (EvtExtern (ExternI fnc arg res)) σ'.

Lemma mach_reddec2 rao G
  : reddec2 (mach_step_adapter rao G).
Proof.
  hnf; intros.
  unfold normal2.
  eapply Coq.Logic.Classical_Prop.classic.
Defined.

Definition mach_result (σ:Mach.state) :=
  match σ with
  | Returnstate nil rs m =>
    match loc_result signature_main with
    | One r => match rs r with
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

Lemma extcall_arg_det rs m sp l v v'
  : extcall_arg rs m sp l v
    -> extcall_arg rs m sp l v'
    -> v = v'.
Proof.
  intros A B.
  general induction A; invt extcall_arg; eauto.
  congruence.
Qed.

Lemma extcall_arguments_det rs m sp ef a a'
  : extcall_arguments rs m sp ef a
    -> extcall_arguments rs m sp ef a'
    -> a = a'.
Proof.
  eapply list_forall_det.
  intros. general induction H; invt extcall_arg_pair; f_equal; eauto using extcall_arg_det.
Qed.

Local Ltac congr :=
  repeat match goal with
         | [ H : ?t = ?x, H' : ?t = ?y |- _ ] =>
           assert (x = y) by congruence; subst; clear H' || clear H
         | [ H : eval_builtin_args ?G ?rs ?sp ?m ?a ?vargs,
                 H' :  eval_builtin_args ?G ?rs ?sp ?m ?a ?vargs' |- _ ]
           => eapply eval_builtin_args_determ in H; eauto; subst
         | [ H : extcall_arguments ?rs ?m ?sp ?ef ?a,
               H' : extcall_arguments ?rs ?m ?sp ?ef ?a' |- _ ]
         => eapply extcall_arguments_det in H; eauto; subst

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

Lemma mach_int_det rao (RF:rel3_functional rao) G
  : internally_deterministic (mach_step_adapter rao G).
Proof.
  hnf; intros.
  inv H; inv H0; eauto.
  - inv H1; inv H2; congr; clear_trivial_eqs; try now (split; eauto; congr; try congruence).
    + specialize (RF _ _ _ _ H5 H17); eauto. subst. eauto.
  - inv H1; inv H2; exfalso; repeat (congr; clear_trivial_eqs).
Qed.

Lemma mach_ext_det rao (RF:rel3_functional rao) G
  : externally_determined (mach_step_adapter rao G).
Proof.
  hnf. intros.
  invc H; invc H0; eauto.
  - inv H1; inv H; repeat (congr; clear_trivial_eqs);
      try now (split; eauto; congr; try congruence).
    + specialize (RF _ _ _ _ H3 H15); eauto. subst. eauto.
  - inv H1; inv H6; repeat (congr; clear_trivial_eqs); eauto.
Qed.

Instance MachStateType rao (RF:rel3_functional rao) G : StateType Mach.state :=
  @Build_StateType _ (mach_step_adapter rao G) mach_result (mach_reddec2 rao G)
                   (mach_int_det rao RF G) (mach_ext_det rao RF G).

  Lemma toMach_correct r (L:I.labenv) I (V:onv val) s bv vv rs m rao RF G
    : @sim _ _ Mach.state (MachStateType rao RF G) r Sim (L, V, s)
           ((State nil bv vv (fst (toMach I (1%positive) s nil)) rs m):Mach.state).
  Proof.
    destruct s; simpl.
    - destruct e; simpl.
      +

  Qed.




Definition transf_program (s:stmt) : Mach.program :=
  let sig := mksignature (Tint::Tint::nil) (Some Tint)
                        (mkcallconv false false false) in
  let sz := 0 in
  let fnc := mkfunction sig (fst (toMach nil xH s nil)) sz (Ptrofs.repr 0) (Ptrofs.repr  0) in
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
  exists st2, Mach.initial_state (transf_program s) st2.
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
  : forward_simulation (semantics s) (Mach.semantics (fun _ _ _ => False) (transf_program s)).
Proof.
  eapply forward_simulation_plus.
  - simpl. intros. unfold Genv.globalenv, transf_program. simpl.
    admit.
  - intros. admit.
  - admit.
  - admit.
Admitted.