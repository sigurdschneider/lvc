Require Import Coqlib Errors AST Integers Linear.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL Sawtooth SmallStepRelations.
Require Import InfinitePartition.
Require Import SimI.


Require Import Smallstep Globalenvs common.Events.

Set Implicit Arguments.


Fixpoint mkVars X (L:list X) (f:var) : var * list var :=
  match L with
  | nil => (f, nil)
  | _::L => let f' := Pos.succ f in
           let (f'', xl) := mkVars L f' in
           (f'', f::xl)
  end.


Lemma mkVars_length X (L:list X) f
  : ❬snd (mkVars L f)❭ = ❬L❭.
Proof.
  general induction L; simpl; repeat let_pair_case_eq; eauto; subst; simpl.
  rewrite IHL; eauto.
Qed.


Smpl Add match goal with
         | [ H : context [ ❬snd (@mkVars ?X ?L ?f)❭ ] |- _ ]
           => setoid_rewrite (@mkVars_length X L f) in H
         | [ |- context [ ❬snd (@mkVars ?X ?L ?f)❭ ] ]
           => setoid_rewrite (@mkVars_length X L f)
         end : len.

Lemma mkVars_le X L f
  : (f <= fst (@mkVars X L f))%positive.
Proof.
  general induction L; simpl.
  - reflexivity.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    rewrite <- IHL. eapply Ple_succ.
Qed.


Lemma mkVars_get_le X (L:list X) f n i
  :  get (snd (mkVars L f)) n i
     -> (f <= i)%positive.
Proof.
  intros GET.
  general induction L; simpl in *.
  - isabsurd.
  - revert GET; let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    intros GET. inv GET.
    + reflexivity.
    + eapply IHL in H3. rewrite <- H3. eapply Ple_succ.
Qed.

Lemma mkVars_get_lt X (L:list X) f n i
  :  get (snd (mkVars L f)) n i
     -> (i < fst (mkVars L f))%positive.
Proof.
  intros GET.
  general induction L; simpl in *.
  - isabsurd.
  - revert GET; let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    intros GET. inv GET.
    + eapply Pos.lt_le_trans. eapply Plt_succ. rewrite <- mkVars_le. reflexivity.
    + eapply IHL; eauto.
Qed.


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
                   (@linear_int_det G) (@linear_ext_det G).

Section ToLinear.

  Parameter (fe: frame_env).
  Parameter (p:inf_partition var).

  Definition offset_local (x: Z) := fe.(fe_ofs_local) + 4 * x.
  Definition toSlot (x:var) := Zpos (Pos.div2 (x-1)%positive)%positive.
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


  Definition isReg x := Even.even_pos_fast x.

  Inductive simplOp : op -> Prop :=
  | SCon v : simplOp (Con v)
  | SVar x : simplOp (Var x)
  | SNeg x (RGa:isReg x) :  simplOp (UnOp UnOpNeg (Var x))
  | SBinOp bop x y (RGa:isReg x) (RGb:isReg y) : simplOp (BinOp bop (Var x) (Var y))
  .

  Definition simplExp e := match e with
                              | Operation e' => simplOp e'
                              | _ => False
                              end.

  Inductive simplLet x : op -> Prop :=
  | SimpleOp e (RG:isReg x) (SO:simplOp e) : simplLet x e
  | SimpleStore y (RG: isReg y) (MM:~isReg x) : simplLet x (Var y).

  Definition dummyinstr := Lop Op.Omove (R3::nil) R3.

  Definition translateLetOp (x:var) (e:op)  :=
    let r := toReg x in
    match e with
     | Con v => Lop (Op.Ointconst v) nil r::nil
     | UnOp o (Var y) =>
       match o with
       | UnOpToBool => nil
       | UnOpNeg => Lop (Op.Ocmp (Op.Ccompimm Ceq Int.zero)) (toReg y ::  nil) r::nil
       end
     | BinOp o (Var y1) (Var y2) =>
       Lop match o with
       | BinOpAdd => Op.Oadd
       | BinOpSub => Op.Osub
       | BinOpMul => Op.Omul
       | BinOpDiv => Op.Odiv
       | BinOpEq  => (Op.Ocmp (Op.Ccomp Ceq))
       | BinOpLt  => (Op.Ocmp (Op.Ccomp Clt))
       end (toReg y1 :: toReg y2 :: nil) r::nil
     | Var y =>
       match isReg x, isReg y with
       | true, true => Lop Op.Omove (toReg y :: nil) r::nil
       | false, true => Lsetstack (toReg y) Local (toSlot x) Tint::nil
       | true, false => Lgetstack Local (toSlot y) Tint r::nil
       | false, false => nil
       end
     | _ => nil
    end
  .
(*
  Definition translateLet (x:var) (e:op)
    := if [ isReg x ]
       then let dst := toReg x in
            match e with
            | Var y => if [ isReg y ]
                      then Lop (Ops.Omove) (toReg y :: nil) dst
                      else Lgetstack Local (Zpos y) Tint dst
            | _ => translateLetOp dst e
            end
       else match e with
            | Var y => if [ isReg y ]
                      then Lsetstack (toReg y) Local (Zpos x) Tint
                      else dummyinstr
            | _ => dummyinstr
            end
  .*)

  Ltac single_step_linear := econstructor; econstructor; eauto.

  Smpl Add single_step_linear : single_step.

  Definition mrel V rs :=
    forall x v, V x = Some v ->
           Locmap.get
             (if [isReg x] then R (toReg x) else S Local (toSlot x) Tint)
             rs = Values.Vint v.

  Smpl Add
       match goal with
       | [ EQ : @equiv ?V (@_eq ?V (@SOT_as_OT _ _ _)) _ _ _ |- _ ] =>
         invc EQ
       end : inv_trivial.

  Lemma locmap_get_set_RR x v rs
    : Locmap.get (R x) (Locmap.set (R x) v rs) = v.
  Proof.
    unfold Locmap.get, Locmap.set; cases; reflexivity.
  Qed.

  Lemma locmap_get_set_RS x v rs s y t
    : Locmap.get (R x) (Locmap.set (S s y t) v rs) = Locmap.get (R x) rs.
  Proof.
    unfold Locmap.get, Locmap.set; repeat cases; eauto.
  Qed.

  Lemma locmap_get_set_SR x v rs s y t
    : Locmap.get (S s y t) (Locmap.set (R x) v rs) = Locmap.get (S s y t) rs.
  Proof.
    unfold Locmap.get, Locmap.set; repeat cases; eauto.
  Qed.

  Lemma locmap_get_set_SS v rs s y
    : Locmap.get (S s y Tint) (Locmap.set (S s y Tint) (Values.Vint v) rs) = Values.Vint v.
  Proof.
    unfold Locmap.get, Locmap.set; repeat cases; eauto.
  Qed.

  Local Hint Extern 1 =>
  match goal with
  | [ H : false = ?x, I : Is_true ?x |- _ ] => exfalso; rewrite <- H in I; inv I
  end.

  Lemma translateLet_step (G:Genv.t fundef unit) V x e bv vv l rs m (SM:simplLet x e)
         (MR:mrel V rs) v
         (EV:op_eval V e = Some v)
    :  plus2 (@StateType.step _ (LinearStateType G))
             (State nil bv vv (translateLetOp x e ++ l) rs m)
             nil
             (State nil bv vv l (Locmap.set (if [isReg x] then R (toReg x) else
                                               S Local (toSlot x) Tint)
                                            (Values.Vint v) rs) m).
  Proof.
    unfold translateLetOp.
    inv SM; simpl.
    - inv SO; cases; only 2: repeat cases; simpl in *;
        try monad_inv EV;
        repeat match goal with
               | [ H: V ?x = Some ?v' |- _ ] => eapply MR in H; repeat cases in H
               end;
        try (eapply SmallStepRelations.star2_plus2;
             [ single_step; simpl in *; try reflexivity
             | eapply star2_refl]; try f_equal; eauto).
      + eapply SmallStepRelations.star2_plus2;
          [ try single_step; simpl in *
          | eapply star2_refl]; f_equal; eauto.
      + rewrite <- Heq in *; isabsurd.
      + eapply SmallStepRelations.star2_plus2;
          [ try single_step; simpl in *
          | ].
        simpl in *.
        unfold Locmap.get in EV. rewrite EV.
        eapply star2_refl.
      + eapply SmallStepRelations.star2_plus2;
          [ try single_step; simpl in *
          | eapply star2_refl ].
        unfold Locmap.get in EQ. rewrite EQ. simpl.
        unfold Int.notbool. cases; simpl; reflexivity.
      + unfold Locmap.get in *.
        cases; simpl;
          (eapply SmallStepRelations.star2_plus2;
           [ try single_step; simpl in *
           | eapply star2_refl ]);
          try now (try rewrite EQ; try rewrite EQ1; simpl; eauto;
                   repeat cases; try reflexivity; intros; clear_trivial_eqs).
        * revert EQ2. cases; intros; clear_trivial_eqs.
          rewrite EQ, EQ1. simpl. cases; eauto.
          exfalso. eapply NOTCOND.
          eapply Is_true_eq_right in Heq.
          eapply orb_prop_elim in Heq.
          destruct Heq. left. pose proof (Int.eq_spec x2 Int.zero).
          cases in H0; eauto.
          eapply andb_prop_elim in H. destruct H.
          right. split.
          pose proof (Int.eq_spec x1 (Int.repr Int.min_signed)).
          cases in H1; eauto.
          pose proof (Int.eq_spec x2 Int.mone).
          cases in H1; eauto.
    - repeat cases.
      + isabsurd.
      + eapply SmallStepRelations.star2_plus2.
        * single_step.
        * eapply MR in EV. cases in EV.
          unfold Locmap.get in EV. rewrite EV.
          eapply star2_refl.
  Qed.

  Lemma toSlot_inj x y
    : ~ isReg x -> ~ isReg y -> x <> y -> toSlot x <> toSlot y.
  Proof.
    intros. unfold toSlot. intro.
    injection H2; intros. clear H2.
    unfold Pos.div2 in H3.
    unfold isReg in *. unfold Even.even_pos_fast in *.
    destruct x, y; simpl in *; try congruence; isabsurd.
    admit.
  Admitted.

  Lemma  translateLet_correct r G L V x e s bv vv l rs m (SM:simplLet x e)
         (MR:mrel V rs)
         (IH:forall V rs,  mrel V rs ->
             upaco3 (@sim_gen IL.I.state _  Linear.state (LinearStateType G)) r Sim (L, V, s)
                    (State nil bv vv l rs m))
    :  @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, stmtLet x (Operation e) s)
            (State nil bv vv (translateLetOp x e ++ l) rs m).
  Proof.
    case_eq (op_eval V e); intros.
    - pfold. eapply SimSilent; [eapply plus2O; [single_step | eauto]| |].
      eapply translateLet_step; eauto.
      eapply IH.
      try intros ? ?.
      intros; simpl in *; try monad_inv H; lud; clear_trivial_eqs.
      + repeat cases;
          try solve [exfalso; eauto
                    | rewrite locmap_get_set_RR; eauto;
                      rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                    | rewrite locmap_get_set_SR;
                      rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                    | rewrite locmap_get_set_SS; eauto].
      + repeat cases;
          try solve [exfalso; eauto
                    | rewrite locmap_get_set_RR; eauto;
                      rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                    | rewrite locmap_get_set_SR;
                      rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                    | rewrite locmap_get_set_RS;
                      rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                    | rewrite locmap_get_set_SS; eauto].
        * admit.
        * unfold Locmap.get, Locmap.set.
          cases.
          -- exfalso. eapply toSlot_inj. eapply NOTCOND. eauto. eauto.
             symmetry. unfold toSlot. congruence.
          -- cases. eapply MR in H0. cases in H0; eauto. exfalso; eauto.
             exfalso. eapply n0. hnf. right. simpl. unfold toSlot.
             exploit toSlot_inj. eapply NOTCOND. eauto. eauto.
             unfold toSlot in H3. admit.
    - pno_step_left.
  Qed.

  Definition toLinearCond (l:label) (e:op) : instruction :=
    match e with
    | Var y => Lcond (Op.Ccompimm Cne Int.zero) (toReg y :: nil) l
    | BinOp BinOpLt (Var y1) (Var y2) => Lcond (Op.Ccomp Clt) (toReg y1 :: toReg y2 :: nil) l
    | _ => dummyinstr
    end.

  Inductive simplCond : op -> Prop :=
  | SimplCondVar x (RG:isReg x)
    : simplCond (Var x)
  | SimplCondLt x y (RG1:isReg x) (RG2:isReg y)
    : simplCond (BinOp BinOpLt (Var x) (Var y)).

  Definition ret_reg_name := 2%positive.



  Definition toLinearFun
             (toLinear:forall (Λ:list label) (l:label) (s:stmt), code * label)
             (Λ':list label) :=
             fix r l (F:〔params* stmt〕) (Λ:list var) {struct F} : code * label :=
    match F, Λ with
    | Zs::F, g::Λ =>
      let (cs, l') := toLinear Λ' l (snd Zs) in
      let (cF, l'') := r l' F Λ in
      (Llabel g :: cs ++ cF , l'')
    | _, _ => (nil, l)
    end.

  Fixpoint toLinear
           (Λ:list label)
           (l:label) (* the next unused label *)
           (s:stmt)
    : code * label :=
    match s with
    | stmtLet x (Operation e) s =>
      let (c', l') := toLinear Λ l s in
      (translateLetOp x e ++ c', l')
    | stmtLet x (Call e Y) s =>
      toLinear Λ l s (* this is incorrect *)
    | stmtIf e s t =>
      let l' := Pos.succ l in
      let (alt, l'') := toLinear Λ l' t in
      let (csq, l''') := toLinear Λ l'' s in
      (toLinearCond l e
                    :: alt (* we don't need to jump out,
                              because alt's last intstruction is either Lreturn or Lgoto *)
                    ++ Llabel l :: csq,
       l''') (* missing jump & label *)
    | stmtApp f Y =>
      let l' := nth (counted f) Λ xH in
      (Lgoto l' :: nil, l)
    | stmtReturn e =>
      (translateLetOp ret_reg_name e ++ Lreturn::nil, l)
    | stmtFun F t =>
      let (l', ΛF) := mkVars F (Pos.succ l) in
      let Λ' := ΛF ++ Λ in
      let (ct, l'') := toLinear Λ' l' t in
      let (cF, l''') := toLinearFun toLinear Λ' l'' F ΛF in
      (Llabel l :: ct ++ cF, l''')
    end.


  Definition cc := mkcallconv false false false.
  Definition sig := mksignature (Tint::Tint::Tint::nil) (Some Tint) cc.
  Definition fnc s c := mkfunction sig s c.
  Definition fundef s c := (Internal (fnc s c)).
  Definition prg id s c : Linear.program
    := mkprogram ((id, Gfun (fundef s c))::nil) (id::nil) (1%positive).

End ToLinear.

Definition ILItoLinear id s := prg id (0%Z) (fst (toLinear nil default_var s)).

Definition not_contains_label C l :=
  forall n l', get C n (Llabel l') -> l' <> l.

Definition all_labels_smaller C l :=
  forall n l', get C n (Llabel l') -> (l' < l)%positive.

Definition all_labels_ge C l :=
  forall n l', get C n (Llabel l') -> (l <= l')%positive.

Lemma all_not_labels C l
  : all_labels_smaller C l
    ->  not_contains_label C l.
Proof.
  intros. hnf; intros. exploit H; eauto.
  intro. subst.
  eapply Pos.lt_irrefl. eauto.
Qed.

Lemma all_not_labels_ge C l
  : all_labels_ge C (Pos.succ l)
    -> not_contains_label C l.
Proof.
  intros. hnf; intros. exploit H; eauto.
  intro. subst.
  eapply Pos.le_succ_l in H1.
  eapply Pos.lt_irrefl. eauto.
Qed.

Hint Resolve all_not_labels.

Lemma not_contains_label_app1 C C' l
  : not_contains_label C l -> not_contains_label C' l -> not_contains_label (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_smaller_app1 C C' l
  : all_labels_smaller C l -> all_labels_smaller C' l -> all_labels_smaller (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_ge_app1 C C' l
  : all_labels_ge C l -> all_labels_ge C' l -> all_labels_ge (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_smaller_le C l l'
  : all_labels_smaller C l
    -> (l <= l')%positive
    -> all_labels_smaller C l'.
Proof.
  intros; hnf; intros.
  eapply H in H1. eapply Pos.lt_le_trans; eauto.
Qed.

Lemma all_labels_ge_le C l l'
  : all_labels_ge C l
    -> (l' <= l)%positive
    -> all_labels_ge C l'.
Proof.
  intros; hnf; intros.
  eapply H in H1. etransitivity; eauto.
Qed.

Lemma get_singleton X (x y:X) n
  : get (x::nil) n y -> x = y.
Proof.
  intros. inv H; isabsurd; eauto.
Qed.

Smpl Add match goal with
         | [ H : get (?x::nil) _ ?y |- _ ] =>
           eapply get_singleton in H;
             try subst x; try subst y
         end : inv_get.

Lemma all_labels_smaller_translateOp x e l
  : all_labels_smaller (translateLetOp x e) l.
Proof.
  unfold translateLetOp; repeat cases; hnf; intros;
    inv_get.
Qed.

Lemma all_labels_ge_translateOp x e l
  : all_labels_ge (translateLetOp x e) l.
Proof.
  unfold translateLetOp; repeat cases; hnf; intros;
    inv_get.
Qed.

Lemma find_label_app C C' l
  (ML: not_contains_label C l)
  : find_label l (C ++ C') = find_label l C'.
Proof.
  general induction C; simpl in *; eauto.
  cases.
  - exfalso. destruct a; isabsurd.
    exploit ML; eauto using get.
    unfold is_label in Heq.
    cases in Heq; subst; isabsurd.
  - rewrite IHC; eauto. hnf; eauto using get.
Qed.

Lemma find_label_first C C' l c
  : find_label l C = Some c
  -> find_label l (C ++ C') = Some (c ++ C').
Proof.
  general induction C; simpl in *; eauto.
  cases; eauto.
Qed.


Lemma toLinearFun_le' I f F D
      (IH: forall I f n Zs, get F n Zs -> (f <= snd (toLinear I f (snd Zs)))%positive)
  : (f <= snd (toLinearFun toLinear I f F D))%positive.
Proof.
  general induction F; destruct D; simpl; try reflexivity;
    repeat cases; repeat simpl_pair_eqs; subst; simpl.
  etransitivity; [| eapply IHF; eauto using get].
  rewrite <- IH; eauto using get. reflexivity.
Qed.

Lemma toLinear_le I f s
  : (f <= (snd (toLinear I f s)))%positive.
Proof.
  revert I f.
  sind s; destruct s; intros;
    simpl; repeat cases; repeat simpl_pair_eqs; subst; simpl; try reflexivity; eauto.
  - etransitivity; [|eapply (IH s1); eauto].
    rewrite <- (IH s2); eauto. eapply Ple_succ.
  - rewrite <- toLinearFun_le'.
    + rewrite <- IH; eauto.
      rewrite <- mkVars_le. eapply Ple_succ.
    + intros. eapply IH; eauto.
Qed.

Lemma toLinearFun_le I f F D
  : (f <= snd (toLinearFun toLinear I f F D))%positive.
Proof.
  eapply toLinearFun_le'; eauto using toLinear_le.
Qed.

Lemma all_labels_ge_toLinearFun' F D I f (Len:❬F❭=❬D❭) g
      (IH:forall I f n Zs, get F n Zs -> all_labels_ge (fst (toLinear I f (snd Zs))) f)
      (LED:forall n i, get D n i -> (g <= i)%positive)
      (LE:(g <= f)%positive)
  : all_labels_ge (fst (toLinearFun toLinear I f F D)) g.
Proof.
  general induction Len; simpl.
  - isabsurd.
  - repeat cases; repeat simpl_pair_eqs; subst; simpl.
    rewrite cons_app.
    + eapply all_labels_ge_app1; eauto.
      * hnf; intros; inv_get. eauto using get.
      * eapply all_labels_ge_app1; eauto.
        -- eapply all_labels_ge_le.
           eapply IH; eauto using get.
           eauto.
        -- eapply all_labels_ge_le.
           eapply IHLen; eauto using get.
           rewrite <- toLinear_le; eauto.
           reflexivity.
Qed.


Lemma all_labels_ge_toLinear I f s
  : all_labels_ge (fst (toLinear I f s)) f.
Proof.
  revert I f.
  sind s; simpl; intros; destruct s; simpl;
    repeat cases; repeat simpl_pair_eqs; subst; simpl;
      eauto using all_labels_ge_translateOp, all_labels_ge_app1.
  - rewrite cons_app.
    eapply all_labels_ge_app1; eauto.
    + hnf; intros; inv_get.
      destruct e; simpl in *; isabsurd.
      destruct b; simpl in *; isabsurd.
      destruct e1; simpl in *; isabsurd.
      destruct e2; simpl in *; isabsurd.
    + eapply all_labels_ge_app1; eauto.
      * eapply all_labels_ge_le.
        eapply (IH s2); eauto.
        eapply Ple_succ.
      * rewrite cons_app.
        eapply all_labels_ge_app1; eauto.
        -- hnf; intros; inv_get; reflexivity.
        -- eapply all_labels_ge_le.
           eapply (IH s1); eauto.
           rewrite <- toLinear_le.
           eapply Ple_succ.
  - hnf; intros; inv_get.
  - eapply all_labels_ge_app1; eauto using all_labels_ge_translateOp.
    hnf; intros; inv_get.
  - rewrite cons_app.
    eapply all_labels_ge_app1; eauto.
    + hnf; intros; inv_get; reflexivity.
    + eapply all_labels_ge_app1; eauto.
      * eapply all_labels_ge_le.
        eapply (IH s); eauto.
        rewrite <- mkVars_le. eapply Ple_succ.
      * eapply all_labels_ge_toLinearFun'; eauto with len.
        -- intros.
           eapply mkVars_get_le in H.
           rewrite <- H. eapply Ple_succ.
        -- rewrite <- toLinear_le.
           rewrite <- mkVars_le. eapply Ple_succ.
Qed.


Lemma all_labels_smaller_toLinearFun' F D I f (Len:❬F❭=❬D❭)
      (IH:forall I f n Zs, get F n Zs -> all_labels_smaller (fst (toLinear I f (snd Zs)))
                                                      (snd (toLinear I f (snd Zs))))
      (LED:forall n i, get D n i -> (i < f)%positive)
  : all_labels_smaller (fst (toLinearFun toLinear I f F D)) (snd (toLinearFun toLinear I f F D)).
Proof.
  general induction Len; simpl.
  - isabsurd.
  - repeat cases; repeat simpl_pair_eqs; subst; simpl.
    rewrite cons_app.
    + eapply all_labels_smaller_app1; eauto.
      * hnf; intros; inv_get.
        exploit LED; eauto using get.
        eapply Pos.lt_le_trans; eauto.
        rewrite <- toLinearFun_le.
        rewrite <- toLinear_le; reflexivity.
      * eapply all_labels_smaller_app1; eauto.
        -- eapply all_labels_smaller_le.
           eapply IH; eauto using get.
           rewrite <- toLinearFun_le.
           reflexivity.
        -- eapply all_labels_smaller_le.
           eapply IHLen; eauto using get.
           intros.
           eapply Pos.lt_le_trans. eauto using get.
           rewrite <- toLinear_le; eauto. reflexivity.
           reflexivity.
Qed.

Lemma all_labels_smaller_toLinear I f s
  : all_labels_smaller (fst (toLinear I f s)) (snd (toLinear I f s)).
Proof.
  revert I f.
  sind s; destruct s; intros; simpl;
    repeat cases; repeat simpl_pair_eqs; subst; simpl;
      eauto using all_labels_smaller_translateOp, all_labels_smaller_app1.
  - rewrite cons_app.
    eapply all_labels_smaller_app1; eauto.
    + hnf; intros; inv_get.
      destruct e; simpl in *; isabsurd.
      destruct b; simpl in *; isabsurd.
      destruct e1; simpl in *; isabsurd.
      destruct e2; simpl in *; isabsurd.
    + eapply all_labels_smaller_app1; eauto.
      * eapply all_labels_smaller_le; [|eapply toLinear_le].
        eapply IH; eauto.
      * rewrite cons_app.
        eapply all_labels_smaller_app1; eauto.
        hnf; intros; inv_get.
        eapply Pos.lt_le_trans. eapply Plt_succ.
        rewrite <- !toLinear_le. reflexivity.
  - hnf; intros; inv_get.
  - eapply all_labels_smaller_app1;
      eauto using all_labels_smaller_translateOp.
    hnf; intros; inv_get.
  - rewrite cons_app.
    eapply all_labels_smaller_app1; eauto.
    + hnf; intros; inv_get.
      eapply Pos.lt_le_trans. eapply Plt_succ.
      rewrite <- !toLinearFun_le.
      rewrite <- toLinear_le. rewrite <- mkVars_le. reflexivity.
    + eapply all_labels_smaller_app1; eauto.
      * eapply all_labels_smaller_le.
        eapply IH; eauto.
        rewrite <- toLinearFun_le. reflexivity.
      * eapply all_labels_smaller_toLinearFun'; eauto with len.
        intros.
        eapply Pos.lt_le_trans; swap 1 2.
        rewrite <- toLinear_le. reflexivity.
        eapply mkVars_get_lt; eauto.
Qed.

Inductive isLinearizable : stmt->Prop :=
| IsLinLet x e s
    (LinIH:isLinearizable s)
    (SimplLet:simplLet x e)
    : isLinearizable (stmtLet x (Operation e) s)
| IsLinIf e s t
          (SimplCond:simplCond e)
          (LinIH1:isLinearizable s)
          (LinIH2:isLinearizable t)
  : isLinearizable (stmtIf e s t)
| IsLinApp l Y :
   isLinearizable (stmtApp l Y)
| IsLinExp e :
    isLinearizable (stmtReturn e)
| IsLinCall F t
  : (forall n Zs, get F n Zs -> isLinearizable (snd Zs))
    -> isLinearizable t
    -> isLinearizable (stmtFun F t).

Inductive noParams : stmt->Prop :=
| NoParamsLet
    x e s
    (NoParamsIH:noParams s)
    : noParams (stmtLet x e s)
| NoParamsIf
    e s t
    (NoParamsIH1:noParams s)
    (NoParamsIH2:noParams t)
  : noParams (stmtIf e s t)
| NoParamsApp l :
   noParams (stmtApp l nil)
| NoParamsExp e :
    noParams (stmtReturn e)
| NoParamsCall F t
  (NoParamsIHF:forall n Zs, get F n Zs -> noParams (snd Zs))
  (NoParamsF:forall n Zs, get F n Zs -> fst Zs = nil)
  (NoParamsIHt:noParams t)
  : noParams (stmtFun F t).



Lemma toLinear_correct r (L:I.labenv) I l (V:onv val) s bv vv rs m G C C'
      (MR:mrel V rs)
      (ML:all_labels_smaller C l)
      (CODE:fn_code bv = C ++ (fst (toLinear I l s)) ++ C')
      (ILEN:❬I❭=❬L❭)
      (IsLin:isLinearizable s)
      (NoParams:noParams s)
      (ST:sawtooth L)
      (IINV:forall n i b,
          get L n b -> get I n i ->
          exists C C' l, fn_code bv =
                    C ++ (Llabel i::fst (toLinear (drop (n - block_n b) I) l (I.block_s b)))
                      ++ C'
                    /\ not_contains_label C i
                    /\ all_labels_smaller C l
                    /\ isLinearizable (I.block_s b)
                    /\ noParams (I.block_s b)
                    /\ (i < l)%positive)
  : @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, s)
         ((State nil bv vv (fst (toLinear I l s) ++ C') rs m):Linear.state).
Proof.
  revert C C' L I l V s vv rs m r MR CODE ML ILEN IINV IsLin NoParams ST.
  pcofix CIH; intros.
  destruct s; invt isLinearizable; invt noParams; simpl in *.
  - revert CODE. let_pair_case_eq. simpl_pair_eqs. subst. simpl.
    rewrite <- !app_assoc. intros.
    eapply  translateLet_correct; eauto.
    * intros.
      right.
      simpl in *.
      rewrite app_assoc in CODE. eauto.
      eapply CIH; eauto.
      eapply all_labels_smaller_app1; eauto.
      eapply all_labels_smaller_translateOp; eauto.
  - revert CODE.
    repeat (let_pair_case_eq; simpl_pair_eqs); subst. simpl. intros.
    rewrite <- !app_assoc in *.
    case_eq (op_eval V e); intros.
    + case_eq (val2bool v); intros.
      * invt simplCond. simpl.
        pfold.
        econstructor 1; try eapply plus2O.
        -- single_step.
        -- reflexivity.
        -- econstructor. econstructor; only 2: reflexivity.
           ++ simpl. simpl in *.
             exploit MR as LMEQ; eauto. cases in LMEQ. unfold Locmap.get in LMEQ.
             rewrite LMEQ. simpl.
             unfold val2bool in H0. cases in H0.
             unfold Int.eq. cases; eauto.
             exfalso. eapply NOTCOND. eauto.
           ++ rewrite CODE. rewrite find_label_app; eauto.
             simpl.
             rewrite find_label_app. simpl. cases.
             ** reflexivity.
             ** eapply all_not_labels_ge.
                eapply all_labels_ge_le.
                eapply all_labels_ge_toLinear. reflexivity.
        -- reflexivity.
        -- right.
           simpl in *.
           eapply CIH; eauto.
           instantiate (
               1:=C++Lcond (Op.Ccompimm Cne Int.zero) (toReg x :: nil) l
                     :: fst (toLinear I (Pos.succ l) s2) ++
                     Llabel l::nil). simpl.
           rewrite CODE. rewrite <- !app_assoc. simpl.
           rewrite <- !app_assoc. simpl. reflexivity.
           apply all_labels_smaller_app1.
           eapply all_labels_smaller_le; eauto. rewrite <- toLinear_le. eapply Ple_succ.
           rewrite cons_app. apply all_labels_smaller_app1.
           clear_all; hnf; intros; inv_get.
           apply all_labels_smaller_app1.
           eapply all_labels_smaller_toLinear.
           clear_all; hnf; intros; inv_get.
           eapply Pos.lt_le_trans. eapply Plt_succ. eapply toLinear_le.
        -- admit.
      * admit.
    + pno_step_left.
  - destruct (get_dec L (counted l0)) as [[? ?]|]; [| pno_step_left].
    + decide (length (block_Z x) = ❬@nil var❭); [|pno_step_left].
      case_eq (block_Z x); simpl in *;
        [intros EQ|intros ? ? EQ]; rewrite EQ in *; simpl in *; clear_trivial_eqs.
      inv_get. erewrite get_nth; eauto.
      edestruct IINV as [? [? [? ?]]]; eauto. simpl in *; dcr.
      pfold. eapply SimSilent; try eapply plus2O; eauto.
      -- single_step. rewrite EQ; eauto.
      -- econstructor. econstructor.
         rewrite H1.
         rewrite find_label_app; eauto.
         simpl. cases; eauto.
      -- simpl. try rewrite EQ in *; eauto.
         right.
         eapply CIH. eauto.
         ++ rewrite H1. rewrite cons_app. rewrite app_assoc. reflexivity.
         ++ eapply all_labels_smaller_app1; eauto.
           hnf; intros; inv_get. eauto.
         ++ eauto with len.
         ++ intros; inv_get.
           edestruct IINV as [? [? [? [? ?]]]]; eauto.
           do 3 eexists. rewrite H8. split.
           ** rewrite drop_drop.
              change I.block_n with (@block_n I.block _).
              erewrite sawtooth_drop_eq; eauto.
           ** eauto.
         ++ eauto.
         ++ eauto.
         ++ eauto.
  - admit.
  - revert CODE; repeat let_pair_case_eq; subst; simpl; intros.
    pfold. econstructor; try eapply plus2O; eauto.
    single_step.
    econstructor; econstructor; eauto.
    right.
    rewrite <- app_assoc in *.
    eapply CIH; eauto.
    + rewrite CODE. rewrite cons_app. rewrite app_assoc. reflexivity.
    + eapply all_labels_smaller_app1.
      eapply all_labels_smaller_le; eauto.
      rewrite <- mkVars_le. eapply Ple_succ.
      hnf; intros ? ? Get; inv Get; isabsurd.
      eapply Pos.lt_le_trans.
      eapply Plt_succ.
      eapply mkVars_le.
    + len_simpl. rewrite app_length. len_simpl. eauto.
    + intros.
      eapply get_app_cases in H as [?|[? ?]]; inv_get.
      * rewrite get_app_lt in H0; [|eauto with len].
        rewrite CODE. admit.
      * len_simpl. rewrite get_app_ge in H0; len_simpl; eauto.
        inv_get.
        edestruct IINV as [? [? [? [? ?]]]]; eauto.
        setoid_rewrite H4.
        rewrite drop_app_gen; len_simpl.
        -- do 3 eexists; split; eauto.
           orewrite (n - I.block_n b - ❬F❭ = n - ❬F❭ - I.block_n b)%nat.
           reflexivity.
        -- exploit (sawtooth_smaller ST); eauto. simpl in *. omega.
ed.



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