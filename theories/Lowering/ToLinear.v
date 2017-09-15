Require Import Coqlib Errors AST Integers Linear.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL Sawtooth.
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

(*
Lemma mkVars_get_inv X (L:list X) f n i
  :  get (snd (mkVars L f)) n i
     -> i = (f+Pos.of_nat n)%positive.
Proof.
  intros GET.
  general induction L; simpl in *.
  - isabsurd.
  - revert GET; let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    intros GET. inv GET.
Qed.
 *)

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

  Inductive simplOp : op -> Prop :=
  | SCon v : simplOp (Con v)
  | SVar x : simplOp (Var x)
  | SNeg x : simplOp (UnOp UnOpNeg (Var x))
  | SBinOp bop x y : simplOp (BinOp bop (Var x) (Var y))
  .

  Definition simplExp e := match e with
                              | Operation e' => simplOp e'
                              | _ => False
                              end.

  Definition isReg x := Even.even_pos_fast x.

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
       | UnOpNeg => Lop Op.Onot (toReg y :: nil) r::nil
       end
     | BinOp o (Var y1) (Var y2) =>
       match o with
       | BinOpAdd => Lop Op.Oadd
       | BinOpSub => Lop Op.Osub
       | BinOpMul => Lop Op.Omul
       | BinOpDiv => Lop Op.Odiv
       | BinOpEq  => (fun _ _ => dummyinstr)
       (*PROBLEM! there is only Oxor & Onot: we 2 instructions here.*)
       | BinOpLt  => Lop (Op.Ocmp (Op.Ccomp Clt))
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

  Local Hint Extern 1 =>
  match goal with
  | [ H : false = ?x, I : Is_true ?x |- _ ] => exfalso; rewrite <- H in I; inv I
  end.

  Lemma  translateLet_correct r G L V x e s bv vv l rs m (SM:simplLet x e)
         (MR:mrel V rs)
         (IH:forall V rs,  mrel V rs ->
             upaco3 (@sim_gen IL.I.state _  Linear.state (LinearStateType G)) r Sim (L, V, s)
                    (State nil bv vv l rs m))
    :  @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, stmtLet x (Operation e) s)
            (State nil bv vv (translateLetOp x e ++ l) rs m).
  Proof.
    case_eq (op_eval V e); intros.
    - unfold translateLetOp.
      inv SM; simpl.
      + inv SO; repeat cases;
          pone_step; try reflexivity;
            try (eapply IH; hnf; eauto); try intros ? ?; try cases;
              intros; simpl in *; try monad_inv H; lud; clear_trivial_eqs;
                try solve [exfalso; eauto
                          | rewrite locmap_get_set_RR; eauto;
                            rewrite <- MR; eauto; cases; eauto; try exfalso; eauto
                          | rewrite locmap_get_set_SR;
                            rewrite <- MR; eauto; cases; eauto; try exfalso; eauto].
        * admit.
        * admit.
        * admit.
        *
          rewrite locmap_get_set_RR; eauto. simpl in *.
          exploit MR as MRX; eauto; cases in MRX; unfold Locmap.get in MRX; eauto;
            try rewrite MRX.
          admit.
          admit.
        * admit.
        * rewrite locmap_get_set_RR; eauto. simpl in *.
          exploit MR as MRX; eauto; cases in MRX; unfold Locmap.get in MRX; eauto;
            try rewrite MRX;
          exploit (MR x0) as MRX'; eauto; cases in MRX'; unfold Locmap.get in MRX'; eauto;
            try rewrite MRX';
            simpl. invc H0. reflexivity.
          admit. admit. admit.
        * admit.
        * rewrite locmap_get_set_RR; eauto. simpl in *.
          admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * rewrite locmap_get_set_RR; eauto. simpl in *.
          admit.
        * admit.
      + repeat cases.
        pone_step.
        eapply IH. hnf; intros.
        cases; lud; simpl in *; clear_trivial_eqs.
        * invc e.
          exfalso; eauto.
        * unfold Locmap.get, Locmap.set.
          repeat cases.
          rewrite <- MR; eauto. cases. reflexivity.
        * invc e.
          unfold Locmap.get, Locmap.set.
          repeat cases. simpl. exploit MR; eauto. cases in H2.
          unfold Locmap.get in H2. cases; eauto.
          exfalso; eauto.
          exfalso; eauto.
        * unfold Locmap.get, Locmap.set.
          repeat cases.
          exfalso. invc e. admit.
          rewrite <- MR; eauto. cases. exfalso; eauto. reflexivity.
          exfalso. eapply n0. hnf. admit.
    - pno_step_left.
  Admitted.

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
    | Zs::F, g::Lambda =>
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
      let (csq, l'') := toLinear Λ l' s in
      let (alt, l''') := toLinear Λ l'' t in
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
      (Llabel l :: ct ++ cF, l'')
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
      (ML:not_contains_label C l)
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
                    /\ not_contains_label C i)
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
      admit.
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
             rewrite LMEQ. simpl. admit.
           ++ rewrite CODE. rewrite find_label_app; eauto.
             simpl.
             rewrite find_label_app. simpl. cases. reflexivity.
             admit.
        -- reflexivity.
        -- right.
           simpl in *.
           eapply CIH; eauto.
           instantiate (
               1:=C++Lcond (Op.Ccompimm Cne Int.zero) (toReg x :: nil) l
                     :: fst (toLinear I (snd (toLinear I (Pos.succ l) s1)) s2) ++
                     Llabel l::nil). simpl.
           rewrite CODE. rewrite <- !app_assoc. simpl.
           rewrite <- !app_assoc. simpl. reflexivity.
           admit.
        -- admit.
      * admit.
    + pno_step_left.
  - destruct (get_dec L (counted l0)) as [[? ?]|]; [| pno_step_left].
    + decide (length (block_Z x) = ❬@nil var❭); [|pno_step_left].
      case_eq (block_Z x); simpl in *;
        [|intros ? ? EQ; rewrite EQ in *; clear_trivial_eqs].
      inv_get. erewrite get_nth; eauto.
      edestruct IINV as [? [? [? ?]]]; eauto. simpl in *; dcr.
      pfold. eapply SimSilent; try eapply plus2O; eauto.
      -- single_step.
      -- econstructor. econstructor.
         rewrite H1.
         rewrite find_label_app; eauto.
         simpl. cases; eauto.
      -- simpl.
         right.
         eapply CIH. eauto.
         rewrite H1. rewrite cons_app. rewrite app_assoc. reflexivity.
         ++ (* revert H2; clear_all; unfold not_contains_label; intros.
           eapply get_app_cases in H as [?|[? ?]]; eauto. *)
           admit.
         ++ eauto with len.
         ++ intros; inv_get.
           edestruct IINV as [? [? [? [? ?]]]]; eauto.
           do 3 eexists. rewrite H4. split.
           rewrite drop_drop.
           rewrite sawtooth_drop_eq.
           (* the old sawtooth invariant *)

           admit.  eauto.
         ++
  - admit.
  - revert CODE; repeat let_pair_case_eq; subst; simpl; intros.
    pfold. econstructor; try eapply plus2O; eauto.
    single_step.
    econstructor; econstructor; eauto.
    right.
    rewrite <- app_assoc in *.
    eapply CIH; eauto.
    + rewrite CODE. rewrite cons_app. rewrite app_assoc. reflexivity.
    + admit.
    + len_simpl. rewrite app_length. len_simpl. eauto.
    + intros.
      eapply get_app_cases in H as [?|[? ?]]; inv_get.
      * rewrite get_app_lt in H0; [|eauto with len].
        rewrite CODE. admit.
      * len_simpl.
        edestruct IINV as [? [? [? [? ?]]]]; eauto.
        setoid_rewrite H3.
        rewrite drop_app_gen; len_simpl.
        -- admit.
        -- admit.
Admitted.



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