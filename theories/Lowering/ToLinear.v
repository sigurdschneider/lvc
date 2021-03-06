Require Import Coqlib Errors AST Integers Linear.
Require Import Bounds Conventions Locations Stacklayout.
Require Import IL NoParams Sawtooth SmallStepRelations.
Require Import InfinitePartition.
Require Import SimI VarP MkVars.
Require Import Smallstep Globalenvs common.Events.
Require Import LinearStateType LabelRelations IsLinearizable.

Set Implicit Arguments.

Section ToLinear.

  Parameter (fe: frame_env).
  Parameter (p:inf_partition var).

  Definition offset_local (x: Z) := fe.(fe_ofs_local) + 4 * x.
  Definition toSlot (x:var) := Zpos (Pos.div2 x)%positive.
  Definition toReg (x:var) :=
    match x with
    | (1%positive) => R3
    | (3%positive) => R4
    | (5%positive) => R5
    | (7%positive) => R6
    | (9%positive) => R7
    | (11%positive) => R8
    | (13%positive) => R9
    | (15%positive) => R10
    | (17%positive) => R11
    | (19%positive) => R12
    | _ => R31 (*dummy *)
    end.

  Definition max_reg := 20%positive.

  Lemma toReg_inj x y
    : isReg x -> isReg y -> (x <= max_reg)%positive -> (y <= max_reg)%positive -> x <> y -> toReg x = toReg y ->
      x = y.
  Proof.
    unfold isReg, Even.even_pos_fast, toReg, Pos.div2;
      repeat cases; cbv; intros;
        try solve [try destruct b1; try destruct b; isabsurd].
  Qed.

  Definition dummyinstr := Lop Op.Omove (R3::nil) R3.

  Definition translateLetOp (x:var) (e:op)  :=
    let r := toReg x in
    match e with
     | Con v => Lop (Op.Ointconst v) nil r::nil
     | UnOp o (Var y) =>
       match o with
       | UnOpToBool => nil
       | UnOpNot => Lop (Op.Ocmp (Op.Ccompimm Ceq Int.zero)) (toReg y ::  nil) r::nil
       | UnOpNeg => Lop (Op.Osubimm val_zero) (toReg y ::  nil) r::nil
       end
     | BinOp o (Var y1) (Var y2) =>
       Lop match o with
           | BinOpAdd => Op.Oadd
           | BinOpSub => Op.Osub
           | BinOpMul => Op.Omul
           | BinOpDiv => Op.Odiv
           | BinOpEq  => (Op.Ocmp (Op.Ccomp Ceq))
           | BinOpLt  => (Op.Ocmp (Op.Ccomp Clt))
           | BinOpLe  => (Op.Ocmp (Op.Ccomp Cle))
           | BinOpGt  => (Op.Ocmp (Op.Ccomp Cgt))
           | BinOpGe  => (Op.Ocmp (Op.Ccomp Cge))
           end (toReg y1 :: toReg y2 :: nil) r::nil
     | BinOp o (Var y1) (Con y2) =>
       Lop match o with
           | BinOpAdd => Op.Oaddimm y2
           | BinOpSub => Op.Oaddimm (Int.neg y2)
           | BinOpMul => Op.Omulimm y2
           | BinOpDiv => Op.Odiv
           | BinOpEq  => (Op.Ocmp (Op.Ccompimm Ceq y2))
           | BinOpLt  => (Op.Ocmp (Op.Ccompimm Clt y2))
           | BinOpLe  => (Op.Ocmp (Op.Ccompimm Cle y2))
           | BinOpGt  => (Op.Ocmp (Op.Ccompimm Cgt y2))
           | BinOpGe  => (Op.Ocmp (Op.Ccompimm Cge y2))
           end (toReg y1 :: nil) r::nil
     | BinOp o (Con y2) (Var y1)  =>
       Lop match o with
           | BinOpAdd => Op.Oaddimm y2
           | BinOpSub => Op.Osubimm y2
           | BinOpMul => Op.Omulimm y2
           | BinOpDiv => Op.Odiv
           | BinOpEq  => (Op.Ocmp (Op.Ccompimm Ceq y2))
           | BinOpLt  => (Op.Ocmp (Op.Ccompimm Cgt y2))
           | BinOpLe  => (Op.Ocmp (Op.Ccompimm Cge y2))
           | BinOpGt  => (Op.Ocmp (Op.Ccompimm Clt y2))
           | BinOpGe  => (Op.Ocmp (Op.Ccompimm Cle y2))
           end (toReg y1 :: nil) r::nil
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

  Definition mrel V rs :=
    forall x v, V x = Some v -> regbnd max_reg x ->
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
         (REGBOUND:For_all (regbnd max_reg) (Ops.freeVars e)) st
    :  plus2 (@StateType.step _ (LinearStateType G))
             (State st bv vv (translateLetOp x e ++ l) rs m)
             nil
             (State st bv vv l (Locmap.set (if [isReg x] then R (toReg x) else
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
        hnf in REGBOUND. cset_tac.
      + eapply SmallStepRelations.star2_plus2;
          [ try single_step; simpl in *
          | eapply star2_refl ].
        unfold Locmap.get in EQ. rewrite EQ. simpl.
        unfold Int.notbool. cases; simpl; reflexivity.
        hnf in REGBOUND; cset_tac.
      + eapply SmallStepRelations.star2_plus2;
          [ try single_step; simpl in *
          | eapply star2_refl ].
        unfold Locmap.get in EQ. rewrite EQ. simpl.
        reflexivity.
        hnf in REGBOUND; cset_tac.
      + unfold Locmap.get in *.
        exploit REGBOUND as RB1. cset_tac.
        exploit (REGBOUND x0) as RB2. cset_tac.
        cases; simpl;
          (eapply SmallStepRelations.star2_plus2;
           [ try single_step; simpl in *
           | eapply star2_refl ]);
          only 1-3,5,6:
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
          cases in H1; eauto. eauto. eauto.
        * rewrite EQ, EQ1; eauto; simpl;
          case_eq (Int.lt x2 x1); simpl in *; intros; try reflexivity.
        * rewrite EQ, EQ1; eauto; simpl.
          case_eq (Int.lt x2 x1); simpl in *; intros; try reflexivity.
        * rewrite EQ, EQ1; eauto; simpl.
          case_eq (Int.lt x1 x2); simpl in *; intros; try reflexivity.
      + unfold Locmap.get in *.
        exploit REGBOUND as RB1. cset_tac.
        cases;
        simpl;
          (eapply SmallStepRelations.star2_plus2;
           [ try single_step; simpl in *
           | try eapply star2_refl ]);
          rewrite EQ; eauto.
        * rewrite Int.sub_add_opp. simpl. reflexivity.
        * simpl; cases; eauto.
        * simpl. cases; eauto.
        * simpl. cases; eauto.
        * simpl. cases; eauto.
        * simpl. cases; eauto.
      + unfold Locmap.get in *.
        exploit REGBOUND as RB1. cset_tac.
         cases;
        simpl;
          (eapply SmallStepRelations.star2_plus2;
           [ try single_step; simpl in *
           | try eapply star2_refl ]);
          rewrite EQ; eauto; simpl.
        * rewrite Int.add_commut. reflexivity.
        * rewrite Int.mul_commut. reflexivity.
        * rewrite Int.eq_sym.
          cases; eauto.
        * cases; eauto.
        * cases; eauto.
        * cases; eauto.
        * cases; eauto.
    - repeat cases.
      + isabsurd.
      + eapply SmallStepRelations.star2_plus2.
        * single_step.
        * eapply MR in EV. cases in EV.
          unfold Locmap.get in EV. rewrite EV.
          eapply star2_refl.
          exploit REGBOUND; eauto. simpl. cset_tac.
  Qed.

  Lemma toSlot_inj x y
    : ~ isReg x -> ~ isReg y -> x <> y -> toSlot x <> toSlot y.
  Proof.
    intros. unfold toSlot. intro.
    injection H2; intros; clear H2.
    unfold Pos.div2 in H3.
    unfold isReg in *. unfold Even.even_pos_fast in *.
    destruct x, y; simpl in *; try congruence; isabsurd.
  Qed.

  Lemma  translateLet_correct r G L V x e s bv vv l rs m (SM:simplLet x e)
         (MR:mrel V rs)
         (REGBOUND:For_all (regbnd max_reg) (Ops.freeVars e))
         (REGBOUNDx:regbnd max_reg x) st
         (IH:forall V rs,  mrel V rs ->
             upaco3 (@sim_gen IL.I.state _  Linear.state (LinearStateType G)) r Sim (L, V, s)
                    (State st bv vv l rs m))
    :  @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, stmtLet x (Operation e) s)
            (State st bv vv (translateLetOp x e ++ l) rs m).
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
        * unfold Locmap.get, Locmap.set.
          repeat cases; eauto.
          -- exfalso. exploit (@toReg_inj x0 x); eauto.
          -- eapply MR in H0. cases in H0. eauto.
          -- exfalso. eapply n0. hnf. congruence.
        * unfold Locmap.get, Locmap.set.
          cases.
          -- exfalso. eapply toSlot_inj. eapply NOTCOND. eauto. eauto.
             symmetry. unfold toSlot. congruence.
          -- cases. eapply MR in H0. cases in H0; eauto. exfalso; eauto.
             exfalso. eapply n0. hnf. right. simpl. unfold toSlot.
             exploit toSlot_inj. eapply NOTCOND. eauto. eauto.
             unfold toSlot in H4.
             decide ((Pos.div2 x < Pos.div2 x0)%positive).
             ++ left. hnf; intros H5.
               eapply Zcompare_Gt_not_Lt in H5.
               rewrite Pos.add_comm in H5.
               rewrite Pos.add_1_l in H5.
               rewrite Pos2Z.inj_succ in H5.
               rewrite Z.add_comm in H5.
               rewrite Z.add_1_l in H5.
               rewrite Zcompare_succ_compat in H5.
               rewrite <- Pos2Z.inj_compare in H5. eauto.
             ++ right. hnf; intros H5.
               eapply Zcompare_Gt_not_Lt in H5.
               rewrite Pos.add_comm in H5.
               rewrite Pos.add_1_l in H5.
               rewrite Pos2Z.inj_succ in H5.
               rewrite Z.add_comm in H5.
               rewrite Z.add_1_l in H5.
               rewrite Zcompare_succ_compat in H5.
               rewrite <- Pos2Z.inj_compare in H5. eauto.
               unfold Pos.lt in n1.
               eapply Pos.compare_ge_iff in n1.
               unfold Pos.le in n1.
               eapply H4. f_equal.
               hnf.
               eapply Pos.compare_eq_iff.
               destruct ((Pos.div2 x0 ?= Pos.div2 x)%positive); eauto; congruence.
    - pno_step_left.
  Qed.




  Definition toLinearCond (l:label) (e:op) : instruction :=
    match e with
    | Var y => Lcond (Op.Ccompimm Ceq Int.zero) (toReg y :: nil) l
    | BinOp bop (Var y1) (Var y2) =>
      Lcond match bop with
            | BinOpLt => Op.Ccomp Cge
            | BinOpLe => Op.Ccomp Cgt
            | BinOpGe => Op.Ccomp Clt
            | BinOpGt => Op.Ccomp Cle
            | BinOpEq => Op.Ccomp Cne
            | _ => Op.Ccomp Ceq
            end (toReg y1 :: toReg y2 :: nil) l
    | BinOp bop (Var y1) (Con y2) =>
      Lcond match bop with
            | BinOpLt => Op.Ccompimm Cge y2
            | BinOpLe => Op.Ccompimm Cgt y2
            | BinOpEq => Op.Ccompimm Cne y2
            | BinOpGe => Op.Ccompimm Clt y2
            | BinOpGt => Op.Ccompimm Cle y2
            | _ => Op.Ccomp Ceq
            end (toReg y1 :: nil) l
    | BinOp bop (Con y1) (Var y2) =>
      Lcond match bop with
            | BinOpLt => Op.Ccompimm Cle y1
            | BinOpLe => Op.Ccompimm Cle y1
            | BinOpEq => Op.Ccompimm Cne y1
            | BinOpGe => Op.Ccompimm Cgt y1
            | BinOpGt => Op.Ccompimm Cge y1
            | _ => Op.Ccomp Ceq
            end (toReg y2 :: nil) l
    | _ => dummyinstr
    end.

  Lemma toLinearCond_step G V v l e bv vv rs m c
        (EV:op_eval V e = Some v)
        (TRUE:val2bool v = true) (SC:simplCond e)
        (MR:mrel V rs) (REGBOUND:For_all (regbnd max_reg) (Ops.freeVars e)) st
      : plus2 (@StateType.step _ (LinearStateType G))
              (State st bv vv (toLinearCond l e :: c) rs m) nil
              (State st bv vv c rs m).
  Proof.
    invt simplCond; simpl in *.
    - exploit REGBOUND; eauto. cset_tac.
      econstructor 1.
      + econstructor. eapply exec_Lcond_false; only 2: reflexivity.
        * simpl. simpl in *.
          exploit MR as LMEQ; eauto. cases in LMEQ. unfold Locmap.get in LMEQ.
          rewrite LMEQ. simpl.
          unfold val2bool in TRUE. cases in TRUE.
          unfold Int.eq. cases; eauto.
          exfalso. eapply NOTCOND. eauto.
      + reflexivity.
    - exploit REGBOUND; eauto. cset_tac.
      exploit (REGBOUND x); eauto. cset_tac.
      monad_inv EV.
      econstructor 1; eauto.
      econstructor.
      exploit MR as LMEQ1; eauto.
      exploit MR as LMEQ2; try eapply EQ; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      cases in LMEQ2. unfold Locmap.get in LMEQ2.
      eapply exec_Lcond_false; only 2: (cases; reflexivity);
      destruct op; isabsurd; simpl; revert EQ2; rewrite LMEQ1, LMEQ2; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try eapply negb_false_iff;
            rewrite val2bool_bool2val in *; eauto.
      + eapply negb_true_iff in TRUE. eauto.
    - exploit REGBOUND; eauto. cset_tac.
      monad_inv EV.
      econstructor 1; eauto.
      econstructor.
      exploit MR as LMEQ1; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      eapply exec_Lcond_false; only 2: (cases; reflexivity).
      destruct op; isabsurd; simpl; revert EQ0; rewrite LMEQ1; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try eapply negb_false_iff;
            rewrite val2bool_bool2val in *; eauto.
       eapply negb_true_iff in TRUE. eauto.
    - exploit REGBOUND; eauto. cset_tac.
      monad_inv EV.
      econstructor 1; eauto.
      econstructor.
      exploit MR as LMEQ1; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      eapply exec_Lcond_false; only 2: (cases; reflexivity).
      destruct op; isabsurd; simpl; revert EQ0; try rewrite LMEQ1; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try eapply negb_false_iff;
            try rewrite val2bool_bool2val in *; eauto.
      + rewrite Int.eq_sym. eauto.
      + eapply negb_true_iff in TRUE. eauto.
  Qed.

    Lemma toLinearCond_step_false G V v l e bv vv rs m c c'
        (EV:op_eval V e = Some v)
        (TRUE:val2bool v = false) (SC:simplCond e)
        (MR:mrel V rs) (REGBOUND:For_all (regbnd max_reg) (Ops.freeVars e))
        (FIND:  find_label l (fn_code bv) = ⎣ c' ⎦) st
      : plus2 (@StateType.step _ (LinearStateType G))
              (State st bv vv (toLinearCond l e :: c) rs m) nil
              (State st bv vv c' rs m).
  Proof.
    invt simplCond; simpl in *.
    - exploit REGBOUND; eauto. cset_tac.
      econstructor 1.
      + econstructor. eapply exec_Lcond_true; only 2: reflexivity.
        * simpl. simpl in *.
          exploit MR as LMEQ; eauto. cases in LMEQ. unfold Locmap.get in LMEQ.
          rewrite LMEQ. simpl.
          unfold val2bool in TRUE. cases in TRUE; eauto. isabsurd.
        * eauto.
      + reflexivity.
    - exploit REGBOUND; eauto. cset_tac.
      exploit (REGBOUND x); eauto. cset_tac.
      monad_inv EV.
      exploit MR as LMEQ1; eauto.
      exploit MR as LMEQ2; try eapply EQ; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      cases in LMEQ2. unfold Locmap.get in LMEQ2.
      econstructor 1; eauto.
      econstructor.
      eapply exec_Lcond_true; only 2: (cases; reflexivity).
      destruct op; isabsurd; simpl; rewrite LMEQ1, LMEQ2; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try rewrite negb_true_iff;
            rewrite val2bool_bool2val in *;
            try rewrite negb_false_iff in TRUE;
            eauto. eauto.
    - exploit REGBOUND; eauto. cset_tac.
      monad_inv EV.
      exploit MR as LMEQ1; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      econstructor 1; eauto.
      econstructor.
      eapply exec_Lcond_true; only 2: (cases; reflexivity).
      destruct op; isabsurd; simpl; rewrite LMEQ1; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try rewrite negb_true_iff;
            rewrite val2bool_bool2val in *;
            try rewrite negb_false_iff in TRUE;
            eauto. eauto.
    - exploit REGBOUND; eauto. cset_tac.
      monad_inv EV.
      exploit MR as LMEQ1; eauto.
      cases in LMEQ1. unfold Locmap.get in LMEQ1.
      econstructor 1; eauto.
      econstructor.
      eapply exec_Lcond_true; only 2: (cases; reflexivity).
      destruct op; isabsurd; simpl; rewrite LMEQ1; simpl;
        unfold option_lift2; simpl; intros; clear_trivial_eqs;
          f_equal; try rewrite negb_true_iff;
            rewrite val2bool_bool2val in *;
            try rewrite negb_false_iff in TRUE;
            eauto. eauto.
      + rewrite Int.eq_sym; eauto.
      + eauto.
  Qed.

  Definition ret_reg_name := 1%positive.

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
      let (csq, l'') := toLinear Λ l' s in
      let (alt, l''') := toLinear Λ l'' t in
      (toLinearCond l e
                    :: csq (* we don't need to jump out,
                              because alt's last intstruction is either Lreturn or Lgoto *)
                    ++ Llabel l :: alt,
       l''') (* missing jump & label *)
    | stmtApp f Y =>
      let l' := nth (counted f) Λ xH in
      (Lgoto l' :: nil, l)
    | stmtReturn e =>
      if [ e = (Var ret_reg_name)] then
        (Lreturn::nil, l)
      else (translateLetOp ret_reg_name e ++ Lreturn::nil, l)
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


Lemma all_labels_smaller_translateOp x e l
  : all_labels_smaller (translateLetOp x e) l.
Proof.
  unfold translateLetOp; repeat cases; hnf; intros;
    inv_get.
Qed.

Lemma all_labels_smaller_toLinearCond e l l'
  : all_labels_smaller (toLinearCond l e::nil) l'.
Proof.
  unfold toLinearCond; repeat cases; hnf; intros;
    inv_get.
Qed.

Lemma not_contains_label_toLinearCond e l l'
  : not_contains_label (toLinearCond l e::nil) l'.
Proof.
  unfold toLinearCond; repeat cases; hnf; intros;
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
  - etransitivity; [|eapply (IH s2); eauto].
    rewrite <- (IH s1); eauto. eapply Ple_succ.
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
      revert H; repeat cases; eauto; isabsurd.
    + eapply all_labels_ge_app1; eauto.
      * eapply all_labels_ge_le.
        eapply (IH s1); eauto.
        eapply Ple_succ.
      * rewrite cons_app.
        eapply all_labels_ge_app1; eauto.
        -- hnf; intros; inv_get; reflexivity.
        -- eapply all_labels_ge_le.
           eapply (IH s2); eauto.
           rewrite <- toLinear_le.
           eapply Ple_succ.
  - hnf; intros; inv_get.
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
      revert H; repeat cases; isabsurd.
    + eapply all_labels_smaller_app1; eauto.
      * eapply all_labels_smaller_le.
        eapply IH; eauto.
        setoid_rewrite <- toLinear_le at 2. reflexivity.
      * rewrite cons_app.
        eapply all_labels_smaller_app1; eauto.
        hnf; intros; inv_get.
        eapply Pos.lt_le_trans. eapply Plt_succ.
        rewrite <- !toLinear_le. reflexivity.
  - hnf; intros; inv_get.
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

Lemma toLinearFun_get F l I f n Zs
      (GetF:get F n Zs)
      (LT:forall n i, get I n i -> (i < (fst (mkVars F l)))%positive)
      (GE:(fst (mkVars F l) <= f)%positive)
  : exists C C' l' i,
    fst
      (toLinearFun toLinear I f
                    F
                   (snd (mkVars F l))) =
    C ++ Llabel i :: fst (toLinear I l' (snd Zs)) ++ C'
    /\ get (snd (mkVars F l)) n i
    /\ (f <= l')%positive
    /\ not_contains_label C i
    /\ all_labels_smaller C l'.
Proof.
  general induction GetF; simpl.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
    simpl.
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
    simpl.
    do 4 eexists.
    instantiate (10:=nil). simpl. split. f_equal.
    split. eauto using get.
    split. reflexivity.
    split; hnf; intros; inv_get.
  - revert LT GE; simpl.
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
    simpl.
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
    simpl in *. intros.
    edestruct (IHGetF (Pos.succ l) I (snd (toLinear I f (snd x')))); eauto using get; dcr.
    rewrite GE. rewrite <- toLinear_le. reflexivity.
    intros. simpl in *.
    do 2 eexists. exists x2, x3.
    split.
    + erewrite H1.
      rewrite cons_app.
      rewrite app_assoc.
      rewrite app_assoc. f_equal.
    + split; eauto using get.
      split.
      rewrite <- toLinear_le in H2. eauto.
      split.
      * eapply not_contains_label_app1; eauto.
        eapply not_contains_label_app1; eauto.
        hnf; intros; inv_get. intro; subst.
        eapply mkVars_get_le in H0.
        eapply Pos.le_succ_l in H0.
        eapply Pos.lt_irrefl in H0; eauto.
        eapply all_not_labels_ge.
        eapply all_labels_ge_le.
        eapply all_labels_ge_toLinear.
        eapply mkVars_get_lt in H0.
        eapply Pos.le_succ_l.
        eapply Pos.lt_le_trans; eauto.
      * eapply all_labels_smaller_app1; eauto.
        eapply all_labels_smaller_app1; eauto.
        hnf; intros; inv_get.
        eapply Pos.lt_le_trans. eapply Plt_succ.
        rewrite <- H2. rewrite <- toLinear_le.
        rewrite <- GE. rewrite <- mkVars_le. reflexivity.
        eapply all_labels_smaller_le.
        eapply all_labels_smaller_toLinear. eauto.
Qed.

Lemma toLinearCond_correct G r L V s1 s2 st bv vv l e code1 code2 code rs m
      (SC:simplCond e) (MR:mrel V rs) (RB: For_all (regbnd max_reg) (Ops.freeVars e))
      (IH1:upaco3 (@sim_gen IL.I.state _  Linear.state (LinearStateType G)) r Sim (L, V, s1)
             (State st bv vv (code1 ++ (Llabel l :: code2) ++ code) rs m))
      (FL:find_label l (fn_code bv) = ⎣ code2 ++ code ⎦)
      (IH2: upaco3 (@sim_gen IL.I.state _  Linear.state (LinearStateType G)) r Sim (L, V, s2)
                          (State st bv vv (code2 ++ code) rs m))
  : @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, stmtIf e s1 s2)
         (State st bv vv (toLinearCond l e :: code1 ++ (Llabel l :: code2) ++ code) rs m).
Proof.
  case_eq (op_eval V e); intros.
  - case_eq (val2bool v); intros.
    * pfold.
      econstructor 1.
      -- eapply plus2O. single_step.
         reflexivity.
      -- rewrite !app_assoc. simpl.
         eapply toLinearCond_step; eauto.
      -- rewrite <- !app_assoc.
         eapply IH1.
    * pfold.
      econstructor 1.
      -- eapply plus2O. single_step.
         reflexivity.
      -- rewrite !app_assoc. simpl.
         eapply toLinearCond_step_false; eauto.
      -- eapply IH2.
  - pno_step_left.
Qed.

Lemma toLinear_correct r (L:I.labenv) I l (V:onv val) s bv vv rs m G C C'
      (MR:mrel V rs)
      (ML:all_labels_smaller C l)
      (CODE:fn_code bv = C ++ (fst (toLinear I l s)) ++ C')
      (ILEN:❬I❭=❬L❭)
      (IsLin:isLinearizable s)
      (NoParams:noParams s)
      (ST:sawtooth L)
      (LTI:forall n i, get I n i -> (i < l)%positive)
      (REGBOUND:var_P (regbnd max_reg) s) stk
      (STACKINV:vv = (Values.Vptr stk Ptrofs.zero)) m'
      (STACKFREEOK:Memory.Mem.free m stk 0 (fn_stacksize bv) = Some m')
      (IINV:forall n i b,
          get L n b -> get I n i ->
          exists C C' l, fn_code bv =
                    C ++ (Llabel i::fst (toLinear (drop (n - block_n b) I) l (I.block_s b)))
                      ++ C'
                    /\ (forall n' i, get (drop (n - block_n b) I) n' i -> (i < l)%positive)
                    /\ not_contains_label C i
                    /\ all_labels_smaller C l
                    /\ (i < l)%positive
                    /\ isLinearizable (I.block_s b)
                    /\ noParams (I.block_s b)
                    /\ var_P (regbnd max_reg) (I.block_s b)) st
  : @sim _ _ Linear.state (LinearStateType G) r Sim (L, V, s)
         ((State st bv vv (fst (toLinear I l s) ++ C') rs m):Linear.state).
Proof.
  revert C C' L I l V s vv rs m r MR CODE ML ILEN IINV IsLin NoParams ST REGBOUND LTI
         STACKINV STACKFREEOK.
  pcofix CIH; intros.
  destruct s; invt isLinearizable; invt noParams; invt var_P; simpl in *.
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
    eapply toLinearCond_correct; eauto.
    + intros. right. eapply CIH; eauto.
      ++ rewrite CODE.
        rewrite cons_app.
        rewrite app_assoc. f_equal.
      ++ apply all_labels_smaller_app1.
        eapply all_labels_smaller_le; eauto. eapply Ple_succ.
        eapply all_labels_smaller_toLinearCond.
      ++ intros. eapply LTI in H; eauto.
        etransitivity; eauto. eapply Plt_succ.
    + rewrite CODE.
      rewrite cons_app.
      rewrite find_label_app; eauto.
      rewrite find_label_app; eauto using not_contains_label_toLinearCond.
      rewrite find_label_app; eauto.
      simpl. cases; eauto.
      eapply all_not_labels_ge.
      eapply all_labels_ge_toLinear.
    + right. eapply CIH; eauto.
      ++ rewrite CODE.
        rewrite cons_app.
        rewrite app_assoc.
        rewrite app_assoc.
        setoid_rewrite cons_app at 2.
        rewrite app_assoc.
        f_equal.
      ++ apply all_labels_smaller_app1.
        apply all_labels_smaller_app1.
        apply all_labels_smaller_app1.
        eapply all_labels_smaller_le; eauto. rewrite <- toLinear_le. eapply Ple_succ.
        eapply all_labels_smaller_toLinearCond.
        eapply all_labels_smaller_toLinear.
        hnf; intros; inv_get.
        eapply Pos.lt_le_trans. eapply Plt_succ.
        rewrite <- toLinear_le. reflexivity.
      ++ intros. eapply LTI in H.
        etransitivity; eauto.
        eapply Pos.lt_le_trans. eapply Plt_succ.
        rewrite <- toLinear_le. reflexivity.
  - destruct (get_dec L (counted l0)) as [[? ?]|]; [| pno_step_left].
    + decide (length (block_Z x) = ❬@nil var❭); [|pno_step_left].
      case_eq (block_Z x); simpl in *;
        [intros EQ|intros ? ? EQ]; rewrite EQ in *; simpl in *; clear_trivial_eqs.
      inv_get. erewrite get_nth; eauto.
      edestruct IINV as [? [? [? ?]]]; eauto. simpl in *; dcr.
      pfold. eapply SimSilent; try eapply plus2O; eauto.
      -- single_step. rewrite EQ; eauto.
      -- econstructor. econstructor.
         rewrite H2.
         rewrite find_label_app; eauto.
         simpl. cases; eauto.
      -- simpl. try rewrite EQ in *; eauto.
         right.
         eapply CIH. eauto.
         ++ rewrite H2. rewrite cons_app. rewrite app_assoc. reflexivity.
         ++ eapply all_labels_smaller_app1; eauto.
           hnf; intros; inv_get. eauto.
         ++ eauto with len.
         ++ intros; inv_get.
           edestruct IINV as [? [? [? [? [? ?]]]]]; eauto.
           do 3 eexists. rewrite H11. split; [|split].
           ** repeat rewrite !drop_drop.
              change I.block_n with (@block_n I.block _).
              erewrite sawtooth_drop_eq; eauto.
           ** intros. rewrite drop_drop in H14.
              eapply get_drop in H14.
              change I.block_n with (@block_n I.block _) in H14.
              erewrite sawtooth_drop_eq in H14; eauto.
              eapply H12.
              eapply drop_get. eauto.
           ** eauto.
         ++ eauto.
         ++ eauto.
         ++ eauto.
         ++ eauto.
         ++ eauto.
         ++ reflexivity.
         ++ eauto.
  - case_eq (op_eval V e); intros.
    + dcr. subst.
      cases.
      * { pone_step_right.
          pno_step. simpl in *.
          unfold Locmap.get. simpl.
          simpl. unfold Locmap.set.
          exploit MR; eauto. cases in H1.
          simpl in H1. unfold Locmap.get in H1.
          rewrite H1. eauto.
        }
      * { pfold.
          eapply SimTerm; swap 1 3.
          * eapply star2_trans_silent.
            -- eapply plus2_star2.
               simpl. rewrite <- app_assoc.
               eapply translateLet_step; eauto.
               econstructor; eauto.
            -- simpl. eapply star2_silent.
               econstructor.
               econstructor. eauto. eapply star2_refl.
          * eapply star2_refl.
          * simpl.
            unfold Locmap.get. simpl.
            simpl. unfold Locmap.set.
            destruct (Loc.eq (R R3) (R R3)); eauto.
            isabsurd.
          * stuck2.
          * stuck2.
        }
    + pfold. eapply SimErr; try eapply star2_refl; eauto.
      stuck2.
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
        rewrite CODE.
        edestruct (@toLinearFun_get F (Pos.succ l) ((snd (mkVars F (Pos.succ l)) ++ I))
                                    (snd (toLinear (snd (mkVars F (Pos.succ l)) ++ I)
                                                   (fst (mkVars F (Pos.succ l))) s)))
          as [? [? [? [? [? [? [? ?]]]]]]]; eauto.
        -- intros. eapply get_app_cases in H6 as [? |[? ?]].
           eapply mkVars_get_lt in H6; eauto.
           len_simpl. exploit LTI; eauto.
           etransitivity; eauto.
           eapply Pos.lt_le_trans; eauto. eapply Plt_succ.
           rewrite <- mkVars_le. reflexivity.
        -- rewrite <- toLinear_le. reflexivity.
        -- inv_get.
           rewrite H6. simpl. orewrite (n - n = 0)%nat; simpl.
           eexists. exists (x1 ++ C'). exists x2.
           split.
           ++ instantiate (1:= C ++
                                Llabel l
                                :: fst (toLinear (snd (mkVars F (Pos.succ l)) ++ I)
                                                 (fst (mkVars F (Pos.succ l))) s) ++ x0).
           repeat (repeat rewrite <- !app_assoc; repeat rewrite !app_comm_cons).
           f_equal.
           ++ assert (LI:(l < i)%positive). {
               eapply mkVars_get_le in H0.
               eapply Pos.lt_le_trans; eauto. eapply Plt_succ.
             }
             assert (LI':(i < x2)%positive). {
               rewrite <- toLinear_le in H8.
               eapply mkVars_get_lt in H0.
               eapply Pos.lt_le_trans; eauto.
             }
             split; [|split; [|split]]; eauto 20.
             ** intros. eapply get_app_cases in H7 as [?|[? ?]].
                --- eapply mkVars_get_lt in H7.
                    eapply Pos.lt_le_trans; eauto.
                    etransitivity; eauto.
                    rewrite <- toLinear_le. reflexivity.
                --- exploit LTI; eauto.
                    repeat (etransitivity; eauto).
             ** eapply not_contains_label_app1; eauto.
                eapply all_not_labels.
                eapply all_labels_smaller_le. eauto.
                eapply Pos.lt_le_incl. eauto.
                rewrite cons_app.
                eapply not_contains_label_app1; eauto.
                hnf; intros; inv_get.
                intro. subst. eapply Pos.lt_irrefl; eauto.
                eapply not_contains_label_app1; eauto.
                eapply all_not_labels_ge.
                eapply all_labels_ge_le.
                eapply all_labels_ge_toLinear.
                eapply mkVars_get_lt in H0.
                eapply Pos.le_succ_l. eauto.
             ** eapply all_labels_smaller_app1; eauto.
                eapply all_labels_smaller_le. eauto.
                eapply Pos.lt_le_incl.
                etransitivity; eauto.
                rewrite cons_app.
                eapply all_labels_smaller_app1; eauto.
                hnf; intros; inv_get.
                eapply Pos.lt_le_trans; try eapply H8.
                eapply Pos.lt_le_trans. eapply Plt_succ.
                rewrite <- toLinear_le. rewrite <- mkVars_le. reflexivity.
                eapply all_labels_smaller_app1; eauto.
                eapply all_labels_smaller_le.
                eapply all_labels_smaller_toLinear. eauto.
      * len_simpl. rewrite get_app_ge in H0; len_simpl; eauto.
        inv_get.
        edestruct IINV as [? [? [? [? [? ?]]]]]; eauto.
        setoid_rewrite H7.
        rewrite drop_app_gen; len_simpl.
        -- do 3 eexists; split; eauto.
           orewrite (n - I.block_n b - ❬F❭ = n - ❬F❭ - I.block_n b)%nat.
           reflexivity.
           split; eauto.
           orewrite (n - I.block_n b - ❬F❭ = n - ❬F❭ - I.block_n b)%nat.
           eauto.
        -- exploit (sawtooth_smaller ST); eauto. simpl in *. omega.
    + intros. eapply get_app_cases in H as [?|[? ?]].
      eapply mkVars_get_lt in H. eauto.
      eapply LTI in H.
      eapply Pos.lt_le_trans; eauto.
      rewrite <- mkVars_le. eapply Ple_succ.
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


Theorem transf_program_correct (s:stmt)
  : forward_simulation (semantics s) (Linear.semantics (fun _ _ _ => False) (transf_program s)).
Proof.
  eapply forward_simulation_plus.
  - simpl. intros. unfold Genv.globalenv, transf_program. simpl.
  - intros.

*)