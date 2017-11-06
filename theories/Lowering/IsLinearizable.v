Require Import Util IL Even DecSolve Indexwise MoreList NoParams VarP.

Definition isReg x := Even.even_pos_fast x.

Definition regbnd k (x:positive) := isReg x -> (x <= k)%positive.

Instance regbnd_computable k x : Computable (regbnd x k).
Proof.
  unfold regbnd. eauto with typeclass_instances.
Qed.

Inductive simplOp : op -> Prop :=
| SCon v : simplOp (Con v)
| SVar x : simplOp (Var x)
| SNot x (RGa:isReg x) :  simplOp (UnOp UnOpNot (Var x))
| SNeg x (RGa:isReg x) :  simplOp (UnOp UnOpNeg (Var x))
| SBinOp bop x y (RGa:isReg x) (RGb:isReg y) : simplOp (BinOp bop (Var x) (Var y))
| SBinOpV1 bop x y (RGa:isReg x) (notDiv:bop <> BinOpDiv) : simplOp (BinOp bop (Var x) (Con y))
| SBinOpV2 bop x y (RGb:isReg y) (notDiv:bop <> BinOpDiv) : simplOp (BinOp bop (Con x) (Var y))
.

Instance simplOp_computable o : Computable (simplOp o).
Proof.
  destruct o; try dec_solve.
  destruct u, o; try dec_solve; decide (isReg p); dec_solve.
  destruct o1, o2; try dec_solve;
    try decide (isReg p); try decide (isReg p0); try dec_solve;
      decide (b = BinOpDiv); try dec_solve.
Qed.

Definition simplExp e := match e with
                        | Operation e' => simplOp e'
                        | _ => False
                        end.

Instance simplExp_computable e : Computable (simplExp e).
Proof.
  destruct e; simpl; eauto with typeclass_instances.
Qed.

Inductive simplLet x : op -> Prop :=
| SimpleOp e (RG:isReg x) (SO:simplOp e) : simplLet x e
| SimpleStore y (RG: isReg y) (MM:~isReg x) : simplLet x (Var y).

Instance simplLet_computable x o : Computable (simplLet x o).
Proof.
  decide (isReg x).
  - decide (simplOp o); dec_solve.
  - destruct o; try dec_solve.
    decide (isReg p); dec_solve.
Qed.

Definition isComparision (bop:binop) :=
  match bop with
  | BinOpLt => true
  | BinOpEq => true
  | BinOpGe => true
  | BinOpGt => true
  | _ => false
  end.

Inductive simplCond : op -> Prop :=
| SimplCondVar x (RG:isReg x)
  : simplCond (Var x)
| SimplCondLt x y (RG1:isReg x) (RG2:isReg y) op
              (OP:isComparision op)
  : simplCond (BinOp op (Var x) (Var y))
| SimplCondLt1 x y (RG1:isReg x) op
               (OP:isComparision op)
  : simplCond (BinOp op (Var x) (Con y))
| SimplCondLt2 x y (RG2:isReg y) op
               (OP:isComparision op)
  : simplCond (BinOp op (Con x) (Var y)).

Instance simplCond_computable o : Computable (simplCond o).
Proof.
  destruct o; try dec_solve.
  - decide (isReg p); dec_solve.
  - decide (isComparision b); try dec_solve.
    destruct o1, o2; try decide (isReg p); try decide (isReg p0); try dec_solve.
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
| IsLinExp e
           (SimplReg:simplOp e)
  : isLinearizable (stmtReturn e)
| IsLinCall F t
  : (forall n Zs, get F n Zs -> isLinearizable (snd Zs))
    -> isLinearizable t
    -> isLinearizable (stmtFun F t).

Instance isLinearizable_computable s : Computable (isLinearizable s).
Proof.
  sind s; destruct s.
  - destruct e; try dec_solve.
    decide (simplLet x e); try dec_solve.
    destruct (IH s); try dec_solve.
  - decide (simplCond e); try dec_solve.
    destruct (IH s1); eauto; try dec_solve;
      destruct (IH s2); eauto; try dec_solve.
  - left; eauto using isLinearizable.
  - decide (simplOp e); try dec_solve.
  - destruct (IH s); eauto; try dec_solve.
    assert (Computable (forall n Zs, get F n Zs -> isLinearizable (snd Zs))). {
      eapply indexwise_P_dec. intros. eapply IH; eauto.
    }
    destruct H; dec_solve.
Qed.

Definition isLinearizableStmt s := B[isLinearizable s].

Require Import Status.

Definition toLinearPreconditions k s : status unit :=
  if [noParams s] then
    if [isLinearizable s] then
      if [ var_P (regbnd k) s ] then
        Success tt
      else
        Error "Register bound not OK"
    else
      Error "Program is not linearizable"
  else
    Error "There are parameters left in the program".
