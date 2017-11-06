Require Import Util IL DecSolve Indexwise.

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

Instance noParams_computable s : Computable (noParams s).
Proof.
    sind s; destruct s.
  - destruct (IH s); try dec_solve.
  - destruct (IH s1); eauto; try dec_solve;
      destruct (IH s2); eauto; try dec_solve.
  - destruct Y; dec_solve.
  - dec_solve.
  - destruct (IH s); eauto; try dec_solve.
    assert (Computable (forall n Zs, get F n Zs -> noParams (snd Zs))). {
      eapply indexwise_P_dec.
      intros.
      destruct (IH (snd a)); eauto;
        dec_solve.
    }
    assert (Computable (forall n Zs, get F n Zs -> fst Zs = nil)). {
      eapply indexwise_P_dec. intros.
      destruct (fst a); try dec_solve.
    }
    destruct H, H0; dec_solve.
Qed.