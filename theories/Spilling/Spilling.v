Require Import List Map Env AllInRel Exp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.


Notation "'spilling'"
  := (ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄) + ⦃var⦄))).

Notation "'getSp' sl" := (fst (fst (getAnn sl))) (at level 40).
Notation "'getL' sl" := (snd (fst (getAnn sl))) (at level 40).

Notation "'getRm' sl" := (snd (getAnn sl)) (at level 40, only parsing).

Inductive spill_sound (k:nat) :
  (list params)
  -> (list (⦃var⦄ * ⦃var⦄))
  -> (⦃var⦄ * ⦃var⦄)
  -> stmt
  -> spilling
  -> Prop
  :=

  | SpillLet
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K Kx : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> spill_sound k ZL Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s sl
      -> Exp.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
      -> spill_sound k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,None) sl)

  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (e : op)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal ((R\K) ∪ L) <= k
      -> spill_sound k ZL Λ (R,M) (stmtReturn e)
                    (ann0 (Sp,L,None))

  | SpillIf
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)

    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> spill_sound k ZL Λ (R\K ∪ L, Sp ∪ M) s sl_s
      -> spill_sound k ZL Λ (R\K ∪ L, Sp ∪ M) t sl_t
      -> spill_sound k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,None) sl_s sl_t)

  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K R_f M_f Sl : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> get ZL (counted f) Z
      -> get Λ (counted f) (R_f,M_f)
      -> R_f \ of_list Z ⊆ R\K ∪ L
      -> M_f \ of_list Z ⊆ Sp ∪ M
      -> list_union (Op.freeVars ⊝ Y) ⊆ Sl ∪ (R\K ∪ L)
      -> Sl ⊆ Sp ∪ M
      -> spill_sound k ZL Λ (R,M) (stmtApp f Y)
                     (ann0 (Sp,L,(Some (inr Sl))))

  | SpillFun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> length F = length sl_F
      -> length F = length rms
      -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
      -> (forall n rm Zs, get rms n rm 
                          -> get F n Zs
                          -> disj (fst rm ∩ of_list (fst Zs)) (snd rm ∩ of_list (fst Zs)))
      -> (forall n Zs rm sl_s, get rms n rm
                         -> get F n Zs
                         -> get sl_F n sl_s
                         -> spill_sound k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) rm (snd Zs) sl_s
        )
      -> spill_sound k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t sl_t
      -> spill_sound k ZL Λ (R,M) (stmtFun F t)
                    (annF (Sp,L,Some (inl rms)) sl_F sl_t)
.

Inductive fv_e_bounded : nat -> stmt -> Prop :=

| BoundLet k x e s
  : cardinal (Exp.freeVars e) <= k
    -> fv_e_bounded k s
    -> fv_e_bounded k (stmtLet x e s)

| BoundReturn k e
  : cardinal (Op.freeVars e) <= k
    -> fv_e_bounded k (stmtReturn e)

| BoundIf k e s t
  : cardinal (Op.freeVars e) <= k
    -> fv_e_bounded k s
    -> fv_e_bounded k t
    -> fv_e_bounded k (stmtIf e s t)

| BoundApp k f Y
  : cardinal (list_union (Op.freeVars ⊝ Y)) <= k
    -> fv_e_bounded k (stmtApp f Y)

| BoundFun k F t
  : (forall n Zs, get F n Zs -> fv_e_bounded k (snd Zs))
    -> fv_e_bounded k t
    -> fv_e_bounded k (stmtFun F t)
.
