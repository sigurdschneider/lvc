Require Import List Map Env AllInRel Exp.
Require Import IL Annotation AnnP InRel AutoIndTac Liveness LabelsDefined.
Require Import ExpVarsBounded.


Notation "'spilling'"
  := (ann (⦃var⦄ * ⦃var⦄ * list (⦃var⦄ * ⦃var⦄))).

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
      -> k > 0
      -> cardinal (R\K ∪ L) <= k
      -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
      -> spill_sound k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,nil) sl)

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
                    (ann0 (Sp,L,nil))

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
      -> spill_sound k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,nil) sl_s sl_t)

  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K R_f M_f R' M' : ⦃var⦄)
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
      -> list_union (Op.freeVars ⊝ Y) ⊆ (R\K ∪ L) ∪ M'
      -> R' [=] R\K ∪ L
      -> M' ⊆ Sp ∪ M
      -> spill_sound k ZL Λ (R,M) (stmtApp f Y)
                     (ann0 (Sp,L, (R', M')::nil))

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
      -> (forall n Zs rm sl_s, get rms n rm
                         -> get F n Zs
                         -> get sl_F n sl_s
                         -> spill_sound k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) rm (snd Zs) sl_s
        )
      -> spill_sound k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t sl_t
      -> spill_sound k ZL Λ (R,M) (stmtFun F t)
                    (annF (Sp,L,rms) sl_F sl_t)
.



Lemma Sp_sub_R
      (ZL : list params)
      (k : nat)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    spill_sound k ZL Λ (R,M) s sl
    -> getSp sl ⊆ R
.
Proof.
  intros spillSnd.
  invc spillSnd;
    cset_tac.
Qed.



Lemma L_sub_SpM
      (ZL : list params)
      (k : nat)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    spill_sound k ZL Λ (R,M) s sl
    -> getL sl ⊆ getSp sl ∪ M
.
Proof.
  intros spillSnd.
  invc spillSnd; cset_tac.
Qed.

Definition merge (RM : set var * set var) :=
  fst RM ∪ snd RM.

Inductive spill_live
          (VD : ⦃var⦄)
  :
    spilling -> ann (set var) -> Prop
  :=
  | SomeSpLv0 a b
    : spill_live VD (ann0 a) (ann0 b)
  | SomeSpLv1 a b sl lv
    : spill_live VD sl lv
      -> spill_live VD (ann1 a sl) (ann1 b lv)
  | SomeSpLv2 a b sl1 sl2 lv1 lv2
    : spill_live VD sl1 lv1
      -> spill_live VD sl2 lv2
      -> spill_live VD (ann2 a sl1 sl2) (ann2 b lv1 lv2)
  | SomeSpLvF a b sl_F sl_t lv_F lv_t rms
    : PIR2 Equal (merge ⊝ rms) (getAnn ⊝ lv_F)
      -> spill_live VD sl_t lv_t
      -> (forall n rm,
            get rms n rm
            -> fst rm ⊆ VD /\ snd rm ⊆ VD)
      -> (forall n sl_s lv_s,
            get sl_F n sl_s
            -> get lv_F n lv_s
            -> spill_live VD sl_s lv_s
        )
      -> spill_live VD (annF (a, rms) sl_F sl_t)
                              (annF b lv_F lv_t)
.
