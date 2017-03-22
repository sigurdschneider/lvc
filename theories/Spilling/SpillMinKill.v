Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty RegLive.
Require Import Take TakeSet.


Set Implicit Arguments.


(* TODO : - adjust spill_min_kill such that no explicit kill set is necessary 
          - prove spill_sound -> spill_min_kill *)


Inductive spill_min_kill (k:nat) :
  (list params)
  -> (list (⦃var⦄ * ⦃var⦄))
  -> (⦃var⦄ * ⦃var⦄)
  -> stmt
  -> ann ⦃var⦄
  -> spilling
  -> Prop
  :=

  | SpillLet
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
      (rlv : ann ⦃var⦄)
    : let K := set_take_avoid (cardinal (R ∪ L) - k) (R \ Exp.freeVars e) (getAnn rlv) in
      let Kx:= set_take_avoid (1 + cardinal (R \ K ∪ L) - k) (R \ K ∪ L) (getAnn rlv) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> spill_min_kill k ZL Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s rlv sl
      -> Exp.freeVars e ⊆ R\K ∪ L
      -> k > 0
      -> cardinal (R\K ∪ L) <= k
      -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
      -> spill_min_kill k ZL Λ (R,M) (stmtLet x e s) (ann1 Rlv rlv) (ann1 (Sp,L,nil) sl)
                       
  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv: ⦃var⦄)
      (e : op)
    : let K := set_take (cardinal (R ∪ L) - k) (R \ Op.freeVars e) in 
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal ((R\K) ∪ L) <= k
      -> spill_min_kill k ZL Λ (R,M) (stmtReturn e) (ann0 Rlv) (ann0 (Sp,L,nil))

  | SpillIf
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv: ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)
      (rlv1 rlv2 : ann ⦃var⦄)
    : let K := set_take_avoid (cardinal (R ∪ L) - k) (R \ Op.freeVars e ) (getAnn rlv1 ∪ getAnn rlv2) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> spill_min_kill k ZL Λ (R\K ∪ L, Sp ∪ M) s rlv1 sl_s
      -> spill_min_kill k ZL Λ (R\K ∪ L, Sp ∪ M) t rlv2 sl_t
      -> spill_min_kill k ZL Λ (R,M) (stmtIf e s t) (ann2 Rlv rlv1 rlv2) (ann2 (Sp,L,nil) sl_s sl_t)

  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L R_f M_f R' M' Rlv : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
    : let K := set_take (cardinal (R ∪ L) - k) (R \ R_f) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> get ZL (counted f) Z
      -> get Λ (counted f) (R_f,M_f)
      -> R_f \ of_list Z ⊆ R\K ∪ L
      -> M_f \ of_list Z ⊆ Sp ∪ M
      -> list_union (Op.freeVars ⊝ Y) ⊆ (R\K ∪ L) ∪ M'
      -> M' ⊆ Sp ∪ M
      -> spill_min_kill k ZL Λ (R,M) (stmtApp f Y) (ann0 Rlv) (ann0 (Sp,L, (R', M')::nil))

  | SpillFun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
      (rlv_t : ann ⦃var⦄)
      (rlv_F : list (ann ⦃var⦄))
    : let K := set_take_avoid (cardinal (R ∪ L) - k) R (getAnn rlv_t) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> length F = length sl_F
      -> length F = length rms
      -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
      -> (forall n Zs rm rlv_s sl_s, get rms n rm
                         -> get F n Zs
                         -> get rlv_F n rlv_s
                         -> get sl_F n sl_s
                         -> spill_min_kill k ((fst ⊝ F) ++ ZL)
                                          (rms ++ Λ) rm (snd Zs) rlv_s sl_s
        )
      -> spill_min_kill k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t rlv_t sl_t
      -> spill_min_kill k ZL Λ (R,M) (stmtFun F t) (annF Rlv rlv_F rlv_t) (annF (Sp,L,rms) sl_F sl_t)
.


Lemma spill_sound_spill_min_kill k ZL Λ R R' M s sl rlv :
  spill_sound k ZL Λ (R,M) s sl
  -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
  -> getAnn rlv ⊆ R'
  -> spill_min_kill k ZL Λ (R',M) s rlv sl
.
Proof.
  intros spillSnd rlive rlv_sub. general induction spillSnd; invc rlive; cbn in rlv_sub.
  - econstructor; eauto;
      set (K' := set_take_avoid (cardinal (R' ∪ L) - k) (R' \ Exp.freeVars e) (getAnn al));
      set (Kx':= set_take_avoid (1 + cardinal (R' \ K' ∪ L) - k) (R' \ K' ∪ L) (getAnn al)).
    + admit. (* Sp ⊆ getAnn rlv Lemma *)
    + eapply IHspillSnd; eauto. admit. (* disj (set_take_avoid s t) t Lemma *)
    + rewrite <-rlv_sub. admit. (* solvable *)
    + admit. (* Lemma *)
    + admit. (* analogous *)
  -           
  
      

