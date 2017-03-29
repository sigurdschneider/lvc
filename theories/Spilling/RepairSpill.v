Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.
Require Import Take TakeSet PickLK.


Set Implicit Arguments.

(** * Repair Spill  *)

Fixpoint stretch_rms (X : Type) (k : nat) (F : list X) (rms : list (⦃var⦄ * ⦃var⦄)) (lvF : list ⦃var⦄)
  {struct F} : list (⦃var⦄ * ⦃var⦄) :=
  match F,rms,lvF with
    | (x::F) , nil          , (LV::lvF) => let Rf := set_take k LV in
                                          (Rf, LV \ Rf) :: stretch_rms k F nil lvF
    | (x::F), ((Rf,Mf)::rms), (LV::lvF) => let Rf':= set_take_prefer k Rf LV in
                                          (Rf', (LV \ Rf') ∪ (Mf ∩ LV)):: stretch_rms k F rms lvF
    | _,_,_ => nil
  end
.

Fixpoint repair_spill
         (k : nat)
         (ZL: list params)
         (Λ : list (⦃var⦄ * ⦃var⦄))
         (R M : ⦃var⦄)
         (s : stmt)
         (rlv : ann ⦃var⦄) (* liveness of register variables *)
         (lv : ann ⦃var⦄)  (* normal liveness *)
         (sl : spilling)
         {struct s}
  : spilling :=
  match s,rlv,lv,sl with

  | stmtLet x e s, ann1 _ rlv', ann1 _ lv', ann1 (Sp,L,_) sl'
    => let Fv_e := Exp.freeVars e in (* this v has to be done also elsewhere !!!! *)
      let L'   := set_take_prefer (k - cardinal (Fv_e ∩ R \ L)) (L ∩ ((Sp ∩ R) ∪ M)) (Fv_e \ R) in
      (* we only use register liveness at 3 points to make some preferences
         in the selection of the kill set: (here)
         if the register liveness is incorrect we will still get a correct spilling *)
      let K    := pick_kill k R L' (Exp.freeVars e) (getAnn rlv) in
      let R_e  := R \ K ∪ L' in
      let K_x  := pick_killx k x R_e (getAnn rlv) in
   (* here we need normal liveness, because we have to spill variables that are loaded later on *)
      let Sp'  := (getAnn lv' ∩ (K ∪ K_x) \ M) ∪ (Sp ∩ R) in 
      ann1 (Sp',L',nil) (repair_spill k ZL Λ {x; R_e \ K_x} (Sp' ∪ M) s rlv' lv' sl')
           
  | stmtReturn e, _, _, ann0 (Sp,L,_)
    => let Fv_e := Op.freeVars e in
      let L'   := set_take_prefer (k - cardinal (Fv_e ∩ R \ L)) (L ∩ ((Sp ∩ R) ∪ M)) (Fv_e \ R) in
      let Sp'  := Sp ∩ R in
      ann0 (Sp',L',nil)

  | stmtIf e s1 s2, ann2 _ rlv1 rlv2, ann2 _ lv1 lv2, ann2 (Sp,L,_) sl1 sl2
    => let Fv_e := Op.freeVars e in
      let L'   := set_take_prefer (k - cardinal (Fv_e ∩ R \ L)) (L ∩ ((Sp ∩ R) ∪ M)) (Fv_e \ R) in
      (* here is the second use of register liveness *)
      let K    := pick_kill k R L' (Op.freeVars e) (getAnn rlv1 ∪ getAnn rlv2) in
      let Sp'  := ((getAnn lv1 ∪ getAnn lv2) ∩ K \ M) ∪ (Sp ∩ R) in
      ann2 (Sp',L',nil)
           (repair_spill k ZL Λ (R \ K ∪ L') (Sp' ∪ M) s1 rlv1 lv1 sl1)
           (repair_spill k ZL Λ (R \ K ∪ L') (Sp' ∪ M) s2 rlv2 lv2 sl2)

  | stmtApp f Y, _, _, ann0 (Sp,L,(R',M')::nil)
    => let fv_Y:= list_union (Op.freeVars ⊝ Y) in
      let R_f := fst (nth (counted f) Λ (∅,∅)) in
      let M_f := snd (nth (counted f) Λ (∅,∅)) in
      let Z   := nth (counted f) ZL nil in
      let L'  := set_take_prefer k (L ∩ ((Sp ∩ R) ∪ M)) (R_f \ of_list Z \ R) in
      let K   := pick_kill k R L' (R_f \ of_list Z) (list_union (Op.freeVars ⊝ Y) \ M') in
      let M'' := (M \ (R \ K ∪ L)) ∩ fv_Y ∪ (M' ∩ (Sp ∪ M)) in
      let Sp' := ((fv_Y ∩ K \ M) ∪ (M_f  \ of_list Z \ M)) ∪ (Sp ∩ R) in
      ann0 (Sp',L',(R', M'')::nil)

  | stmtFun F t, annF rLV rlv_F rlv_t, annF LV lv_F lv_t, annF (Sp,L,rms) sl_F sl_t
    => let rms' := stretch_rms k F rms (getAnn ⊝ lv_F) in
      let ZL'  := fst ⊝ F ++ ZL in
      let Λ'   := rms' ++ Λ in
      let L'   := set_take k (L ∩ ((Sp ∩ R) ∪ M)) in
      (* here is the third use of register liveness *)
      let K    := pick_kill k R L' ∅ (getAnn rlv_t) in
      let Sp'  := ((getAnn lv_t) ∩ K \ M) ∪ (Sp ∩ R) in

       annF (Sp, L, rms)
            ((fun f rmlvsl
              => match rmlvsl with (rm, rLv, Lv, sl)
                                => repair_spill k ZL' Λ' (fst rm) (snd rm) (snd f) rLv Lv sl
                 end)
               ⊜ F (pair ⊜ (pair ⊜ (pair ⊜ rms rlv_F) lv_F) sl_F))
            (repair_spill k ZL' Λ' (R \ K ∪ L) M t rlv_t lv_t sl_t)

  | _,_,_,_ => ann0 (∅, ∅, nil)

  end
.
