Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.
Require Import Take TakeSet PickLK.


Set Implicit Arguments.

(** * Repair Spill  *)

Fixpoint stretch_rms (k : nat) (F : list params) (rms : list (⦃var⦄ * ⦃var⦄)) (lvF : list ⦃var⦄)
  {struct F} : list (⦃var⦄ * ⦃var⦄) :=
  match F,rms,lvF with
    | (x::F) , nil          , (LV::lvF) => (∅, LV) :: stretch_rms k F nil lvF
    | (x::F), ((Rf,Mf)::rms), (LV::lvF) => let Rf' := set_take k (Rf ∩ LV) in
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
      let L'   := pick_load k R M Sp L Fv_e in
      (* we only use register liveness at 3 points to make some preferences
         in the selection of the kill set: (here)
         if the register liveness is incorrect we will still get a correct spilling *)
      let K    := pick_kill k R L' (Exp.freeVars e) (getAnn rlv') in
      let R_e  := R \ K ∪ L' in
      let K_x  := pick_killx k R_e (getAnn rlv') in
   (* here we need normal liveness, because we have to spill variables that are loaded later on *)
      let Sp'  := (getAnn lv' ∩ (K ∪ K_x) \ M) ∪ (Sp ∩ R) in
      ann1 (Sp',L',nil) (repair_spill k ZL Λ {x; R_e \ K_x} (Sp' ∪ M) s rlv' lv' sl')

  | stmtReturn e, _, _, ann0 (Sp,L,_)
    => let Fv_e := Op.freeVars e in
      let L'   := pick_load k R M Sp L Fv_e in
      let Sp'  := Sp ∩ R in
      ann0 (Sp',L',nil)

  | stmtIf e s1 s2, ann2 _ rlv1 rlv2, ann2 _ lv1 lv2, ann2 (Sp,L,_) sl1 sl2
    => let Fv_e := Op.freeVars e in
      let L'   := pick_load k R M Sp L Fv_e in
      (* here is the second use of register liveness *)
      let K    := pick_kill k R L' (Op.freeVars e) (getAnn rlv1 ∪ getAnn rlv2) in
      let Sp'  := ((getAnn lv1 ∪ getAnn lv2) ∩ K \ M) ∪ (Sp ∩ R) in
      ann2 (Sp',L',nil)
           (repair_spill k ZL Λ (R \ K ∪ L') (Sp' ∪ M) s1 rlv1 lv1 sl1)
           (repair_spill k ZL Λ (R \ K ∪ L') (Sp' ∪ M) s2 rlv2 lv2 sl2)

  | stmtApp f Y, _, _, ann0 (Sp,L,RMappL)
    => let RMapp := nth 0 RMappL (∅,∅) in
      let fv_Y:= list_union (Op.freeVars ⊝ Y) in
      let R_f := fst (nth (counted f) Λ (∅,∅)) in
      let M_f := snd (nth (counted f) Λ (∅,∅)) in
      let Z   := nth (counted f) ZL nil in
      let L'  := pick_load k R M Sp L (R_f \ of_list Z) in
      let K   := pick_kill k R L' (R_f \ of_list Z)
                           (list_union (Op.freeVars ⊝ Y) ∩ fst RMapp) in
      let R'' := fst RMapp ∩ (R \ K ∪ L') ∩ fv_Y in
      let M'' := (fv_Y \ R'') ∪ (snd RMapp ∩ fv_Y) in
      let Sp' := ((M'' ∪ (M_f \ of_list Z)) ∩ (R \ M)) ∪ (Sp ∩ R) in
      ann0 (Sp',L',(R'', M'')::nil)

  | stmtFun F t, annF rLV rlv_F rlv_t, annF LV lv_F lv_t, annF (Sp,L,rms) sl_F sl_t
    => let rms' := stretch_rms k (fst ⊝ F) rms (getAnn ⊝ lv_F) in
      let ZL'  := fst ⊝ F ++ ZL in
      let Λ'   := rms' ++ Λ in
      let L'   := pick_load k R M Sp L ∅ in
      (* here is the third use of register liveness *)
      let K    := pick_kill k R L' ∅ (getAnn rlv_t) in
      let Sp'  := ((getAnn lv_t) ∩ K \ M) ∪ (Sp ∩ R) in

       annF (Sp', L', rms')
            ((fun f rmlvsl
              => match rmlvsl with (rm, rLv, Lv, sl)
                                => repair_spill k ZL' Λ' (fst rm) (snd rm) (snd f) rLv Lv sl
                 end)
               ⊜ F (pair ⊜ (pair ⊜ (pair ⊜ rms' rlv_F) lv_F) sl_F))
            (repair_spill k ZL' Λ' (R \ K ∪ L') (Sp' ∪ M) t rlv_t lv_t sl_t)

  | _,_,_,_ => ann0 (∅, ∅, nil)

  end
.

Lemma stretch_rms_length alv rms k F :
  length F = length alv -> length (stretch_rms k F rms alv) = length F
.
Proof.
  intros lenF. general induction F; destruct rms; destruct alv; isabsurd; cbn; eauto.
  destruct p as [Rf Mf]. cbn. rewrite IHF; eauto.
Qed.


Lemma stretch_rms_cardinal k F rms lvs n rm :
  get (stretch_rms k F rms lvs) n rm
  -> cardinal (fst rm) <= k
.
Proof.
  intros gett. general induction gett; destruct F; cbn; eauto; isabsurd.
  - cbn in *. destruct rms, lvs; isabsurd.
    + invc Heql. cbn. rewrite empty_cardinal. omega.
    + destruct p. isabsurd.
    + destruct p as [Rf Mf]. invc Heql. cbn. apply set_take_size.
  - cbn in *. destruct rms, lvs; invc Heql; isabsurd.
    + eapply IHgett; eauto.
    + destruct p; isabsurd.
    + destruct p as [Rf Mf]. invc H0. eapply IHgett; eauto.
Qed.



Lemma stretch_rms_lv k F rms lvs :
  length F = length lvs
  -> PIR2 Equal lvs (merge ⊝ stretch_rms k F rms lvs)
.
Proof.
  intros lenF. general induction F; destruct lvs; isabsurd; cbn in lenF; eauto.
  apply eq_add_S in lenF. destruct rms; cbn.
  - econstructor; unfold merge; cbn; eauto. cset_tac.
  - destruct p as [Rf Mf]. econstructor; eauto; unfold merge. cbn.
    setoid_rewrite <-inter_subset_equal at 3; swap 1 2.
    + rewrite set_take_incl, meet_comm. apply meet_in_left.
    + cset_tac.
Qed.