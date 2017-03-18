Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.
Require Import Take TakeSet.


Set Implicit Arguments.

Definition set_take (X:Type) `{OrderedType X} (k:nat) (x:⦃X⦄)
  := of_list (take k (elements x))
.

Definition set_take_prefer (X:Type) `{OrderedType X} (k:nat) (x y : ⦃X⦄)
  := of_list (take k (elements (x ∩ y) ++ elements (x \ y)))
.

Definition set_take_avoid (X:Type) `{OrderedType X} (k:nat) (x y : ⦃X⦄)
  := of_list (take k (elements (x \ y) ++ elements (x ∩ y)))
.


Lemma set_take_incl (X:Type) `{OrderedType X} k (x:⦃X⦄)
  : set_take k x ⊆ x
.
Proof.
  apply take_set_incl.
Qed.


Lemma set_take_prefer_incl (X:Type) `{OrderedType X} k (x y:⦃X⦄)
  : set_take_prefer k x y ⊆ x
.
Proof.
  decide (k < cardinal (x ∩ y)); unfold set_take_prefer; try rewrite <-elements_length in *;
    [rewrite take_app_le|rewrite take_app_ge]; [|omega| |omega].
  - rewrite take_set_incl. cset_tac.
  - rewrite of_list_app.
    apply union_incl_split; [rewrite of_list_elements|rewrite take_set_incl]; cset_tac.
Qed.


Lemma set_take_avoid_incl (X:Type) `{OrderedType X} k (x y:⦃X⦄)
  : set_take_avoid k x y ⊆ x
.
Proof.
  decide (k < cardinal (x \ y)); unfold set_take_avoid; try rewrite <-elements_length in *;
    [rewrite take_app_le|rewrite take_app_ge]; [|omega| |omega].
  - rewrite take_set_incl. cset_tac.
  - rewrite of_list_app.
    apply union_incl_split; [rewrite of_list_elements|rewrite take_set_incl]; cset_tac.
Qed.


Lemma set_take_prefer_eq (X:Type) `{OrderedType X} k (x y:⦃X⦄)
  : cardinal x <= k -> set_take_prefer k x y [=] x
.
Proof.
  intros card.
  decide (x ⊆ y); unfold set_take_prefer; try rewrite <-elements_length in *.
  - rewrite take_app_ge, of_list_app, of_list_elements, union_comm, union_subset_equal;
      [cset_tac|rewrite take_set_incl; cset_tac|rewrite elements_length, inter_subset_equal];
      eauto; rewrite <-elements_length; eauto.
  - rewrite take_app_ge; [|rewrite elements_length in *;rewrite <-meet_in_left in card; eauto].
    rewrite of_list_app, take_eq_ge, !of_list_elements; [cset_tac|].
    unfold ge. rewrite !elements_length in *.
    enough (cardinal (x ∩ y) + cardinal (x \ y) <= cardinal x); [rewrite <-H0 in card; omega|].
    rewrite <-union_cardinal; [rewrite <-set_decomp; eauto|].
    cset_tac.
Qed.

Lemma set_take_avoid_incl2 (X:Type) `{OrderedType X} k (x y:⦃X⦄)
  : k <= cardinal (x \ y) -> set_take_avoid k x y ⊆ x \ y
.
Proof.
  intros card.
  unfold set_take_avoid. rewrite <-elements_length in card. rewrite take_app_le; eauto.
  apply set_take_incl.
Qed.


Fixpoint stretch_rms (X : Type) (k : nat) (F : list X) (rms : list (⦃var⦄ * ⦃var⦄)) (lvF : list ⦃var⦄)
  {struct F} : list (⦃var⦄ * ⦃var⦄) :=
  match F,rms,lvF with
    | (x::F) , nil          , (LV::lvF) => let Rf := set_take k LV in
                                          (Rf, LV \ Rf) :: stretch_rms k F nil lvF
    | (x::F), ((Rf,Mf)::rms), (LV::lvF) => let Rf':= set_take k Rf in
                                          (Rf, LV \ Rf'):: stretch_rms k F rms lvF
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
    => let Fv_e := Exp.freeVars e in
      let L'   := (Fv_e \ R) ∪ (L ∩ ((Sp ∩ R) ∪ M)) in
      (* we only use register liveness at 2 points to make some preferences in the selection of the kill set: (here)
         if the register liveness is incorrect we will still get a correct spilling *)
      let K    := of_list (take (cardinal (R ∪ L') - k) (elements (R \ Fv_e \ getAnn rlv')
                                                                  ++ elements (getAnn rlv' ∩ R \ Fv_e))) in
      let R_e  := R \ K ∪ L' in
      let K_x  := one_or_empty_if' k R_e (R_e \ getAnn rlv') in
      (* here we need normal liveness, because we have to spilled variables that are loaded later on *)
      let Sp'  := (getAnn lv' ∩ (K ∪ K_x) \ M) ∪ (Sp ∩ R) in
      let R_s  := {x; R_e \ K_x} in
      ann1 (Sp',L',nil) (repair_spill k ZL Λ R_s (Sp' ∪ M) s rlv' lv' sl')
           
  | stmtReturn e, _, _, ann0 (Sp,L,_)
    => let Fv_e := Op.freeVars e in
      let L'   := set_take_prefer k (Fv_e \ R ∪ (L ∩ ((Sp ∩ R) ∪ M))) Fv_e in
      let K    := set_take (cardinal (R ∪ L') - k) (R \ Fv_e) in
      let R_e  := R \ K ∪ L' in
      let Sp'  := Sp ∩ R in
      ann0 (Sp',L',nil)

  | stmtIf e s1 s2, ann2 _ rlv1 rlv2, ann2 _ lv1 lv2, ann2 (Sp,L,_) sl1 sl2
    => let Fv_e := Op.freeVars e in
      let L'   := (Fv_e \ R) ∪ (L ∩ ((Sp ∩ R) ∪ M)) in
      (* here is the second use of register liveness *)
      let K    := of_list (take (cardinal (R ∪ L') - k)
                                (elements (R \ Fv_e \ getAnn rlv1 \ getAnn rlv2)
                                          ++ elements ((getAnn rlv1 ∪ getAnn rlv2) ∩ R \ Fv_e))) in
       let R_e  := R \ K ∪ L' in
       let Sp'  := ((getAnn lv1 ∪ getAnn lv2) ∩ K \ M) ∪ (Sp ∩ R) in
       ann2 (Sp',L',nil)
            (repair_spill k ZL Λ R_e (Sp' ∪ M) s1 rlv1 lv1 sl1)
            (repair_spill k ZL Λ R_e (Sp' ∪ M) s2 rlv2 lv2 sl2)

  | stmtApp f Y, _, _, ann0 (Sp,L,(R',M')::nil)
    => let R_f := fst (nth (counted f) Λ (∅,∅)) in
      let M_f := snd (nth (counted f) Λ (∅,∅)) in
      let Z   := nth (counted f) ZL nil in
      let L'  := (R_f \ of_list Z \ R) ∪ (L ∩ ((Sp ∩ R) ∪ M)) in
      let K   := set_take (cardinal (R ∪ L') - k) (R \ R_f) in
      let Sp' := (M_f  \ of_list Z \ M) ∪ (Sp ∩ R) in
      ann0 (Sp',L',(R',(Sp' ∪ M) ∩ list_union (Op.freeVars ⊝ Y) \ (R \ K ∪ L') ∪ M')::nil)

  | stmtFun F t, annF rLV rlv_F rlv_t, annF LV lv_F lv_t, annF (Sp,L,rms) sl_F sl_t
    => let rms' := stretch_rms k F rms (getAnn ⊝ lv_F) in
      let ZL'  := fst ⊝ F ++ ZL in
      let Λ'   := rms' ++ Λ in
      let L'   := L ∩ ((Sp ∩ R) ∪ M) in
      (* here is the third use of register liveness *)
      let K    := of_list (take (cardinal (R ∪ L') - k)
                                (elements (R \ getAnn rlv_t) ++ elements (getAnn rlv_t ∩ R))) in
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

          