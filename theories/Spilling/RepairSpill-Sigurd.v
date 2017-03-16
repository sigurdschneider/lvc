Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation AnnP InRel AutoIndTac.
Require Import Liveness.Liveness LabelsDefined Filter.
Require Import SimI.
Require Import ExpVarsBounded SpillSound ReconstrLive.
Require Import Take TakeSet MoreTac.

Set Implicit Arguments.

(** * SimplSpill *)

Definition one_or_empty_if k X `{OrderedType X} (s:set X) : set X
  := if [cardinal s >= k] then
      match choose s with
      | Some x => singleton x
      | None => ∅
      end
    else
      ∅.

Lemma one_or_empty_of_incl k X `{OrderedType X} (s:set X)
  : one_or_empty_if k s ⊆ s.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  exploit choose_1; eauto. cset_tac.
Qed.

Lemma one_or_empty_cardinal_ge k X `{OrderedType X} (s:set X)
  : k > 0 -> cardinal s >= k -> cardinal (one_or_empty_if k s) = 1.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  - intros; exfalso.
    exploit choose_2; eauto.
    exploit cardinal_1; eauto. omega.
  - intros; omega.
Qed.

Lemma one_or_empty_cardinal_lt k X `{OrderedType X} (s:set X)
  : cardinal s < k -> one_or_empty_if k s = ∅.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  - intros; exfalso. omega.
Qed.

Definition subAnn X (a : ann X) : ann X :=
  match a with
  | ann0 a0 => a
  | ann1 a0 a1 => a1
  | ann2 a1 a2 a3 => a2
  | annF a0 sa a1 => a1
  end.

Definition subAnn2 X (a : ann X) : ann X :=
  match a with
  | ann0 a0 => a
  | ann1 a0 a1 => a1
  | ann2 a1 a2 a3 => a3
  | annF a0 sa a1 => a1
  end.

Definition subF X (a : ann X) : list (ann X) :=
  match a with
  | ann0 a0 => nil
  | ann1 a0 a1 => nil
  | ann2 a1 a2 a3 => nil
  | annF a0 sa a1 => sa
  end.


Definition subset X `{OrderedType X} (n:nat) (s:set X) :=
  of_list (take n (elements s)).

Lemma in_subset_inv X `{OrderedType X} k s x
  : x ∈ subset k s
    -> x ∈ s.
Proof.
  unfold subset.
  cset_tac'.
  rewrite take_set_incl in H0. eauto.
Qed.

Lemma incl_subset X `{OrderedType X} k s
  : subset k s ⊆ s.
Proof.
  eapply take_set_incl.
Qed.

Lemma subset_cardinal_ge (X : Type) (H : OrderedType X) k s
  : k >= cardinal s -> subset k s [=] s.
Proof.
  intros GE. unfold subset.
  rewrite take_eq_ge; eauto.
  rewrite of_list_elements; eauto.
  rewrite <- SetInterface.cardinal_1. eauto.
Qed.

Print Scopes.

Local Notation "'getR' sl" := (fst (fst sl)) (at level 40).
Local Notation "'getM' sl" := (snd (fst sl)) (at level 40).

Definition addToLoadSet (a:spilling) (L:set var) :=
  setTopAnn a (getSp a, L ∪ getL a, getRm a).

Local Notation "'getAppR' sl" := (fst (hd (∅,∅) (snd (getAnn (sl:spilling))))) (at level 40).
Local Notation "'getAppM' sl" := (snd (hd (∅,∅) (snd (getAnn (sl:spilling))))) (at level 40).

Fixpoint repairSpill
         (k : nat)
         (ZL: list params)
         (Λ : list (⦃var⦄ * ⦃var⦄))
         (R M : ⦃var⦄)
         (s : stmt)
         (Lv : ann ⦃var⦄)
         (Sp: spilling)
         {struct s}
  : ⦃var⦄ * ⦃var⦄ * spilling :=
  match s,Lv,Sp with

  | stmtLet x e s, ann1 LV lv, sp
    => let Fv_e := Exp.freeVars e in
      let Rec  := repairSpill k ZL Λ ({x; getL sp ∪ R}) (getSp sp ∪ M) s lv (subAnn sp) in
      let LE := (Fv_e \ R) ∪ (Fv_e ∩ getL sp) in
      let Ladd  := subset (k - cardinal Fv_e) (getL sp \ Fv_e) in
      let L    := LE ∪ Ladd in
      let Rcom := subset (k - cardinal Fv_e - cardinal Ladd)
                        (getR Rec \ {x; L}) in
      let Sp   := getSp sp ∪ (getM Rec \ M) in
      let LRec := getR Rec \ {x; L ∪ Rcom} in
      let a    := addToLoadSet (snd Rec) LRec in

      (Rcom ∪ (Fv_e \ L), (L ∪ getM Rec) \ ((getSp sp ∪ getM Rec) \ M) , ann1 (Sp,L,nil) a)

  | stmtReturn e, _, _
    => let Fv_e := Op.freeVars e in
      let L    := Fv_e \ R in
      let Sp   := ∅ in
      (Fv_e \ L, Sp, ann0 (Sp,L,nil))

  | stmtIf e s1 s2, ann2 LV lv1 lv2, sp
    => let Fv_e := Op.freeVars e in
      let Rec1 := repairSpill k ZL Λ (R ∪ getL sp) (getSp sp ∪ M) s1 lv1 (subAnn sp) in
      let Rec2 := repairSpill k ZL Λ (R ∪ getL sp) (getSp sp ∪ M) s2 lv2 (subAnn2 sp) in
      let LE   := (Fv_e \ R) ∪ (Fv_e ∩ getL sp) in
      let Ladd  := subset (k - cardinal Fv_e) (getL sp \ Fv_e) in
      let L     := LE ∪ Ladd in
      let Rcom := subset (k - cardinal Fv_e - cardinal Ladd)
                        ((getR Rec1 ∪ getR Rec2) \ L) in
      let LRec1 := getR Rec1 \ Rcom in
      let LRec2 := getR Rec2 \ Rcom in
      let a1    := addToLoadSet (snd Rec1) LRec1 in
      let a2    := addToLoadSet (snd Rec2) LRec2 in
      let Sp    := getSp sp ∪ ((getM Rec1 ∪ getM Rec2) \ M) in
      (Rcom ∪ (Fv_e \ L) ,
       (L ∪ getM Rec1 ∪ getM Rec2) \ ((getSp sp ∪ getM Rec1 ∪ getM Rec2) \ M),
       ann2 (Sp,L,nil) a1 a2)

  | stmtApp f Y, _, sp
    => let RM_f := nth (counted f) Λ (∅,∅) in
      let R_f  := fst RM_f in
      let M_f  := snd RM_f in
      let Z    := nth (counted f) ZL nil in
      let RReq := (R_f \ of_list Z) \ getL sp in
      let Ladd    := subset (k - cardinal RReq) (getAppR sp \ RReq) in
      let L    := (RReq ∪ Ladd) \ R in
      let MReq := getAppM sp ∪ (M_f \ of_list Z) in
      let Sp   := getSp sp ∪ MReq \ M in
      ((RReq ∪ Ladd) ∩ R, M ∪ (L ∪ MReq) \ getSp sp,
       ann0 (Sp, L, (RReq ∪ Ladd, list_union (Op.freeVars ⊝ Y) \ (RReq ∪ Ladd))::nil))

  | stmtFun F t, annF LV als lv_t, sp
    => let rms:= (fun f alsp =>
                   let Lv  := getAnn (fst alsp) in (* liveness in fn body *)
                   let Z  := fst f in    (* params of fn *)
                   let RM:set var * set var :=
                       hd (∅,∅) (snd (getAnn (snd alsp)))  in
                   if [ R ∪ M [=] Lv ] then (R, M)
                   else
                     let R_f := of_list (take k (elements Lv)) in
                     let M_f := Lv \ R_f in
                     (R_f, M_f)
                ) ⊜ F (zip pair als (subF sp)) in
       let ZL':= (fun f => fst f) ⊝ F ++ ZL in
       let Λ' := rms ++ Λ in
       let RecF :=
           ((fun f rmlvsp
             => match rmlvsp with ((rm, sp), Lv)
                                 => (repairSpill k ZL' Λ' (fst rm) (snd rm) (snd f) Lv sp)
               end)
              ⊜ F (pair ⊜ (zip pair rms (subF sp)) als)) in
       let Rec := repairSpill k ZL' Λ' R M t lv_t (subAnn sp) in
       (getR Rec, getM Rec, annF (∅, ∅, rms) (snd ⊝ RecF) (snd Rec))

  | _,_,_ => (∅, ∅, ann0 (∅, ∅, nil))

  end
.

Check
 (prod (prod (set nat) (set nat)) (list (prod (set nat) (set nat)))).


Lemma cardinal_union_left X `{OrderedType X} s t
  : cardinal s <= cardinal (s ∪ t).
Proof.
  eapply subset_cardinal. cset_tac.
Qed.

Lemma cardinal_union_right X `{OrderedType X} s t
  : cardinal t <= cardinal (s ∪ t).
Proof.
  eapply subset_cardinal. cset_tac.
Qed.

Definition spLe (a b:⦃nat⦄ * ⦃nat⦄ * list (⦃nat⦄ * ⦃nat⦄) ) :=
  prod_eq Subset Subset (fst a) (fst b) /\ PIR2 (prod_eq Subset Subset) (snd a) (snd b).

Lemma ann_R_spLE_addToLoadSet sl sl' s
  : ann_R spLe sl sl'
    -> s ⊆ getL sl'
    -> ann_R spLe
            (addToLoadSet sl s) sl'.
Proof.
  intros A.
  inv A; simpl; econstructor; eauto; hnf; simpl; invt spLe; split; eauto;
  destruct a as [[]],b as[[]]; try econstructor; simpl in *;
    invt @prod_eq;
    eauto with cset.
Qed.

Lemma ann_R_spLE_addToLoadSet' sl sl' s
  : ann_R spLe sl sl'
    -> s ⊆ getL sl
    -> ann_R spLe
            (addToLoadSet sl s) sl'.
Proof.
  intros A.
  inv A; simpl; econstructor; eauto; hnf; simpl; invt spLe; split; eauto;
  destruct a as [[]],b as[[]]; try econstructor; simpl in *;
    invt @prod_eq;
    eauto with cset.
Qed.

Lemma repairSpill_spillSound_id (k:nat) (s:stmt) (R R' M: set var)
  (Λ Λ': list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) sl :
  exp_vars_bounded k s
  -> live_sound Imperative ZL Lv s alv
  -> spill_sound k ZL Λ (R,M) s sl
  -> R ⊆ R'
  -> Λ === Λ'
(*-> PIR2 (fun RMf G => match RMf with (R_f,M_f)
                   => cardinal R_f <= k /\ R_f ∪ M_f ⊆ G end) Λ Lv*)
-> ann_R spLe (snd (repairSpill k ZL Λ R' M s alv sl)) sl
  /\ getM (repairSpill k ZL Λ R' M s alv sl) [=] M
  /\ getR (repairSpill k ZL Λ R' M s alv sl) ⊆ R'.
Proof.
  intros EVB LS SPS REQ LEQ.
  general induction SPS; invt live_sound; invt exp_vars_bounded; simpl in *.
  - edestruct IHSPS. eauto. eauto. reflexivity.
    instantiate (1:={x; L ∪ R'}). rewrite <- REQ.
    clear; cset_tac. eauto. dcr.
    split; [|split].
    + econstructor.
      split; eauto.
      econstructor.
      rewrite H7. clear; cset_tac.
      rewrite <- REQ.
      rewrite H1 at 1 2.
      unfold subset. rewrite take_set_incl.
      clear; cset_tac.
      econstructor.
      eapply ann_R_spLE_addToLoadSet'; eauto.
      rewrite H9 at 1.
      eapply ann_R_get in H5. hnf in H5; dcr.
      rewrite subset_cardinal_ge at 1.
      rewrite subset_cardinal_ge at 1.
      rewrite subset_cardinal_ge at 1.
      admit.
      admit.
      admit.
      admit.
    + rewrite H7.
      unfold subset.
      revert REQ H1 H0 H.
      clear.
      intros. cset_tac'.
      eapply in_subset_inv in H7. cset_tac.
    + dcr.
      assert (CardL:cardinal L <= k). {
        rewrite <- H3. eapply cardinal_union_right.
      }
      rewrite incl_subset.
      rewrite subset_cardinal_ge.
      rewrite H9.
      revert REQ.
      clear; cset_tac'.
      assert (L \ Exp.freeVars e ⊆ (R0 \ K ∪ L) \ Exp.freeVars e) by
          (clear; cset_tac).
      hnf. rewrite H6.
      rewrite cardinal_difference'; eauto. omega.
  - split.
    econstructor. econstructor. econstructor.
    cset_tac.
    cset_tac.
    econstructor.
    split. reflexivity. cset_tac.
  - edestruct IHSPS1. eauto. eauto. reflexivity.
    instantiate (1 := R' ∪ L). rewrite <- REQ.
    clear; cset_tac. eauto. dcr.
    edestruct IHSPS2. eauto. eauto. reflexivity.
    instantiate (1 := R' ∪ L). rewrite <- REQ.
    clear; cset_tac. eauto. dcr.
    econstructor.
    + econstructor.
      * econstructor; simpl; eauto using PIR2; split.
        -- rewrite H16,H5. clear; cset_tac.
        -- rewrite incl_subset.
           revert H1 REQ;
             clear; cset_tac'.
      * admit.
      * admit.
    + rewrite !H5. rewrite !H16.
      split.
      * rewrite subset_cardinal_ge.
        -- revert REQ H H0 H1;
             clear; cset_tac'.
        -- assert (L \ Op.freeVars e ⊆ (R0 \ K ∪ L) \ Op.freeVars e) by
              (clear; cset_tac).
           hnf. rewrite H15.
           rewrite cardinal_difference'; eauto. omega.
      * rewrite incl_subset.
        rewrite H8, H17.
        rewrite subset_cardinal_ge.
        -- revert REQ H H0 H1;
             clear; cset_tac'.
        -- assert (L \ Op.freeVars e ⊆ (R0 \ K ∪ L) \ Op.freeVars e) by
              (clear; cset_tac).
           hnf. rewrite H15.
           rewrite cardinal_difference'; eauto. omega.
  - inv_get.
    erewrite !get_nth; eauto. simpl.
    split.
    + econstructor. econstructor.
      * econstructor.
        -- rewrite H8. rewrite H5. clear; cset_tac.
        -- rewrite incl_subset.
           rewrite H7. rewrite <- REQ.
           rewrite H4 at 1.
           clear; cset_tac'.
      * econstructor; eauto using PIR2.
        econstructor; eauto.
        -- rewrite incl_subset.
           rewrite H7.
           rewrite H4 at 1.
           clear; cset_tac'.
        -- rewrite subset_cardinal_ge.
           rewrite H7.
           revert H6 H4; clear; cset_tac'.
           rewrite H7.
           hnf.
           assert ((R_f \ of_list Z) \ L ⊆ (R0 \ K ∪ L)) by
               (revert H4; clear; cset_tac).
           rewrite cardinal_difference'; eauto. omega.
    + split.
      * eapply incl_eq.
        -- clear; cset_tac.
        -- rewrite incl_subset.
           rewrite H4 at 1 3.
           rewrite H5. rewrite H7.
           revert H REQ H8 H0.
           clear; cset_tac'.
      * rewrite incl_subset.
        rewrite H7.
        rewrite H4 at 1.
        revert REQ. clear; cset_tac.
  - econstructor.
    + admit.
    + split. admit.
Admitted.

Lemma simplSpill_sat_spillSound (k:nat) (s:stmt) (R R' M M': set var)
  (Λ Λ': list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) sl
  : R [=] R'
    -> M [=] M'
    -> Λ === Λ'
    -> cardinal R' <= k
    -> getAnn alv ⊆ R ∪ M
    -> exp_vars_bounded k s
    -> live_sound Imperative ZL Lv s alv
    -> PIR2 (fun RMf G => match RMf with (R_f,M_f)
                                     => cardinal R_f <= k /\ R_f ∪ M_f ⊆ G end) Λ Lv
    (*-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv*)
    -> spill_sound k ZL Λ (R,M) s (snd (repairSpill k ZL Λ R' M' s alv sl)).
Proof.
intros ReqR' MeqM' ΛeqΛ' RleqK fvRM fvBound lvSound (*aeFree*) pir2.

general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt
       |k0 f0 Y0
       |k0 Z0 s0 t0 fvBs fvBt];
  (*inversion_clear aeFree;*)
   simpl in *.
- econstructor.
  assert (rke := @rke var _ R' (Exp.freeVars e) k RleqK fvBcard).
  assert (fTake := @fTake var _ R' (Exp.freeVars e) (cardinal (Exp.freeVars e \ R'))).
  set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  decide (cardinal (R' \ K ∪ Exp.freeVars e \ R') >= k).
  { rename g into sizeRL.
    set (K_x:=one_or_empty_if k (R' \ K ∪ Exp.freeVars e \ R' )).

    assert (rkk := @rkk var _ R' (Exp.freeVars e) k x).

    eapply SpillLet with (K:= K) (Kx := K_x); eauto.
    + subst K K_x; simpl in *.
      rewrite take_set_incl at 1.
      rewrite one_or_empty_of_incl; eauto.
      rewrite Exp.freeVars_live at 4; eauto.
      rewrite fvRM. rewrite ReqR', MeqM'.
      clear; cset_tac.
    + rewrite Exp.freeVars_live; eauto.
      rewrite fvRM. rewrite ReqR', MeqM'. clear; cset_tac.
    + eapply IHlvSound;
        try rewrite ReqR'; try rewrite <- MeqM'; try rewrite ΛeqΛ'; eauto.
      * unfold Subset; intro a. decide (a = x); [cset_tac|].
        intro aInAnn. rewrite union_iff.
        (** this can be simplified using al_in_rkl **)
        decide (   a ∈ K
              \/ a ∈ K_x
              \/ a ∈ M
             ).
        -- right. revert n aInAnn o; clear; cset_tac.
        -- left. apply not_or_dist in n0. destruct n0 as [nK nM].
           decide (a = x).
           ++ cset_tac.
           ++ apply add_iff. right.
              unfold Subset in H0. specialize (H0 a).
              unfold Subset in fvRM. specialize (fvRM a).
              assert (a ∈ (getAnn al \ (singleton x))). {
                revert aInAnn n0; clear; cset_tac.
              }
              assert (a ∈ R'). {
                rewrite <- ReqR'.
                revert nM H3 H0 fvRM. clear; cset_tac.
              }
              assert (a ∈ R' \ K). {
                revert H4 nK; clear; cset_tac.
              }
              revert nM H5; clear; cset_tac.
    + rewrite ReqR'. apply fTake.
    + rewrite ReqR'. apply rke.

    + rewrite ReqR'. apply rkk; eauto.
  }

  {
  rename n into sizeRL.


  assert (cardinal (Exp.freeVars e) < k) as leqK.
  { apply not_ge in sizeRL.
    rewrite <- fTake in sizeRL. exact sizeRL. }

  eapply SpillLet with
            (K:= of_list (take
                            (cardinal (Exp.freeVars e \ R'))
                            (elements (R' \ Exp.freeVars e))
                          )
            )
              (Kx := ∅).
  + subst K; simpl in *.
    rewrite take_set_incl at 1.
    rewrite one_or_empty_of_incl; eauto.
    rewrite Exp.freeVars_live at 4; eauto.
    rewrite fvRM. rewrite ReqR', MeqM'.
    clear; cset_tac.
  + rewrite Exp.freeVars_live at 1; eauto.
    rewrite fvRM. rewrite ReqR', MeqM'. clear; cset_tac.
  + eapply IHlvSound; eauto.
    * rewrite one_or_empty_cardinal_lt; try omega.
      subst K. rewrite ReqR'. cset_tac.
    * rewrite MeqM'. cset_tac.
    * rewrite one_or_empty_cardinal_lt; try omega.
      clear - sizeRL. rewrite add_cardinal. apply not_ge in sizeRL.
      rewrite minus_empty. omega.
    * rewrite ReqR', MeqM'. simpl in *. rewrite fvRM in H0.
      rewrite ReqR', MeqM' in H0.
      clear - sizeRL H0 fvRM ReqR' MeqM'.
      rewrite one_or_empty_cardinal_lt; try omega.
      unfold Subset; intro a. decide (a === x); [cset_tac|].
        intro aInAnn. rewrite union_iff.
        (** this can be simplified using al_in_rkl **)
        decide (   a ∈ K
              \/ a ∈ M'
             ).
      -- right. revert aInAnn o. clear. cset_tac.
      -- refold. clearbody K.
         revert aInAnn n0 n H0. clear; cset_tac.
  + rewrite ReqR'. eauto.
  + eauto.
  + subst K... rewrite ReqR'. exact rke.
  + rewrite minus_empty. rewrite add_cardinal. apply not_ge in sizeRL.
    rewrite ReqR'. clear - sizeRL. subst K... omega.
  }
- set (K := of_list (take
                       (cardinal (Op.freeVars e \ R'))
                       (elements (R' \ Op.freeVars e))
                  )) in *.
  eapply SpillIf with (K:= K);
  [  |  | rewrite ReqR'; apply fTake
  | rewrite ReqR'; apply rke; eauto
  | eapply IHlvSound1
  | eapply IHlvSound2 ];
  try rewrite ReqR'; try rewrite <- MeqM'; eauto;
  [ | | apply rke ; eauto  | | apply rke; eauto | ];
  [ | | rewrite <- seteq_1 | rewrite <- seteq_2 ];
  try (subst K; apply al_in_rkl; eauto;
       rewrite <- ReqR'; eauto with cset).
  simpl in *. subst K.
  rewrite take_set_incl. clear; cset_tac.
  rewrite Op.freeVars_live; eauto. simpl in *.
  rewrite fvRM. rewrite ReqR'. clear; cset_tac.
- eapply PIR2_nth_2 with (l:=counted l) in pir2; eauto using zip_get.
  destruct pir2 as [[R_f M_f] [pir2_get [pir2_R1 pir2_R2]]]. simpl in *.
  repeat erewrite get_nth; eauto; simpl.
  assert (Incl:(R_f ∪ M_f) \ of_list Z [<=] blv \ of_list Z).
  rewrite <- pir2_R2; eauto.
  set (K := of_list (take
                      (cardinal ((R_f \ R') \ of_list Z))
                      (elements (R' \ R_f))
                     )) in *.
  eapply SpillApp with (K:= K); try rewrite ReqR'; try rewrite MeqM'; eauto.
  + subst K.
    rewrite Op.freeVars_live_list; eauto.
    rewrite take_set_incl.
    rewrite fvRM. rewrite ReqR', MeqM'.
    rewrite H1, fvRM in Incl. revert Incl.
    rewrite ReqR', MeqM'.
    clear; cset_tac.
  + rewrite H1, fvRM in Incl. revert Incl.
    rewrite ReqR', MeqM'.
    clear; cset_tac.
  + subst K.
    eauto using rke'.
  + rewrite <- minus_incl with (s:=R'\K) (t:=of_list Z).
    rewrite minus_union_minus.
    apply incl_minus_lr with (s:=R_f) (s':=R'\K ∪ R_f \ R') (t:=of_list Z) (t':=of_list Z).
    * subst K. eapply fTake.
    * eauto.
  + cset_tac.
  + subst K.
    assert (forall (s t : ⦃var⦄), s ⊆ s \ t ∪ t) by (clear; cset_tac).

    intro a. decide (a ∈ (R' \ of_list (take (cardinal ((R_f \ R') \ of_list Z)) (elements (R' \ R_f)))
          ∪ (R_f \ R') \ of_list Z));
               cset_tac.
  + edestruct @list_eq_get; eauto; dcr. destruct x as [R_f' M_f']; invc H6.
    repeat erewrite get_nth; eauto; simpl.
    rewrite H1, fvRM, ReqR', MeqM' in Incl.
    exploit Op.freeVars_live_list; eauto. rewrite fvRM in H4.
    rewrite ReqR' in H4. rewrite MeqM' in H4.
    revert H4. clear. clearbody K. cset_tac.
- set (K := of_list (take
                       (cardinal (Op.freeVars e \ R'))
                       (elements (R' \ Op.freeVars e))
                  )) in *.
  eapply SpillReturn with (K:= K); try rewrite ReqR'; eauto.
  + cset_tac.
  + rewrite Op.freeVars_live; eauto.
    rewrite <- ReqR'. rewrite fvRM. cset_tac.
  + apply fTake.
  + apply rke; eauto.
- eapply SpillFun with (K:=∅); eauto.
  + clear. cset_tac.
  + assert (forall s:set var, s \ ∅ ∪ ∅ [=] s) as seteq'. { cset_tac. }
    rewrite (seteq' R). rewrite ReqR'. apply RleqK.
  + symmetry. apply zip_length2. rewrite H.
    symmetry. apply zip_length1.
    apply zip_length1.
    assumption.
  + symmetry. apply zip_length2. assumption.
  + intros ; inv_get. simpl. apply take_of_list_cardinal.
  + intros ; inv_get.
    eapply H1; eauto.
    * simpl. apply take_of_list_cardinal.
    * clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. split.
      -- apply take_of_list_cardinal.
      -- rewrite take_set_incl at 1.
         clear; eauto with cset.
  + eapply IHlvSound; eauto.
    * rewrite ReqR'. clear. cset_tac.
   (* * (8 apply list_eq_app.
      -- reflexivity.
      -- apply ΛeqΛ'. *)
    * rewrite H3. simpl in fvRM. rewrite fvRM. clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. split.
      -- apply take_of_list_cardinal.
      -- rewrite take_set_incl at 1.
         clear; eauto with cset.
         Grab Existential Variables. eauto. eauto.
Qed.


Lemma simplSpill_spill_live VD k ZL Lv Λ R M s alv
      (LS:live_sound Imperative ZL Lv s alv)
      (lvIncl:ann_P (fun lv => lv ⊆ VD) alv)
  : spill_live VD (simplSpill k ZL Λ R M s alv) alv.
Proof.
  move s before k.
  revert_until s.
  sind s.
  intros; destruct s; simpl; invt live_sound; invt ann_P;
    eauto using spill_live.
  - econstructor; intros; inv_get; simpl in *; eauto using spill_live.
    + eapply PIR2_get; intros; inv_get; unfold merge; simpl; eauto with len.
      rewrite union_comm. rewrite <- equiv_minus_union;
                            eauto using take_set_incl with cset.
    + simpl.
      exploit H7; eauto. eapply ann_P_get in H4. rewrite <- H4.
      rewrite take_set_incl at 1; simpl; eauto 20 with cset.
Qed.
