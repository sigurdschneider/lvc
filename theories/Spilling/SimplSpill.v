Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation AnnP InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.
Require Import SpillSound ReconstrLive.
Require Import Take TakeSet.

Set Implicit Arguments.

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

Fixpoint simplSpill
         (k : nat)
         (ZL: list params)
         (Λ : list (⦃var⦄ * ⦃var⦄))
         (R M : ⦃var⦄)
         (s : stmt)
         (Lv : ann ⦃var⦄)
         {struct s}
  : spilling :=
  match s,Lv with

  | stmtLet x e s, ann1 LV lv
    => let Fv_e := Exp.freeVars e in
       let L    := Fv_e \ R in
       let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
       let R_e  := R \ K ∪ L in

       let K_x  := one_or_empty_if k R_e in
       let Sp   := getAnn lv ∩ (K ∪ K_x) \ M in
       let R_s  := {x; R_e \ K_x} in

       ann1 (Sp,L,nil) (simplSpill k ZL Λ R_s (Sp ∪ M) s lv)

  | stmtReturn e, _
    => let Fv_e := Op.freeVars e in
       let L    := Fv_e \ R in
       let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
       let R_e  := R \ K ∪ L in
       let Sp   := ∅ in

       ann0 (Sp,L,nil)

  | stmtIf e s1 s2, ann2 LV lv1 lv2
    => let Fv_e := Op.freeVars e in
       let L    := Fv_e \ R in
       let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
       let R_e  := R \ K ∪ L in
       let Sp   := (getAnn lv1 ∪ getAnn lv2) ∩ K in

       ann2 (Sp,L,nil) (simplSpill k ZL Λ R_e (Sp ∪ M) s1 lv1)
            (simplSpill k ZL Λ R_e (Sp ∪ M) s2 lv2)

  | stmtApp f Y, _
    => let R_f := fst (nth (counted f) Λ (∅,∅)) in
       let M_f := snd (nth (counted f) Λ (∅,∅)) in
       let Z   := nth (counted f) ZL nil in
       let L   := R_f \ R \ of_list Z in
       let K    := of_list (take (cardinal L) (elements (R \ R_f))) in
       let Sp   := M_f \ M \ of_list Z ∪ (((list_union (Op.freeVars ⊝ Y) \ M) ∩ K)) in

       ann0 (Sp,L, (R \ K ∪ L, list_union (Op.freeVars ⊝ Y) \ (R \ K ∪ L))::nil)

  | stmtFun F t, annF LV als lv_t
    => let rms:= (fun f al =>
                   let Lv  := getAnn al in (* liveness in fn body *)
                   let Z  := fst f in    (* params of fn *)
                   let R_f := of_list (take k (elements Lv)) in
                   let M_f := Lv \ R_f in
                   (R_f, M_f)
                ) ⊜ F als in
       let ZL':= (fun f => fst f) ⊝ F ++ ZL in
       let Λ' := rms ++ Λ in


       annF (∅, ∅, rms)
            ((fun f rmlv
              => match rmlv with (rm, Lv)
                                => simplSpill k ZL' Λ' (fst rm) (snd rm) (snd f) Lv
                 end)
               ⊜ F ((fun rm al => (rm,al)) ⊜ rms als))
            (simplSpill k ZL' Λ' R M t lv_t)

  | _,_ => ann0 (∅, ∅, nil)

  end
.


(**********************************************************************)

Lemma seteq X `{OrderedType X} (s t : set X)
:  s \ (s \ t) ∪ t \ s [=] t.
Proof.
  rewrite minus_minus. clear. cset_tac.
Qed.

Lemma seteq_1 X `{OrderedType X} s t u1 u2 v w :
          s ∪ t ∪ (u1 ∩ v ∪ w)⊆ s ∪ t ∪ (u1 ∪ u2 ∩ v ∪ w).
Proof.
cset_tac.
Qed.

Lemma seteq_2 X `{OrderedType X} s t u1 u2 v w :
          s ∪ t ∪ (u2 ∩ v ∪ w) ⊆ s ∪ t ∪ (u1 ∪ u2 ∩ v ∪ w).
Proof.
cset_tac.
Qed.

Lemma minus_union_minus X `{OrderedType X} (s t u : set X)
: s \ t ∪ u \ t [=] (s ∪ u) \ t.
Proof.
cset_tac.
Qed.

Lemma fTake X `{OrderedType X} (s t : set X) n
 : t ⊆ (s \ of_list (take n (elements (s \ t))) ∪ t \ s).
Proof.
  assert (of_list (take n (elements ( s \ t))) ⊆ s \ t) as takeIncl. {
    rewrite take_set_incl. eauto with cset.
  }
  apply incl_minus_incl with (u:=s) in takeIncl.
  rewrite <- takeIncl.
  rewrite seteq at 1.
  reflexivity.
Qed.


Lemma rke X `{OrderedType X} (s t: set X) (k : nat)
: cardinal s <= k ->
  cardinal t <= k ->
  cardinal (s \ of_list (take (cardinal (t \ s)) (elements (s \ t))) ∪ t \ s) <= k.
Proof.
set (K := of_list (take (cardinal (t \ s)) (elements (s \ t)))) in *.
decide (cardinal (t \ s) <= cardinal (s \ t)).
* assert (cardinal K = cardinal (t \ s)) as crdKL.
  { subst K. rewrite <- elements_length.
    rewrite elements_of_list_size.
    + rewrite take_length_le; eauto. rewrite elements_length. eauto.
    + apply take_dupFree.
  }
 rewrite union_cardinal_le. rewrite cardinal_difference'.
  + rewrite crdKL.
    decide (cardinal (t \ s) <= cardinal s).
    - rewrite plus_comm.
      rewrite <- le_plus_minus; eauto. (* uses RleqK *)
    - rewrite not_le_minus_0.
      ** simpl. rewrite cardinal_difference. eauto.
      ** eauto.
  + subst K. rewrite take_set_incl. eauto with cset.
* apply not_le in n. subst K. rewrite take_eq_ge.
  + rewrite of_list_elements. rewrite minus_minus.
    enough (s ∩ t ∪ t \ s [=] t).
    { rewrite H0. eauto. }
    clear. cset_tac.
  + clear - n. rewrite elements_length. omega.
Qed.

Lemma rke' X `{OrderedType X} (s t u: set X) (k : nat)
: cardinal s <= k ->
  cardinal t <= k ->
  cardinal (s \ of_list (take (cardinal (t \ s \ u)) (elements (s \ t))) ∪ t \ s \ u) <= k.
Proof.
set (K := of_list (take (cardinal (t \ s \ u)) (elements (s \ t)))) in *.
decide (cardinal (t \ s \ u) <= cardinal (s \ t)).
* assert (cardinal K = cardinal (t \ s \ u)) as crdKL.
  { subst K. rewrite <- elements_length.
    rewrite elements_of_list_size.
    + rewrite take_length_le; eauto. rewrite elements_length. eauto.
    + apply take_dupFree.
  }
 rewrite union_cardinal_le. rewrite cardinal_difference'.
  + rewrite crdKL.
    decide (cardinal (t \ s \ u) <= cardinal s).
    - rewrite plus_comm.
      rewrite <- le_plus_minus; eauto.
    - rewrite not_le_minus_0.
      ** simpl. intros.
         rewrite !cardinal_difference. eauto.
      ** intro. eauto.
  + subst K. rewrite take_set_incl. eauto with cset.
* apply not_le in n. subst K. rewrite take_eq_ge.
  + rewrite of_list_elements. rewrite minus_minus.
    enough (s ∩ t ∪ t \ s \ u [=] t \ (u \ s ∩ t)).
    { rewrite H0. intros; rewrite cardinal_difference; eauto. }
    clear. cset_tac. decide (a ∈ s); cset_tac.
  + clear - n. rewrite elements_length. omega.
Qed.

Lemma rkk X `{OrderedType X} (s t  : set X) (k : nat) (x y : X)
: let K :=  of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  ) in
  let  K_x := one_or_empty_if k (s \ K ∪ t \ s) in
   cardinal s <= k
-> cardinal (t) <= k
-> k > 0
-> cardinal (s \ K ∪ t \ s) >= k

-> cardinal {x; (s \ K ∪ t \ s) \ K_x} <= k.
Proof.
intros K K_x RleqK fvBcard kgeq1 sizeRL.
rewrite add_cardinal. rewrite cardinal_difference'.
- subst K_x. rewrite one_or_empty_cardinal_ge.
  assert (rke := @rke X _ s t k RleqK fvBcard).
  remember (cardinal (s \ K ∪ t \ s)).
  destruct n.
  + omega. (*uses kgt0*)
  + simpl.
    enough (S n <= k). { omega. } rewrite Heqn. subst. exact rke.
  + omega.
  + eauto.
- subst K_x. eapply one_or_empty_of_incl.
Qed.

Lemma al_in_rkl X `{OrderedType X}
(s t u : set X) (al : ann (set X)) (x : X) :
let K :=  of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  ) in
getAnn al ⊆ s ∪ u ->
 getAnn al
   [<=] (s \
         of_list
           (take (cardinal (t \ s))
              (elements (s \ t))) ∪ t \ s)
        ∪ (getAnn al ∩ K ∪ u).
Proof.
intros K annRM a aIn.
apply union_iff.
decide (a ∈ of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                    )
        \/ a ∈ u).
- right. cset_tac.
- left. apply not_or_dist in n. destruct n as [nK nM].
  assert (a ∈ s) as aInR.
  { clear - nM annRM aIn. unfold Subset in annRM.
    specialize (annRM a aIn). cset_tac. }
  cset_tac.
Qed.

(* move somewhere *)
Lemma zip_length1
      (X : Type)
      (Y : Type)
      (Z : Type)
      (f : X -> Y -> Z)
      (xl: list X)
      (yl: list Y)
  :
    length xl = length yl -> length (f ⊜ xl yl) = length yl
.
Proof.
  intro eq_len.
  rewrite <- eq_len.
  apply zip_length2.
  assumption.
Qed.


    Lemma diff_inter_cardinal' X `{OrderedType X} (s s':set X)
      : cardinal (s \ s') = cardinal s - cardinal (s ∩ s').
    Proof.
      rewrite <- (diff_inter_cardinal s s'). omega.
    Qed.
    Lemma diff_inter_cardinal'' X `{OrderedType X} (s s':set X)
      : cardinal (s ∩ s') = cardinal s - cardinal (s \ s').
    Proof.
      rewrite <- (diff_inter_cardinal s s'). omega.
    Qed.

    Lemma diff_inter_cardinal_incl X `{OrderedType X} (s s':set X)
      : s' ⊆ s -> cardinal (s ∩ s') = cardinal s'.
    Proof.
      rewrite (diff_inter_cardinal'' s s').
      intros.
      rewrite cardinal_difference'; eauto.
      eapply subset_cardinal in H0. omega.
    Qed.
    Lemma take_of_list_cardinal_eq X `{OrderedType X} n (l : list X)
      : n <= length l
        -> NoDupA _eq l
        -> cardinal (of_list (take n l)) = n.
    Proof.
      revert n. induction l; intros n LE ND.
      - rewrite take_nil; simpl in *. rewrite empty_cardinal. omega.
      - destruct n; simpl in *.
        + rewrite empty_cardinal. omega.
        + inv ND.
          rewrite add_cardinal_2. rewrite IHl; try omega; eauto.
          intro; eapply H2. eapply InA_in.
          eapply take_list_incl; eauto.
    Qed.



(**********************************************************************)

Lemma simplSpill_sat_spillSound (k:nat) (s:stmt) (R R' M M': set var)
  (Λ Λ': list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> M [=] M'
-> Λ === Λ'
-> cardinal R' <= k
-> getAnn alv ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> PIR2 (fun RMf G => match RMf with (R_f,M_f)
                   => cardinal R_f <= k /\ R_f ∪ M_f ⊆ G end) Λ Lv
(*-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv*)
-> spill_sound k ZL Λ (R,M) s (simplSpill k ZL Λ R' M' s alv).

Proof.
intros kgeq1 ReqR' MeqM' ΛeqΛ' RleqK fvRM fvBound lvSound (*aeFree*) pir2.

general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt
       |k0 f0 Y0
       |k0 Z0 s0 t0 fvBs fvBt];
  (*inversion_clear aeFree;*)
   simpl.



- assert (rke := @rke var _ R' (Exp.freeVars e) k RleqK fvBcard).
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
        -- right. cset_tac; decide (a ∈ M); cset_tac.
        -- left. apply not_or_dist in n0. destruct n0 as [nK nM].
           decide (a = x).
           ++ cset_tac.
           ++ apply add_iff. right.
              unfold Subset in H0. specialize (H0 a).
              unfold Subset in fvRM. specialize (fvRM a).
              assert (a ∈ (getAnn al \ (singleton x))). { cset_tac. }
              assert (a ∈ R'). { cset_tac. }
              assert (a ∈ R' \ K).
              { cset_tac. } cset_tac.
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
      -- right. cset_tac.
      -- subst K. decide (a ∈ R'); cset_tac.
         exfalso.
         exploit H0; eauto; cset_tac.
  + rewrite ReqR'. eauto.
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
    clear; cset_tac. exploit H1; cset_tac.
  + rewrite H1, fvRM in Incl. revert Incl.
    rewrite ReqR', MeqM'.
    clear; cset_tac. exploit H; cset_tac.
  + subst K.
    eauto using rke'.
  + rewrite <- minus_incl with (s:=R'\K) (t:=of_list Z).
    rewrite minus_union_minus.
    apply incl_minus_lr with (s:=R_f) (s':=R'\K ∪ R_f \ R') (t:=of_list Z) (t':=of_list Z).
    * subst K. eapply fTake.
    * eauto.
  + cset_tac; decide (a ∈ M'); cset_tac.
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
    cset_tac. decide (a ∈ M'); eauto. left.
    decide (a ∈ K); eauto. left.
    subst K.
    exfalso. decide (a ∈ R'); eauto.
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
  + intros ; inv_get. eapply H1; eauto with cset.
(*     * apply list_eq_app; eauto. reflexivity. *)
    * simpl. apply take_of_list_cardinal.
    * clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. split.
      -- apply take_of_list_cardinal.
      -- rewrite take_set_incl at 1. eauto with cset.
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
      -- rewrite take_set_incl at 1. eauto with cset.
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
