Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation AnnP AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.
Require Import SimI.
Require Import ExpVarsBounded SpillSound ReconstrLive.
Require Import Take TakeSet MoreTac.
Require Import OneOrEmpty.

Set Implicit Arguments.

(** * SplitSpill *)

Class kill_oracle_spec (kill_oracle:nat -> set var -> set var) :=
  {
    kill_oracle_incl : forall k (X:set var), kill_oracle k X ⊆ X;
    kill_oracle_card : forall k X, cardinal X >= k -> cardinal (kill_oracle k X) = k;
    kill_oracle_idem : forall k X, cardinal X < k -> kill_oracle k X [=] X
  }.

Section KO.
  Variable (kill_oracle:nat -> set var -> set var).

Fixpoint splitSpillKO
         (k : nat)
         (ZL: list params)
         (Λ : list (⦃var⦄ * ⦃var⦄))
         (R M : ⦃var⦄)
         (s : stmt)
         (Lv : ann ⦃var⦄)
         {struct s}
  : spilling :=
  match s,Lv with

  | stmtLet x e s, ann1 lv lvs
    => let Fv_e := Exp.freeVars e in
      let R := R ∩ lv in
      let L    := Fv_e \ R in
      let K    := kill_oracle (cardinal L - (k - cardinal R)) (R \ Fv_e) in
      let R_e  := R \ K ∪ L in

      let K_x  := one_or_empty_if k R_e in
      let Sp   := getAnn lvs ∩ (K ∪ K_x) \ M in
      let R_s  := {x; R_e \ K_x} in

      ann1 (Sp,L,nil) (splitSpillKO k ZL Λ R_s (Sp ∪ M) s lvs)

  | stmtReturn e, ann0 lv
    => let Fv_e := Op.freeVars e in
      let R := R ∩ lv in
       let L    := Fv_e \ R in
       let K    := kill_oracle (cardinal L - (k - cardinal R)) (R \ Fv_e) in
       let R_e  := R \ K ∪ L in
       let Sp   := ∅ in

       ann0 (Sp,L,nil)

  | stmtIf e s1 s2, ann2 lv lv1 lv2
    => let Fv_e := Op.freeVars e in
      let R := R ∩ lv in
       let L    := Fv_e \ R in
       let K    := kill_oracle (cardinal L - (k - cardinal R)) (R \ Fv_e) in
       let R_e  := R \ K ∪ L in
       let Sp   := (getAnn lv1 ∪ getAnn lv2) ∩ K in

       ann2 (Sp,L,nil) (splitSpillKO k ZL Λ R_e (Sp ∪ M) s1 lv1)
            (splitSpillKO k ZL Λ R_e (Sp ∪ M) s2 lv2)

  | stmtApp f Y, ann0 lv
    => let R_f := fst (nth (counted f) Λ (∅,∅)) in
      let M_f := snd (nth (counted f) Λ (∅,∅)) in
      let R := R ∩ lv in
       let Z   := nth (counted f) ZL nil in
       let L   := R_f \ R \ of_list Z in
       let K    := kill_oracle (cardinal L - (k - cardinal R)) (R \ R_f) in
       let fvY  := list_union (Op.freeVars ⊝ Y) in
       let Sp   := M_f \ M \ of_list Z ∪ (((fvY \ M) ∩ K)) in
       let R'   := R \ K ∪ L in
       let Rapp := fvY ∩ R' in
       let Mapp := fvY \ R' in
       ann0 (Sp,L, (Rapp,Mapp)::nil)

  | stmtFun F t, annF LV als lv_t
    =>
    let rms:= (fun f al =>
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
                                => splitSpillKO k ZL' Λ' (fst rm) (snd rm) (snd f) Lv
                 end)
               ⊜ F ((fun rm al => (rm,al)) ⊜ rms als))
            (splitSpillKO k ZL' Λ' R M t lv_t)

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

Variable kos : kill_oracle_spec kill_oracle.

Lemma kill_oracle_incl2 (s t : set var) n
 : t ⊆ (s \ kill_oracle n (s \ t)) ∪ t \ s.
Proof.
  rewrite kill_oracle_incl. cset_tac.
Qed.


Lemma omega_help1 X k Y
 : X - (k - Y) <= Y
   ->  Y <= k
   -> X + (Y - (X - (k - Y))) <= k.
Proof.
  omega.
Qed.

Lemma rke (s t: set var) (k : nat)
: cardinal s <= k ->
  cardinal t <= k ->
  cardinal (s \ kill_oracle (cardinal (t \ s) -(k - cardinal s)) (s \ t) ∪ t \ s) <= k.
Proof.
set (K := kill_oracle (cardinal (t \ s)-(k - cardinal s)) (s \ t)) in *.
decide (cardinal (t \ s) - (k - cardinal s) <= cardinal (s \ t)).
- assert (cardinal K = cardinal (t \ s)-(k - cardinal s)) as crdKL.
  { subst K. rewrite kill_oracle_card; eauto.
  }
  rewrite union_cardinal_le. rewrite cardinal_difference'.
  + rewrite crdKL.
    decide (cardinal (t \ s) - (k - cardinal s) <= cardinal s).
    * rewrite plus_comm.
      intros. eapply omega_help1; eauto.
    * rewrite not_le_minus_0.
      -- simpl. rewrite cardinal_difference. eauto.
      -- eauto.
  + subst K. rewrite kill_oracle_incl. eauto with cset.
- apply not_le in n. subst K.
  rewrite kill_oracle_idem; eauto.
  rewrite minus_minus.
  assert (EQ:s ∩ t ∪ t \ s [=] t) by (clear; cset_tac).
  rewrite EQ; eauto.
Qed.

Lemma rke' (s t u: set var) (k : nat)
: cardinal s <= k ->
  cardinal t <= k ->
  cardinal (s \ kill_oracle (cardinal (t \ s \ u) -(k - cardinal s)) (s \ t) ∪ t \ s \ u) <= k.
Proof.
set (K := kill_oracle (cardinal (t \ s \ u) -(k - cardinal s) ) (s \ t)) in *.
decide (cardinal (t \ s \ u) -(k - cardinal s) <= cardinal (s \ t)).
- assert (cardinal K = cardinal (t \ s \ u) -(k - cardinal s)) as crdKL.
  { subst K.
    rewrite kill_oracle_card; eauto.
  }
  rewrite union_cardinal_le. rewrite cardinal_difference'.
  + rewrite crdKL.
    decide (cardinal (t \ s \ u) - (k - cardinal s) <= cardinal s).
    * rewrite plus_comm.
      intros. eapply omega_help1; eauto.
    * rewrite not_le_minus_0.
      -- simpl. intros.
         rewrite !cardinal_difference. eauto.
      -- intro. eauto.
  + subst K. rewrite kill_oracle_incl. eauto with cset.
- apply not_le in n. subst K.
  rewrite kill_oracle_idem; eauto.
  rewrite minus_minus.
  enough (s ∩ t ∪ t \ s \ u [=] t \ (u \ s ∩ t)).
  { rewrite H. intros; rewrite cardinal_difference; eauto. }
  clear. cset_tac.
Qed.

Lemma rkk (s t  : set var) (k : nat) (x : var)
: let K :=  kill_oracle (cardinal (t \ s) - (k - cardinal s)) (s \ t) in
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
  assert (rke := @rke s t k RleqK fvBcard).
  remember (cardinal (s \ K ∪ t \ s)).
  destruct n.
  + omega. (*uses kgt0*)
  + simpl.
    enough (S n <= k). { omega. } rewrite Heqn. subst.
    eapply rke.
  + omega.
  + eauto.
- subst K_x. eapply one_or_empty_of_incl.
Qed.

Lemma al_in_rkl (s t u : set var) (al : ann (set var)) k :
let K := kill_oracle (cardinal (t \ s)  - (k - cardinal s)) (s \ t) in
getAnn al ⊆ s ∪ u ->
 getAnn al
   [<=] (s \ K ∪ t \ s)
        ∪ (getAnn al ∩ K ∪ u).
Proof.
intros K annRM a aIn. subst K.
apply union_iff.
decide (a ∈ kill_oracle (cardinal (t \ s)  - (k - cardinal s)) (s \ t) \/ a ∈ u).
- right. cset_tac.
- left. apply not_or_dist in n. destruct n as [nK nM].
  assert (a ∈ s) as aInR.
  { clear - nM annRM aIn. unfold Subset in annRM.
    specialize (annRM a aIn). cset_tac. }
  cset_tac.
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

Lemma splitSpillKO_sat_spillSound (k:nat) (s:stmt) (R R' M M': set var)
  (Λ Λ': list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
R [=] R'
-> M [=] M'
-> Λ === Λ'
-> cardinal R' <= k
-> getAnn alv ⊆ R ∪ M
-> exp_vars_bounded k s
-> live_sound Imperative ZL Lv s alv
-> PIR2 (fun RMf G => match RMf with (R_f,M_f)
                   => cardinal R_f <= k /\ R_f ∪ M_f ⊆ G end) Λ Lv
(*-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv*)
-> spill_sound k ZL Λ (R,M) s (splitSpillKO k ZL Λ R' M' s alv).

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
   simpl.
- assert (RleqK' : cardinal (R' ∩ lv) <= k). {
    rewrite subset_cardinal. eapply RleqK.
    clear. cset_tac.
  }
  assert (rke := @rke (R' ∩ lv) (Exp.freeVars e) k RleqK' fvBcard).
  set (K := kill_oracle
             (cardinal (Exp.freeVars e \ (R' ∩ lv)) - (k - cardinal (R' ∩ lv)))
             ((R' ∩ lv) \ Exp.freeVars e)
       ) in *.

  { (*rename g into sizeRL.*)
    set (K_x:=one_or_empty_if k ((R' ∩ lv) \ K ∪ Exp.freeVars e \ (R' ∩ lv))).

    assert (rkk := @rkk (R' ∩ lv) (Exp.freeVars e) k x).
    assert (cardinal {x; ((R' ∩ lv) \ K ∪ Exp.freeVars e \ (R' ∩ lv)) \ K_x} <= k). {
      decide (cardinal
                ((R' ∩ lv) \
                           kill_oracle (cardinal (Exp.freeVars e \ (R' ∩ lv))
                                        - (k - cardinal (R' ∩ lv)))
                           ((R' ∩ lv) \ Exp.freeVars e) ∪ Exp.freeVars e \ (R' ∩ lv)) < k).
      - subst K K_x. eauto.
        rewrite one_or_empty_cardinal_lt; try omega.
        rewrite add_cardinal.
        rewrite minus_empty. omega.
      - eapply rkk; eauto.
        apply not_ge in n. omega.
    }

    assert (spill_sound k ZL Λ (R ∩ lv, M) (stmtLet x e s)
    (ann1 (getAnn al ∩ (K ∪ K_x) \ M', Exp.freeVars e \ (R' ∩ lv), nil)
       (splitSpillKO k ZL Λ {x; ((R' ∩ lv) \ K ∪ Exp.freeVars e \ (R' ∩ lv)) \ K_x}
          (getAnn al ∩ (K ∪ K_x) \ M' ∪ M') s al))).
    eapply SpillLet with (K:= K) (Kx := K_x); eauto.
    + subst K K_x; simpl in *.
      rewrite kill_oracle_incl at 1.
      rewrite one_or_empty_of_incl; eauto.
      rewrite Exp.freeVars_live at 4; eauto.
      revert fvRM.
      rewrite ReqR', MeqM'.
      clear; cset_tac.
    + rewrite Exp.freeVars_live at 1; eauto.
      revert fvRM. simpl.
      rewrite ReqR', MeqM'.
      clear; cset_tac.
    + eapply IHlvSound;
        try rewrite ReqR'; try rewrite <- MeqM'; try rewrite ΛeqΛ'; eauto.
      * simpl in *.
        eapply Exp.freeVars_live in H; eauto.
        revert H0 fvRM H.
        rewrite ReqR'.
        clear. clearbody K K_x. cset_tac'.
    + rewrite ReqR'. apply kill_oracle_incl2.
    + rewrite ReqR'. apply rke.

    + rewrite ReqR'; eauto.
    + eapply spill_sound_incl_R; eauto.
      * clear; cset_tac.
      * rewrite ReqR'. eauto.
  }

- rewrite <- ReqR' in RleqK.
  assert (Incl:R' ∩ lv ⊆ R) by (rewrite ReqR'; clear; cset_tac).
  assert (Card:cardinal (R' ∩ lv) <= k) by (rewrite Incl; eauto).
  eapply spill_sound_incl_R with (R:=R' ∩ lv); eauto.
  set (K := kill_oracle (cardinal (Op.freeVars e \ (R' ∩ lv)) - (k - cardinal (R' ∩ lv)))
                       ((R' ∩ lv) \ Op.freeVars e)) in *.
  eapply SpillIf with (K:= K);
  [  |  | apply kill_oracle_incl2
  | apply rke; eauto
  | eapply IHlvSound1
  | eapply IHlvSound2 ]; eauto;
    try rewrite ReqR'; try rewrite MeqM';
      try eapply rke; eauto.
  + subst K. rewrite kill_oracle_incl. clear; cset_tac.
  + rewrite Op.freeVars_live; eauto.
    simpl in *. revert fvRM. rewrite ReqR', MeqM'.
    clear; cset_tac.
  + subst K.
    rewrite (@al_in_rkl (R' ∩ lv) (Op.freeVars e) M' _ k) at 1.
    clear. cset_tac. revert fvRM H0; simpl; rewrite ReqR', MeqM'.
    clear. cset_tac.
  + subst K.
    rewrite (@al_in_rkl (R' ∩ lv) (Op.freeVars e) M' _ k) at 1.
    clear. cset_tac. revert fvRM H1; simpl; rewrite ReqR', MeqM'.
    clear. cset_tac.
- assert (InclR':R' ∩ lv ⊆ R) by (rewrite ReqR'; clear; cset_tac).
  eapply spill_sound_incl_R with (R:=R' ∩ lv); [ | |rewrite ReqR'];eauto.
  eapply PIR2_nth_2 with (l:=counted l) in pir2; eauto using zip_get.
  destruct pir2 as [[R_f M_f] [pir2_get [pir2_R1 pir2_R2]]]. simpl in *.
  repeat erewrite get_nth; eauto; simpl.
  assert (Incl:(R_f ∪ M_f) \ of_list Z [<=] blv \ of_list Z). {
    rewrite <- pir2_R2; eauto.
  }
  set (K := kill_oracle
             (cardinal ((R_f \ (R' ∩ lv)) \ of_list Z) - (k - cardinal (R' ∩ lv)))
             ((R' ∩ lv) \ R_f)) in *.
  eapply SpillApp with (K:= K); try rewrite ReqR'; try rewrite MeqM'; eauto.
  + subst K.
    rewrite Op.freeVars_live_list; eauto.
    rewrite (@kill_oracle_incl _ kos).
    rewrite H1 in Incl.
    revert fvRM Incl.
    rewrite ReqR', MeqM'.
    clear; cset_tac.
  + rewrite H1, fvRM in Incl. revert Incl.
    rewrite ReqR', MeqM'.
    rewrite <- pir2_R2 in H1. revert H1.
    clear; cset_tac'.
  + subst K.
    eapply rke'; eauto. rewrite InclR'; eauto. rewrite ReqR'; eauto.
  + rewrite <- minus_incl with (s:=(R' ∩ lv)\K) (t:=of_list Z).
    rewrite minus_union_minus.
    apply incl_minus_lr with (s:=R_f) (s':=(R' ∩ lv)\K ∪ R_f \ (R' ∩ lv))
                                      (t:=of_list Z) (t':=of_list Z).
    * subst K. eapply kill_oracle_incl2.
    * eauto.
  + clearbody K. clear_all. cset_tac.
  + clearbody K. clear_all. cset_tac.
  + subst K.
    assert (forall (s t : ⦃var⦄), s ⊆ s \ t ∪ t) by (clear; cset_tac).

    intro a. decide (a ∈ (R' \ of_list (take (cardinal ((R_f \ R') \ of_list Z)) (elements (R' \ R_f)))
                             ∪ (R_f \ R') \ of_list Z)).
    * revert i. clear_all. cset_tac.
    * revert n. clear_all. cset_tac.
  + edestruct @list_eq_get; eauto; dcr.
    destruct x as [R_f' M_f']; invc H6.
    rewrite <- pir2_R2 in H1.
    exploit Op.freeVars_live_list; eauto.
    revert H1 H4 fvRM. rewrite ReqR'. rewrite MeqM'.
    clear. clearbody K. cset_tac.
- assert (InclR':R' ∩ lv ⊆ R) by (rewrite ReqR'; clear; cset_tac).
  eapply spill_sound_incl_R with (R:=R' ∩ lv); [ | |rewrite ReqR'];eauto.

  set (K := kill_oracle (cardinal (Op.freeVars e \ (R' ∩ lv)) - (k - cardinal (R' ∩ lv)))
                       ((R' ∩ lv)\ Op.freeVars e)) in *.
  eapply SpillReturn with (K:= K); try rewrite ReqR'; eauto.
  + clear_all. cset_tac.
  + rewrite Op.freeVars_live; eauto.
    rewrite <- ReqR'. revert fvRM. simpl. clear. cset_tac.
  + apply kill_oracle_incl2.
  + apply rke; eauto. rewrite <- RleqK.
    eapply subset_cardinal. cset_tac.
- eapply SpillFun with (K:=∅); eauto.
  + clear. cset_tac.
  + assert (forall s:set var, s \ ∅ ∪ ∅ [=] s) as seteq'. {
      clear_all.
      cset_tac.
    }
    rewrite (seteq' R). rewrite ReqR'. apply RleqK.
  + eauto with len.
  + eauto with len.
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
    * rewrite H3. simpl in fvRM. rewrite fvRM. clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. split.
      -- apply take_of_list_cardinal.
      -- rewrite take_set_incl at 1.
         clear; eauto with cset.
Qed.


Lemma splitSpillKO_spill_live VD k ZL Lv Λ R M s alv
      (LS:live_sound Imperative ZL Lv s alv)
      (lvIncl:ann_P (fun lv => lv ⊆ VD) alv)
  : spill_live VD (splitSpillKO k ZL Λ R M s alv) alv.
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


Instance taken_kos : kill_oracle_spec (@set_take var _).
Proof.
  econstructor; intros;
    eauto using set_take_cardinal_eq, set_take_eq, set_take_incl.
  eapply set_take_eq; eauto. omega.
Qed.

End KO.

Definition splitSpill := @splitSpillKO (@set_take var _).

Definition splitSpill_sat_spillSound := @splitSpillKO_sat_spillSound _ taken_kos.
Definition splitSpill_spill_live := @splitSpillKO_spill_live (@set_take var _).
