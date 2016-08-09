Require Import List Map Env AllInRel Exp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined AppExpFree.
Require Import SimI.
Require Import Spilling.
Require Import Take TakeSet.

Set Implicit Arguments.

Fixpoint simplSpill
(k : nat)
(ZL: list params)
(Λ : list (set var * set var))
(R : set var)
(M : set var)
(s : stmt)
(Lv : ann (set var))
{struct s}
: ann (set var * set var * option (list (set var * set var))) :=
match s,Lv with

| stmtLet x e s, ann1 LV lv
  => let Fv_e := Exp.freeVars e in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e : set var  := R \ K ∪ L in

     let K_x  := if [(cardinal R_e) >= k]
                      then singleton (hd 0 (elements R_e))
                      else ∅ in
     let Sp   := getAnn lv ∩ (K ∪ K_x) in
     let R_s  := {x; R_e \ K_x} in

     ann1 (Sp,L,None) (simplSpill k ZL Λ R_s (Sp ∪ M) s lv)

| stmtReturn e, _
  => let Fv_e := Op.freeVars e in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e  := R \ K ∪ L in
     let Sp   := ∅ in

     ann0 (Sp,L,None)

| stmtIf e s1 s2, ann2 LV lv1 lv2
  => let Fv_e := Op.freeVars e in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e  := R \ K ∪ L in
     let Sp   := (getAnn lv1 ∪ getAnn lv2) ∩ K in

     ann2 (Sp,L,None) (simplSpill k ZL Λ R_e (Sp ∪ M) s1 lv1)
                      (simplSpill k ZL Λ R_e (Sp ∪ M) s2 lv2)

| stmtApp f Y, _
  => let R_f := fst (nth (counted f) Λ (∅,∅)) in
     let M_f := snd (nth (counted f) Λ (∅,∅)) in
     let Z   := nth (counted f) ZL nil in
     let L   := R_f \ R \ of_list Z in
     (*let K    := of_list (take (cardinal L) (elements (R \ R_f)) in*)
     let Sp   := M_f \ M \ of_list Z in

     ann0 (Sp,L,None)

| stmtFun F t, annF LV als lv_t
  => let rms:= (fun f al =>
                  let Lv  := getAnn al in (* liveness in fn body *)
                  let ZL  := fst f in    (* params of fn *)
                  let R_f := of_list (take k (elements Lv)) in
                  let M_f := Lv \ R_f in
                     (R_f, M_f)
               ) ⊜ F als in
     let ZL':= (fun f => fst f) ⊝ F ++ ZL in
     let Λ' := rms ++ Λ in


     annF (∅, ∅, Some rms)
          ((fun f rmlv => match rmlv with (rm, Lv)
                       => simplSpill k ZL' Λ' (fst rm) (snd rm) (snd f) Lv end)
           ⊜ F ((fun rm al => (rm,al)) ⊜ rms als))
                        (simplSpill k ZL' Λ' R M t lv_t)

| _,_ => ann0 (∅, ∅, None)
end.


(**********************************************************************)

Lemma seteq X `{OrderedType X} (s t : set X)
:  s \ (s \ t) ∪ t \ s [=] t.
Proof.
rewrite minus_minus. clear. cset_tac.
decide (a ∈ s).
* left. split; eauto with cset.
* right. split; eauto with cset.
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

Lemma fTake X `{OrderedType X} (s t : set X)
 : (t)
            ⊆
            (s \
              of_list (
                take
                  (cardinal (t \ s))
                  (elements (s \ t))
              ) ∪ t \ s).
Proof.
    assert (
           of_list (
             take
               (cardinal ( t \ s))
               (elements ( s \ t))
           )
           ⊆ s \ t
         ) as takeIncl. { rewrite take_set_incl. eauto with cset. }
         apply incl_minus_incl with (u:=s) in takeIncl.
         rewrite <- takeIncl.
         rewrite seteq at 1.
         reflexivity.
Qed.

Lemma rke X `{OrderedType X} (s t: set X) (k : nat)
: cardinal s <= k ->
cardinal (t) <= k ->  cardinal (s \
of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  )
 ∪ t \ s) <= k.
Proof.
set (K := of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  )) in *.

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
    clear. cset_tac. decide (a ∈ s); cset_tac.
  + clear - n. rewrite elements_length. omega.
Qed.


Lemma rkk X `{OrderedType X} (s t  : set X) (k : nat) (x y : X)
: let K :=  of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  ) in
  let  K_x := singleton (hd y (elements (
                        s \ K ∪ t \ s ))) in
   cardinal s <= k
-> cardinal (t) <= k
-> k > 0
-> cardinal (s \ K ∪ t \ s) >= k

-> cardinal {x; (s \ K ∪ t \ s) \ K_x} <= k.
Proof.
intros K K_x RleqK fvBcard kgeq1 sizeRL.
rewrite add_cardinal. rewrite cardinal_difference'.
- subst K_x. rewrite singleton_cardinal.
  assert (rke := @rke X _ s t k RleqK fvBcard).
  remember (cardinal (s \ K ∪ t \ s)).
  destruct n.
  + omega. (*uses kgt0*)
  + simpl.
    enough (S n <= k). { omega. } rewrite Heqn. subst. exact rke.
- subst K_x. apply incl_singleton.
  apply hd_in_elements. intro no.
  assert (k >= 1) as geq. { omega. }
  assert (cardinal (s \ K ∪ t \ s) = 0) as emptRE.
  { rewrite no. apply empty_cardinal. }
  rewrite emptRE in sizeRL. omega.
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

Lemma nth_listeq X (R : relation X) `{Reflexive _ R} (L L' : list X) (x : X) n
 : list_eq R L L' -> R (nth n L x) (nth n L' x).
Proof.
intro H0. revert n.
induction H0; intros.
- apply H.
- destruct n; simpl.
  + eauto.
  + apply IHlist_eq.
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
-> app_expfree s
-> PIR2 (fun RMf G => match RMf with (R_f,M_f)
                   => cardinal R_f <= k end) Λ Lv
(*-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv*)
-> spill_sound k ZL Λ (R,M) s (simplSpill k ZL Λ' R' M' s alv).

Proof.
intros kgeq1 ReqR' MeqM' ΛeqΛ' RleqK fvRM fvBound lvSound aeFree pir2.

general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt
       |k0 f0 Y0
       |k0 Z0 s0 t0 fvBs fvBt];
  inversion_clear aeFree;
   simpl.



- assert (rke := @rke var _ R' (Exp.freeVars e) k RleqK fvBcard).
  assert (fTake := @fTake var _ R' (Exp.freeVars e)).
  set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  decide (cardinal (R' \ K ∪ Exp.freeVars e \ R') >= k).
  { rename g into sizeRL.
    set (K_x:=singleton (hd 0 (elements (
                        R' \ K ∪ Exp.freeVars e \ R' )))).

    assert (rkk := @rkk var _ R' (Exp.freeVars e) k x).

    eapply SpillLet with (K:= K) (Kx := K_x); eauto.

    + eapply IHlvSound;
      try rewrite ReqR'; try rewrite <- MeqM'; try rewrite ΛeqΛ'; eauto.
      * unfold Subset; intro a. decide (a = x); [cset_tac|].
        intro aInAnn. rewrite union_iff.
        (** this can be simplified using al_in_rkl **)
        decide (   a ∈ K
              \/ a ∈ K_x
              \/ a ∈ M
             ).
        -- right. cset_tac.
        -- left. apply not_or_dist in n0. destruct n0 as [nK nM].
           decide (a = x).
           ++ cset_tac.
           ++ apply add_iff. right.
              unfold Subset in H0. specialize (H0 a).
              unfold Subset in fvRM. specialize (fvRM a).
              assert (a ∈ (getAnn al \ (singleton x))). { cset_tac. }
              assert (a ∈ R'). { cset_tac. rewrite <- ReqR'. eauto. }
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
    apply subset_cardinal in fTake.
    rewrite <- fTake in sizeRL. exact sizeRL. }

  eapply SpillLet with
            (K:= of_list (take
                            (cardinal (Exp.freeVars e \ R'))
                            (elements (R' \ Exp.freeVars e))
                          )
            )
            (Kx := ∅).
  + eapply IHlvSound; eauto.
    * rewrite ReqR'. cset_tac.
    * rewrite MeqM'. cset_tac.
    * clear - sizeRL. rewrite add_cardinal. apply not_ge in sizeRL.
      rewrite minus_empty. omega.
    * rewrite ReqR'. clear - H0 fvRM ReqR'.

      (** This can be simplified using al_in_rkl **)
      unfold Subset. intros a aIn.
      apply union_iff.
      decide (a ∈ of_list (take
                            (cardinal (Exp.freeVars e \ R'))
                            (elements (R' \ Exp.freeVars e))
                          )
              \/ a ∈ M
             ).
      -- right. cset_tac.
      -- left. apply not_or_dist in n. destruct n as [nK nM].
         decide (a = x).
         ++ cset_tac.
         ++ apply add_iff. right.
            unfold Subset in H0. specialize (H0 a).
            unfold Subset in fvRM. specialize (fvRM a).
            assert (a ∈ (getAnn al \ (singleton x))). { cset_tac. }
            rewrite minus_empty.
            assert (a ∈ R). { cset_tac. } rewrite ReqR' in H1. cset_tac.
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
  [rewrite ReqR'; apply fTake
  | rewrite ReqR'; apply rke; eauto
  | eapply IHlvSound1
  | eapply IHlvSound2 ];
  try rewrite ReqR'; try rewrite <- MeqM'; eauto;
  [ apply rke ; eauto  | | apply rke; eauto | ];
  [ rewrite <- seteq_1 | rewrite <- seteq_2 ];
  subst K; apply al_in_rkl; eauto;
  rewrite <- ReqR'; eauto with cset.
- eapply PIR2_nth_2 with (l:=counted l) in pir2; eauto using zip_get.
  destruct pir2 as [[R_f M_f] [pir2_get pir2_R ]]. simpl in *.
  set (K := of_list (take
                      (cardinal (R_f \ R))
                      (elements (R \ R_f))
                     )) in *.

  eapply SpillApp with (K:= K); try rewrite ReqR'; try rewrite MeqM'; eauto.
  + subst K. assert (forall s t, nth l Λ (s,t) === nth l Λ' (s,t)).
    { intros s t. clear - pir2_get ΛeqΛ'. apply nth_listeq.
      apply equiv_reflexive. apply ΛeqΛ'. }
    enough (fst (nth l Λ (∅,∅)) [=] R_f) as Rf_nth.
    { rewrite <- Rf_nth in pir2_R. rewrite <- H6.
      rewrite cardinal_union_difference. rewrite <- ReqR'. rewrite Rf_nth.
      apply rke; [rewrite ReqR' | rewrite Rf_nth in pir2_R]; eauto.
    }
    clear - pir2_get. apply get_nth with (d:=(∅,∅)) in pir2_get.
    rewrite pir2_get. eauto.
  + erewrite <- (nth_listeq _ _ ΛeqΛ'). rewrite (get_nth _ pir2_get). simpl.
    erewrite get_nth; eauto.
    rewrite <- minus_incl with (s:=R'\K) (t:=of_list Z).
    rewrite minus_union_minus.
    apply incl_minus_lr with (s:=R_f) (s':=R'\K ∪ R_f \ R') (t:=of_list Z) (t':=of_list Z).
    * subst K. rewrite <- ReqR'. apply fTake.
    * eauto.
  + erewrite <- (nth_listeq _ _ ΛeqΛ'). rewrite (get_nth _ pir2_get). simpl.
    erewrite get_nth; eauto.
    erewrite <- minus_incl with (s:=M') (t:=of_list Z) at 2.
    rewrite minus_union_minus.
    apply incl_minus_lr with (s:=M_f) (s':=M_f \M' ∪ M') (t:=of_list Z) (t':=of_list Z).
    * clear. cset_tac.
    * eauto.
- set (K := of_list (take
                       (cardinal (Op.freeVars e \ R'))
                       (elements (R' \ Op.freeVars e))
                  )) in *.
  eapply SpillReturn with (K:= K); try rewrite ReqR'; eauto.
  + apply fTake.
  + apply rke; eauto.
- eapply SpillFun with (K:=∅); eauto.
  + assert (forall s:set var, s \ ∅ ∪ ∅ [=] s) as seteq'. { cset_tac. }
    rewrite (seteq' R). rewrite ReqR'. apply RleqK.
  + intros ; inv_get. simpl. apply take_of_list_cardinal.
  + intros ; inv_get. eapply H1; eauto with cset.
    * apply list_eq_app; eauto. reflexivity.
    * simpl. apply take_of_list_cardinal.
    * clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. apply take_of_list_cardinal.
  + eapply IHlvSound; eauto.
    * rewrite ReqR'. clear. cset_tac.
    * apply list_eq_app.
      -- reflexivity.
      -- apply ΛeqΛ'.
    * rewrite H3. simpl in fvRM. rewrite fvRM. clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. apply take_of_list_cardinal.
Qed.