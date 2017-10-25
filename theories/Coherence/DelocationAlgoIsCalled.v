Require Import Util LengthEq IL RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness.Liveness Coherence Delocation.
Require Import AddParam AddAdd MoreListSet DelocationAlgo.

Set Implicit Arguments.


Lemma computeParameters_isCalled_Some_F' b Lv ZL AP als D Z F s alb l
      k k' x0 x1 Zs
      (IH : forall k Zs,
          get F k Zs ->
          forall (ZL : 〔params〕) (Lv AP : 〔⦃var⦄〕) (lv : ann ⦃var⦄)
            (n : nat) (D : ⦃var⦄) (Z : params) (p : ؟ ⦃var⦄),
            live_sound Imperative ZL Lv (snd Zs) lv ->
            ❬AP❭ = ❬Lv❭ ->
            ❬Lv❭ = ❬ZL❭ ->
            isCalled b (snd Zs) (LabI n) ->
            get Lv n D ->
            get ZL n Z ->
            get (snd (computeParameters (Lv \\ ZL) AP (snd Zs) lv)) n p ->
            exists Za : ⦃var⦄, p = ⎣ Za ⎦ /\ D \ of_list Z \ Za ⊆ getAnn lv)
      (LEN1 : ❬AP❭ = ❬Lv❭) (LEN2 : ❬Lv❭ = ❬ZL❭) (LEN3 : ❬F❭ = ❬als❭)
      (GetDL : get (getAnn ⊝ als ++ Lv) l D) (GetZL : get (fst ⊝ F ++ ZL) l Z)
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) s alb)
      (LSF : forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (INCL: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get als n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
      (GetLV : get (olu F als Lv ZL AP s alb) l x0)
      (GetF : get F k Zs) (GetAls : get als k x1)
      (IC : isCalled b (snd Zs) (LabI k'))
      (CC: callChain (isCalled b) F (LabI k') (LabI l))
  :  exists Za : ⦃var⦄,
     addAdd
       (list_union (oget ⊝ take ❬F❭ (olu F als Lv ZL AP s alb))
        ∪ list_union (fst ∘ of_list ⊝ F)) (D \ of_list Z) x0 =
     ⎣ Za ⎦ /\
     D \ of_list Z \ Za
     ⊆ getAnn x1 \ of_list (fst Zs) \
       (list_union (oget ⊝ take ❬F❭ (olu F als Lv ZL AP s alb))
                   ∪ list_union (fst ∘ of_list ⊝ F)).
Proof.
  general induction CC.
  - destruct (@get_in_range _ (snd
                                 (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                    (tab {} ‖F‖ ++ AP) (snd Zs) x1)) l0)
      as [pF GETpF].
    rewrite computeParameters_length; [ |eauto | eauto with len | eauto with len].
    eapply get_range in GetDL. eauto.
    edestruct (IH k Zs); try eapply GETpF;
      eauto using get_app_right, map_get_1 with len;
      dcr; subst.
    edestruct get_olist_union_A' as [? [? ?]]; try eapply GetLV;
      eauto using map_get_1, zip_get.
    eapply computeParametersF_length; eauto with len.
    rewrite computeParameters_length; eauto with len.
    subst; simpl. eexists; split; eauto.
    rewrite <- H0, <- H1.
    repeat rewrite minus_union.
    assert (of_list (fst Zs) ⊆ list_union (fst ∘ of_list ⊝ F)). {
      eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    }
    revert H; clear_all; cset_tac.
  - inv_get.
    exploit IHCC; try eapply H0; eauto.
    dcr. eexists; split; eauto.
    rewrite H5.
    destruct (@get_in_range _ (snd
                                 (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                    (tab {} ‖F‖ ++ AP) (snd Zs0) x1)) k'0)
      as [pF' GETpF'].
    rewrite computeParameters_length; [ |eauto | eauto with len | eauto with len].
    rewrite app_length, map_length. eapply get_range in H1. omega.
    exploit (IH k0 Zs0); try eapply GETpF'; eauto using get_app, map_get_1 with len.
    dcr; subst. rewrite <- H7.
    assert (x3 ⊆ list_union (oget ⊝ take ❬F❭
                                  (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                               (snd
                                                  (computeParameters
                                                     ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                     (tab {} ‖F‖ ++ AP) s alb))))).
    {
      exploit (@get_olist_union_A _ _ (snd ⊝ computeParametersF F als Lv ZL AP));
        [| eapply GETpF' | | ]. instantiate (1:=k0).
      eapply map_get_1. eapply zip_get_eq; [| | reflexivity]. eauto. eauto.
      instantiate (1:=(snd
                         (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                            (tab {} ‖F‖ ++ AP) s alb))).
      rewrite computeParameters_length; eauto.
      eapply computeParametersF_length; eauto with len.
      eauto with len. eauto with len.
      dcr.
      eapply incl_list_union. eapply map_get_1.
      eapply get_take; try eapply H6; eauto using get_range. eauto.
    }
    rewrite H2.
    assert (of_list (fst Zs0) ⊆ list_union (fst ∘ of_list ⊝ F)). {
      eapply incl_list_union. eapply map_get_1.
      instantiate (1:=Zs0). eauto. eauto.
    }
    revert H3; clear_all; cset_tac.
Qed.

Lemma computeParameters_isCalled_Some b ZL Lv AP s lv n D Z p
  : live_sound Imperative ZL Lv s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> isCalled b s (LabI n)
    -> get Lv n D
    -> get ZL n Z
    -> get (snd (computeParameters (Lv \\ ZL) AP s lv)) n p
    -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  revert ZL Lv AP lv n D Z p.
  sind s; destruct s;
    intros ZL Lv AP lv n D Z p LS LEN1 LEN2 IC GetDL GetZL GetLV;
    simpl in * |- *; inv LS; invt isCalled;
      repeat let_case_eq; repeat let_pair_case_eq; subst; simpl in *.
  - edestruct (IH s) as [Za [A B]]; try eapply GetLV; eauto with len;
      subst; simpl.
    eexists; split; eauto.
    inv_get.
    exploit (@computeParameters_AP_LV Lv ZL (addParam x (Lv \\ ZL) AP));
      try eapply H2; eauto with len.
    PIR2_inv. unfold addParam in H3. inv_get.
    rewrite <- H7.
    revert H10 B. clear_all; cases; intros; cset_tac.
  - inv_get.
    edestruct (IH s1) as [? [? SUB]]; eauto; subst.
    setoid_rewrite <- H8. setoid_rewrite <- SUB.
    destruct x0;
      eexists; simpl; split; eauto; clear_all; cset_tac.
  - inv_get.
    edestruct (IH s2) as [? [? SUB]]; eauto; subst.
    setoid_rewrite <- H9. setoid_rewrite <- SUB.
    destruct x;
      eexists; simpl; split; eauto; clear_all; cset_tac.
  - simpl in *. unfold keep in GetLV.
    inv_get.
    cases; eauto.
    eexists; split; eauto.
    rewrite <- H3. eauto with cset.
  - lnorm. inv_get.
    invc H4.
    + exploit (computeParameters_length (tab {} ‖F‖ ++ AP) H1) as Len;
        [ eauto with len | eauto with len | ].
      assert (LE:❬F❭ + n < ❬snd
                           (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                              (tab {} ‖F‖ ++ AP) s alb)❭).
      rewrite Len, app_length, map_length. exploit (get_range GetDL). omega.
      destruct (get_in_range _ LE) as [pF GETpF].
      edestruct (IH s) with (AP:=tab {} ‖F‖ ++ AP); eauto.
      eauto with len. eauto with len.
      eapply get_app_right; eauto using map_get_1.
      eauto with len.
      eapply get_app_right; eauto using map_get_1.
      eauto with len.
      dcr; subst.
      edestruct (@get_olist_union_b _ _ (snd ⊝ computeParametersF F als Lv ZL AP))
        as [? [? ?]]; try eapply GETpF.
      eapply computeParametersF_length; eauto.
      get_functional.
      eexists; split; try reflexivity.
      rewrite <- H0, <- H8, <- H4.
      clear_all; cset_tac.
    + inv_get.
      destruct (@get_in_range _ (snd
                                   (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                      (tab {} ‖F‖ ++ AP) s alb)) k)
        as [ps GETps]; eauto.
      rewrite computeParameters_length; eauto with len.
      exploit (IH s); try eapply GETps; eauto using get_app, map_get_1 with len.
      dcr; subst.
      setoid_rewrite <- H8. setoid_rewrite <- H13.
      assert (x2 ⊆ list_union (oget ⊝ take ❬F❭
                                    (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                                 (snd
                                                    (computeParameters
                                                       ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                       (tab {} ‖F‖ ++ AP) s alb))))
                 ∪ list_union (fst ∘ of_list ⊝ F)). {
        exploit (@get_olist_union_b _ _ (snd ⊝ computeParametersF F als Lv ZL AP));
          try eapply GETps.
        eapply computeParametersF_length; eauto with len.
        rewrite computeParameters_length; eauto with len.
        dcr. eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1.
        eapply get_take; eauto using get_range.
        eauto.
      }
      clear H8 H13 LS GETps. setoid_rewrite H10. clear H7 H10.
      eapply computeParameters_isCalled_Some_F'; eauto.
      intros. eapply (IH (snd Zs0)); eauto.
      eapply get_app_right; eauto. eauto with len.
      eapply get_app_right; eauto. eauto with len.
      intros; edestruct H6; eauto.
Qed.

Lemma computeParameters_isCalled_get_Some b Lv ZL AP s lv n p A D Z
  : live_sound Imperative ZL Lv s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> isCalled b s (LabI n)
    -> n < ❬snd (computeParameters (Lv \\ ZL) AP s lv)❭
    -> get Lv n D
    -> get ZL n Z
    -> get (olist_union A (snd (computeParameters (Lv \\ ZL) AP s lv))) n p
    -> (forall (n0 : nat) (a : 〔؟⦃var⦄〕),
          get A n0 a -> ❬a❭ = ❬snd (computeParameters (Lv \\ ZL) AP s lv)❭)
    -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  intros LS LEN1 LEN2 IC LE GETDL GETZL GET LEN3.
  destruct (get_in_range _ LE); eauto.
  edestruct computeParameters_isCalled_Some; eauto; dcr; subst.
  edestruct get_olist_union_b; eauto; dcr.
  get_functional.
  eexists; split; try reflexivity. rewrite <- H1, <- H2; eauto.
Qed.

Lemma computeParameters_isCalledFrom_get_Some b Lv ZL AP F alv s lv p Da Zs l
      (LSF : forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get alv n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ alv ++ Lv) (snd Zs) a)
       (INCL: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get alv n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
  : live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ alv ++ Lv) s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> length F = length alv
    -> isCalledFrom (isCalled b) F s (LabI l)
    -> get alv l Da
    -> get F l Zs
    -> get (olist_union (snd ⊝ computeParametersF F alv Lv ZL AP)
                       (snd (computeParameters ((getAnn ⊝ alv ++ Lv) \\ (fst ⊝ F ++ ZL))
                                               (tab {} ‖F‖ ++ AP)
                                               s lv))) l p
    -> exists Za, p = Some Za /\ getAnn Da \ of_list (fst Zs) \ Za \
                                 list_union (oget ⊝ take ❬F❭ (olu F alv Lv ZL AP s lv))
                                 \ list_union (fst ∘ of_list ⊝ F) ⊆ (getAnn lv).
Proof.
  intros LS LEN1 LEN2 LEN3 [[n] [IC CC]] GETDL GETZL GET.
  exploit callChain_range' as LE; eauto using get_range. simpl in *.
  assert (NLE:n < ❬snd (computeParameters ((getAnn ⊝ alv ++ Lv)
                                     \\ (fst ⊝ F ++ ZL))
                                  (tab {} ‖F‖ ++ AP) s lv)❭).
  rewrite computeParameters_length; eauto with len.
  destruct (get_in_range _ NLE); eauto.
  assert (LE':n < ❬getAnn ⊝ alv ++ Lv❭).
  rewrite app_length, map_length. omega.
  destruct (get_in_range _ LE'); eauto.
  assert (LE'':n < ❬fst ⊝ F ++ ZL❭).
  rewrite app_length, map_length. omega.
  destruct (get_in_range _ LE''); eauto.
  edestruct computeParameters_isCalled_Some; try eapply g; eauto; dcr; subst.
  eauto with len. eauto with len.
  edestruct get_olist_union_b; eauto; dcr.
  intros.
  eapply computeParametersF_length; eauto.
  eapply computeParameters_length; eauto with len.
  setoid_rewrite <- H1.
  inv CC.
  - inv_get. eexists; split; eauto.
    rewrite H2. clear_all; cset_tac.
  - inv_get.
    exploit computeParameters_isCalled_Some_F'; try eapply H4; try eapply H5;
      eauto using get_app, map_get_1.
    intros. eapply computeParameters_isCalled_Some; eauto.
    dcr. destruct p; simpl in *; invc H8.
    eexists; split; [ reflexivity | ].
    rewrite H2.
    assert (Incl:x ⊆  (list_union (oget ⊝ take ❬F❭ (olu F alv Lv ZL AP s lv))
                             ∪ list_union (fst ∘ of_list ⊝ F))). {
      eapply incl_union_left.
      eapply incl_list_union.
      eapply map_get_1. eapply get_take; eauto using get_range. reflexivity.
    }
    rewrite Incl. rewrite <- H9.
    rewrite union_comm.
    rewrite <- minus_union.
    clear_all; cset_tac.
Qed.
