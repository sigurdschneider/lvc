Require Import Util IL RenamedApart LabelsDefined OptionR.
Require Import Annotation Exp SetOperations Liveness.Liveness Restrict Coherence.

Set Implicit Arguments.


(** *** In a coherent program, the globals of every function that can eventually be called are live *)

Lemma srd_globals_live_F (isCalled:stmt -> lab -> Prop)  ZL Lv F als f lv' Z' l DL
      (LEN1 : ❬F❭ = ❬als❭) (Len2:❬ZL❭=❬Lv❭) (Len3:❬ZL❭=❬DL❭)
      (IH : forall k Zs, get F k Zs ->
                    forall (ZL : 〔params〕) (Lv : 〔⦃var⦄〕) (DL : 〔؟ ⦃var⦄〕) (alv : ann ⦃var⦄) (f : lab),
                      live_sound Imperative ZL Lv (snd Zs) alv ->
                      srd DL (snd Zs) alv ->
                      PIR2 (ifFstR Equal) DL (Lv \\ ZL) ->
                      isCalled (snd Zs) f ->
                      ❬ZL❭ = ❬Lv❭ ->
                      ❬ZL❭ = ❬DL❭ ->
                      exists (lv : ⦃var⦄) (Z : params), get ZL f Z /\ get DL f ⎣ lv ⎦ /\ lv ⊆ getAnn alv)
      (LS: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (SRD: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          srd (restr (getAnn a \ of_list (fst Zs)) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL))
              (snd Zs) a)
      (PE:PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
               ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)))
      (CC:callChain isCalled F l f)
      (GetZL : get (fst ⊝ F ++ ZL) l Z')
      (GetLv : get (getAnn ⊝ als ++ Lv) l lv')
      dv (GetDL : get (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL) l ⎣ dv ⎦)
      (dvEq:dv [=] lv' \ of_list Z')
  : exists (lv : ⦃var⦄) (Z : params) dv,
    get (fst ⊝ F ++ ZL) (labN f) Z
    /\ get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ get (restr (lv \ of_list Z) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) (labN f) (Some dv)
    /\ dv [=] (lv \ of_list Z) /\ lv \ of_list Z ⊆ lv' \ of_list Z'.
Proof.
  general induction CC.
  - do 2 eexists; eexists (dv); split; [| split; [|split]]; eauto.
    eapply map_get_eq; eauto using zip_get, map_get_1.
    simpl; cases; eauto. eauto. exfalso. apply NOTCOND; rewrite dvEq; eauto.
  - inv_get.
    assert (Incl:(of_list (fst Zs)) ⊆ (list_union ((fun Zs : params * stmt => of_list (fst Zs) ∪ definedVars (snd Zs)) ⊝ F))). {
      eapply incl_list_union; eauto using map_get_1.
    }
    exploit (IH k Zs); eauto using restrict_ifFstR; [ eauto with len | eauto with len |].
    dcr.
    edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
    eauto with len. inv_get.
    PIR2_inv; inv_get.
    exploit IHCC; try eapply H4; eauto.
    eapply get_app_cases in H3. destruct H3; dcr; inv_get.
    + do 3 eexists; split; [| split; [|split] ]; eauto.
      eapply map_get_eq. eauto. simpl. cases; eauto.
      split; eauto.
      rewrite <- H5. rewrite <- H14. eauto.
    + do 2 eexists; eexists x5; split; [| split ]; eauto.
      assert (Len4:❬Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F)❭ = ❬F❭) by eauto with len.
      rewrite get_app_ge in H1; eauto with len.
      rewrite get_app_ge in H4. len_simpl. inv_get.
      split.
      * eapply map_get_eq; eauto. simpl; cases; eauto.
      * split; eauto.
        rewrite <- H5, H9. eauto.
      * len_simpl. omega.
      * len_simpl. omega.
Qed.

Lemma srd_globals_live b s ZL Lv DL alv f
  (LS:live_sound Imperative ZL Lv s alv)
  (SRD:srd DL s alv)
  (PE:PIR2 (ifFstR Equal) DL (Lv \\ ZL))
  (IC:isCalled b s f)
  (Len1:❬ZL❭=❬Lv❭) (Len2:❬ZL❭=❬DL❭)
  : exists lv Z, get ZL (counted f) Z
            /\ get DL (counted f) (Some lv)
            /\ lv ⊆ getAnn alv.
Proof.
  revert_except s.
  sind s.
  intros.
  invt live_sound; invt srd; invt isCalled; simpl in * |- *.
  - edestruct (IH s0) as [lv' [Z' ?]]; eauto using restrict_ifFstR with len; dcr.
    inv_get.
    do 2 eexists; split; [| split]. eauto. eauto.
    idtac "improve". rewrite H3. eauto with cset.
  - edestruct (IH s1); eauto; dcr; inv_get. eauto with cset.
  - edestruct (IH s2); eauto; dcr; inv_get. eauto with cset.
  - PIR2_inv. inv_get.
    do 2 eexists; split; [| split]; eauto with cset.
    idtac "improve"; rewrite H7; eauto.
  - assert (PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                 ((getAnn ⊝ als) \\ (fst ⊝ F) ++ Lv \\ ZL)). {
      eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
    }
    edestruct (IH t); eauto with len. rewrite zip_app; eauto with len.
    destruct l'; simpl in *; dcr; inv_get.
    edestruct PIR2_nth; eauto; dcr. invc H13.
    edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
    eauto with len.
    rewrite <- zip_app in H9; eauto with len. inv_get.
    exploit srd_globals_live_F; eauto using restrict_ifFstR.
    intros; eapply (IH (snd Zs)); eauto.
    rewrite zip_app; eauto with len.
    dcr; destruct f; simpl in *; inv_get.
    do 2 eexists; split; [|split]; eauto.
    rewrite <- H3, <- H14, H15, H18. eauto.
Qed.


Lemma srd_globals_live_From b ZL Lv DL s F als f alv
      (ICF:isCalledFrom (isCalled b) F s f)
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) s alv)
      (SRD:srd ((Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) s alv)
      (Len1 : ❬F❭ = ❬als❭)
      (Len2 : ❬ZL❭ = ❬Lv❭)
      (Len3 : ❬ZL❭ = ❬DL❭)
      (LSF: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (SRDF: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          srd (restr (getAnn a \ of_list (fst Zs)) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL))
              (snd Zs) a)
      (PE:PIR2 (ifFstR Equal) DL (Lv \\ ZL))

  : exists (lv : ⦃var⦄) (Z : params),
    get (fst ⊝ F ++ ZL) (labN f) Z /\
    get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ (lv \ of_list Z) ⊆ getAnn alv.
Proof.
  destruct ICF as [? [IC CC]]; dcr.
  assert (PE':PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))). {
    rewrite zip_app; eauto with len.
    eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
  }
  exploit srd_globals_live; eauto using restrict_ifFstR with len.
  dcr.
  setoid_rewrite <- H3. inv_get.
  simpl in *.
  edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
  eauto with len.
  PIR2_inv; inv_get.
  exploit srd_globals_live_F; eauto using get_app_right, srd_globals_live.
  dcr. do 2 eexists; split; [|split]; eauto.
  rewrite H10, H5; eauto.
Qed.

(** *** On a coherent program a liveness analysis which is sound imperatively is also sound functionally. *)

Local Hint Extern 1 =>
match goal with
| [ |- context [ (?A ++ ?B) \\ (?C ++ ?D) ] ] =>
  rewrite (zip_app _ A C B D);
    [| eauto with len]
| [ |- context [ restr ?G ⊝ (?A ++ ?B) ] ] =>
  rewrite (@List.map_app _ _ (restr G) A B)
end.

Lemma srd_live_functional b s ZL Lv DL alv  (Len2 : ❬ZL❭ = ❬Lv❭) (Len3 : ❬ZL❭ = ❬DL❭)
: live_sound Imperative ZL Lv s alv
  -> srd DL s alv
  -> PIR2 (ifFstR Equal) DL (Lv \\ ZL)
  -> noUnreachableCode (isCalled b) s
  -> live_sound FunctionalAndImperative ZL Lv s alv.
Proof.
  intros LS SRD PE NUC.
  general induction SRD;
    invt live_sound; invt noUnreachableCode; simpl in * |- *;
      only 1-4: eauto using live_sound, restrict_ifFstR with len.
  - assert(PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))). {
      eauto using PIR2_app, PIR2_ifFstR_refl.
    }
    econstructor; eauto.
    + eapply IHSRD; eauto with len.
    + intros.
      eapply H1; eauto 10 using restrict_ifFstR with len.
    + intros. exploit H12; eauto; dcr.
      simpl; split; eauto.
      exploit H6; eauto using get_range.
      len_simpl.
      edestruct srd_globals_live_From as [lv' [Z' ?]]; eauto; dcr.
      inv_get.
      rewrite <- H13, <- H20. eauto.
Qed.
