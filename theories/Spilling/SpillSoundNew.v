Require Import List Map Env AllInRel Exp.
Require Import IL Annotation AnnP InRel.
Require Import LabelsDefined SpillSound SpillUtil.


Inductive spill_sound2 (k:nat) :
  (list params)
  -> (list (⦃var⦄ * ⦃var⦄))
  -> (⦃var⦄ * ⦃var⦄)
  -> stmt
  -> spilling
  -> Prop
  :=
  | Spill2Let
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Kx : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
    : spill_sound2 k ZL Λ ({x;R\Kx},M) s sl
      -> k > 0
      -> cardinal {x; R \ Kx } <= k
      -> Exp.freeVars e ⊆ R
      -> spill_sound2 k ZL Λ (R,M) (stmtLet x e s) (ann1 (∅,∅,nil) sl)

  | Spill2Return
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M: ⦃var⦄)
      (e : op)
    : Op.freeVars e ⊆ R
      -> spill_sound2 k ZL Λ (R,M) (stmtReturn e) (ann0 (∅,∅,nil))

  | Spill2If
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)

    : Op.freeVars e ⊆ R
      -> spill_sound2 k ZL Λ (R,M) s sl_s
      -> spill_sound2 k ZL Λ (R,M) t sl_t
      -> spill_sound2 k ZL Λ (R,M) (stmtIf e s t) (ann2 (∅,∅,nil) sl_s sl_t)

  | Spill2App
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K R_f M_f R' M' : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
    : get ZL (counted f) Z
      -> get Λ (counted f) (R_f,M_f)
      -> R_f \ of_list Z ⊆ R
      -> M_f \ of_list Z ⊆ M
      -> list_union (Op.freeVars ⊝ Y) ⊆ R' ∪ M'
      -> R' [=] R
      -> M' ⊆ M
      -> spill_sound2 k ZL Λ (R,M) (stmtApp f Y)
                     (ann0 (∅,∅, (R', M')::nil))

  | Spill2Fun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
    : length F = length sl_F
      -> length F = length rms
      -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
      -> (forall n Zs rm sl_s, get rms n rm
                         -> get F n Zs
                         -> get sl_F n sl_s
                         -> spill_sound2 k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) rm (snd Zs) sl_s
        )
      -> spill_sound2 k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R,M) t sl_t
      -> spill_sound2 k ZL Λ (R,M) (stmtFun F t)
                    (annF (∅,∅,rms) sl_F sl_t)

  | Spill2Load
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
    : Sp [=] getSp sl
      -> L [=] getL sl
      -> Empty Sp
      -> L ⊆ M
      -> cardinal (R\K ∪ L) <= k
      -> spill_sound2 k ZL Λ (R\K ∪ L, M) s (clear_L sl)
      -> spill_sound2 k ZL Λ (R,M) s sl

  | Spill2Spill
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp: ⦃var⦄)
      (s : stmt)
      (sl : spilling)
    : getSp sl [=] Sp
      -> Sp ⊆ R
      -> spill_sound2 k ZL Λ (R, Sp ∪ M) s (clear_Sp sl)
      -> spill_sound2 k ZL Λ (R,M) s sl
.

Lemma clear_clear (sl : spilling) :
  clear_L (clear_Sp sl)
  = match sl with
    | ann0 (Sp,L,rm) => ann0 (∅,∅,rm)
    | ann1 (Sp,L,rm) sl' => ann1 (∅,∅,rm) sl'
    | ann2 (Sp,L,rm) sl1 sl2 => ann2 (∅,∅,rm) sl1 sl2
    | annF (Sp,L,rm) slF slt => annF (∅,∅,rm) slF slt
    end
.
Proof.
  induction sl, a, p, l; simpl; eauto.
Qed.

Lemma spill_sound_card
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl: spilling)
  : spill_sound k ZL Λ (R,M) s sl
    -> exists K, cardinal (R \ K ∪ getL sl) <= k.
Proof.
  intros H. general induction H; simpl; eauto.
Qed.

(*
Lemma spill_sound2_card
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl: spilling)
  : spill_sound2 k ZL Λ (R,M) s sl -> cardinal R <= k.
Proof.
  intros H. general induction H; eauto.
  - eapply IHspill_sound2.
*)




Lemma spill_sound_ext
      (k : nat)
      (ZL ZL2 : list params)
      (Λ Λ2 : list (⦃var⦄ * ⦃var⦄))
      (R R2 M M2 : ⦃var⦄)
      (s s2 : stmt)
      (sl sl2 : spilling)
  :
      ZL === ZL2
    -> Λ === Λ2
    -> R [=] R2
    -> M [=] M2
    -> s === s2
    -> sl === sl2
    -> spill_sound k ZL Λ (R,M) s sl -> spill_sound k ZL2 Λ2 (R2,M2) s sl2
.
Proof.
  intros ZLeq Λeq Req Meq seq sleq H.
  general induction H; simpl; eauto;
    destruct sl2; isabsurd;
      destruct a as [[Sp' L'] rm'].
  - destruct rm'; [|clear - sleq; invc sleq; invc H2; isabsurd].
    eapply SpillLet with (K:=K) (Kx:=Kx); simpl; eauto; invc sleq; invc H9; invc H10.
    + rewrite <-Req, <-H9. assumption.
    + rewrite <-Meq, <-H14, <-H9. assumption.
    + eapply IHspill_sound; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite H9, Meq; clear; cset_tac.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
  - destruct rm'; [|clear - sleq; invc sleq; invc H1; isabsurd].
    eapply SpillReturn with (K:=K); invc sleq; invc H5; invc H7.
    + rewrite <-Req, <-H6. assumption.
    + rewrite <-Meq, <-H10, <-H6. assumption.
    + rewrite <-Req, <-H10. assumption.
    + rewrite <-Req, <-H10. assumption.
  - destruct rm'; [|clear - sleq; invc sleq; invc H3; isabsurd].
    eapply SpillIf with (K:=K); invc sleq; invc H9; invc H8.
    + rewrite <-H9, <-Req. assumption.
    + rewrite <-Meq, <-H9, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + eapply IHspill_sound1; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite Meq, H9; clear; cset_tac.
    + eapply IHspill_sound2; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite Meq, H9; clear; cset_tac.
Admitted.


Lemma PIR2_eq
      (X : Type) `{OrderedType X} (L L' : list X)
  : PIR2 _eq L L' <-> L === L'.
Proof.
  split; intros H1; induction H1; econstructor; eauto.
Qed.



Lemma spill_sound2_ext
      (k : nat)
      (ZL ZL2 : list params)
      (Λ Λ2 : list (⦃var⦄ * ⦃var⦄))
      (R R2 M M2 : ⦃var⦄)
      (s s2 : stmt)
      (sl sl2 : spilling)
  :
    ZL === ZL2
    -> Λ === Λ2
    -> R [=] R2
    -> M [=] M2
    -> s === s2
    -> sl === sl2
    -> spill_sound2 k ZL Λ (R,M) s sl -> spill_sound2 k ZL2 Λ2 (R2,M2) s sl2
.
Proof.
  intros .
  invc H. admit.

Admitted.



Lemma spill_sound_spill_sound2
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  : spill_sound k ZL Λ (R,M) s sl -> spill_sound2 k ZL Λ (R,M) s sl
.
Proof.
  intros H.
  general induction H;
    eapply Spill2Spill with (Sp:=Sp); simpl; eauto;
      eapply Spill2Load with (Sp:=∅) (L:=L); simpl; eauto; try apply empty_1.
  + econstructor; eauto.
  + econstructor; eauto.
  + econstructor; eauto.
  + econstructor; eauto. rewrite H6, <-H7. reflexivity.
  + econstructor; eauto.
    intros. inv_get. eapply H6 with (R:=fst rm) (M:=snd rm); eauto.
    apply injective_projections; simpl; eauto.
Qed.


Lemma spill_sound2_spill_sound
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    cardinal R <= k
    -> spill_sound2 k ZL Λ (R,M) s sl -> spill_sound k ZL Λ (R,M) s sl
.
Proof.
  intros card H.
  assert (forall s : ⦃var⦄, s \ ∅ ∪ ∅ [=] s) as seteq by (clear; cset_tac).
  general induction H.
  - eapply SpillLet with (K:=∅) (Kx:=Kx); eauto with cset;
      [|rewrite seteq|rewrite seteq]; eauto.
    eapply spill_sound_ext with (R:={x; R0 \ Kx}) (M:=M0); eauto;
      [clear; cset_tac|clear;cset_tac].
  - eapply SpillReturn; eauto with cset.
    rewrite seteq; eauto.
  - econstructor; eauto with cset.
    + rewrite seteq; eauto.
    + eapply spill_sound_ext with (R:=R0) (M:=M0); eauto with cset.
      clear;cset_tac.
    + eapply spill_sound_ext with (R:=R0) (M:=M0); eauto with cset.
      clear;cset_tac.
  - econstructor; eauto with cset; rewrite seteq; eauto. rewrite <-H4; eauto.
  - econstructor; eauto with cset; try instantiate (1 := ∅); eauto.
    + rewrite seteq. eauto.
    + intros. inv_get. eapply H3 with (R:=fst rm); eauto. instantiate (1:=snd rm).
      apply injective_projections; simpl; eauto.
    + eapply spill_sound_ext with (R:=R0) (M:=M0); eauto; clear; cset_tac.
  - induction H4; simpl in *.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + apply empty_is_empty_1 in H3. clear - H3 n. contradiction.


    Lemma spill_sound2_match
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
    : spill_sound2 k ZL Λ (R,M) s (clear_L sl)
      -> match s with
        | stmtLet x e s
          => exists sl', sl = ann1 (getSp sl,getL sl,nil) sl'
        | stmtReturn e
          => exists Sp L,
            spill_sound2 k ZL Λ (R,M) (stmtReturn e) (ann0 (Sp,L,nil))
        | stmtIf e s t
          => exists Sp L sl1 sl2,
            spill_sound2 k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,nil) sl1 sl2)
        | stmtApp f Y
          => exists Sp L R' M',
            spill_sound2 k ZL Λ (R,M) (stmtApp f Y) (ann0 (Sp,L,(R',M')::nil))
        | stmtFun F t
          => exists Sp L rmF slF slt,
            spill_sound2 k ZL Λ (R,M) (stmtFun F t) (annF (Sp,L,rmF) slF slt)
        end
    .
    Proof.
    Admitted.


    specialize (IHspill_sound2 (R0 \ K ∪ L)).
    exploit IHspill_sound2; eauto.
    general induction H5.
    +

      Definition setL :=
        fun (sl : spilling) (L : ⦃nat⦄) => setTopAnn sl (getSp sl,L, snd (getAnn sl)).
      Lemma setL_clearL (L : ⦃var⦄) (sl : spilling)
        : setL (clear_L sl) (getL sl) = sl.
      Proof.
        induction sl; simpl; destruct a; simpl; eauto; destruct p; simpl; eauto.
      Qed.
      apply f_equal with (f:= fun x => setL x (getL sl0)) in Heqa.
      rewrite setL_clearL in Heqa.
      simpl in Heqa.
      rewrite <-Heqa.
      econstructor; eauto.
      rewrite <-Heqa in H6; simpl in H6.

    apply spill_sound2_match in H4.
    remember (clear_L sl).
    induction H5.
    + destruct H4 as [sl' H4]. rewrite H4.
      econstructor; eauto.





  eapply Spill2Spill with (Sp:=getSp sl2).
  { reflexivity. }
  { rewrite <-Req. eapply Sp_sub_R. induction sl2. apply H. }
  assert (H' := spill_sound_card k ZL Λ R M s sl H). destruct H' as [K H'].
  eapply Spill2Load with (sl:=sl).
  { rewrite getSp_clearSp. apply empty_1. }
  { rewrite getL_clearSp. rewrite <-Meq, <-sleq. eapply L_sub_SpM. apply H. }
  { rewrite getL_clearSp. rewrite <-sleq, <-Req. apply H'. }
  rewrite getL_clearSp.
  general induction H.
  - eapply IHspill_sound.


  - general induction H.
    + apply IHs0 in s0.
      apply Spill2Spill with (Sp:=Sp); simpl; eauto.
      econstructor 2; simpl;eauto;[apply empty_1|].
      econstructor 3; simpl; eauto.
      apply IHs0. intros.
    + apply Spill2Spill with (Sp:=Sp); simpl; eauto.
      econstructor 2; simpl;eauto;[apply empty_1|].
      econstructor 4; simpl; eauto.
    + apply Spill2Spill with (Sp:=Sp); simpl; eauto.
      econstructor 2; simpl;eauto;[apply empty_1|].
      econstructor 5. simpl; eauto; [apply s0_1|apply s0_2].

    + apply Spill2Spill with (Sp:=Sp); simpl; eauto.
      econstructor 2; simpl;eauto;[apply empty_1|].
      econstructor 3; simpl; eauto.


           apply IHs0.




             ewrite getL_clearSp. rewrite <-sleq. simpl. rewrite <-Meq.
           clear - H0; cset_tac.
        -- rewrite getL_clearSp. rewrite <-sleq. simpl. rewrite <-Req. apply H4.
        -- rewrite getL_clearSp. rewrite clear_clear; inversion sleq. destruct b, p.
           destruct l;[| clear - H8; isabsurd].
           econstructor 3; simpl; eauto.
           ++ apply H1. _sound.



      eapply Spill2Spill with (Sp:=Sp).
      * inversion sleq; inversion H8; inversion H13. simpl. symmetry. assumption.
      *
      * econstructor 2. with (Sp:=Sp).
        -- rewrite getSp_clearSp. apply empty_1.
        -- rewrite getL_clearSp. rewrite <-sleq. simpl. apply IHspill_sound.

      apply IHspill_sound.
      inversion H1.
      rewrite <-sleq, <-Req.
      rewrite <-ReqR; eauto.
      econstructor; simpl; eauto. cset_tac.
