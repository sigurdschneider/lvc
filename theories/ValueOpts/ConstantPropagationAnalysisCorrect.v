Require Import Util SizeInduction Get MapDefined.
Require Import IL Var Val.
Require Import CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice.
Require Import AnalysisForwardSSA Subterm CSet MapAgreement RenamedApart.
Require Import Infra.PartialOrder Infra.Lattice Infra.WithTop.
Require Import LabelsDefined Annotation.
Require Import ConstantPropagation ConstantPropagationAnalysis.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} ftransform ZL ZLIncl st.

Lemma option_R_inv x y
  : @OptionR.option_R (withTop Val.val) (withTop Val.val)
         (@poEq (withTop Val.val)
                (@withTop_PO Val.val Val.int_eq Val.Equivalence_eq_int' Val.int_eq_dec)) x y
    -> x = y.
Proof.
  intros. inv H; eauto.
  inv H0; eauto.
  do 2 f_equal. eauto.
Qed.

Opaque cp_trans_domain.

Lemma add_dead (G:set var) (AE:Dom) x v (NOTIN:x ∉ G)
  : agree_on (OptionR.option_R (withTop_eq (R:=Val.int_eq))) G (domenv AE)
             (domenv (add x v AE)).
Proof.
  hnf; intros. unfold domenv.
  mlud. cset_tac. reflexivity.
Qed.

Lemma remove_dead (G:set var) (AE:Dom) x (NOTIN:x ∉ G)
  : agree_on (OptionR.option_R (withTop_eq (R:=Val.int_eq))) G (domenv AE)
             (domenv (remove x AE)).
Proof.
  hnf; intros. unfold domenv.
  mlud. cset_tac. reflexivity.
Qed.

Lemma domupd_dead (G:set var) x AE v (NOTIN:x ∉ G)
  : agree_on (OptionR.option_R (withTop_eq (R:=Val.int_eq))) G (domenv AE)
             (domenv (domupd AE x v)).
Proof.
  unfold domupd; cases.
  + eapply add_dead; eauto.
  + eapply remove_dead; eauto.
Qed.

Lemma fold_left_join_start_swap X `{JoinSemiLattice X} (a b:X) A
  : poEq (fold_left join A (join a b)) (join b (fold_left join A a)).
Proof.
  general induction A; simpl.
  - simpl. rewrite join_commutative. reflexivity.
  - rewrite !IHA.
    rewrite <- !join_associative.
    setoid_rewrite join_commutative at 2.
    reflexivity.
Qed.

Lemma domenv_proper G
  : Proper (poEq ==> agree_on poEq G) domenv.
Proof.
  unfold Proper, respectful, domenv, agree_on; intros.
  eauto.
Qed.

Lemma proj1_sig_poEq X `{PartialOrder X} P (a b:{ x : X | P x })
  : poEq a b -> poEq (proj1_sig a) (proj1_sig b).
Proof.
  destruct a,b; eauto.
Qed.

Lemma agree_domenv_join sT (G:set var) (a b:DDom sT) c
      : agree_on poEq G (domenv (proj1_sig a)) (domenv c)
        -> agree_on poEq G (domenv (proj1_sig b)) (domenv c)
        -> agree_on poEq G (domenv (proj1_sig (join a b))) (domenv c).
Proof.
  destruct a,b;
    unfold domenv; simpl proj1_sig.
  intros A B.
  hnf; intros z IN.
  unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  specialize (A z IN).
  specialize (B z IN). cbv beta in *.
  rewrite A, B. rewrite join_idempotent. reflexivity.
Qed.

Class JoinRespectsLowerBound (A : Type) `{JoinSemiLattice A} `{@LowerBounded A H} :=
  {
    bottom_neutral : forall (a:A), poEq (join bottom a) a
  }.

Instance Dom_JRLB
  : JoinRespectsLowerBound Dom.
Proof.
  econstructor.
  intros. hnf; intros.
  simpl. unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  rewrite MapFacts.empty_o. simpl.
  cases; reflexivity.
Qed.

Instance DDom_JRLB sT
  : JoinRespectsLowerBound (DDom sT).
Proof.
  econstructor.
  intros. hnf; intros.
  simpl. unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  rewrite MapFacts.empty_o. simpl.
  cases; reflexivity.
Qed.

Lemma agree_domenv_join_bot sT (G:set var) (a b:DDom sT) c
      : a === bottom
        -> agree_on poEq G (domenv (proj1_sig b)) (domenv c)
        -> agree_on poEq G (domenv (proj1_sig (join a b))) (domenv c).
Proof.
  destruct a,b;
    unfold domenv, poEq at 1; simpl proj1_sig.
  intros A B.
  hnf; intros z IN.
  unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  specialize (B z IN). cbv beta in *.
  rewrite B.
  hnf in A. simpl proj1_sig in *.
  rewrite A, <- B.
  setoid_rewrite <- bottom_neutral at 3.
  simpl join at 2. unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
Qed.

Lemma agree_domenv_join_bot2 sT (G:set var) (a b:DDom sT) c
      : agree_on poEq G (domenv (proj1_sig a)) (domenv c)
        -> b === bottom
        -> agree_on poEq G (domenv (proj1_sig (join a b))) (domenv c).
Proof.
  destruct a,b;
    unfold domenv, poEq at 2; simpl proj1_sig.
  intros A B.
  hnf; intros z IN.
  unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  specialize (A z IN). cbv beta in *.
  rewrite A.
  hnf in B. simpl proj1_sig in *.
  rewrite <- A, B.
  setoid_rewrite <- bottom_neutral at 3.
  simpl join at 2. unfold joinMap.
  rewrite MapFacts.map2_1bis; eauto.
  rewrite join_commutative. eauto.
Qed.

(*
Lemma agree_on_fold_left (sT:IL.stmt) (ZL:list (list var)) F ans (LEN:❬F❭ = ❬ans❭)
      (ZLIncl: list_union (of_list ⊝ ZL) [<=] IL.occurVars sT) t
      (G:set var) (Dt:set var) (AE:DDom sT) ZL' ZL'Incl
      (pf : domain (proj1_sig AE) [<=] IL.occurVars sT) STF
      (H1:forall ST, agree_on poEq
                   (G \ (list_union (defVars ⊜ F ans) ∪ Dt ∪ list_union (of_list ⊝ (fst ⊝ F ++ ZL))))
                   (domenv (proj1_sig AE))
                   (domenv (proj1_sig (forward cp_trans_dep ZL' ZL'Incl t ST AE)))
                \/ (forward cp_trans_dep ZL' ZL'Incl t ST AE === bottom))
      (H2:forall n Zs y ST, get F n Zs -> get ans n y ->
                       agree_on poEq
                                (G \ (list_union (defVars ⊜ F ans) ∪ Dt ∪ defVars Zs y
                                                 ∪ list_union (of_list ⊝ ZL)))
                           (domenv
                              (proj1_sig
                                 (forward cp_trans_dep ZL' ZL'Incl (snd Zs) ST AE)))
                           (domenv (proj1_sig AE)) \/
                       (forward cp_trans_dep ZL' ZL'Incl (snd Zs) ST AE === bottom))
  : forall ST, agree_on poEq
             (G \ (list_union (defVars ⊜ F ans) ∪ Dt ∪ list_union (of_list ⊝ ZL)))
             (domenv (proj1_sig AE))
             (domenv
                (proj1_sig
                   (fold_left
                      join
                      (forwardF (forward cp_trans_dep ZL' ZL'Incl) F AE STF)
                      (forward cp_trans_dep ZL' ZL'Incl t ST AE)))) \/
          fold_left join
                    (forwardF (forward cp_trans_dep ZL' ZL'Incl) F AE STF)
                    (forward cp_trans_dep ZL' ZL'Incl t ST AE) === bottom.
Proof.
  Opaque poEq bottom.
  general induction LEN.
  - eapply H1.
  - Opaque join. simpl.
    edestruct (IHLEN sT ZL ZLIncl t) as [AGRF|BOTF]; eauto.
    + intros.
      edestruct H1; eauto.
      left. eapply agree_on_incl; eauto.
      instantiate (1:=defVars x y ∪ Dt).
      instantiate (1:=G). simpl.
      unfold defVars at 2 4. clear.
      setoid_rewrite list_union_start_swap at 3 4.
      cset_tac.
    + intros. exploit (H2 (S n)) as IH; eauto using get.
      destruct IH; eauto. left.
      eapply agree_on_incl; eauto. simpl.
      setoid_rewrite list_union_start_swap at 3.
      clear; cset_tac'.
    + edestruct H2 as [AGRsndx|BOTsndx]; eauto using get;
      try instantiate (1:=STF _ _ ltac:(eauto using get)) in AGRsndx.
      * left.
        symmetry.
        etransitivity.
        eapply domenv_proper.
        eapply proj1_sig_poEq.
        eapply fold_left_join_start_swap.
        eapply agree_domenv_join.
        -- eapply agree_on_incl; eauto. simpl.
           setoid_rewrite list_union_start_swap at 1 3 4.
           unfold defVars at 1 3 5.
           clear; cset_tac'.
        -- eapply agree_on_incl.
           symmetry. eauto.
           setoid_rewrite list_union_start_swap at 1.
           clear. cset_tac.
      * left. symmetry.
        etransitivity.
        eapply domenv_proper.
        eapply proj1_sig_poEq.
        eapply fold_left_join_start_swap.
        eapply agree_domenv_join_bot; eauto.
        -- eapply agree_on_incl.
           symmetry. eauto.
           setoid_rewrite list_union_start_swap at 1.
           clear. cset_tac.
    + edestruct H2 as [AGRsndx|BOTsndx]; eauto using get;
      try instantiate (1:=STF _ _ ltac:(eauto using get)) in AGRsndx.
      * left.
        symmetry.
        etransitivity.
        eapply domenv_proper.
        eapply proj1_sig_poEq.
        eapply fold_left_join_start_swap.
        eapply agree_domenv_join_bot2.
        -- eapply agree_on_incl; eauto. simpl.
           setoid_rewrite list_union_start_swap at 1 3 4.
           unfold defVars at 1 3 5.
           clear; cset_tac'.
        -- eauto.
      * right.
        rewrite fold_left_join_start_swap.
        rewrite BOTF. rewrite BOTsndx.
        eapply bottom_neutral.
Qed.
 *)

(*
Lemma cp_forward_agree sT ZL (AE:Dom) pf G s (ST:subTerm s sT) ra ZLIncl
  (RA:renamedApart s ra)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig (forward cp_trans_dep ZL ZLIncl s ST (exist _ AE pf))))
    \/ (forward cp_trans_dep ZL ZLIncl s ST (exist _ AE pf) === bottom
       /\ ~ defined_on (fst (getAnn ra)) (domenv AE)).
Proof.
  general induction RA; simpl in *.
  - destruct e.
    + rewrite H1.
      edestruct IHRA.
      * left.
        symmetry.
        etransitivity.
        symmetry.
        eapply agree_on_incl.
        eapply H3.
        -- rewrite H2. simpl.
           instantiate (1:=G). clear; cset_tac.
        -- symmetry.
           eapply domupd_dead. cset_tac.
      * right; dcr. split; eauto.
        admit.
    + rewrite H1.
      edestruct IHRA.
      * left.
        symmetry.
        etransitivity.
        symmetry.
        eapply agree_on_incl.
        eapply H3.
        -- rewrite H2. simpl.
           instantiate (1:=G). clear; cset_tac.
        -- symmetry.
           eapply add_dead. cset_tac.
      * right; dcr; split; eauto. admit.
  - repeat cases.
    + admit.
    + clear Heq0. admit.
    + admit.
    + right. split; eauto. admit.
  - left; eauto.
  - left.
    destruct (get_dec ZL (Var.labN f)); dcr.
    + erewrite get_nth; eauto.
      admit.
    + erewrite not_get_nth_default; eauto. simpl. reflexivity.
  - (*rewrite <- H5.
    eapply agree_on_fold_left; eauto.
    + intros. eapply agree_on_incl.
      eapply IHRA; eauto.
      * pe_rewrite. eauto.
      * pe_rewrite. instantiate (1:=G); clear. cset_tac.
    + intros.
      decide (forward cp_trans_dep (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)
                      (snd Zs) ST0
                      (exist (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT) AE pf) ===
                      (⊥)); eauto.

      symmetry.
      eapply agree_on_incl.
      eapply H1; eauto.
      * edestruct H2; eauto; dcr.
        rewrite H8. admit.
      * pe_rewrite. instantiate (1:=G).
        unfold defVars at 2.
        rewrite List.map_app. rewrite list_union_app.
        revert H.
        clear. cset_tac'.
        eapply list_union_get in H2. destruct H2; dcr. inv_get.
        eapply H4. eapply incl_list_union; eauto using zip_get, map_get_1.
        unfold defVars. eauto with cset. cset_tac.*)
Admitted.
*)

(*
Lemma cp_forward_agree_def sT ZL (AE:Dom) pf G s (ST:subTerm s sT) ra ZLIncl
  (RA:renamedApart s ra) (Def:defined_on (fst (getAnn ra)) (domenv AE))
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig (forward cp_trans_dep ZL ZLIncl s ST (exist _ AE pf)))).
Proof.
  edestruct cp_forward_agree; dcr; eauto.
  exfalso. eauto.
Qed.
 *)

Arguments exist {A} {P} x _.

Definition cp_sound sT AE AE' DIncl Cp ZL s (ST:subTerm s sT) ZLIncl ra anr
  : let X := forward cp_trans_dep ZL ZLIncl s ST (@exist _ _ AE DIncl) anr in
    renamedApart s ra
    -> annotation s anr
    -> labelsDefined s (length ZL)
    -> poEq (fst X) ((@exist _ _ AE DIncl),anr)
    -> poEq AE' AE
    -> cp_sound (domenv AE') Cp (snd X) s anr.
Proof.
  intros LET RA ANN LD EQ1 EQ2. subst LET.
  general induction LD; invt @renamedApart;
    try invt @annotation; simpl in *; simpl;
      simpl in *; dcr;
        repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst;
          simpl in *; try invt @ann_R; subst.
  - destruct e; simpl in *; simpl in *.
    + econstructor; eauto.
      assert (eqMap AE (domupd AE x (op_eval (domenv AE) e))).
      * eapply IHLD; eauto.

        split; eauto.
        -- etransitivity; eauto. admit.
        -- etransitivity; eauto.
      econstructor; eauto.
      *
        exploit (IHLD sT  (exist (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT)
            (domupd AE x (op_eval (domenv AE) e))
            (cp_trans_domain' ZL ST ZLIncl
               (exist (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT) AE
                      DIncl)))); eauto.
        rewrite EQ.
        Transparent poEq. simpl. admit.
        eapply EQ.
        etransitivity.. eapply EQ.
        simpl. simpl in *.
        admit.
      * simpl in *.
        pose proof (EQ x).
        eapply cp_forward_agree in H4; eauto.
        instantiate (2:=(domupd AE x (op_eval (domenv AE) e))) in H4.
        specialize (H4 x). pe_rewrite.
        exploit H4. admit. clear H4.
        instantiate (1:= (cp_trans_domain' ZL ST ZLIncl
                                           (exist (fun m : Map [nat, withTop val] =>
                                                     domain m [<=] occurVars sT) AE DIncl))) in H0.
        instantiate (1:=(subTerm_EQ_Let eq_refl ST)) in H0.
        instantiate (1:=ZLIncl) in H0.
        rewrite H in H0.
        eapply option_R_inv in H0.
        unfold domenv. rewrite <- H0.
        unfold domenv,domupd. cases. mlud; eauto.
        exfalso; eauto. mlud; eauto. exfalso; eauto.
        pe_rewrite. admit.
    + econstructor; eauto.

      eapply IHLD; eauto. hnf; intros.
      rewrite <- EQ; eauto.


    + econstructor; eauto.
      simpl. admit.
  - let_case_eq; try let_pair_case_eq; subst; simpl in *;
      repeat cases in EQ; simpl in *;
        econstructor; intros; eauto;
          try rewrite COND in *; simpl in *;
            try rewrite Val.val2bool_true in *;
            try rewrite Val.val2bool_false in *;
            isabsurd.
    + admit.
    + admit.
    + eapply IHLD1; eauto. admit.
    + eapply IHLD2; eauto. admit.
  - econstructor.
  - (* invariant with ZL and Cp *) admit.
  - econstructor.
    + intros.
      eapply H0 with (ZL0:=fst ⊝ F ++ ZL); eauto with len.
      admit.
    + eapply IHLD with (ZL0:=fst ⊝ F ++ ZL); eauto with len.
Admitted.
