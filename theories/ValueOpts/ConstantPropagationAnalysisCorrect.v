Require Import Util SizeInduction Get MapDefined Coq.Classes.RelationClasses.
Require Import IL Var Val OptionR.
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

Local Arguments exist {A} {P} x _.
Local Arguments forward {sT} {Dom} ftransform ZL {ZLIncl} st {ST}.
Local Arguments cp_trans_dep {sT} ZL st {ST} {ZLIncl}.
Local Arguments cp_trans_domain {sT} ZL st {ST} {ZLIncl} a b.

Lemma agree_on_R_impl  (X : Type) `{OrderedType X} (Y : Type)
      (R R':Y -> Y -> Prop) (D:set X) (f g:X -> Y)
  : agree_on R D f g
    -> (forall x, x ∈ D -> R (f x) (g x) -> R' (f x) (g x))
    -> agree_on R' D f g.
Proof.
  intros; hnf; intros; eauto.
Qed.

Lemma option_eq_option_R X (R:relation X) x y
  : option_eq R x y <-> OptionR.option_R R x y.
Proof.
  split; inversion 1; econstructor; eauto.
Qed.


Notation "'getAE' X" := (proj1_sig (fst (fst X))) (at level 10, X at level 0).

(*
Lemma forward_defined_on sT ZL (AE:DDom sT) s (ST:subTerm s sT) ZLIncl anr D
      (Def:defined_on D (domenv (proj1_sig AE)))
  : defined_on D  (domenv (proj1_sig
                             (fst (fst (@forward _ _ (@cp_trans_dep) ZL ZLIncl
                                                 s ST AE anr))))).
Proof.
  pose proof (forward_monotone DDom (@cp_trans_dep) (@transf_mon_dep sT) ST ST ZL ZLIncl ZLIncl AE AE ltac:(reflexivity) ltac:(reflexivity) (r:=anr)).
  hnf; intros. destruct (Def _ H0).
  destruct H as [[LE1 LE2] LE3].
  specialize (LE1 x).
Qed.
 *)

Lemma agree_on_option_R_fstNoneOrR  (X : Type) `{OrderedType X} (Y : Type)
      (R R':Y -> Y -> Prop) (D:set X) (f g h:X -> option Y)
  : agree_on (option_R R) D f g
    -> agree_on (fstNoneOrR R') D g h
    -> (forall a b c, R a b -> R' b c -> R' a c)
    -> agree_on (fstNoneOrR R') D f h.
Proof.
  intros AGR1 AGR2 Trans; hnf; intros.
  exploit AGR1 as EQ1; eauto.
  exploit AGR2 as EQ2; eauto.
  inv EQ1; inv EQ2; clear_trivial_eqs; try econstructor; try congruence.
  assert (x0 = b) by congruence; subst.
  eauto.
Qed.


Instance agree_inst (X : Type) `{H : OrderedType X} (Y : Type) (R : relation Y)
  : Proper (SetInterface.Equal ==> eq ==> eq ==> iff) (agree_on R).
Proof.
  unfold Proper, respectful; intros; subst.
  split; intros; hnf; intros; eauto; cset_tac.
Qed.

Instance agree_inst_impl (X : Type) `{H : OrderedType X} (Y : Type) (R : relation Y)
  : Proper (SetInterface.Subset ==> eq ==> eq ==> flip impl) (agree_on R).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  intros; hnf; intros; eauto.
Qed.

Lemma defined_on_agree_fstNoneOrR (X : Type) `{H : OrderedType X}
      (Y : Type) (R : relation Y) (D : ⦃X⦄) (f g : X -> ؟ Y)
  : defined_on D f -> agree_on (fstNoneOrR R) D f g -> defined_on D g.
Proof.
  intros Def Agr.
  hnf; intros. edestruct Def; eauto.
  exploit Agr; eauto. rewrite H1 in H2. inv H2; eauto.
Qed.

Instance int_eq_trans : Transitive (int_eq).
Proof.
  hnf; intros. rewrite H ;eauto.
Qed.

Instance int_eq_sym : Symmetric (int_eq).
Proof.
  hnf; intros. rewrite H ;eauto. reflexivity.
Qed.

Lemma domupd_poLe (m m' : Map [nat, withTop val]) a v
  : poLe (find a m) v
    -> leMap m m'
    -> leMap m (domupd m' a v).
Proof.
  intros. hnf; intros.
  unfold domupd; cases.
  - mlud; eauto. rewrite <- e. eauto.
  - mlud; eauto. rewrite <- e. eauto.
Qed.


Lemma domupd_list_exp (a : Map [nat, withTop val]) (Z : params) (Y : args)
  : leMap a (domupd_list a Z (op_eval (domenv a) ⊝ Y)).
Proof.
  general induction Z; destruct Y; simpl domupd_list; try reflexivity.
  eapply domupd_poLe; eauto.
  unfold ojoin; repeat cases; eauto.
  econstructor. eapply withTop_generic_join_exp.
Qed.


Lemma cp_forward_agree sT ZL (AE:DDom sT) G s (ST:subTerm s sT) ra ZLIncl anr
      (RA:renamedApart s ra) (Def:defined_on (fst (getAnn ra)) (domenv (proj1_sig AE)))
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) ZL ZLIncl
                                            s ST AE anr))))) /\
    agree_on poLe (G \ (snd (getAnn ra)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) ZL ZLIncl
                                            s ST AE anr))))).
Proof.
  general induction RA; destruct anr; simpl in *;
    try now (split; reflexivity); simpl.
  - destruct e;
      repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
        pe_rewrite; set_simpl.
    + edestruct @IHRA; clear IHRA; dcr.
      Focus 2.
      dcr; split.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        eapply domupd_dead. cset_tac.
        cset_tac.
      * simpl. admit.
      * simpl in *.

        eapply agree_on_option_R_fstNoneOrR.
        Focus 2.
        eapply agree_on_incl; eauto.
        cset_tac.
        eapply domupd_dead. cset_tac.
        intros. etransitivity; eauto using withTop_le_refl.
    + edestruct @IHRA; clear IHRA; dcr.
      Focus 2.
      dcr; split.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        set_simpl.
        eapply add_dead. cset_tac.
        cset_tac.
      * simpl.  admit.
      * simpl in *.
        eapply agree_on_option_R_fstNoneOrR.
        Focus 2.
        eapply agree_on_incl; eauto. cset_tac.
        eapply add_dead. cset_tac.
        intros. etransitivity; eauto using withTop_le_refl.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      pe_rewrite; set_simpl.
    split.
    + symmetry; etransitivity; symmetry.
      * eapply agree_on_incl.
        -- eapply IHRA2; eauto.
           eapply defined_on_agree_fstNoneOrR; eauto.
           instantiate (1:=withTop_le (R:=int_eq)).
           edestruct @IHRA1 with (ZL:=ZL) (AE:=(@exist Dom
                    (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT)
                    (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)))
           (anr:=anr1) (G:=D) (ST:= (@subTerm_EQ_If1 sT (stmtIf e s t) e s t
                      (@eq_refl stmt (stmtIf e s t)) ST)) (ZLIncl:=ZLIncl).
           simpl; eauto.
           eapply agree_on_incl.
           simpl in *.
           eapply H4. eapply renamedApart_disj in RA2; pe_rewrite.
           eauto with cset.
        -- cset_tac.
      * symmetry; etransitivity; symmetry.
        -- eapply agree_on_incl. eapply IHRA1; eauto.
           cset_tac.
        -- simpl. reflexivity.
    + etransitivity.
      Focus 2.
      eapply agree_on_incl.
      eapply IHRA2.
      eapply defined_on_agree_fstNoneOrR; eauto.
      instantiate (1:=withTop_le (R:=int_eq)).
      edestruct @IHRA1 with (ZL:=ZL) (AE:=(@exist Dom
                    (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT)
                    (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)))
           (anr:=anr1) (G:=D) (ST:= (@subTerm_EQ_If1 sT (stmtIf e s t) e s t
                      (@eq_refl stmt (stmtIf e s t)) ST)) (ZLIncl:=ZLIncl).
      simpl; eauto.
      eapply agree_on_incl. eapply H4.
      eapply renamedApart_disj in RA2; pe_rewrite.
      eauto with cset. instantiate (1:=G\Ds).
      cset_tac.
      eapply agree_on_incl.
      edestruct @IHRA1 with (ZL:=ZL) (AE:=(@exist Dom
                    (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT)
                    (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)))
           (anr:=anr1) (G:=G) (ST:= (@subTerm_EQ_If1 sT (stmtIf e s t) e s t
                      (@eq_refl stmt (stmtIf e s t)) ST)) (ZLIncl:=ZLIncl).
      eauto. eapply H4. cset_tac.
  - set_simpl.
    destruct (get_dec ZL (Var.labN f)); dcr.
    + erewrite get_nth; eauto. split.
      * admit.
      * hnf; intros.
        eapply domupd_list_exp.
    + admit.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
        pe_rewrite; set_simpl.

    + erewrite not_get_nth_default; eauto. simpl.
      split; reflexivity.
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
