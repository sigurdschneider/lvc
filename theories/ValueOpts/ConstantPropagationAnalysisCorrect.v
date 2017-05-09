Require Import Util SizeInduction Get MapDefined Coq.Classes.RelationClasses.
Require Import IL Var Val OptionR AllInRel.
Require Import CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice.
Require Import Analysis AnalysisForwardSSA Subterm CSet MapAgreement RenamedApart.
Require Import Infra.PartialOrder Infra.Lattice Infra.WithTop.
Require Import LabelsDefined Annotation.
Require Import Reachability ConstantPropagation ConstantPropagationAnalysis.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} ftransform reach_transf ZL ZLIncl st.

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

Lemma domenv_proper' G
  : Proper (poEq ==> agree_on eq G) domenv.
Proof.
  unfold Proper, respectful, domenv, agree_on; intros.
  exploit (H x0); eauto. eapply option_R_inv in H1. eauto.
Qed.

Lemma domenv_proper''
  : Proper (poEq ==> eq ==> eq) domenv.
Proof.
  unfold Proper, respectful, domenv, agree_on; intros; subst.
  exploit (H y0); eauto. eapply option_R_inv in H0. eauto.
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

Notation "'getAE' X" := (proj1_sig (fst (fst X))) (at level 10, X at level 0).

Local Arguments exist {A} {P} x _.
Local Arguments forward {sT} {Dom} ftransform reach_transf ZL {ZLIncl} st {ST}.
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

Lemma domupd_eq m x y a
  : x === y
    -> find x (domupd m y a) = a.
Proof.
  unfold domupd; cases; intros; mlud; eauto.
  - exfalso; eauto.
  - exfalso; eauto.
Qed.

Lemma domupd_list_get AE Z Y x n y
  : NoDupA eq Z
    -> get Z n x
    -> get Y n y
    -> poLe y (find x (domupd_list AE Z Y)).
Proof.
  intros ND GetZ GetY.
  general induction n; simpl domupd_list.
  - rewrite domupd_eq; eauto.
    unfold ojoin; repeat cases; eauto; try constructor.
    rewrite withTop_generic_join_sym.
    eapply withTop_generic_join_exp.
  - inv GetZ; inv GetY.
    simpl domupd_list.
    rewrite domupd_ne; eauto.
    inv ND. intro. eapply H3.
    rewrite <- H. eapply get_InA; eauto.
Qed.

Lemma cp_forwardF_agree (sT:stmt) BL G (F:list (params * stmt)) ans anF ZL'
      (ZL'Incl: list_union (of_list ⊝ ZL') [<=] occurVars sT)
      (Len1: ❬F❭ = ❬ans❭) (Len2:❬F❭ = ❬anF❭)
      (AN:forall (n : nat) (Zs : params * stmt) sa,
          get anF n sa -> get F n Zs -> annotation (snd Zs) sa)
      AE
      (ST: forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT)
      (IH:forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
          get F n Zs ->
          get ans n a ->
          forall (sT : stmt) (ZL : 〔params〕) (AE : DDom sT) (G : ⦃nat⦄)
            (ST : subTerm (snd Zs) sT)
            (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT)
            (anr : ann bool),
            annotation (snd Zs) anr ->
            agree_on (option_R (withTop_eq (R:=int_eq)))
                     (G \ (snd (getAnn a) ∪ list_union (of_list ⊝ ZL)))
                     (domenv (proj1_sig AE))
                     (domenv (getAE
                                (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs)
                                          ST AE anr))) /\
            agree_on (fstNoneOrR (withTop_le (R:=int_eq))) (G \ snd (getAnn a))
                     (domenv (proj1_sig AE))
                     (domenv (getAE
                                (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs)
                                          ST AE anr))))
  : agree_on (option_R (withTop_eq (R:=int_eq)))
             (G \ (list_union (defVars ⊜ F ans) ∪ list_union (of_list ⊝ ZL')))
             (domenv (proj1_sig AE))
             (domenv (getAE (forwardF BL (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) _ ZL'Incl)
                                      F anF AE ST))) /\
    agree_on (fstNoneOrR (withTop_le (R:=int_eq)))
             (G \ (list_union (snd ⊝ getAnn ⊝ ans)))
             (domenv (proj1_sig AE))
             (domenv (getAE (forwardF BL (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) _ ZL'Incl)
                                      F anF AE ST))).
Proof.
  general induction Len1; destruct anF; inv Len2. simpl.
  - split; reflexivity.
  - edestruct (IHLen1 sT BL G anF ZL');
      edestruct (IH 0 x y ltac:(eauto using get) ltac:(eauto using get) sT ZL' AE G ltac:(eauto using get) ZL'Incl a); eauto using get.
    simpl; split; etransitivity; eapply agree_on_incl; eauto.
    + norm_lunion. clear_all. unfold defVars at 1. cset_tac.
    + norm_lunion. clear_all. cset_tac.
    + norm_lunion. clear_all. cset_tac.
    + norm_lunion. unfold defVars. clear_all. cset_tac.
Qed.

Lemma list_union_defVars_decomp F ans (Len:❬F❭ = ❬ans❭)
  : list_union (defVars ⊜ F ans) [=]
               list_union (of_list ⊝ fst ⊝ F) ∪ list_union (snd ⊝ getAnn ⊝ ans).
Proof.
  general induction Len; simpl; eauto.
  - cset_tac.
  - norm_lunion. rewrite IHLen.
    unfold defVars at 1.
    clear_all; cset_tac.
Qed.

Lemma domupd_list_agree (R:relation aval) `{Reflexive _ R} G AE Z Y
  : agree_on R (G \ of_list Z)
             (domenv AE)
             (domenv (domupd_list AE Z Y)).
Proof.
  general induction Z; destruct Y; simpl; try reflexivity.
  hnf; intros. cset_tac'.
  unfold domenv.
  rewrite domupd_ne; [|symmetry; eauto].
  exploit IHZ; eauto.
  exploit H2; eauto. cset_tac.
Qed.


Lemma cp_forward_agree sT ZL (AE:DDom sT) G s (ST:subTerm s sT) ra ZLIncl anr
      (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl
                                            s ST AE anr))))) /\
    agree_on poLe (G \ (snd (getAnn ra)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl
                                            s ST AE anr))))).
Proof.
  general induction RA; invt @annotation; simpl in *;
    try now (split; reflexivity); simpl.
  - destruct e;
      repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
        pe_rewrite; set_simpl.
    + edestruct @IHRA; clear IHRA; dcr; try split.
      * instantiate (1:=(setTopAnn sa a)).
        eapply setTopAnn_annotation; eauto.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        eapply domupd_dead. cset_tac.
        cset_tac.
      * simpl in *.
        eapply agree_on_option_R_fstNoneOrR; [|eapply agree_on_incl; eauto|].
        eapply domupd_dead. cset_tac. cset_tac.
        intros. etransitivity; eauto using withTop_le_refl.
    + edestruct @IHRA; clear IHRA; dcr; try split.
      * instantiate (1:=(setTopAnn sa a)).
        eapply setTopAnn_annotation; eauto.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        set_simpl.
        eapply add_dead. cset_tac.
        cset_tac.
      * simpl in *.
        eapply agree_on_option_R_fstNoneOrR; [|eapply agree_on_incl; eauto|].
        eapply add_dead. cset_tac. cset_tac.
        intros. etransitivity; eauto using withTop_le_refl.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      pe_rewrite; set_simpl.
    split.
    + symmetry; etransitivity; symmetry.
      * eapply agree_on_incl.
        -- eapply IHRA2; eauto.
           eapply setTopAnn_annotation; eauto.
        -- cset_tac.
      * symmetry; etransitivity; symmetry.
        -- eapply agree_on_incl. eapply IHRA1; eauto.
           eapply setTopAnn_annotation; eauto.
           cset_tac.
        -- simpl. reflexivity.
    + edestruct @IHRA1 with (ZL:=ZL)
                              (AE:=(@exist Dom (fun m : Map [nat, withTop val] => domain m [<=] occurVars sT)
                                           (proj1_sig AE)
                                           (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)))
                              (G:=G)
                              (ST:= (@subTerm_EQ_If1 sT (stmtIf e s t) e s t
                                                     (@eq_refl stmt
                                                               (stmtIf e s t)) ST)) (ZLIncl:=ZLIncl);
        [|etransitivity;[ eapply agree_on_incl; eauto |eapply agree_on_incl;[eapply IHRA2|]]];
        try eapply setTopAnn_annotation; eauto; cset_tac.
  - set_simpl.
    destruct (get_dec ZL (Var.labN f)); dcr.
    + erewrite get_nth; eauto. split.
      * cases; try reflexivity.
        eapply agree_on_incl.
        eapply domupd_list_agree; eauto.
        -- hnf; intros. reflexivity.
        -- rewrite <- incl_list_union; eauto.
           cset_tac. reflexivity.
      * hnf; intros; cases; try reflexivity.
        eapply domupd_list_exp.
    + rewrite !not_get_nth_default; eauto.
      repeat cases; eauto; split; simpl; reflexivity.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      pe_rewrite; set_simpl.
    edestruct IHRA with (ZL:=fst ⊝ F ++ ZL) (anr:=(setTopAnn ta a)); eauto using setTopAnn_annotation.
    split.
    + etransitivity.
      * eapply agree_on_incl. eapply H5.
        rewrite list_union_defVars_decomp; eauto.
        rewrite List.map_app.
        rewrite list_union_app; eauto.
        clear_all; cset_tac.
      * eapply agree_on_incl.
        eapply cp_forwardF_agree with (ZL':=fst ⊝ F ++ ZL); eauto.
        -- len_simpl. rewrite H8. eauto with len.
        -- intros. inv_get.
           eapply setTopAnn_annotation; eauto.
        -- rewrite List.map_app. rewrite list_union_app; eauto.
           rewrite list_union_defVars_decomp; eauto with len.
           clear_all. cset_tac.
    + etransitivity.
      * eapply agree_on_incl. eapply H6.
        cset_tac.
      * eapply agree_on_incl.
        eapply cp_forwardF_agree with (ZL':=fst ⊝ F ++ ZL);
          intros; eauto.
        -- len_simpl. rewrite H8. eauto with len.
        -- inv_get. eapply setTopAnn_annotation; eauto.
        -- rewrite list_union_defVars_decomp; eauto.
           clear_all; cset_tac.
Qed.


Lemma disj_union_inv X `{OrderedType X} (x:X) (s t:set X)
  : disj s t
    -> x ∈ s ∪ t
    -> (x ∈ s /\ x ∉ t) \/ (x ∈ t /\ x ∉ s).
Proof.
  cset_tac.
Qed.

Lemma eqMap_forwardF_t
      (F : 〔params * stmt〕)
      (t : stmt)
      (ZL : 〔params〕)
      (ra : 〔ann (⦃nat⦄ * ⦃nat⦄)〕)
      (sT : stmt)
      (AE : DDom sT) BL
      STt STF
      (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT)
      (LenZL:❬ZL❭ >= ❬F❭)
      (sa : 〔ann bool〕)
      (ta : ann bool) AE' tra (RAt:renamedApart t tra) (AN:annotation t ta)
      (EQM : eqMap
               (getAE (forwardF BL
                    (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                    sa
                    AE'
                    STF)) (proj1_sig AE))
      (EQ: eqMap (getAE (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl t STt AE ta)) (proj1_sig AE'))
      (Disj1:disj (snd (getAnn tra)) (list_union (of_list ⊝ ZL)))
      (Disj2:disj (snd (getAnn tra)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj3:disj (list_union (of_list ⊝ ZL)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj5:disj (list_union (of_list ⊝ fst ⊝ F)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj6:PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ra))
      (Len2 : ❬F❭ = ❬ra❭)
      (Len1 : ❬F❭ = ❬sa❭)
      (AnnF : forall (n : nat) (s' : params * stmt) (sa' : ann bool),
         get sa n sa' -> get F n s' -> annotation (snd s') sa')
      (RA : forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
       get F n Zs -> get ra n a -> renamedApart (snd Zs) a)
  : eqMap (getAE (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl t STt AE ta)) (proj1_sig AE)
    /\  forall n Zs r (ST : subTerm (snd Zs) sT),
      get F n Zs ->
      get sa n r ->
      fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs) ST AE r)) ≣ AE.
Proof.
  general induction Len1; simpl in *; eauto.
  - split; isabsurd. etransitivity; eauto.
  - destruct ra; simpl in *; isabsurd.
    revert Disj2 Disj3 Disj5. norm_lunion. intros Disj2 Disj3 Disj5.
    edestruct (IHLen1 t ZL); eauto using get. omega.
    hnf; intros z.
    exploit (@cp_forward_agree sT ZL AE (singleton z) t STt tra ZLIncl); eauto; dcr.
    exploit (@cp_forward_agree sT ZL AE' (singleton z) (snd x) (STF 0 x (getLB XL x)) a ZLIncl); eauto using get; dcr.
    exploit (cp_forwardF_agree sT BL (singleton z) XL ra YL ZL ZLIncl);
      eauto using get; dcr.
    eauto with len.
    intros. inv_get.
    eapply cp_forward_agree; eauto using get.
    instantiate (3:=(fst (fst (forward (@cp_trans_dep)
                                       (@cp_trans_reach) ZL (snd x) AE' y)))) in H4.
    instantiate (1:=(fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                     STF (S n) s (getLS x H))) in H4.
    unfold domenv in *.
    decide (z ∈ snd (getAnn tra) ∪ list_union (of_list ⊝ ZL)).
    + eapply disj_union_inv in i. destruct i; dcr.
      * rewrite EQ.
        eapply H2.
        revert H6 H7 Disj2. clear.
        intros. cset_tac.
      * eapply poLe_antisymmetric.
        -- rewrite EQ.
           eapply H3.
           revert H6 Disj3; clear_all. intros. cset_tac.
        --etransitivity; [| eapply H1].
          rewrite <- EQM.
          eapply H5.
          revert H6 Disj3. clear_all; intros.
          cset_tac.
          revert H7; clear_all; cset_tac.
      * eapply disj_2_incl; try eapply Disj1; eauto.
    + decide (z ∈ (list_union (defVars ⊜ XL ra))).
      * clear H5 H4.
        rewrite EQ. eapply H2.
        eapply (@defVars_drop_disj (x::XL) (a::ra) 0) in Disj6;
          eauto using get. simpl in *.
        unfold defVars in Disj6 at 1.
        rewrite list_union_defVars_decomp in *; eauto.
        revert n i Disj5 Disj6. clear_all.
        intros. cset_tac.
      * exploit (H0 z). revert n; clear_all; cset_tac.
        rewrite <- H.
        rewrite <- EQM. symmetry. eapply H4.
        revert n n0; clear_all; cset_tac.
    + eapply disj_2_incl; eauto.
    + eapply disj_2_incl. eapply Disj3. clear_all; cset_tac.
    + eapply disj_incl. eapply Disj5.
      clear_all; cset_tac.
      clear_all; cset_tac.
    + hnf; intros. eapply Disj6; [|eauto using get|eauto using get]. omega.
    + intros; split; eauto.
      intros. inv H1; inv H2; eauto using get.
      assert (AEQ:AE === AE').
      { hnf; intros.
        rewrite <- EQ. rewrite H. reflexivity.
      }
      assert (EQF:forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) XL YL
                       (fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs) (STF 0 Zs (@getLB (params * stmt) XL Zs)) AE' r)))
                       (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                          STF (S n) s (getLS Zs H)) ===
                       forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) XL YL
                       (fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs) ST AE r)))
                       (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                          STF (S n) s (getLS Zs H))
             ). {
        eapply forwardF_ext; eauto.
        intros. eapply forward_ext; eauto.
        intros. eapply transf_ext; eauto.
        eapply cp_trans_reach_ext; eauto.
        assert ((STF 0 Zs (@getLB (params * stmt) XL Zs)) = ST) by eapply subTerm_PI.
        subst.
        eapply forward_ext; eauto.
        eapply transf_ext; eauto.
        eapply cp_trans_reach_ext; eauto.
        symmetry; eauto.
      }
       hnf; intros z.
    exploit (@cp_forward_agree sT ZL AE (singleton z) (snd Zs) ST a ZLIncl); eauto using get; dcr.
    exploit (cp_forwardF_agree sT BL (singleton z) XL ra YL ZL ZLIncl);
      eauto using get; dcr.
    eauto with len.
    intros. inv_get.
    eapply cp_forward_agree; eauto using get.
    unfold domenv in *.
    decide (z ∈ snd (getAnn tra) ∪ list_union (of_list ⊝ ZL)).
    * eapply disj_union_inv in i. destruct i; dcr.
      -- symmetry.
         eapply (H4 z).
         revert H8 H9 Disj2. clear.
         intros. cset_tac.
      -- eapply poLe_antisymmetric.
         ++ etransitivity.
           eapply H7.
           revert H8 Disj3; clear_all. intros. cset_tac.
           rewrite <- EQM.
           hnf in EQF. dcr.
           hnf in H3. dcr.
           specialize (H11 z).
           rewrite H11. reflexivity.
         ++ eapply H5.
           revert H8 H9 Disj3; clear_all. intros. cset_tac.
      -- eauto.
    * decide (z ∈ (list_union (defVars ⊜ XL ra))).
      -- symmetry.
         eapply H4.
         eapply (@defVars_drop_disj (Zs::XL) (a::ra) 0) in Disj6;
           eauto using get. simpl in *.
        unfold defVars in Disj6 at 1.
        rewrite list_union_defVars_decomp in Disj6; eauto.
        rewrite list_union_defVars_decomp in i; eauto.
        revert n i Disj5 Disj6. clear_all.
        intros. cset_tac.
      -- rewrite (H6 z).
         rewrite <- EQM.
         hnf in EQF. dcr.
         hnf in H3. dcr.
         specialize (H9 z).
         rewrite H9. reflexivity.
         revert n n0; clear_all; cset_tac.
Qed.


Lemma cp_forward_agree_def sT ZL AE G s (ST:subTerm s sT) ra ZLIncl anr pf
  (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach)
                                            ZL ZLIncl
                                            s ST (exist AE pf) anr))))).
Proof.
  edestruct cp_forward_agree with (AE:=exist AE pf); dcr; eauto.
Qed.


Ltac invtc ty :=
  match goal with
      | h: ty |- _ => invc h
      | h: ty _ |- _ => invc h
      | h: ty _ _ |- _ => invc h
      | h: ty _ _ _ |- _ => invc h
      | h: ty _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => invc h
  end.


Lemma ann_R_setTopAnn_right (A B : Type) (R : A -> B -> Prop) (b : B)
      (an : ann A) (bn : ann B)
  : R (getAnn an) b -> ann_R R an bn -> ann_R R an (setTopAnn bn b).
Proof.
  intros. inv H0; simpl; eauto using @ann_R.
Qed.

Lemma eqMap_domupd AE x v
  : find x AE === v
    -> eqMap AE (domupd AE x v).
Proof.
  intros. hnf; intros; unfold domupd; cases; mlud; eauto;
  rewrite <- e; eauto.
Qed.


Lemma funConstr_disj_Dt D Dt F ans (Len:❬F❭=❬ans❭)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj (list_union (of_list ⊝ fst ⊝ F)) Dt.
Proof.
  hnf; intros IW.
  hnf; intros x IN1 IN2.
  eapply list_union_get in IN1.
  destruct IN1; dcr; inv_get; [|cset_tac].
  edestruct IW; eauto; dcr.
  cset_tac.
Qed.

Lemma setTopAnn_eta' A (a:ann A)
  : (setTopAnn a (getAnn a)) = a.
Proof.
  destruct a; simpl; eauto.
Qed.

Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : ann_R _ (snd (fst (@forward ?sT ?Dom ?f ?fr ?ZL ?ZLIncl
                                            ?s ?ST ?a ?sa))) ?sa' |- _ ] =>
           let X := fresh "HEQ" in
           match goal with
           | [ H' : getAnn sa = getAnn sa' |- _ ] => fail 1
           | _ => exploit (@forward_getAnn sT Dom f fr ZL ZLIncl s ST a sa sa' H) as X;
                 subst
           end
         end; subst; try eassumption;
  try rewrite getAnn_setTopAnn in *;
  repeat rewrite setTopAnn_eta' in *.

Lemma PIR2_ann_R_get X Y (R:X->Y->Prop) A B
  : PIR2 (ann_R R) A B
    -> PIR2 R (getAnn ⊝ A) (getAnn ⊝ B).
Proof.
  intros. general induction H; simpl; eauto using PIR2.
  econstructor; eauto.
  eapply ann_R_get in pf; eauto.
Qed.
Lemma PIR2_eq X (A:list X) (B:list X)
  : PIR2 eq A B
    -> A = B.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma getAnn_setTopAnn_zip X A (B:list X)
  : getAnn ⊝ (@setTopAnn _ ⊜ A B) = Take.take (min ❬A❭ ❬B❭) B.
Proof.
  general induction A; destruct B; isabsurd; simpl in *; eauto.
  rewrite getAnn_setTopAnn; f_equal; eauto.
Qed.

Lemma PIR2_R_eq X Y (R:X->Y->Prop) A B B'
  : PIR2 eq B' B
    -> PIR2 R A B'
    -> PIR2 R A B.
Proof.
  intros P1 P2; general induction P1; inv P2; econstructor; eauto.
Qed.

Lemma funConstr_disj_ZL_getAnn ZL (D Dt : ⦃nat⦄)  (F : 〔params * stmt〕)
      (ans : 〔ann (⦃nat⦄ * ⦃nat⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans)
    -> disj (list_union (of_list ⊝ ZL)) (list_union (defVars ⊜ F ans) ∪ Dt)
    -> (forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> ❬F❭ = ❬ans❭
    -> disj (list_union (of_list ⊝ (fst ⊝ F ++ ZL))) (list_union (snd ⊝ getAnn ⊝ ans)).
Proof.
  intros. rewrite List.map_app, list_union_app.
  rewrite list_union_defVars_decomp in *; eauto.
  eapply disj_union_left; symmetry.
  - hnf; intros.
    eapply list_union_get in H4. destruct H4; dcr; [|cset_tac].
    eapply list_union_get in H5. destruct H5; dcr; [|cset_tac].
    decide (x0=x2).
    + subst. inv_get. edestruct H; eauto; dcr.
      exploit H2; eauto. eapply renamedApart_disj in H9.
      rewrite H8 in *. eapply H9; eauto. cset_tac.
    + inv_get. exploit H0; eauto using zip_get.
      eapply (H10 x); unfold defVars. cset_tac. cset_tac.
  - eapply disj_2_incl; eauto. cset_tac.
Qed.

Lemma funConstr_disj_Dt' ZL (D Dt : ⦃nat⦄)  (F : 〔params * stmt〕)
      (ans : 〔ann (⦃nat⦄ * ⦃nat⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj (list_union (of_list ⊝ ZL)) (list_union (defVars ⊜ F ans) ∪ Dt)
    -> ❬F❭ = ❬ans❭
    -> disj Dt (list_union (of_list ⊝ (fst ⊝ F ++ ZL))).
Proof.
  intros. rewrite List.map_app, list_union_app.
  eapply disj_union_right; symmetry.
  - eauto using funConstr_disj_Dt.
  - eapply disj_2_incl; eauto.
Qed.

Lemma disj_Dt_getAnn (D Dt : ⦃nat⦄) (F : 〔params * stmt〕) (ans : 〔ann (⦃nat⦄ * ⦃nat⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> ❬F❭ = ❬ans❭
    -> disj Dt (list_union (snd ⊝ getAnn ⊝ ans)).
Proof.
  intros. hnf; intros.
  eapply list_union_get in H2.
  destruct H2. dcr; inv_get.
  - edestruct H; eauto; dcr.
    eapply H10; eauto. cset_tac.
  - cset_tac.
Qed.

Lemma PIR2_R_impl X Y (R R':X -> Y -> Prop) (L:list X) (L':list Y)
  : (forall x y, R x y -> R' x y) -> PIR2 R L L' -> PIR2 R' L L'.
Proof.
  intros EQ P.
  general induction P; eauto using @PIR2.
Qed.

Lemma PIR2_setTopAnn_zip_left X (R:X->X->Prop) `{Reflexive _ R} (A:list (ann X)) B
  : PIR2 R (Take.take ❬A❭ B) (getAnn ⊝ A)
    -> PIR2 (ann_R R) (@setTopAnn _ ⊜ A B) A.
Proof.
  intros P. general induction P; destruct A, B; isabsurd; eauto using PIR2.
  simpl in *. clear_trivial_eqs.
  econstructor; eauto.
  eapply ann_R_setTopAnn_left; eauto.
Qed.

Lemma PIR2_joinTopAnn_zip_left X `{JoinSemiLattice X} (A:list (ann X)) B
  : PIR2 poLe (Take.take ❬A❭ B) (getAnn ⊝ A)
    -> PIR2 poEq (@joinTopAnn _ _ _ ⊜ A B) A.
Proof.
  intros P. general induction P; destruct A,B; isabsurd; eauto using PIR2.
  simpl in *. clear_trivial_eqs.
  econstructor; eauto.
  eapply ann_R_setTopAnn_left; eauto.
  eapply poLe_antisymmetric. rewrite pf.
  rewrite join_idempotent. eauto.
  eapply join_poLe.
Qed.

Lemma take_ge A (L:list A) n
  : ❬L❭ <= n -> Take.take n L = L.
Proof.
  general induction L; destruct n; isabsurd; simpl; eauto.
  f_equal; eauto. eapply IHL. simpl in *. omega.
Qed.

Lemma snd_forwarF_inv sT BL ZL ZLIncl F sa AE STF
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (forwardF BL (@forward sT _ (@cp_trans_dep)
                                                             (@cp_trans_reach) ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (@forward _ _ (@cp_trans_dep)
                                                   (@cp_trans_reach) ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
  : PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa.
Proof.
  eapply PIR2_ann_R_get in P1.
  rewrite getAnn_setTopAnn_zip in P1.
  pose proof (PIR2_joinTopAnn_zip_left bool sa BL).
  eapply H; clear H.
  etransitivity.
  eapply PIR2_take.
  eapply (@forwardF_mon sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl BL ltac:(omega) F (joinTopAnn (A:=bool) ⊜ sa BL) AE STF).
  etransitivity. Focus 2.
  eapply PIR2_R_impl; try eapply P1; eauto.
  assert (❬sa❭ = (Init.Nat.min
          ❬snd
             (fst
                (forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                   (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
          ❬snd
             (forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                       AE STF)❭)). {
    clear P1.
    rewrite forwardF_length.
    erewrite forwardF_snd_length; try reflexivity.
    + repeat rewrite min_l; eauto; len_simpl;
        rewrite Len1; rewrite min_l; omega.
    + intros; len_simpl; eauto.
  }
  rewrite H. reflexivity.
Qed.

Lemma snd_forwarF_inv' sT BL ZL ZLIncl F sa AE STF
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (forwardF BL (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
  : PIR2 (ann_R eq)
              (snd (fst (forwardF BL (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa.
Proof.
  assert (P2:PIR2 poLe (Take.take ❬sa❭
                               (snd (forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                              (joinTopAnn (A:=bool) ⊜ sa BL) AE
                                              STF))) (getAnn ⊝ sa)). {
    eapply PIR2_ann_R_get in P1.
    rewrite getAnn_setTopAnn_zip in P1.
     etransitivity. Focus 2.
    eapply PIR2_R_impl; try eapply P1; eauto.
    assert (❬sa❭ = (Init.Nat.min
                      ❬snd
                         (fst
                            (forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                      (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
                      ❬snd
                         (forwardF BL (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                                   AE STF)❭)). {
      clear P1.
      rewrite forwardF_length.
      erewrite forwardF_snd_length; try reflexivity.
      + repeat rewrite min_l; eauto; len_simpl;
          rewrite Len1; rewrite min_l; omega.
      + intros; len_simpl; eauto.
    }
    rewrite H. reflexivity.
  }
  assert (PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa). {
    pose proof (PIR2_joinTopAnn_zip_left bool sa BL).
    eapply H; clear H.
    etransitivity.
    eapply PIR2_take.
    eapply (@forwardF_mon sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl BL ltac:(omega) F (joinTopAnn (A:=bool) ⊜ sa BL) AE STF). eauto.
  }
  etransitivity; try eapply P1.
  symmetry.
  eapply (PIR2_setTopAnn_zip_left bool); eauto.
  rewrite <- forwardF_mon';[|len_simpl; rewrite min_l; eauto; omega].
  - len_simpl. rewrite min_r, min_l; eauto; try rewrite Len1; try rewrite min_l; try omega.
    eapply PIR2_ann_R_get in H.
    rewrite H.
    eapply PIR2_ann_R_get in P1.
    etransitivity; try eapply P1.
    eapply PIR2_get; intros; inv_get.
    rewrite getAnn_setTopAnn; eauto.
    len_simpl;[| | reflexivity].
    rewrite min_r; try omega.
    repeat rewrite min_l; try omega.
    intros; eauto with len.
Qed.



Lemma snd_forwarF_inv_get sT BL ZL ZLIncl F sa AE STF
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
      (P1:PIR2 (ann_R eq)
              (snd (fst (forwardF BL (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl) F
                                  (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (P2:PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa)
      n r Zs (Getsa:get sa n r)
      (GetF:get F n Zs) STZs
      (EQ: forall n Zs r ST, get F n Zs -> get sa n r ->
                        poEq (fst (fst (@forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs) ST AE r))) AE)

  : ann_R eq (snd (fst (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl (snd Zs) STZs AE r))) r.
Proof.
  rewrite forwardF_ext in P1; try eapply P2; try reflexivity.
  Focus 2. intros. eapply forward_ext; eauto.
  eapply transf_ext; eauto. eapply cp_trans_reach_ext.
  clear Len3 P2.
  general induction Len1; simpl in *.
  destruct BL; isabsurd; simpl in *. inv Getsa; inv GetF.
  - inv P1.
    assert((STF 0 Zs (@getLB (params * stmt) XL Zs)) = STZs).
    eapply subTerm_PI. rewrite <- H.
    eapply pf.
  - inv P1.
    eapply IHLen1; eauto using get.
    Focus 2.
    rewrite forwardF_ext; eauto.
    intros. eapply forward_ext; eauto. eapply transf_ext; eauto.
    eapply cp_trans_reach_ext; eauto.
    symmetry. eapply EQ; eauto using get. reflexivity. simpl. omega.
Qed.


Definition cp_sound sT AE AE' AV ZL s (ST:subTerm s sT) ZLIncl ra anr
  : let X := @forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s ST AE anr in
    renamedApart s ra
    -> annotation s anr
    -> labelsDefined s (length ZL)
    -> poEq (fst X) (AE,anr)
    -> poEq AE' AE
    -> disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra))
    -> ❬ZL❭ = ❬AV❭
    -> paramsMatch s (length ⊝ ZL)
    -> PIR2 eq AV (List.map (fun Z => lookup_list (domenv (proj1_sig AE')) Z) ZL)
    -> (forall n Z, get ZL n Z -> NoDupA eq Z)
    -> cp_sound (domenv (proj1_sig AE')) (zip pair ZL AV) s anr.
Proof.
  intros LET RA ANN LD EQ1 EQ2 DISJ LEN PM AVREL NODUP. subst LET.
  general induction LD; invt @renamedApart;
    try invt @annotation; simpl in *; simpl; invt @paramsMatch;
      simpl in *; dcr;
        repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst;
          simpl in *; try invtc @ann_R; subst.
  - destruct e; simpl in *; simpl in *; clear_trivial_eqs.
    + assert (EVALEQ:op_eval (domenv (proj1_sig AE')) e = domenv (proj1_sig AE) x). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=(domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e)))
          in AGR.
        instantiate (2:=(cp_trans_domain ZL (stmtLet x (Operation e) s) AE a)) in AGR.
        exploit (AGR x). pe_rewrite. instantiate (2:={x; Ds}).
        eapply renamedApart_disj in H4. pe_rewrite.
        revert H4 DISJ; clear_all. cset_tac.
        exploit (H x).
        eapply option_R_inv in H0.
        eapply option_R_inv in H1. unfold domenv in H0.
        unfold domenv. rewrite <- H1.
        unfold domenv.
        rewrite <- H0.
        rewrite domupd_eq; eauto.
        exploit  eqMap_op_eval. eapply EQ2.
        eapply option_R_inv in H5. eauto.
      }
      assert (MAPEQ:eqMap (proj1_sig AE')
                          (domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e))). {
        rewrite EQ2.
        eapply eqMap_domupd.
        unfold domenv in EVALEQ.
        rewrite <- EVALEQ.
        rewrite <- eqMap_op_eval; [|eapply EQ2].
        reflexivity.
      }
      simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
      econstructor; eauto.
      eapply IHLD with (AE:=(exist (domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e))
                      (cp_trans_domain ZL (stmtLet x (Operation e) s) AE (getAnn sa)))); eauto.
      * split; eauto.
        -- simpl.
           etransitivity; eauto.
           etransitivity; eauto.
           symmetry; eauto.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
      * intros; simpl; eauto.
        rewrite EVALEQ.
        exploit (EQ2 x). eapply option_R_inv in H1.
        unfold domenv. congruence.
    + assert (find x (proj1_sig AE') = ⎣ Top ⎦). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=add x Top (proj1_sig AE)) in AGR.
        instantiate (2:=cp_trans_domain ZL (stmtLet x (Call f Y) s) AE a) in AGR.
        exploit (AGR x). pe_rewrite. instantiate (2:={x; Ds}).
        eapply renamedApart_disj in H4. pe_rewrite.
        revert H4 DISJ; clear_all. cset_tac.
        exploit (H x).
        eapply option_R_inv in H0.
        eapply option_R_inv in H1. unfold domenv in H0.
        exploit (EQ2 x).
        eapply option_R_inv in H5. rewrite H5.
        rewrite <- H1. rewrite <- H0.
        mlud; eauto. exfalso; eauto.
      }
      assert (eqMap (proj1_sig AE') (add x Top (proj1_sig AE))). {
        hnf; intros. mlud; eauto. rewrite <- e.
        rewrite <- H0. reflexivity.
      }
      simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
      econstructor; eauto.
      eapply IHLD with (AE:=(exist (add x Top (proj1_sig AE))
                     (cp_trans_domain ZL (stmtLet x (Call f Y) s) AE (getAnn sa)))); eauto.
      * split; eauto; simpl.
        etransitivity; eauto.
        etransitivity; eauto.
        symmetry; eauto.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
  - assert (MEQ: eqMap (proj1_sig AE')
    (getAE (@forward sT DDom (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s (subTerm_EQ_If1 eq_refl ST)
              (exist (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a))
              (setTopAnn sa
                 (if [op_eval (domenv (proj1_sig AE)) e = ⎣⎦] then false else if [
                  op_eval (domenv (proj1_sig AE)) e = ⎣ wTA val_false ⎦] then false else a))))). {
        hnf; intros.
        edestruct (@cp_forward_agree sT ZL (fst
                     (fst
                        (@forward sT DDom (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s
                                  (subTerm_EQ_If1 eq_refl ST)
                           (exist (proj1_sig AE)
                              (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a))
                           (setTopAnn sa
                              (if [op_eval (domenv (proj1_sig AE)) e = ⎣⎦] then false else if [
                               op_eval (domenv (proj1_sig AE)) e =
                               ⎣ wTA val_false ⎦] then false else a)))))). eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (4:=singleton x) in H1. pe_rewrite.
        decide (x ∈ (Dt ∪ list_union (of_list ⊝ ZL))).
        -- edestruct (@cp_forward_agree sT ZL (exist (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)) (singleton x) s). eauto.
           eapply setTopAnn_annotation; eauto.
           pe_rewrite.
           assert ((x ∈ Dt /\ x ∉ list_union (of_list ⊝ ZL))
                   \/ (x ∈ list_union (of_list ⊝ ZL) /\ x ∉ Dt /\ x ∉ Ds)). {
             revert i DISJ H4.
             clear_all; cset_tac.
           } destruct H15; dcr.
           ++ exploit (H7 x).
             revert H17 H18 H3 i; clear_all. cset_tac.
             unfold domenv in H15.
             etransitivity; eauto.
           ++ etransitivity; eauto.
             eapply poLe_antisymmetric.
             eapply H14. revert H22; clear_all; cset_tac.
             etransitivity.
             eapply H1. revert H21; clear_all; cset_tac.
             exploit (H x).
             rewrite <- H15. unfold domenv. reflexivity.
        -- exploit (H0 x). revert n; clear_all. cset_tac.
           rewrite H7.
           etransitivity. eapply EQ2.
           symmetry. exploit (H x).
           rewrite <- H14.
           unfold domenv. reflexivity.
    }
    simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
    symmetry in HEQ. symmetry in HEQ0.
    rewrite <- (setTopAnn_eta _ HEQ0).
    rewrite <- (setTopAnn_eta _ HEQ).
    econstructor; eauto.
    + eapply IHLD1.
      * eauto.
      * eauto using setTopAnn_annotation.
      * eauto.
      * split.
        -- etransitivity.
           symmetry.
           eapply MEQ. simpl. eauto.
        -- eapply ann_R_setTopAnn_right; eauto.
           ++ rewrite forward_fst_snd_getAnn.
             rewrite getAnn_setTopAnn; eauto.
      * simpl. eauto.
      * pe_rewrite. clear MEQ. set_simpl.
        eapply disj_incl. eapply DISJ.
        eauto. eauto with cset.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
    + eapply IHLD2; eauto.
      * eapply setTopAnn_annotation. eauto.
      * split.
        -- etransitivity; eauto.
           etransitivity; eauto.
           symmetry; eauto.
        -- etransitivity; eauto.
           eapply ann_R_setTopAnn_right; eauto.
      * clear MEQ.
        pe_rewrite. set_simpl.
        eapply disj_incl. eapply DISJ.
        reflexivity. eauto with cset.
  - econstructor.
  - clear_trivial_eqs. set_simpl.
    edestruct get_in_range; eauto.
    erewrite get_nth in *; eauto.
    inv_get.
    edestruct PIR2_nth; eauto using map_get_1, ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; eauto using zip_get; intros.
    + PIR2_inv; clear_trivial_eqs; inv_get.
      eapply PIR2_get.
      * rewrite lookup_list_map.
        intros; inv_get.
        exploit (H0 x1) as EQA. unfold domenv.
        exploit (EQ2 x1) as EQB. rewrite <- EQA in EQB.
        rewrite EQB.
        cases.
        exploit domupd_list_get; [|eapply H6| eapply map_get_1; try eapply H5|].
        -- exploit NODUP; eauto.
        -- etransitivity;[| eapply H7].
           exploit eqMap_op_eval; try eapply EQ2.
           eapply option_R_inv in H8.
           unfold domenv in H8.
           rewrite H8. reflexivity.
      * rewrite map_length. rewrite lookup_list_length; eauto.
  -
    assert (ZipEq:((fun Zs0 : params * stmt => (fst Zs0, lookup_list (domenv (proj1_sig AE')) (fst Zs0))) ⊝ F ++ pair ⊜ ZL AV) = (zip pair (fst ⊝ F ++ ZL) ((fun Zs => lookup_list (domenv (proj1_sig AE')) (fst Zs)) ⊝ F ++ AV))). {
      clear_all. general induction F; simpl; eauto.
      f_equal. eapply IHF.
    }
    simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
    assert (joinTopAnn (A:=bool) ⊜ sa (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t (subTerm_EQ_Fun1 eq_refl ST) AE ta)) = sa). {
      eapply PIR2_eq.
      eapply PIR2_R_impl. intros.
      eapply ann_R_eq. eapply H2.
      eapply snd_forwarF_inv; eauto.
      clear. eauto with len.
      rewrite forward_length. reflexivity.
      eapply PIR2_get in H23; eauto.
    }
    exploit eqMap_forwardF_t; eauto.
    clear. len_simpl. omega.
    reflexivity. pe_rewrite. set_simpl.
    eapply funConstr_disj_Dt'; eauto.
    pe_rewrite.
    rewrite list_union_defVars_decomp in *; eauto. set_simpl.
    eapply disj_Dt_getAnn; eauto.
    set_simpl.
    eapply funConstr_disj_ZL_getAnn; eauto.
    set_simpl.
    eapply disj_1_incl.
    eapply funConstr_disj_ZL_getAnn; eauto.
    rewrite List.map_app. rewrite list_union_app.
    clear_all. cset_tac.
    revert H9. clear_all. len_simpl. intros. rewrite H9. eauto with len.
    intros. inv_get. eapply setTopAnn_annotation. eauto.
    econstructor; eauto.
    + intros; inv_get.
      setoid_rewrite ZipEq.
      pose proof H16 as GET.
      assert (FWDP:forall STZs, PIR2 impb (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) (snd Zs) STZs AE r))
                                (snd
                                   (forwardF (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t ((subTerm_EQ_Fun1 eq_refl ST)) AE ta))
                                             (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) F
                                             (joinTopAnn (A:=bool) ⊜ sa
                                                         (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t ((subTerm_EQ_Fun1 eq_refl ST)) AE ta)))
                                             AE
                                             (subTerm_EQ_Fun2 eq_refl ST)))). {
        intros.
        eapply forwardF_PIR2.
        +++ revert H9. clear_all; intros; len_simpl.
           rewrite H9. eauto with len.
        +++ clear_all. eauto with len.
        +++ intros.
           inv_get.
           destruct H14.
           eapply H26; eauto.
           eapply zip_get; eauto.
        +++ eapply transf_ext.
        +++ eapply cp_trans_reach_ext.
        +++ rewrite H2. eauto.
        +++ eauto.
      }
      eapply H0;
        eauto.
      * clear_all; eauto with len.
      * split.
        -- eapply H14; eauto.
           rewrite H2; eauto.
        -- eapply PIR2_get in H23; eauto.
           exploit snd_forwarF_inv; eauto.
           clear; eauto with len.
           clear; eauto with len.
           exploit snd_forwarF_inv'; eauto.
           clear; eauto with len.
           clear; eauto with len.
           destruct H14.
           rewrite (@forwardF_ext sT DDom _
                                  (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (@ZLIncl_ext sT (stmtFun F t) F t ZL (@eq_refl stmt (stmtFun F t)) ST
                                                                                            ZLIncl)) (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (@ZLIncl_ext sT (stmtFun F t) F t ZL (@eq_refl stmt (stmtFun F t)) ST
                   ZLIncl))) in H20;
             try eapply e; intros; try reflexivity.
           eapply snd_forwarF_inv_get; try eapply H20; eauto.
           clear; eauto with len.
           clear; eauto with len.
           intros.
           eapply PIR2_nth_2 in H19; eauto; dcr.
           intros. eapply p; eauto.
           rewrite ann_R_eq in H27. subst. eauto.
           eapply forward_ext; eauto.
           eapply transf_ext; eauto.
           eapply cp_trans_reach_ext; eauto.
      * set_simpl. eauto.
        eapply disj_2_incl.
        eapply funConstr_disj_ZL_getAnn; eauto.
        eapply incl_list_union; eauto using zip_get.
      * revert LEN; clear_all; eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        clear_all.
        eauto with len.
      * intros ? ? GET2. eapply get_app_cases in GET2. destruct GET2.
        inv_get. edestruct H5; eauto.
        dcr. inv_get. eapply NODUP; eauto.
    + setoid_rewrite ZipEq.
      eapply IHLD; eauto.
      * clear; eauto with len.
      * split; dcr. eauto. eauto.
      * pe_rewrite. set_simpl.
        rewrite List.map_app. rewrite list_union_app.
        eapply disj_union_left.
        -- symmetry.
           eapply funConstr_disj_Dt; eauto.
        -- symmetry. eapply disj_incl; eauto.
      * revert LEN. clear; eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        clear.
        eauto with len.
      * intros ? ? GET. eapply get_app_cases in GET. destruct GET.
        inv_get. edestruct H5; eauto.
        dcr. inv_get. eapply NODUP; eauto.
        Grab Existential Variables.
        eapply subTerm_EQ_Fun2; eauto.
Qed.