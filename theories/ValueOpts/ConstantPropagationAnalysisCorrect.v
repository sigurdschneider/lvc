Require Import Util SizeInduction Get MapDefined Coq.Classes.RelationClasses.
Require Import IL Var Val OptionR AllInRel.
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

Lemma cp_forwardF_agree (sT:stmt) BL G (F:list (params * stmt)) ans anF ZL ZL'
      (ZLIncl: list_union (of_list ⊝ ZL) [<=] occurVars sT)
      (ZL'Incl: list_union (of_list ⊝ ZL') [<=] occurVars sT)
      (Len1: ❬F❭ = ❬ans❭) (Len2:❬F❭ = ❬anF❭)
      (AN:forall (n : nat) (Zs : params * stmt) sa,
          get anF n sa -> get F n Zs -> annotation (snd Zs) sa)
      AE
      (ST: forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT) Dt
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
                                (@forward sT _ (@cp_trans_dep) ZL ZLIncl (snd Zs)
                                          ST AE anr))) /\
            agree_on (fstNoneOrR (withTop_le (R:=int_eq))) (G \ snd (getAnn a))
                     (domenv (proj1_sig AE))
                     (domenv (getAE
                                (@forward sT _ (@cp_trans_dep) ZL ZLIncl (snd Zs)
                                          ST AE anr))))
  : agree_on (option_R (withTop_eq (R:=int_eq)))
             (G \ (list_union (defVars ⊜ F ans) ∪ Dt ∪ list_union (of_list ⊝ ZL')))
             (domenv (proj1_sig AE))
             (domenv (getAE (forwardF BL (@forward sT _ (@cp_trans_dep) _ ZL'Incl)
                                      F anF AE ST))) /\
    agree_on (fstNoneOrR (withTop_le (R:=int_eq)))
             (G \ (list_union (defVars ⊜ F ans) ∪ Dt))
             (domenv (proj1_sig AE))
             (domenv (getAE (forwardF BL (@forward sT _ (@cp_trans_dep) _ ZL'Incl)
                                      F anF AE ST))).
Proof.
  general induction Len1; destruct anF; inv Len2. simpl.
  - split; reflexivity.
  - edestruct (IHLen1 sT BL G anF ZL);
      edestruct (IH 0 x y ltac:(eauto using get) ltac:(eauto using get) sT ZL' AE G ltac:(eauto using get) ZL'Incl a); eauto using get.
    simpl; split; etransitivity; eapply agree_on_incl; eauto.
    + norm_lunion. clear_all. unfold defVars at 1. cset_tac.
    + norm_lunion. clear_all. cset_tac.
    + norm_lunion. clear_all. unfold defVars at 1. cset_tac.
    + norm_lunion. clear_all. cset_tac.
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

Lemma subTermF_occurVars F t sT
  : subTerm (stmtFun F t) sT
    -> list_union (of_list ⊝ fst ⊝ F) ⊆ occurVars sT.
Proof.
  intros. general induction H; simpl.
  - eapply list_union_incl; intros; eauto with cset.
    inv_get.
    rewrite <- incl_list_union; eauto using map_get_1.
    cset_tac. cset_tac.
  - rewrite IHsubTerm; eauto. cset_tac.
  - rewrite IHsubTerm; eauto. cset_tac.
  - rewrite IHsubTerm; eauto. cset_tac.
  - rewrite IHsubTerm; eauto.
  - rewrite IHsubTerm; eauto.
    rewrite <- incl_list_union; eauto using map_get_1.
    instantiate (1:=occurVars (snd Zs)). cset_tac. cset_tac.
Qed.

Lemma domupd_list_agree (R:relation aval) `{Reflexive _ R} G AE Z Y
  : agree_on R (G \ of_list Z)
             (domenv AE)
             (domenv (domupd_list AE Z Y)).
Proof.
  general induction Z; destruct Y; simpl; try reflexivity.
  hnf; intros. cset_tac'.
  admit.
Admitted.


Lemma cp_forward_agree sT ZL (AE:DDom sT) G s (ST:subTerm s sT) ra ZLIncl anr
      (RA:renamedApart s ra) (AN:annotation s anr)
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
        eapply cp_forwardF_agree with (ZL:=fst ⊝ F ++ ZL) (ZL':=fst ⊝ F ++ ZL); eauto.
        -- rewrite List.map_app.
           rewrite list_union_app; eauto.
           rewrite subTermF_occurVars; eauto with len. rewrite ZLIncl. clear; cset_tac.
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
        eapply cp_forwardF_agree with (ZL:=fst ⊝ F ++ ZL) (ZL':=fst ⊝ F ++ ZL);
          intros; eauto.
        -- rewrite List.map_app.
           rewrite list_union_app; eauto.
           rewrite subTermF_occurVars; eauto with len. rewrite ZLIncl. clear; cset_tac.
        -- len_simpl. rewrite H8. eauto with len.
        -- inv_get. eapply setTopAnn_annotation; eauto.
        -- clear_all; cset_tac.
Qed.



Lemma cp_forward_agree_def sT ZL AE G s (ST:subTerm s sT) ra ZLIncl anr pf
  (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig
                        (fst (fst (@forward _ _ (@cp_trans_dep) ZL ZLIncl
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


Lemma eqMap_op_eval e a b
  : eqMap a b
    -> poEq (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_eq, @option_R.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H); repeat cases; eauto using fstNoneOrR, @withTop_eq, @option_R.
    reflexivity.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_eq, option_R.
    + econstructor; econstructor. congruence.
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


Definition cp_sound sT AE AE' RCH DIncl AV ZL s (ST:subTerm s sT) ZLIncl ra anr
  : let X := @forward sT _ (@cp_trans_dep) ZL ZLIncl s ST (@exist _ _ AE DIncl) anr in
    renamedApart s ra
    -> annotation s anr
    -> labelsDefined s (length ZL)
    -> poEq (fst X) ((@exist _ _ AE DIncl),anr)
    -> poEq AE' AE
    -> (getAnn anr -> defined_on (fst (getAnn ra)) (domenv AE'))
    -> disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra))
    -> ❬ZL❭ = ❬AV❭
    -> paramsMatch s (length ⊝ ZL)
    -> PIR2 eq AV (List.map (fun Z => lookup_list (domenv AE') Z) ZL)
    -> PIR2 poLe (snd X) RCH
    -> cp_sound (domenv AE') (zip pair ZL AV) RCH s (snd (fst X)).
Proof.
  intros LET RA ANN LD EQ1 EQ2 RCHDEF DISJ LEN PM AVREL RCHREL. subst LET.
  general induction LD; invt @renamedApart;
    try invt @annotation; simpl in *; simpl; invt @paramsMatch;
      simpl in *; dcr;
        repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst;
          simpl in *; try invtc @ann_R; subst.
  - destruct e; simpl in *; simpl in *; clear_trivial_eqs.
    + assert (EVALEQ:op_eval (domenv AE') e = domenv AE x). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=(domupd AE x (op_eval (domenv AE) e))) in AGR.
        instantiate (2:=(cp_trans_domain ZL (stmtLet x (Operation e) s) (exist AE DIncl) a)) in AGR.
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
      assert (MAPEQ:eqMap AE' (domupd AE x (op_eval (domenv AE) e))). {
        rewrite EQ2.
        eapply eqMap_domupd.
        unfold domenv in EVALEQ.
        rewrite <- EVALEQ.
        rewrite <- eqMap_op_eval; [|eapply EQ2].
        reflexivity.
      }
      econstructor; eauto.
      eapply IHLD; eauto using setTopAnn_annotation.
      * split; eauto.
        rewrite H. rewrite <- EQ2 at 1. eauto.
        eapply ann_R_setTopAnn_right; eauto.
        rewrite forward_fst_snd_getAnn.
        rewrite getAnn_setTopAnn; eauto.
      * pe_rewrite.
        rewrite getAnn_setTopAnn; eauto; intros.
        admit.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
      * intros; simpl; eauto.
        rewrite EVALEQ.
        exploit (EQ2 x). eapply option_R_inv in H1.
        unfold domenv. congruence.
      * intros.
        rewrite forward_fst_snd_getAnn.
        rewrite getAnn_setTopAnn; eauto.
    + assert (find x AE' = ⎣ Top ⎦). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=add x Top AE) in AGR.
        instantiate (2:=cp_trans_domain ZL (stmtLet x (Call f Y) s) (exist AE DIncl) a) in AGR.
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
      assert (eqMap AE' (add x Top AE)). {
        hnf; intros. mlud; eauto. rewrite <- e.
        rewrite <- H0. reflexivity.
      }
      econstructor; eauto.
      eapply IHLD; eauto using setTopAnn_annotation.
      * split; eauto.
        rewrite H. rewrite <- EQ2 at 1. eauto.
        eapply ann_R_setTopAnn_right; eauto.
        rewrite forward_fst_snd_getAnn.
        rewrite getAnn_setTopAnn; eauto.
      * pe_rewrite.
        rewrite getAnn_setTopAnn.
        admit.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
      * intros.
        rewrite forward_fst_snd_getAnn.
        rewrite getAnn_setTopAnn; eauto.
  - econstructor; eauto.
    + eapply IHLD1; eauto.
      * eapply setTopAnn_annotation; eauto.
      * split.
        -- admit.
        -- eapply ann_R_setTopAnn_right; eauto.
           ++ rewrite forward_fst_snd_getAnn.
             rewrite getAnn_setTopAnn; eauto.
      * rewrite getAnn_setTopAnn; simpl; intros.
        pe_rewrite. repeat cases in H0; eauto.
      * pe_rewrite. set_simpl.
        eapply disj_incl. eapply DISJ.
        eauto. eauto with cset.
      * etransitivity; eauto.
        eapply Analysis.PIR2_impb_orb_right.
        eauto with len. reflexivity.
    + admit.
    + intros.
      rewrite forward_fst_snd_getAnn.
      rewrite getAnn_setTopAnn; eauto.
      repeat cases; eauto.
      * admit.
      * eapply H1.
        exploit eqMap_op_eval; try eapply EQ2.
        eapply option_R_inv in H7. rewrite H7.
        rewrite COND. reflexivity.
    + intros.
      rewrite forward_fst_snd_getAnn.
      rewrite getAnn_setTopAnn; eauto.
      repeat cases; eauto.
      * admit.
      * eapply H1.
        exploit eqMap_op_eval; try eapply EQ2.
        eapply option_R_inv in H7. rewrite H7.
        rewrite COND. reflexivity.
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
        exploit (H0 x2) as EQA. unfold domenv.
        exploit (EQ2 x2) as EQB. rewrite <- EQA in EQB.
        rewrite EQB.
        cases.
        exploit domupd_list_get; [|eapply H8| eapply map_get_1; eapply H7|].
        -- admit.
        --

      * rewrite map_length. rewrite lookup_list_length; eauto.
    + destruct a, x1; isabsurd; eauto.
  -
    assert (ZipEq:((fun Zs0 : params * stmt => (fst Zs0, lookup_list (domenv AE') (fst Zs0))) ⊝ F ++ pair ⊜ ZL AV) = (zip pair (fst ⊝ F ++ ZL) ((fun Zs => lookup_list (domenv AE') (fst Zs)) ⊝ F ++ AV))). {
      clear_all. general induction F; simpl; eauto.
      f_equal. eapply IHF.
    }

    econstructor.
    + eauto with len.
    + intros.
      rewrite forward_fst_snd_getAnn.
      rewrite getAnn_setTopAnn; eauto.
    + intros; inv_get.
      setoid_rewrite ZipEq.
      edestruct forwardF_get; eauto; dcr. subst.
      inv_get. destruct x6.
      eapply H0; eauto.
      * eapply setTopAnn_annotation. eauto.
      * eauto with len.
      * admit.
      * admit.
      * admit.
      * eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        eauto with len.
      * admit.
    + setoid_rewrite ZipEq.
      eapply IHLD; eauto.
      * apply setTopAnn_annotation; eauto.
      * eauto with len.
      * split.
        -- admit.
        -- eapply ann_R_setTopAnn_right; eauto.
           rewrite forward_fst_snd_getAnn.
           rewrite getAnn_setTopAnn; eauto.
      * pe_rewrite. set_simpl.
        rewrite List.map_app. rewrite list_union_app.
        eapply disj_union_left.
        -- symmetry.
           eapply funConstr_disj_Dt; eauto.
        -- symmetry. eapply disj_incl; eauto.
      * eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        eauto with len.
      * admit.
Qed.