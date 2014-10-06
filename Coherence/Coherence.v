Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness Restrict Bisim MoreExp SetOperations.

Set Implicit Arguments.

Inductive ssa : stmt -> ann (set var * set var) -> Prop :=
  | ssaExp x e s D D' an
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> ssa s an
      -> pe (getAnn an) (D ∪ {{x}}, D')
      -> ssa (stmtExp x e s) (ann1 (D, D') an)
  | ssaIf  D D' Ds Dt e s t ans ant
    : Exp.freeVars e ⊆ D
      -> Ds ∩ Dt [=] D
      -> Ds ∪ Dt [=] D'
      -> ssa s ans
      -> ssa t ant
      -> pe (getAnn ans) (D, Ds)
      -> pe (getAnn ant) (D, Dt)
      -> ssa (stmtIf e s t) (ann2 (D, D') ans ant)
  | ssaRet D D' e
    : Exp.freeVars e ⊆ D
      -> D [=] D'
      -> ssa (stmtReturn e) (ann0 (D, D'))
  | ssaGoto D D' f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D
      -> D [=] D'
      -> ssa (stmtGoto f Y) (ann0 (D, D'))
  | ssaExtern x f Y s D D' an
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> ssa s an
      -> pe (getAnn an) (D ∪ {{x}}, D')
      -> ssa (stmtExtern x f Y s) (ann1 (D, D') an)
  | ssaLet D D' s t Ds Dt Z ans ant
    : of_list Z ∩ D [=] ∅
      -> Ds ∩ Dt [=] D
      -> Ds ∪ Dt [=] D'
      -> ssa s ans
      -> pe (getAnn ans) (of_list Z ∪ D, Ds)
      -> ssa t ant
      -> pe (getAnn ant) (D, Dt)
      -> ssa (stmtLet Z s t) (ann2 (D,D') ans ant).

Lemma ssa_ext s an an'
  : ann_R (@pe _ _) an an'
  -> ssa s an
  -> ssa s an'.
Proof.
  intros. general induction H0; simpl; invt (ann_R (@pe var _)); invt (@pe var _); eauto using ssa.
  - econstructor. rewrite <- H7; eauto. rewrite <- H7; eauto.
    eapply IHssa; eauto. rewrite <- H7. rewrite (ann_R_get H8) in H2.
    rewrite <- H10. eauto.

  - econstructor. rewrite <- H7; eauto. rewrite <- H7; eauto. rewrite H1; eauto.
    eapply IHssa1; eauto; reflexivity.
    eapply IHssa2; eauto; reflexivity.
    rewrite <- (ann_R_get H10). rewrite <- H7. eauto.
    rewrite <- (ann_R_get H11). rewrite <- H7. eauto.

  - econstructor. rewrite <- H5; eauto. rewrite <- H5, <- H7; eauto.
  - econstructor. rewrite <- H5; eauto. rewrite <- H5, <- H7; eauto.

  - econstructor. rewrite <- H7; eauto. rewrite <- H7; eauto.
    eapply IHssa; eauto. rewrite <- H7, <- H10.
    rewrite <- (ann_R_get H8). eauto.

  - econstructor. rewrite <- H7; eauto.
    rewrite <- H7; eauto.
    rewrite <- H12; eauto.
    eapply IHssa1; eauto. rewrite <- H7. rewrite <- (ann_R_get H10); eauto.
    eapply IHssa2; eauto. rewrite <- H7. rewrite <- (ann_R_get H11); eauto.
Qed.

Instance ssa_morphism
: Proper (eq ==> (ann_R (@pe _ _)) ==> iff) ssa.
Proof.
  intros x s t A; subst. intros. split; intros.
  eapply ssa_ext; eauto.
  eapply ssa_ext; try symmetry; eauto.
Qed.

Lemma ssa_incl s an
  : ssa s an -> fst (getAnn an) ⊆ snd (getAnn an).
Proof.
  intros. general induction H; eauto using ssa; simpl; cset_tac; eauto.
  - rewrite H2 in IHssa; simpl in *. rewrite <- IHssa. cset_tac; intuition.
  - rewrite H4 in IHssa1. rewrite H5 in IHssa2. simpl in *.
    eapply H1; eauto.
  - eapply H0; eauto.
  - eapply H0; eauto.
  - rewrite H2 in IHssa; simpl in *.
    eapply IHssa. cset_tac; intuition.
  - eapply H1. eapply H0 in H6. left; eapply H6.
Qed.

Lemma ssa_freeVars s an
  : ssa s an -> freeVars s ⊆ fst (getAnn an).
Proof.
  intros. general induction H; simpl; eauto.
  - rewrite H0, IHssa, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite H, IHssa1, IHssa2. rewrite H4, H5; simpl.
    cset_tac; intuition.
  - rewrite H0, IHssa, H2; simpl. cset_tac; intuition.
  - rewrite IHssa1, IHssa2. inv H3; inv H5; simpl.
    rewrite H9, H12. cset_tac; intuition.
Qed.

Definition pminus (D'':set var) s :=
  match s with
    | pair s s' => (s \ D'', s' \ D'')
  end.

Lemma ssa_minus D an an' s
  : notOccur D s
    -> ssa s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> ssa s an'.
Proof.
  intros ? ? PE. general induction H0; invt notOccur; try rewrite PE; simpl.
  - econstructor.
    + intro. cset_tac; eauto.
    + eapply Exp.notOccur_freeVars in H9; eauto. rewrite meet_comm in H9.
      rewrite <- H0. rewrite minus_inane_set; eauto. reflexivity.
    + eapply IHssa; eauto. reflexivity.
    + rewrite getAnn_mapAnn. inv H2; simpl.
      rewrite H10, H11. econstructor. cset_tac; intuition.
      eapply H7. rewrite <- H6; eauto.
      reflexivity.
  - eapply Exp.notOccur_freeVars in H8.
    econstructor; eauto. rewrite meet_comm in H8.
    rewrite <- H. rewrite minus_inane_set; eauto. reflexivity.
    rewrite <- minus_dist_intersection. rewrite H0. reflexivity.
    rewrite <- minus_dist_union. rewrite H1. reflexivity.
    eapply IHssa1; eauto; reflexivity.
    eapply IHssa2; eauto; reflexivity.
    rewrite getAnn_mapAnn. inv H2; simpl. rewrite H11, H12.
    reflexivity.
    rewrite getAnn_mapAnn. inv H3; simpl. rewrite H11, H12.
    reflexivity.
  - econstructor.
    eapply Exp.notOccur_freeVars in H3.
    rewrite meet_comm in H3.
    rewrite <- H. rewrite minus_inane_set; eauto. reflexivity.
    rewrite H0. reflexivity.
  - econstructor. unfold list_union.
    hnf; intros. eapply list_union_get in H2.
    destruct H2 as [[? []]|]; dcr. edestruct map_get_4; eauto; dcr; subst.
    exploit H3; eauto.
    eapply Exp.notOccur_freeVars in H3; eauto. rewrite meet_comm in H3.
    cset_tac; intuition.
    rewrite <- H. eapply incl_list_union; eauto. reflexivity.
    eauto. cset_tac; intuition. rewrite H0; reflexivity.
  - econstructor; eauto.
    + cset_tac; intuition.
    + unfold list_union.
      hnf; intros. eapply list_union_get in H4.
      destruct H4 as [[? []]|]; dcr. edestruct map_get_4; eauto; dcr; subst.
      exploit H7; eauto.
      eapply Exp.notOccur_freeVars in H7; eauto. rewrite meet_comm in H7.
      cset_tac; intuition; eauto.
      rewrite <- H0. eapply incl_list_union; eauto. reflexivity.
      eauto. cset_tac; intuition.
    + eapply IHssa; eauto; reflexivity.
    + rewrite getAnn_mapAnn.
      inv H2; simpl. constructor. rewrite H8. revert H9.
      clear_all; cset_tac; intuition; eauto. eapply H9. rewrite <- H0; eauto.
      rewrite H11; reflexivity.
  - econstructor; eauto.
    revert H H8; clear_all; cset_tac; intuition; eauto.
    rewrite <- H0. rewrite minus_dist_intersection. reflexivity.
    rewrite <- H1. rewrite minus_dist_union. reflexivity.
    eapply IHssa1; eauto; reflexivity.
    rewrite getAnn_mapAnn; simpl. inv H2; simpl.
    rewrite H11, H12. constructor; try reflexivity.
    revert H8; clear_all; cset_tac; intuition; eauto.
    eapply IHssa2; eauto; reflexivity.
    rewrite getAnn_mapAnn; simpl. inv H3; simpl.
    rewrite H11, H12. reflexivity.
Qed.

(* shadowing free *)
Inductive shadowing_free : set var -> stmt -> Prop :=
  | shadowing_freeExp x e s D
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> shadowing_free (D ∪ {{x}}) s
      -> shadowing_free D (stmtExp x e s)
  | shadowing_freeIf D e s t
    : Exp.freeVars e ⊆ D
    -> shadowing_free D s
    -> shadowing_free D t
    -> shadowing_free D (stmtIf e s t)
  | shadowing_freeRet D e
    : Exp.freeVars e ⊆ D
    -> shadowing_free D (stmtReturn e)
  | shadowing_freeGoto D f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D
    -> shadowing_free D (stmtGoto f Y)
  | shadowing_freeExtern x f Y s D
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> shadowing_free (D ∪ {{x}}) s
      -> shadowing_free D (stmtExtern x f Y s)
  | shadowing_freeLet D s t Z
    : of_list Z ∩ D [=] ∅
    -> shadowing_free (of_list Z ∪ D) s
    -> shadowing_free D t
    -> shadowing_free D (stmtLet Z s t).

Lemma shadowing_free_ext s D D'
  : D' [=] D
  -> shadowing_free D s
  -> shadowing_free D' s.
Proof.
  intros EQ SF. general induction SF; simpl; econstructor; try rewrite EQ; eauto.
  - eapply IHSF; eauto.
    rewrite EQ; reflexivity.
  - eapply IHSF; eauto. rewrite EQ; reflexivity.
  - eapply IHSF1; eauto. rewrite EQ. reflexivity.
Qed.

Instance shadowing_free_morphism
: Proper (Equal ==> eq ==> iff) shadowing_free.
Proof.
  unfold Proper, respectful; intros; subst.
  split; eapply shadowing_free_ext; eauto. symmetry; eauto.
Qed.

Lemma ssa_shadowing_free s an
  : ssa s an -> shadowing_free (fst (getAnn an)) s.
Proof.
  intros. general induction H; simpl; eauto using shadowing_free.
  - econstructor; eauto. rewrite H2 in IHssa. eauto.
  - rewrite H4 in IHssa1. rewrite H5 in IHssa2.
    econstructor; eauto.
  - econstructor; eauto. rewrite H2 in IHssa; eauto.
  - rewrite H3 in IHssa1. rewrite H5 in IHssa2.
    econstructor; eauto.
Qed.


Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
 | srdExp DL x e s lv al
    : srd (restrict DL (lv\{{x}})) s al
    -> srd DL (stmtExp x e s) (ann1 lv al)
  | srdIf DL e s t lv als alt
    : srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf e s t) (ann2 lv als alt)
  | srdRet e DL lv
    : srd DL (stmtReturn e) (ann0 lv)
  | srdGoto DL lv G' f Y
    : get DL (counted f) (Some G')
    -> G' ⊆ lv
    -> srd DL (stmtGoto f Y) (ann0 lv)
 | srdExtern DL x f Y s lv al
    : srd (restrict DL (lv\{{x}})) s al
    -> srd DL (stmtExtern x f Y s) (ann1 lv al)
  | srdLet DL s t Z lv als alt
    : srd (restrict (Some (getAnn als \ of_list Z)::DL) (getAnn als \ of_list Z))
          s als
    -> srd (Some (getAnn als \ of_list Z)::DL) t alt
    -> srd DL (stmtLet Z s t) (ann2 lv als alt).

Definition peq := prod_eq (@feq var var eq) (@Equal var _ _).

(*
Instance srd_morphism
  : Proper (list_eq (option_eq Equal) ==> Equal ==> eq ==> impl) srd.
Proof.
  unfold Proper, peq, respectful, impl; intros; decompose records; simpl in *; subst.
  general induction H2; simpl in *; eauto using srd.
  + econstructor; eauto.
    - rewrite <- H1; eauto.
    - eapply IHsrd. rewrite H0. rewrite <- H1. reflexivity.
      rewrite H1. reflexivity.

  + econstructor; eauto. rewrite <- H1; eauto.
  + econstructor; eauto. rewrite <- H1; eauto.

  + edestruct (list_eq_get H2 H0); decompose records;
    destruct x; simpl in * |- *; eauto; inv H6.
    econstructor; eauto. rewrite <- H3; eauto.
    rewrite <- H3, <- H8; eauto.

  + econstructor; eauto. rewrite <- H1; eauto.
    eapply IHsrd1; eauto; try reflexivity.
    econstructor; eauto. reflexivity.
    rewrite H0. reflexivity.
    eapply IHsrd2; eauto. constructor; eauto; reflexivity.
Qed.
*)

(* srd decidability is more complicated *)
(*
Definition srd_dec DL G s
  : Computable (srd DL G s).
Proof.
  constructor.
  general induction s; simpl.
  + edestruct IHs;
    decide(Exp.freeVars e ⊆ G);
      solve [ left; econstructor; eauto | right; intro A; inv A; eauto ].
  + edestruct IHs1, IHs2; decide(x ∈ G);
      solve [ left; econstructor; eauto | right; intro A; inv A; eauto ].
  + decide (of_list Y ⊆ G);
    destruct (get_dec DL (counted l)) as [[[G'|] ?]|?];
    (try decide (G' ⊆ G));
      solve [ left; econstructor; eauto | right; intro A; inv A; try (get_functional; subst); eauto ].
  + decide (x ∈ G).
    left; econstructor; eauto.
    right; intro A; inv A; eauto.
  + pose
      ((filter
         (fun G' =>
            andb (sumbool_bool (IHs2 ((Some G')::DL) G))
                       (sumbool_bool (IHs1 (restrict ((Some G')::DL) G') (G' ∪ of_list Z)))
         )
         (powerset (G \ of_list Z)))).
    case_eq (is_empty s); intros.
    right; intro A; inv A. assert (G' ∈ s). unfold s.
    rewrite filter_iff. split. eapply powerset_spec; eauto.
    eapply andb_true_iff; split.
    destruct (IHs2 ((Some G') :: DL) G); simpl; eauto.
    destruct (IHs1 (restrict ((Some G') :: DL) G') (G' ∪ of_list Z)); simpl; eauto.

    Opaque restrict.
    hnf; intros. simpl.
    clear H. clear s.
    destruct (IHs2 ((Some x) :: DL) G),
             (IHs1 (restrict ((Some x) :: DL) x) (x ∪ of_list Z)),
             (IHs2 ((Some y) :: DL) G),
             (IHs1 (restrict ((Some y) :: DL) y) (y ∪ of_list Z));
      simpl; eauto.
    eapply srd_morphism in s0; eauto.
    exfalso; eauto.
    repeat (rewrite restrict_incl; try reflexivity).
    econstructor; eauto. econstructor; eauto. rewrite H0. reflexivity.
    rewrite <- H0. reflexivity.
    eapply srd_morphism in s; eauto.
    exfalso; eauto. econstructor; eauto. econstructor; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s; eauto.
    exfalso; eauto. econstructor; eauto. econstructor; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s3; eauto.
    repeat (rewrite restrict_incl; try reflexivity).
    econstructor; eauto. econstructor; eauto. symmetry; eauto.
    rewrite H0; reflexivity. rewrite H0; reflexivity.
    eapply srd_morphism in s0; eauto.
    econstructor; eauto. econstructor; eauto. symmetry; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s; eauto.
    econstructor; eauto. econstructor; eauto. symmetry; eauto.
    reflexivity. reflexivity.

    eapply is_empty_iff in H. eapply empty_is_empty_1 in H.  cset_tac; eauto.
    case_eq (choose s). intros G' ?.
    eapply choose_1 in H0. unfold s in H0.
    eapply filter_iff in H0. rewrite andb_true_iff in H0. dcr.
    Opaque restrict.
    destruct (IHs2 ((Some G') :: DL) G); simpl in *; eauto; try congruence.
    destruct (IHs1 (restrict ((Some G') :: DL) G') (G' ∪ of_list Z));
      simpl in *; eauto; try congruence.
    eapply powerset_spec in H1.
    left. econstructor; eauto.

    hnf; intros. simpl.
    clear H. clear s.
    destruct (IHs2 ((Some x) :: DL) G),
             (IHs1 (restrict ((Some x) :: DL) x) (x ∪ of_list Z)),
             (IHs2 ((Some y) :: DL) G),
             (IHs1 (restrict ((Some y) :: DL) y) (y ∪ of_list Z));
      simpl; eauto.
    eapply srd_morphism in s0; eauto.
    exfalso; eauto.
    repeat (rewrite restrict_incl; try reflexivity).
    econstructor; eauto. econstructor; eauto.
    rewrite <- H1. reflexivity. rewrite H1; reflexivity.
    eapply srd_morphism in s; eauto.
    exfalso; eauto. econstructor; eauto. econstructor; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s; eauto.
    exfalso; eauto. econstructor; eauto. econstructor; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s3; eauto.
    repeat (rewrite restrict_incl; try reflexivity).
    econstructor; eauto. econstructor; eauto; try reflexivity.
    rewrite H1; reflexivity. rewrite H1; reflexivity.
    rewrite H1; reflexivity.
    eapply srd_morphism in s0; eauto.
    econstructor; eauto. econstructor; eauto. symmetry; eauto.
    reflexivity. reflexivity.
    eapply srd_morphism in s; eauto.
    econstructor; eauto. econstructor; eauto. symmetry; eauto.
    reflexivity. reflexivity.
    intros. exfalso. eapply zchoose_2 in H0; eauto. eapply is_empty_iff in H0.
    rewrite H in H0; eauto; congruence.
Qed.
*)
Transparent restrict.

(*
Fixpoint freeVar_live (s:stmt) : ann (set var) :=
  match s with
    | stmtExp x e s0 => ann1 (freeVars s) (freeVar_live s0)
    | stmtIf x s1 s2 => ann2 (freeVars s) (freeVar_live s1) (freeVar_live s2)
    | stmtGoto l Y => ann0 (freeVars s)
    | stmtReturn x => ann0 (freeVars s)
    | stmtLet Z s1 s2 => ann2 (freeVars s) (freeVar_live s1) (freeVar_live s2)
  end.

Lemma  getAnn_freeVar_live (s:stmt)
  : getAnn (freeVar_live s) = freeVars s.
Proof.
  destruct s; eauto.
Qed.


Lemma free_live_sound s Lv DL D G
  : (forall n blv Z, get Lv n (blv, Z) -> of_list Z ⊆ blv)
  -> srd DL (D, G) s
  -> live_sound Lv s (freeVar_live s).
Proof.
  intros. general induction H0; simpl in * |- *.
  econstructor. eapply IHsrd; eauto. eapply union_subset_2.
  rewrite getAnn_freeVar_live. eapply union_subset_1.
  econstructor; eauto. eapply union_subset_2; cset_tac; eauto.
  rewrite getAnn_freeVar_live. eapply Subset_trans; eauto; eapply union_subset_1.
  rewrite getAnn_freeVar_live. eapply Subset_trans; eauto. eapply union_subset_1.
  rewrite union_comm. eapply union_subset_1.
  econstructor. cset_tac; eauto.
  econstructor. (* here is the counterexample *)
Abort.
*)

Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> list_eq (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor.
    eapply IHsrd; eauto. eapply restrict_subset; eauto. reflexivity.
  + destruct (list_eq_get H1 H); eauto; dcr. inv H4.
    econstructor; eauto. rewrite <- H5; eauto.
  + econstructor. eapply IHsrd; eauto.
    eapply restrict_subset; eauto. reflexivity.
  + econstructor; eauto.
    eapply IHsrd1. repeat rewrite restrict_incl; try reflexivity.
    constructor; eauto. reflexivity.
    eapply restrict_subset; eauto. reflexivity.
    eapply IHsrd2. constructor; eauto. reflexivity.
Qed.

Lemma srd_monotone2 (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> list_eq (fstNoneOrR (flip Subset)) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor.
    eapply IHsrd; eauto. eapply restrict_subset2; eauto. reflexivity.
  + destruct (list_eq_get H1 H); eauto; dcr. inv H4.
    econstructor; eauto. rewrite <- H5; eauto.
  + econstructor. eapply IHsrd, restrict_subset2; eauto. reflexivity.
  + econstructor; eauto.
    eapply IHsrd1. repeat rewrite restrict_incl; try reflexivity.
    constructor; eauto. reflexivity.
    eapply restrict_subset2; eauto. reflexivity.
    eapply IHsrd2. constructor; eauto. reflexivity.
Qed.

(*
Lemma shadowing_free_srd G s DL
   (A:labl DL s)
   (B:bounded DL G)
   (C:forall n s, get DL n s -> s <> None)
   : shadowing_free G s
  -> srd DL G s.
Proof.
  intros. general induction H; inv A; eauto using srd.

  + econstructor; eauto. eapply IHshadowing_free; eauto.
    unfold restrict. eapply labl_other; try eassumption.
    rewrite map_length; eauto.
    eapply bounded_restrict. cset_tac; intuition.
    intros. assert (D [=] D \ {{x}}). cset_tac; intuition.
    intro. eapply H; rewrite H4 in H3; eauto. rewrite <- H3 in H2.
    erewrite bounded_restrict_eq in H2; try eapply B; try reflexivity.
    eapply C; eauto.

  + destruct y. econstructor; eauto. eapply bounded_get; eauto. eapply C in H2. congruence.
  + assert (D [=] D \ of_list Z) by (cset_tac; intuition eauto).
    econstructor; eauto.
    - reflexivity.
    - rewrite union_comm.
      erewrite bounded_restrict_eq; eauto.
      rewrite <- H2 at 2.
      eapply IHshadowing_free1. eapply labl_other; try eassumption; simpl; f_equal.
      simpl. split. cset_tac; intuition. eapply bounded_morphism_subset; eauto; cset_tac; intuition.
      intros. inv H3. congruence. eapply C; eauto. reflexivity.
      simpl; split; try reflexivity. rewrite <- H2; eauto.
    - eapply IHshadowing_free2. eapply labl_other; try eassumption; simpl; f_equal.
      simpl; split; eauto using minus_incl.
      intros. inv H3; eauto; congruence.
Qed.
*)

Definition invariant (s:stmt) :=
  forall (E:onv var), bisim (nil:list F.block,E,s) (nil:list I.block,E,s).

Definition rd_agree (DL:list (option (set var)))
           L (E:onv val)
  := forall n blk G', get L n blk -> get DL n (Some G') ->
                      agree_on eq G' E (F.block_E blk).


Lemma rd_agree_update DL L E G x v
 (RA:rd_agree DL L E)
  : rd_agree (restrict DL (G \ {{x}})) L (E [x <- v]).
Proof.
  intros. hnf; intros.
  unfold restrict in H0. eapply map_get_4 in H0; dcr.
  unfold restr in H2. destruct x0; isabsurd. destruct if in H2; isabsurd.
  inv H2. eapply agree_on_update_dead. rewrite s0. cset_tac; intuition.
  eapply RA; eauto.
Qed.

Lemma rd_agree_update_list DL L E E' (G G':set var) Z n vl
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G' [=] ∅)
 (LEQ:length Z = length vl)
 (AG:agree_on eq G' E E')
: rd_agree (restrict (drop n DL) G') (drop n L) (E'[Z <-- vl]).
Proof.
  hnf; intros.
  assert (G'0 ⊆ G'). {
    eapply bounded_get; eauto. eapply bounded_restrict; reflexivity.
  }
  assert (G'0 [=] G'0 \ of_list Z) by (split; cset_tac; intuition eauto).
  rewrite H2. eapply update_with_list_agree_minus; eauto.

  unfold restrict in H0. rewrite drop_map in H0.
  eapply get_drop in H. eapply get_drop in H0.
  eapply map_get_4 in H0; dcr.
  hnf in RA.
  etransitivity; try eapply RA; eauto.
  symmetry. eauto using agree_on_incl.
  eapply restr_iff in H4; dcr; subst; eauto.
Qed.


Inductive approx'
  : list (option (set var)) -> F.block -> Prop :=
  approxI' DL o Z E s DL' i
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restrict (Some G::DL) G) s a
                /\ live_sound i DL' s a)
     -> approx' (o::DL) (F.blockI E Z s).

Lemma approx_restrict DL L G
: AIR2 approx' DL L
  -> AIR2 approx' (restrict DL G) L.
Proof.
  intros.
  general induction H; simpl; eauto using AIR2.
  econstructor. case_eq (restr G x); intros.
  inv pf. econstructor.
  intros. inv H1.
  eapply restr_iff in H0; dcr; subst.
  specialize (H4 _ H1); dcr.
  rewrite restrict_incl, restrict_idem, <- restrict_incl; eauto; try reflexivity.
  inv pf. econstructor. isabsurd. eapply IHAIR2; eauto.
  Grab Existential Variables. eapply i. eassumption.
Qed.

Unset Printing Records.

Lemma srd_preservation (E E':onv val) L L' s s' DL (G:set var) DA a e i
  (SRD:srd DA s a)
  (RA:rd_agree DA L E)
  (A: AIR2 approx' DA L)
  (LV:live_sound i DL s a)
  (S:F.step (L, E, s) e (L',E',s'))
  : exists DA' DL' a', srd DA' s' a'
                   /\ rd_agree DA' L' E'
                   /\ AIR2 approx' DL' L'.
Proof.
  destruct SRD; try inv S.

  + do 2 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.

  + do 2 eexists; eauto.
  + do 2 eexists; eauto.

  + provide_invariants_2. specialize (H3 _ H4); dcr.
    rewrite H2 in H7. simpl in *.
    do 3 eexists; repeat split; simpl; eauto.
    pose proof (RA _ _ _ H1 H). simpl in *.
    eapply rd_agree_update_list; eauto.
    exploit omap_length; eauto. rewrite map_length. congruence.

  + do 2 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.

  + inv LV. do 3 eexists; repeat split; eauto.
    hnf; intros.
    destruct n; inv H; inv H0. simpl.
    reflexivity.
    eapply RA; eauto.

    econstructor; eauto using agree_on_incl.
    instantiate (1:=Some (getAnn als \ of_list Z)).
    econstructor; eauto.
    split. inv H.
    split; cset_tac; isabsurd; eauto. inv H.
    eexists; eauto. split; [| split;eauto].
    cset_tac; intuition. decide (a ∈ of_list Z); intuition.
Qed.

Definition stripB (b:F.block) : I.block.
  destruct b; eauto using I.block.
Defined.

Definition strip := List.map stripB.

Lemma drop_strip n L
  : drop n (strip L) = strip (drop n L).
Proof.
  unfold strip. rewrite drop_map; eauto.
Qed.

Inductive srdSim : F.state -> I.state -> Prop :=
  | srdSimI (E EI:onv val) L s AL DL a i
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: AIR2 approx' AL L)
  (AG:agree_on eq (getAnn a) E EI)
  (LV:live_sound i DL s a)
  : srdSim (L, E, s) (strip L, EI,s).

Lemma srdSim_sim σ1 σ2
  : srdSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; inv SRD; inv LV; simpl in *; try provide_invariants_2.
  - case_eq (exp_eval E e); intros.
    one_step.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto.
    eapply srdSim_sim; econstructor;
    eauto using approx_restrict, rd_agree_update.
    eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl; eauto.
    no_step.
    erewrite <- exp_eval_live in def; eauto. congruence.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_live_agree; eauto.
    case_eq (val2bool v); intros.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    exploit exp_eval_live_agree; eauto.
    no_step.
  - no_step. simpl. eapply exp_eval_live; eauto.
  - decide (length Z0 = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; eauto.
      pose proof (map_get_1 stripB H1).
      one_step.
      eapply srdSim_sim. rewrite drop_strip.
      simpl. simpl counted in *.
      specialize (H3 _ H5); dcr. rewrite H2 in A1,H13.
      econstructor; simpl; eauto using approx_restrict.
      eapply rd_agree_update_list; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply (RA _ _ _ H1 H).
      eapply update_with_list_agree; eauto. rewrite H12.
      rewrite union_comm. rewrite union_minus_remove.
      pose proof (RA _ _ G' H1 H); dcr. simpl in *.
      eapply agree_on_sym; eauto. eapply agree_on_incl; eauto using incl_minus.
      etransitivity; eauto. symmetry. hnf in RA.
      eapply agree_on_incl; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
    + exploit omap_exp_eval_live_agree; eauto.
      no_step.
    + no_step. get_functional; subst; simpl in *; congruence.
      unfold strip in *.
      edestruct map_get_4; eauto; dcr; get_functional; subst; simpl in *.
      congruence.
  - case_eq (omap (exp_eval E) Y); intros;
    exploit omap_exp_eval_live_agree; eauto.
    extern_step; assert (vl = l) by congruence; subst.
    + eexists; split. econstructor; eauto.
      eapply srdSim_sim; econstructor; eauto using approx_restrict, rd_agree_update.
      eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto.
    + symmetry in AG.
      exploit omap_exp_eval_live_agree; eauto.
      eexists; split. econstructor; eauto.
      eapply srdSim_sim; econstructor; eauto using approx_restrict, rd_agree_update.
      eapply agree_on_update_same. reflexivity.
      symmetry in AG.
      eapply agree_on_incl; eauto.
    + no_step.
  - one_step.
    eapply srdSim_sim; econstructor; eauto.
    hnf; intros.
    destruct n; inv H1; inv H2. simpl.
    reflexivity.
    eapply RA; eauto.

    econstructor; eauto using agree_on_incl. econstructor; eauto.
    intros. inv H1. split.
    split; cset_tac; isabsurd; eauto.
    eexists. split; eauto. cset_tac; intuition.
    decide (a ∈ of_list Z); intuition.
    eapply agree_on_incl; eauto.
Qed.

Lemma srd_implies_invariance DL s a i
: live_sound i DL s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim.
  econstructor; eauto using AIR2; isabsurd; reflexivity.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
