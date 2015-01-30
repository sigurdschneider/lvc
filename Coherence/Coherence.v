Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness Restrict Bisim MoreExp SetOperations DecSolve.

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
      -> unique Z
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

  - econstructor. rewrite <- H8; eauto.
    rewrite <- H8; eauto.
    rewrite <- H13; eauto.
    eapply IHssa1; eauto. rewrite <- H8. rewrite <- (ann_R_get H11); eauto.
    eapply IHssa2; eauto. rewrite <- H8. rewrite <- (ann_R_get H12); eauto.
    eauto.
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
  - eapply H1. eapply H0 in H7. left; eapply H7.
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
    rewrite H10, H13. cset_tac; intuition.
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
      eapply H7. rewrite H6; eauto.
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
      clear_all; cset_tac; intuition; eauto. eapply H9. rewrite H0; eauto.
      rewrite H11; reflexivity.
  - econstructor; eauto.
    revert H H9; clear_all; cset_tac; intuition; eauto.
    rewrite <- H0. rewrite minus_dist_intersection. reflexivity.
    rewrite <- H1. rewrite minus_dist_union. reflexivity.
    eapply IHssa1; eauto; reflexivity.
    rewrite getAnn_mapAnn; simpl. inv H2; simpl.
    rewrite H12, H13. constructor; try reflexivity.
    revert H9; clear_all; cset_tac; intuition; eauto.
    eapply IHssa2; eauto; reflexivity.
    rewrite getAnn_mapAnn; simpl. inv H3; simpl.
    rewrite H12, H13. reflexivity.
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

Definition srd_dec DL s a
  : Computable (srd DL s a).
Proof.
  hnf.
  general induction s; simpl.
  + edestruct a as [|lv a'|]; try dec_solve.
    edestruct (IHs (restrict DL (lv\{{x}})) a'); try dec_solve.
  + edestruct a as [?|?|lv als alt]; try dec_solve.
    edestruct (IHs1 DL als), (IHs2 DL alt); try dec_solve.
  + destruct a;
    destruct (get_dec DL (counted l)) as [[[G'|] ?]|?];
    try dec_solve.
  + destruct a; try dec_solve.
  + edestruct a as [|lv a'|]; try dec_solve.
    edestruct (IHs (restrict DL (lv\{{x}})) a'); try dec_solve.
  + destruct a as [?|?|lv als alt]; try dec_solve.
    edestruct (IHs1 (restrict (Some (getAnn als \ of_list Z)::DL) (getAnn als \ of_list Z)) als);
    edestruct (IHs2 (Some (getAnn als \ of_list Z)::DL) alt); try dec_solve.
Defined.

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
  + destruct (list_eq_get H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
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
  + destruct (list_eq_get H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
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
  : list (option (set var)) -> list (set var * list var) -> F.block -> Prop :=
  approxI' AL DL o Z E s i
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restrict (Some G::AL) G) s a
                /\ live_sound i DL s a)
     -> approx' (o::AL) DL (F.blockI E Z s).

Section AIR21.
  Variable X Y Z : Type.
  Variable R : list X -> list Y -> Z -> Prop.

  Inductive AIR21
    : list X -> list Y -> list Z -> Prop :=
  | AIR21_nil : AIR21 nil nil nil
  | AIR21_cons x XL y (YL:list Y) z (ZL:list Z) (pf:R (x::XL) (y::YL) z)
    : AIR21 XL YL ZL ->
      AIR21 (x::XL) (y::YL) (z::ZL).

  Lemma AIR21_nth XL YL ZL l blkx :
    AIR21 XL YL ZL
    -> get XL l blkx
    -> exists (blky:Y) (blkz:Z),
      get YL l blky /\ get ZL l blkz /\ R (drop l XL) (drop l YL) blkz.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHAIR21 as [blk [A B]]; eauto; dcr.
    do 2 eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR21_drop XL YL ZL n
    : AIR21 XL YL ZL -> AIR21 (drop n XL) (drop n YL) (drop n ZL).
  Proof.
    general induction n; simpl; eauto.
    inv H; simpl; eauto using AIR2.
  Qed.

End AIR21.

Ltac provide_invariants_21 :=
match goal with
  | [ H : AIR21 ?R ?A ?B ?C, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in
    destruct (AIR21_nth H H') as [? [? [? [? X]]]]; eauto; inv X;
    repeat get_functional; (try subst);
    let X'' := fresh H in pose proof (AIR21_drop n H) as X'';
    match goal with
      | [ H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
        (try rewrite <- H'' in X'');
          let X' := fresh H in
          pose proof (get_drop_eq H' H'') as X'; inv X'; try clear X'
    end
end.

Lemma approx_restrict AL DL L G
: AIR21 approx' AL DL L
  -> AIR21 approx' (restrict AL G) DL L.
Proof.
  intros.
  general induction H; simpl; eauto using AIR21.
  econstructor. case_eq (restr G x); intros.
  inv pf. econstructor.
  intros. inv H1.
  eapply restr_iff in H0; dcr; subst.
  specialize (H5 _ H1); dcr.
  rewrite restrict_incl, restrict_idem, <- restrict_incl; eauto; try reflexivity.
  inv pf. econstructor. isabsurd. eapply IHAIR21; eauto.
  Grab Existential Variables. eapply i.
Qed.

Unset Printing Records.

Lemma srd_preservation (E E':onv val) L L' s s' DL (G:set var) DA a e i
  (SRD:srd DA s a)
  (RA:rd_agree DA L E)
  (A: AIR21 approx' DA DL L)
  (LV:live_sound i DL s a)
  (S:F.step (L, E, s) e (L',E',s'))
  : exists DA' DL' a', srd DA' s' a'
                   /\ rd_agree DA' L' E'
                   /\ AIR21 approx' DA' DL' L'.
Proof.
  destruct SRD; try inv S.

  + do 3 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.

  + do 3 eexists; eauto.
  + do 3 eexists; eauto.

  + provide_invariants_21. specialize (H3 _ H4); dcr.
    rewrite H2 in H7. simpl in *.
    do 3 eexists; repeat split; simpl; eauto.
    pose proof (RA _ _ _ H1 H). simpl in *.
    eapply rd_agree_update_list; eauto.
    exploit omap_length; eauto. rewrite map_length. congruence.
    eapply approx_restrict; eauto.
  + do 3 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.

  + inv LV. do 3 eexists; repeat split; eauto.
    hnf; intros.
    destruct n; inv H; inv H0. simpl.
    reflexivity.
    eapply RA; eauto.

    econstructor; eauto using agree_on_incl.
    econstructor; eauto.
    split. inv H.
    split; cset_tac; isabsurd; eauto. inv H.
    eexists; eauto. split; [| split;eauto].
    cset_tac; intuition. decide (a ∈ of_list Z); intuition.
Qed.

Inductive approxI
  : list (option (set var)) -> list (set var * list var) -> I.block -> Prop :=
  approxII' AL DL o Z s i
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restrict (Some G::AL) G) s a
                /\ live_sound i DL s a)
     -> approxI (o::AL) DL (I.blockI Z s).

Lemma approxI_restrict AL DL L G
: AIR21 approxI AL DL L
  -> AIR21 approxI (restrict AL G) DL L.
Proof.
  intros.
  general induction H; simpl; eauto using AIR21.
  econstructor. case_eq (restr G x); intros.
  inv pf. econstructor.
  intros. inv H1.
  eapply restr_iff in H0; dcr; subst.
  specialize (H5 _ H1); dcr.
  rewrite restrict_incl, restrict_idem, <- restrict_incl; eauto; try reflexivity.
  inv pf. econstructor. isabsurd. eapply IHAIR21; eauto.
  Grab Existential Variables. eapply i.
Qed.

Lemma srd_preservation_I (E E':onv val) L L' s s' DL (G:set var) DA a e i
  (SRD:srd DA s a)
  (A: AIR21 approxI DA DL L)
  (LV:live_sound i DL s a)
  (S:I.step (L, E, s) e (L',E',s'))
  : exists DL' DA' a', srd DA' s' a' /\ AIR21 approxI DA' DL' L'.
Proof.
  destruct SRD; try inv S.

  - do 3 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approxI_restrict, rd_agree_update.

  - eexists; eauto.
  - eexists; eauto.

  - provide_invariants_21.
    specialize (H3 _ H4); dcr.
    rewrite H2 in H7. simpl in *.
    do 3 eexists; repeat split; simpl; eauto using approxI_restrict.
  - eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approxI_restrict, rd_agree_update.

  - inv LV. do 3 eexists; repeat split; eauto.
    econstructor; eauto.
    econstructor; eauto.
    split; inv H.
    + cset_tac; intuition.
    + eexists; eauto. split; [| split;eauto].
      * cset_tac; intuition. decide (a ∈ of_list Z); intuition.
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


Inductive fstNoneOrR' {X Y:Type} (R:X->Y->Prop)
  : option X -> Y -> Prop :=
| fstNone' (y:Y) : fstNoneOrR' R None y
| bothR' (x:X) (y:Y) : R x y -> fstNoneOrR' R (Some x) y
.

Definition eqReq := (fstNoneOrR' (fun (s : set var) (t : set var * params) =>
                                   s [=] fst t \ of_list (snd t))).

Lemma restrict_eqReq DL DL' G
: PIR2 eqReq DL DL'
  -> PIR2 eqReq (restrict DL G) DL'.
Proof.
  intros. induction H; simpl; econstructor; eauto.
  unfold restr. destruct pf. constructor.
  destruct if; eauto. subst. constructor; eauto. constructor.
Qed.

Inductive srdSim : F.state -> I.state -> Prop :=
  | srdSimI (E EI:onv val) L s AL DL a i
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: AIR21 approx' AL DL L)
  (AG:agree_on eq (getAnn a) E EI)
  (LV:live_sound i DL s a)
  (ER:PIR2 eqReq AL DL)
  : srdSim (L, E, s) (strip L, EI,s).

Lemma srdSim_sim σ1 σ2
  : srdSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; inv SRD; inv LV; simpl in *; try provide_invariants_21.
  - case_eq (exp_eval E e); intros.
    one_step.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto.
    eapply srdSim_sim; econstructor;
    eauto using approx_restrict, rd_agree_update.
    eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl; eauto.
    eauto using restrict_eqReq.
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
      specialize (H4 _ H3); dcr. rewrite H2 in A1,H12.
      econstructor; simpl; eauto using approx_restrict.
      eapply rd_agree_update_list; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply (RA _ _ _ H1 H).
      eapply update_with_list_agree; eauto. rewrite H11.
      rewrite union_comm. rewrite union_minus_remove.
      pose proof (RA _ _ G' H1 H); dcr. simpl in *.
      eapply agree_on_sym; eauto. eapply agree_on_incl; eauto using incl_minus.
      etransitivity; eauto. symmetry. hnf in RA.
      eapply agree_on_incl; eauto.
      edestruct PIR2_nth_2; eauto; dcr. get_functional; eauto; subst.
      inv H16. rewrite H13. simpl. eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply restrict_eqReq. eapply PIR2_drop; eauto.
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
      eauto using restrict_eqReq; eauto.
    + symmetry in AG.
      exploit omap_exp_eval_live_agree; eauto.
      eexists; split. econstructor; eauto.
      eapply srdSim_sim; econstructor; eauto using approx_restrict, rd_agree_update.
      eapply agree_on_update_same. reflexivity.
      symmetry in AG.
      eapply agree_on_incl; eauto.
      eauto using restrict_eqReq; eauto.
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
    econstructor; eauto. econstructor; reflexivity.
Qed.

Lemma srd_implies_invariance s a i
: live_sound i nil s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim.
  econstructor; eauto using AIR21, PIR2; isabsurd.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
