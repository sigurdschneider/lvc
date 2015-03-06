Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness Restrict Bisim MoreExp SetOperations.
Require Import DecSolve RenamedApart LabelsDefined.

Set Implicit Arguments.

(* shadowing free *)
Inductive shadowing_free : set var -> stmt -> Prop :=
  | shadowing_freeExp x e s D
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> shadowing_free {x; D} s
      -> shadowing_free D (stmtLet x e s)
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
    -> shadowing_free D (stmtApp f Y)
  | shadowing_freeExtern x f Y s D
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> shadowing_free {x; D} s
      -> shadowing_free D (stmtExtern x f Y s)
  | shadowing_freeLet D s t Z
    : of_list Z ∩ D [=] ∅
    -> shadowing_free (of_list Z ∪ D) s
    -> shadowing_free D t
    -> shadowing_free D (stmtFun Z s t).

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

Lemma renamedApart_shadowing_free s an
  : renamedApart s an -> shadowing_free (fst (getAnn an)) s.
Proof.
  intros. general induction H; simpl; eauto using shadowing_free.
  - econstructor; eauto. rewrite H2 in IHrenamedApart. eauto.
  - rewrite H4 in IHrenamedApart1. rewrite H5 in IHrenamedApart2.
    econstructor; eauto.
  - econstructor; eauto. rewrite H2 in IHrenamedApart; eauto.
  - rewrite H3 in IHrenamedApart1. rewrite H5 in IHrenamedApart2.
    econstructor; eauto.
Qed.


Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
 | srdExp DL x e s lv al
    : srd (restrict DL (lv\{{x}})) s al
    -> srd DL (stmtLet x e s) (ann1 lv al)
  | srdIf DL e s t lv als alt
    : srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf e s t) (ann2 lv als alt)
  | srdRet e DL lv
    : srd DL (stmtReturn e) (ann0 lv)
  | srdGoto DL lv G' f Y
    : get DL (counted f) (Some G')
    -> srd DL (stmtApp f Y) (ann0 lv)
 | srdExtern DL x f Y s lv al
    : srd (restrict DL (lv\{{x}})) s al
    -> srd DL (stmtExtern x f Y s) (ann1 lv al)
  | srdLet DL s t Z lv als alt
    : srd (restrict (Some (getAnn als \ of_list Z)::DL) (getAnn als \ of_list Z))
          s als
    -> srd (Some (getAnn als \ of_list Z)::DL) t alt
    -> srd DL (stmtFun Z s t) (ann2 lv als alt).

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
    | stmtLet x e s0 => ann1 (freeVars s) (freeVar_live s0)
    | stmtIf x s1 s2 => ann2 (freeVars s) (freeVar_live s1) (freeVar_live s2)
    | stmtApp l Y => ann0 (freeVars s)
    | stmtReturn x => ann0 (freeVars s)
    | stmtFun Z s1 s2 => ann2 (freeVars s) (freeVar_live s1) (freeVar_live s2)
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
   -> PIR2 (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor.
    eapply IHsrd; eauto. eapply restrict_subset; eauto. reflexivity.
  + destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
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
   -> PIR2 (fstNoneOrR (flip Subset)) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor.
    eapply IHsrd; eauto. eapply restrict_subset2; eauto. reflexivity.
  + destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  + econstructor. eapply IHsrd, restrict_subset2; eauto. reflexivity.
  + econstructor; eauto.
    eapply IHsrd1. repeat rewrite restrict_incl; try reflexivity.
    constructor; eauto. reflexivity.
    eapply restrict_subset2; eauto. reflexivity.
    eapply IHsrd2. constructor; eauto. reflexivity.
Qed.

Lemma renamedApart_coherent s ang DL
: renamedApart s ang
  -> labelsDefined s (length DL)
  -> bounded (List.map Some DL) (fst (getAnn ang))
  -> srd (List.map Some DL) s (mapAnn fst ang).
Proof.
  intros. general induction H; invt labelsDefined; simpl.
  - econstructor; eauto.
    eapply srd_monotone.
    eapply IHrenamedApart; eauto.
    rewrite H2. simpl in *. rewrite <- incl_add'; eauto.
    erewrite bounded_restrict_eq; simpl; eauto. reflexivity.
    simpl. cset_tac; intuition.
  - econstructor; eauto.
    + eapply IHrenamedApart1; eauto.
      rewrite H4; eauto.
    + eapply IHrenamedApart2; eauto.
      rewrite H5; eauto.
  - econstructor.
  - edestruct get_in_range as [a ?]; eauto.
    econstructor. eapply map_get_1; eauto.
  - econstructor; eauto.
    eapply srd_monotone.
    eapply IHrenamedApart; eauto.
    rewrite H2. simpl in *. rewrite <- incl_add'; eauto.
    erewrite bounded_restrict_eq; simpl; eauto. reflexivity.
    simpl. cset_tac; intuition.
  - econstructor.
    + eapply srd_monotone.
      eapply (IHrenamedApart1 (D::DL)); eauto using labelsDefined.
      rewrite H3. simpl in *. rewrite <- incl_right.
      split; eauto; reflexivity.
      rewrite getAnn_mapAnn; simpl.
      destruct if.
      * econstructor. econstructor. rewrite H3; simpl.
        cset_tac; intuition; eauto.
        simpl in *. rewrite H3; simpl.
        erewrite bounded_restrict_eq; simpl; eauto. reflexivity.
        simpl. cset_tac; intuition; eauto.
      * exfalso. eapply n. rewrite H3; simpl. reflexivity.
    + eapply srd_monotone.
      eapply (IHrenamedApart2 (D::DL)); eauto using labelsDefined.
      rewrite H5. simpl; intuition.
      rewrite getAnn_mapAnn; simpl.
      econstructor. econstructor. rewrite H3; simpl.
      cset_tac; intuition; eauto.
      reflexivity.
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

Lemma restrict_get DL lv n s
: get (restrict DL lv) n ⎣ s ⎦
  -> get DL n (Some s) /\ s ⊆ lv.
Proof.
  intros. general induction H.
  - destruct DL; simpl in *; isabsurd.
    inv Heql. unfold restr in H0. destruct o.
    destruct if in H0. inv H0.
    eauto using get. congruence. congruence.
  - destruct DL; simpl in *; isabsurd.
    inv Heql. edestruct IHget; eauto.
    eauto using get.
Qed.

Lemma srd_globals_live s DL AL alv f
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> isCalled s f
  -> exists lv, get DL (counted f) (Some lv) /\ lv ⊆ getAnn alv.
Proof.
  intros. general induction H0; invt live_sound; invt isCalled; simpl in * |- *.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct IHsrd1; eauto. dcr.
    eexists; split; eauto. rewrite <- H12; eauto.
  - edestruct IHsrd2; eauto. dcr.
    eexists; split; eauto. rewrite <- H13; eauto.
  - eexists; split; eauto.
    edestruct PIR2_nth; eauto; dcr. get_functional; subst.
    inv H5; simpl in *. rewrite H6; eauto.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct IHsrd1; eauto. econstructor; eauto using restrict_eqReq.
    destruct if; simpl. econstructor. simpl. reflexivity. econstructor.
    destruct f; simpl in *. dcr.
    inv H3.
    edestruct restrict_get; eauto.
    edestruct IHsrd2; eauto. econstructor; eauto using restrict_eqReq.
    econstructor. simpl. reflexivity.
    simpl in *; dcr. inv H14.
    eexists; split; eauto. rewrite <- H13, <- H16; eauto.
  - edestruct IHsrd2; eauto. econstructor; eauto using restrict_eqReq.
    econstructor. reflexivity.
    destruct f; simpl in *; dcr.
    inv H3.
    eexists; split; eauto. rewrite H4; eauto.
Qed.

Lemma srd_live_functional s DL AL alv
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> noUnreachableCode s
  -> live_sound FunctionalAndImperative AL s alv.
Proof.
  intros. general induction H0; invt live_sound; invt noUnreachableCode; simpl in * |- *;
          eauto using live_sound, restrict_eqReq.
  - econstructor; eauto.
    + eapply IHsrd1; eauto.
      econstructor; eauto using restrict_eqReq.
      destruct if; econstructor; reflexivity.
    + eapply IHsrd2; eauto.
      econstructor; eauto using restrict_eqReq.
      econstructor; reflexivity.
    + simpl. edestruct srd_globals_live; eauto.
      econstructor; eauto. econstructor; reflexivity.
      dcr. inv H3. rewrite H4; eauto.
Qed.

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
  approxI' AL DL o Z E s
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z)
                /\ srd (restrict (Some G::AL) G) s a
                /\ live_sound Imperative DL s a)
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
Qed.

Unset Printing Records.

Lemma srd_preservation (E E':onv val) L L' s s' DL (G:set var) DA a e
  (SRD:srd DA s a)
  (RA:rd_agree DA L E)
  (A: AIR21 approx' DA DL L)
  (LV:live_sound Imperative DL s a)
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

Inductive srdSim : F.state -> I.state -> Prop :=
  | srdSimI (E EI:onv val) L s AL DL a
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: AIR21 approx' AL DL L)
  (AG:agree_on eq (getAnn a) E EI)
  (LV:live_sound Imperative DL s a)
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

Lemma srd_implies_invariance s a
: live_sound Imperative nil s a -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim.
  econstructor; eauto using AIR21, PIR2; isabsurd.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
