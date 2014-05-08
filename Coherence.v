Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness ParamsMatch Restrict Sim MoreExp.

Set Implicit Arguments.

(* renamed apart, coincides with classic SSA condition *)
Inductive ssa : set var -> stmt -> set var -> Prop :=
  | ssaExp x e s D D'
    : x ∉ D 
      -> Exp.freeVars e ⊆ D
      -> ssa (D ∪ {{x}}) s D'
      -> ssa D (stmtExp x e s) D'
  | ssaIf  D D' Ds Dt e s t
    : Exp.freeVars e ⊆ D
      -> Ds ∩ Dt [=] D
      -> Ds ∪ Dt [=] D'
      -> ssa D s Ds 
      -> ssa D t Dt
      -> ssa D (stmtIf e s t) D'
  | ssaRet D D' e
    : Exp.freeVars e ⊆ D
      -> D [=] D'
      -> ssa D (stmtReturn e) D'
  | ssaGoto D D' f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D 
      -> D [=] D'
      -> ssa D (stmtGoto f Y) D'
  | ssaLet D D' s t Ds Dt Z
    : of_list Z ∩ D [=] ∅
      -> Ds ∩ Dt [=] D
      -> Ds ∪ Dt [=] D'
      -> ssa (of_list Z ∪ D) s Ds 
      -> ssa D t Dt
      -> ssa D (stmtLet Z s t) D'.

Lemma ssa_ext D1 D1' s D2 D2' 
  : D1 [=] D1' -> D2 [=] D2'
  -> ssa D1 s D2
  -> ssa D1' s D2'.
Proof. 
  intros. general induction H1; simpl; eauto using ssa.
  - econstructor. rewrite <- H2; eauto. rewrite <- H2; eauto.
    eapply IHssa; eauto. rewrite H2; reflexivity. 
  
  - econstructor. rewrite <- H2; eauto. rewrite <- H2; eauto. rewrite <- H3; eauto. 
    eapply IHssa1; eauto; reflexivity.
    eapply IHssa2; eauto; reflexivity.
  
  - econstructor. rewrite <- H1; eauto. rewrite <- H1, H0; eauto.
  - econstructor. rewrite <- H1; eauto. rewrite <- H1, H0; eauto.

  - econstructor. rewrite <- H2; eauto.
    rewrite <- H2; eauto.
    rewrite <- H3; eauto.
    eapply IHssa1. rewrite <- H2; reflexivity. reflexivity.
    eapply IHssa2; eauto. reflexivity.  
Qed.

Add Parametric Morphism : ssa
  with signature SetInterface.Equal ==> 
    eq ==> SetInterface.Equal ==> iff as ssa_morphism.
Proof.
  intros x s t A. intros. split; intros.
  eapply ssa_ext; eauto.
  eapply ssa_ext; try symmetry; eauto.
Qed.
 
Lemma ssa_incl D D' s
  : ssa D s D' -> D ⊆ D'.
Proof. 
  intros. general induction H; eauto using ssa; cset_tac.
  eapply IHssa. cset_tac; intuition.
  rewrite <- H1. cset_tac; intuition.
  rewrite <- H0; intuition.
  rewrite <- H0; intuition.
  rewrite <- H1. cset_tac; intuition.
Qed.

Lemma ssa_freeVars D D' s
  : ssa D s D' -> freeVars s ⊆ D.
Proof.
  intros. general induction H; simpl; eauto.
  - rewrite H0, IHssa. cset_tac; intuition.
  - rewrite H, IHssa1, IHssa2. cset_tac; intuition.
  - rewrite IHssa1, IHssa2. cset_tac; intuition.
Qed.

Lemma list_union_minus_dist Y D'' s s'
  :
    s \ D'' [=] s'
 ->  fold_left union (List.map Exp.freeVars Y) s \ D''
[=] fold_left union (List.map (fun y : exp => Exp.freeVars y \ D'') Y) s'.
Proof.
  general induction Y; simpl; eauto.
  - eapply IHY. rewrite <- H. clear_all.
    cset_tac; intuition.
Qed.

Instance fold_left_union_morphism X `{OrderedType X}:
  Proper (list_eq Equal ==> Equal ==> Equal) (fold_left union).
Proof.
  unfold Proper, respectful; intros.
  general induction H0; simpl; eauto.
  - rewrite IHlist_eq; eauto. reflexivity.
    rewrite H0, H2. reflexivity.
Qed.

Lemma ssa_minus D D' D'' s
  : notOccur D'' s -> ssa D s D' -> ssa (D \ D'') s (D' \ D'').
Proof.
  intros. general induction H0. 
  - inv H2. econstructor. intro. cset_tac; eauto.
    eapply Exp.notOccur_freeVars in H8; eauto. rewrite meet_comm in H8.
    rewrite <- H0. rewrite minus_inane_set; eauto. reflexivity.
    assert ((D \ D'') ∪ {{x}} [=] (D ∪ {{x}}) \ D''). cset_tac. 
    unfold Equivalence.equiv, _eq; simpl. 
    split; intuition. subst; eauto. rewrite H3. eapply IHssa; eauto.
  - inv H2. eapply Exp.notOccur_freeVars in H6.
    econstructor; eauto. rewrite <- H. cset_tac; intuition; eauto.
    rewrite <- minus_dist_intersection. rewrite H0. reflexivity.
    rewrite <- minus_dist_union. rewrite H1. reflexivity.
  - inv H1. eapply Exp.notOccur_freeVars in H3. econstructor.
    cset_tac; intuition; eauto. rewrite H0; reflexivity.
  - inv H1. 
    econstructor. rewrite <- H. unfold list_union.
    rewrite list_union_minus_dist; eauto;try reflexivity.
    eapply incl_set_left.
    eapply fold_left_union_morphism.
    eapply map_ext_get.
    intros; simpl. exploit H3; eauto. eapply Exp.notOccur_freeVars in X.
    revert X; clear_all. cset_tac; intuition; eauto.
    cset_tac; intuition.
    rewrite H0. reflexivity.
  - inv H2. 
    rewrite <- H0, <- H1. rewrite minus_dist_union. rewrite minus_dist_intersection. 
    econstructor. rewrite <- minus_dist_intersection. rewrite H0.
    eapply incl_eq. eapply incl_empty. rewrite <- H. 
    eapply incl_meet_lr; eauto. reflexivity. eapply minus_incl.
    reflexivity. reflexivity.  
    rewrite <- minus_dist_intersection. 
    rewrite <- (minus_inane_set _ _ _ H6). rewrite <- minus_dist_union.
    rewrite H0. eapply IHssa1; eauto.
    rewrite <- minus_dist_intersection. rewrite H0. eapply IHssa2; eauto.
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
  | shadowing_freeLet D s t Z
    : of_list Z ∩ D [=] ∅
    -> shadowing_free (of_list Z ∪ D) s
    -> shadowing_free D t
    -> shadowing_free D (stmtLet Z s t).

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
  | srdLet DL s t Z lv als alt
    : srd (restrict (Some (getAnn als \ of_list Z)::DL) (getAnn als \ of_list Z))
          s als
    -> srd (Some (getAnn als \ of_list Z)::DL) t alt
    -> srd DL (stmtLet Z s t) (ann2 lv als alt).

Definition peq := prod_eq (@feq var var _ _) (@Equal var _ _).

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

(*
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

Lemma ssa_shadowing_free D D' s
  : ssa  D s D' -> shadowing_free D s.
Proof.
  intros. general induction H; eauto using shadowing_free.
Qed.

Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a 
   -> list_eq (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor. 
    eapply IHsrd; eauto. eapply restrict_subset; eauto. cset_tac; intuition.
  + destruct (list_eq_get H1 H); eauto; dcr. inv H4.
    econstructor; eauto. rewrite <- H5; eauto.
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
  forall (E:onv var), sim (nil:list F.block,E,s) (nil:list I.block,E,s).

Definition rd_agree (DL:list (option (set var)))
           L (E:onv val)
  := forall n blk G', get L n blk -> get DL n (Some G') ->
                      agree_on G' E (F.block_E blk).


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

Lemma update_list_agree_minus X `{OrderedType X} Y `{Equivalence Y} lv (E E' f:X -> Y) XL
:  agree_on lv E' E 
   -> agree_on (lv\of_list XL) (update_list E' f XL) E.
Proof.
  intros. general induction XL; simpl. rewrite minus_empty. eassumption.
  rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union. 
  eapply agree_on_update_dead.
  cset_tac. intro; decompose records; eauto. 
  eauto using agree_on_incl, incl_minus.
Qed.

Lemma update_with_list_agree_minus X `{OrderedType X} Y `{Equivalence Y}
      lv (E E':X -> Y) XL YL 
: length XL = length YL
  -> agree_on lv E' E 
  -> agree_on (lv\of_list XL) (E' [ XL <-- YL ]) E.
Proof.
  intros. eapply length_length_eq in H1. 
  general induction H1; simpl. rewrite minus_empty. eassumption.
  rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union. 
  eapply agree_on_update_dead.
  cset_tac. intro; decompose records; eauto. 
  eauto using agree_on_incl, incl_minus.
Qed.

Lemma rd_agree_update_list DL L E E' (G G':set var) Z n vl
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G' [=] ∅)
 (LEQ:length Z = length vl)
 (AG:agree_on G' E E')
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
  eapply agree_on_trans. eapply agree_on_sym; eauto using agree_on_incl.
  eapply RA; eauto. eapply restr_iff in H4; dcr; subst; eauto.
Qed.


Inductive approx' 
  : list (option (set var)) -> F.block -> Prop :=
  approxI' DL o Z E s DL'
  :  (forall G, o = Some G -> of_list Z ∩ G [=] ∅ /\
           exists a, getAnn a [=] (G ∪ of_list Z) 
                /\ srd (restrict (Some G::DL) G) s a
                /\ live_sound DL' s a)
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
  Grab Existential Variables. eassumption.
Qed.

Unset Printing Records.

Lemma srd_preservation (E E':onv val) L L' s s' DL (G:set var) DA a
  (SRD:srd DA s a)
  (RA:rd_agree DA L E)
  (A: AIR2 approx' DA L)
  (LV:live_sound DL s a)
  (S:F.step (L, E, s) (L',E',s'))
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

  + inv LV. do 3 eexists; repeat split; eauto.
    hnf; intros.
    destruct n; inv H; inv H0. simpl.
    eapply agree_on_refl. 
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
  | srdSimI (E EI:onv val) L s AL DL a
  (SRD:srd AL s a)
  (RA:rd_agree AL L E)
  (A: AIR2 approx' AL L)
  (AG:agree_on (getAnn a) E EI)
  (LV:live_sound DL s a)
  : srdSim (L, E, s) (strip L, EI,s).

Lemma srdSim_sim σ1 σ2
  : srdSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; inv SRD; inv LV; simpl in *; try provide_invariants_2.
  + case_eq (exp_eval E e); intros.
    one_step.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto.
    eapply srdSim_sim; econstructor; 
    eauto using approx_restrict, rd_agree_update.
    eapply agree_on_update_same; eapply agree_on_incl; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite <- exp_eval_live in def; eauto. congruence.
  + case_eq (exp_eval E e); intros.
    exploit exp_eval_live_agree; eauto.
    case_eq (val2bool v); intros.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    one_step.
    eapply srdSim_sim; econstructor; eauto using agree_on_incl.
    exploit exp_eval_live_agree; eauto.
    no_step.
  + no_step. simpl. eapply exp_eval_live; eauto.
  + decide (length Z0 = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    - exploit omap_exp_eval_live_agree; eauto.
      pose proof (map_get_1 stripB H1).
      one_step.
      eapply srdSim_sim. rewrite drop_strip.  
      simpl. simpl counted in *.
      specialize (H3 _ H5); dcr. rewrite H2 in A1,H13.
      econstructor; simpl; eauto using approx_restrict.
      eapply rd_agree_update_list; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
      eapply (RA _ _ _ H1 H).
      eapply update_with_list_agree. rewrite H12.
      rewrite union_comm. rewrite union_minus_remove.
      pose proof (RA _ _ G' H1 H); dcr. simpl in *.
      eapply agree_on_sym. eapply agree_on_incl; eauto using incl_minus.
      eapply agree_on_trans; eauto. eapply agree_on_sym. hnf in RA.
      eapply agree_on_incl; eauto.
      exploit omap_length; eauto. rewrite map_length. congruence.
    - exploit omap_exp_eval_live_agree; eauto.
      no_step. 
    - no_step. get_functional; subst; simpl in *; congruence.
      unfold strip in *.
      edestruct map_get_4; eauto; dcr; get_functional; subst; simpl in *. 
      congruence.
  + one_step.
    eapply srdSim_sim; econstructor; eauto.
    hnf; intros.
    destruct n; inv H1; inv H2. simpl.
    eapply agree_on_refl. 
    eapply RA; eauto. 

    econstructor; eauto using agree_on_incl. econstructor; eauto.
    intros. inv H1. split. 
    split; cset_tac; isabsurd; eauto. 
    eexists. split; eauto. cset_tac; intuition.
    decide (a ∈ of_list Z); intuition.
    eapply agree_on_incl; eauto.
Qed.

Lemma srd_implies_invariance DL s a
: live_sound DL s a -> params_match nil s -> srd nil s a -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim. 
  econstructor; eauto using AIR2; isabsurd; reflexivity.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
