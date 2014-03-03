Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Liveness ParamsMatch Sim.

Set Implicit Arguments.

(* renamed apart, coincides with classic SSA condition *)
Inductive ssa : set var -> stmt -> set var -> Prop :=
  | ssaExp x e s D D'
    : x ∉ D 
      -> (Exp.freeVars e) ⊆ D
      -> ssa (D ∪ {{x}}) s D'
      -> ssa D (stmtExp x e s) D'
  | ssaIf  D D' Ds Dt x s t
    : x ∈ D
    -> Ds ∩ Dt [=] D
    -> Ds ∪ Dt [=] D'
    -> ssa D s Ds 
    -> ssa D t Dt
    -> ssa D (stmtIf x s t) D'
  | ssaRet D D' x
    : x ∈ D
    -> D [=] D'
    -> ssa D (stmtReturn x) D'
  | ssaGoto D D' f Y
    : of_list Y ⊆ D 
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
  intros. general induction H1.
  econstructor. rewrite <- H2; eauto. rewrite <- H2; eauto.
  eapply IHssa; eauto. rewrite H2; reflexivity. 
  
  econstructor. rewrite <- H2; eauto. rewrite <- H2; eauto. rewrite <- H3; eauto. 
  eapply IHssa1; eauto; reflexivity.
  eapply IHssa2; eauto; reflexivity.
  
  econstructor. rewrite <- H1; eauto. rewrite <- H1, H0; eauto.
  econstructor. rewrite <- H1; eauto. rewrite <- H1, H0; eauto.

  econstructor. rewrite <- H2; eauto.
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
  cset_tac; intuition. specialize (IHssa _ H2). cset_tac; intuition.
  cset_tac; intuition. rewrite H5; eauto.
  cset_tac; eauto.
  cset_tac; intuition. specialize (IHssa1 _ H4). cset_tac; intuition.
Qed.

Lemma ssa_minus D D' D'' s
  : notOccur D'' s -> ssa D s D' -> ssa (D \ D'') s (D' \ D'').
Proof.
  intros. general induction H0. 
  inv H2. econstructor. intro. cset_tac; eauto.
  eapply Exp.notOccur_freeVars in H8; eauto. rewrite meet_comm in H8.
  rewrite <- H0. rewrite minus_inane_set; eauto. reflexivity.
  assert ((D \ D'') ∪ {{x}} [=] (D ∪ {{x}}) \ D''). cset_tac. 
  unfold Equivalence.equiv, _eq; simpl. 
  split; intuition. subst; eauto. rewrite H3. eapply IHssa; eauto.
  
  inv H2. rewrite <- H0, <- H1, minus_dist_union, minus_dist_intersection.
  econstructor. rewrite <- H0 in H. cset_tac; eauto. reflexivity. reflexivity.
  rewrite <- minus_dist_intersection, H0. eapply IHssa1; eauto.
  rewrite <- minus_dist_intersection, H0. eapply IHssa2; eauto.
  econstructor. inv H1. eauto using in_in_minus. rewrite H0. reflexivity.
  econstructor. inv H1. hnf; intros. eapply in_in_minus; eauto. 

  intros. cset_tac; firstorder.
  cset_tac; firstorder.
  
  inv H2. rewrite <- H0, <- H1. rewrite minus_dist_union. rewrite minus_dist_intersection. 
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
      -> (Exp.freeVars e) ⊆ D
      -> shadowing_free (D ∪ {{x}}) s
      -> shadowing_free D (stmtExp x e s)
  | shadowing_freeIf D x s t
    : x ∈ D
    -> shadowing_free D s 
    -> shadowing_free D t
    -> shadowing_free D (stmtIf x s t)
  | shadowing_freeRet D x
    : x ∈ D
    -> shadowing_free D (stmtReturn x)
  | shadowing_freeGoto D f Y
    : of_list Y ⊆ D 
    -> shadowing_free D (stmtGoto f Y)
  | shadowing_freeLet D s t Z
    : of_list Z ∩ D [=] ∅
    -> shadowing_free (of_list Z ∪ D) s
    -> shadowing_free D t
    -> shadowing_free D (stmtLet Z s t).

Definition restr (G:set var) (o:option (set var)) :=
  match o with
    | None => None
    | Some G' => if [G' ⊆ G] then Some G' else None
  end.

Lemma restr_iff G o G'
  : restr G o = Some G' <-> G' ⊆ G /\ o = Some G'.
Proof.
  unfold restr; destruct o; intros. 
  destruct if; intuition; try inv H; try inv H1; eauto; isabsurd.
  split; intros; dcr; congruence.
Qed.

Lemma restr_idem G o G'
  : G' ⊆ G -> restr G' (restr G o) = restr G' o.
Proof.
  unfold restr; destruct o. repeat destruct if; eauto; isabsurd. 
  intros. exfalso. eapply n; cset_tac; intuition.
  eauto.
Qed.

Lemma restr_comm o G G'
  : restr G' (restr G o) = restr G (restr G' o).
Proof.
  destruct o; unfold restr; repeat destruct if; eauto; isabsurd.
Qed.

Instance restr_morphism
  : Proper (Equal ==> option_eq Equal ==> option_eq Equal) restr.
Proof.
  unfold Proper, respectful; intros.
  destruct x0,y0; unfold restr; 
  repeat destruct if; try econstructor;
  inv H0; eauto. 
  exfalso. eapply n. rewrite <- H3, <- H; eauto.
  exfalso. eapply n. rewrite H3, H; eauto.
Qed.

Instance restr_morphism_eq
  : Proper (Equal ==> eq ==> eq) restr.
Proof.
  unfold Proper, respectful; intros.
  destruct x0,y0; unfold restr; 
  repeat destruct if; try econstructor;
  inv H0; eauto. 
  exfalso. eapply n. rewrite <- H; eauto.
  exfalso. eapply n. rewrite H; eauto.
Qed.

Definition restrict (DL:list (option (set var))) (G:set var)
  := List.map (restr G) DL.

Lemma restrict_idem DL G G'
  : G ⊆ G' -> restrict (restrict DL G') G = restrict DL G.
Proof.
  general induction DL; simpl; eauto.
  f_equal; eauto using restr_idem.
Qed.

Lemma restrict_incl G G' DL
 : G' ⊆ G -> restrict (Some G'::DL) G = Some G'::restrict DL G.
Proof.
  intros. unfold restrict, List.map; f_equal.
  eapply restr_iff; eauto.
Qed.

Lemma restrict_not_incl G G' DL
 : ~G' ⊆ G -> restrict (Some G'::DL) G = None::restrict DL G.
Proof.
  intros. unfold restrict, List.map; f_equal.
  unfold restr. destruct if; firstorder.
Qed.

Lemma restrict_comm DL G G'
: restrict (restrict DL G) G' = restrict (restrict DL G') G.
Proof.
  general induction DL; simpl; eauto. f_equal; eauto using restr_comm.
Qed.

Instance restrict_morphism
  : Proper (list_eq (option_eq Equal) ==> 
                    Equal ==> list_eq (option_eq Equal)) restrict.
Proof.
  unfold Proper, respectful; intros.
  general induction H; simpl; try econstructor; eauto.
  rewrite H1, H. reflexivity.
Qed.

Instance restrict_morphism_eq
  : Proper (eq ==> Equal ==> eq) restrict.
Proof.
  unfold Proper, respectful; intros; subst. 
  general induction y; simpl; try econstructor; eauto.
  f_equal. rewrite H0; reflexivity. eauto.
Qed.

Inductive srd : list (option (set var)) -> stmt -> ann live -> Prop :=
 | srdExp DL x e s lv al
    : srd (restrict DL (lv\{{x}})) s al
    -> srd DL (stmtExp x e s) (annExp lv al)
  | srdIf DL x s t lv als alt
    :  srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf x s t) (annIf lv als alt)
  | srdRet x DL lv
    : srd DL (stmtReturn x) (annReturn lv)
  | srdGoto DL lv G' f Y
    : get DL (counted f) (Some G')
    -> G' ⊆ lv
    -> srd DL (stmtGoto f Y) (annGoto lv)
  | srdLet DL s t Z lv als alt
    : srd (restrict (Some (getAnn als \ of_list Z)::DL) (getAnn als \ of_list Z))
          s als
    -> srd (Some (getAnn als \ of_list Z)::DL) t alt
    -> srd DL (stmtLet Z s t) (annLet lv als alt).

Definition peq := prod_eq (@feq var var _ _) (@Equal var _ _).

Lemma list_eq_get {X:Type} (L L':list X) eqA n x
  : list_eq eqA L L' -> get L n x -> exists x', get L' n x' /\ eqA x x'.
Proof.
  intros. general induction H.
  inv H0. 
  inv H1. eauto using get. 
  edestruct IHlist_eq; eauto. firstorder using get.
Qed.

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
    destruct_prop(Exp.freeVars e ⊆ G);
      solve [ left; econstructor; eauto | right; intro A; inv A; eauto ].
  + edestruct IHs1, IHs2; destruct_prop(x ∈ G);
      solve [ left; econstructor; eauto | right; intro A; inv A; eauto ].
  + destruct_prop (of_list Y ⊆ G);
    destruct (get_dec DL (counted l)) as [[[G'|] ?]|?];
    (try destruct_prop (G' ⊆ G));
      solve [ left; econstructor; eauto | right; intro A; inv A; try (get_functional; subst); eauto ].
  + destruct_prop (x ∈ G).
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


Fixpoint freeVar_live (s:stmt) : ann live :=
  match s with
    | stmtExp x e s0 => annExp (freeVars s) (freeVar_live s0)
    | stmtIf x s1 s2 => annIf (freeVars s) (freeVar_live s1) (freeVar_live s2)
    | stmtGoto l Y => annGoto (freeVars s)
    | stmtReturn x => annReturn (freeVars s)
    | stmtLet Z s1 s2 => annLet (freeVars s) (freeVar_live s1) (freeVar_live s2)
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

Fixpoint bounded (DL:list (option (set var))) (G:set var) :=
  match DL with
    | nil => True
    | Some G'::DL => G' ⊆ G /\ bounded DL G
    | None::DL => bounded DL G
  end.

Instance bounded_morphism_subset
  : Proper (eq ==> Subset ==> impl) bounded.
Proof.
  unfold Proper, respectful, impl; intros.
  subst. general induction y; simpl; eauto.
  destruct a; simpl in *; cset_tac; intuition. 
  eapply IHy; eauto. eapply IHy; eauto.
Qed.

Instance bounded_morphism 
  : Proper (eq ==> Equal ==> iff) bounded.
Proof.
  unfold Proper, respectful, impl; intros; split; intros; subst;
  eapply double_inclusion in H0; dcr. 
  rewrite <- H; eauto.
  rewrite <- H2; eauto.
Qed.

Lemma bounded_get DL G G' n
  : bounded DL G -> get DL n (Some G') -> G' ⊆ G.
Proof.
  intros. general induction H0; simpl in *; intuition.
  destruct x'; eapply IHget; intuition.
Qed.

Lemma bounded_restrict DL G' G 
  : G' ⊆ G -> bounded (restrict DL G') G. 
Proof. 
  general induction DL; simpl; eauto.
  case_eq (restr G' a); intros; try split; eauto.
  eapply restr_iff in H0; intuition.
  transitivity G'; eauto.
Qed.

Lemma bounded_restrict_eq DL G' G 
  : G ⊆ G' -> bounded DL G -> restrict DL G' = DL. 
Proof. 
  general induction DL; simpl; eauto.
  case_eq (restr G' a); intros; try split; eauto.
  eapply restr_iff in H1; intuition. 
  subst; simpl in *; dcr.
  f_equal. eapply (IHDL _ _ H H3).
  destruct a; unfold restr in H1; dcr.
  destruct if in H1; isabsurd. simpl in H0.
  exfalso. eapply n. dcr. rewrite H2; eauto.
  f_equal. eapply IHDL; eauto.
Qed.



Inductive fstNoneOrR {X Y:Type} (R:X->Y->Prop)
  : option X -> option Y -> Prop :=
| fstNone (x:option Y) : fstNoneOrR R None x
| bothR (x:X) (y:Y) : R x y -> fstNoneOrR R (Some x) (Some y)
.


Lemma restrict_subset DL DL' G G'
: list_eq (fstNoneOrR eq) DL DL' 
  -> G ⊆ G'
  -> list_eq (fstNoneOrR eq) (restrict DL G) (restrict DL' G').
Proof.
  intros. induction H; simpl; econstructor; eauto.
  inv H. simpl. econstructor.
  unfold restr. repeat destruct if; try econstructor; eauto.
  exfalso. eapply n. transitivity G; eauto.
Qed.


Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a 
   -> list_eq (fstNoneOrR eq) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  + econstructor. 
    eapply IHsrd; eauto. eapply restrict_subset; eauto. cset_tac; intuition.
  + destruct (list_eq_get H1 H); eauto; dcr. inv H4.
    econstructor; eauto. 
  + econstructor; eauto. 
    eapply IHsrd1. constructor; eauto. eapply bothR.
    constructor. reflexivity. eauto. rewrite H. eapply incl_minus_lr; intuition.
    eapply IHsrd1; eauto. repeat rewrite restrict_incl; try reflexivity.
    econstructor. econstructor; reflexivity. 
    eapply restrict_subset; intuition. reflexivity.
Qed.

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


Definition invariant (s:stmt) :=
  forall (E:env var), sim (nil:list F.block,E,s) (nil:list I.block,E,s).

Definition rd_agree (DL:list (option (set var)))
           L (E:env val)
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

Lemma rd_agree_update_list DL L E E' (G G':set var) Z Y n
 (RA:rd_agree DL L E)
 (ZD:of_list Z ∩ G' [=] ∅)
 (LEQ:length Z = length Y)
 (AG:agree_on G' E E')
: rd_agree (restrict (drop n DL) G') (drop n L) (updE E' E Z Y).
Proof.
  hnf; intros.
  assert (G'0 ⊆ G'). eapply bounded_get; eauto. eapply bounded_restrict; reflexivity.
  assert (G'0 [=] G'0 \ of_list Z) by (split; cset_tac; intuition eauto).
  rewrite H2. unfold updE. eapply update_with_list_agree_minus. rewrite lookup_list_length; eauto.

  unfold restrict in H0. rewrite drop_map in H0. 
  eapply get_drop in H. eapply get_drop in H0.
  eapply map_get_4 in H0; dcr.
  eapply agree_on_trans. eapply agree_on_sym; eauto using agree_on_incl.
  eapply RA; eauto. eapply restr_iff in H4; dcr; subst; eauto.
Qed.

Inductive approx' 
  : list (option (set var)) -> F.block -> Prop :=
  approxI' DL o Z E s
  :  (forall G, o = Some G -> srd (restrict (Some G::DL) G) (G ∪ of_list Z) s 
                              /\ of_list Z ∩ G [=] ∅ )
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
Qed.

Unset Printing Records.

Lemma srd_preservation (E E':env val) L L' s s' (DL DL':list (option (set var))) (G:set var)
  (SRD:srd DL G s)
  (RA:rd_agree DL L E)
  (A: AIR2 approx' DL L)
  (PM:params_match L s)
  (S:F.step (L, E, s) (L',E',s'))
  : exists DL' G', srd DL' G' s' 
                   /\ rd_agree DL' L' E' 
                   /\ AIR2 approx' DL' L'. 
Proof.
  destruct SRD; try inv S; try params_match_tac.

  + do 2 eexists; repeat split; try eassumption;
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.

  + do 2 eexists; eauto.
  + do 2 eexists; eauto.

  + provide_invariants_2. specialize (H6 _ H7); dcr.
    rewrite H5 in H8. simpl in *.
    do 2 eexists; repeat split; simpl; eauto.
    eapply rd_agree_update_list; eauto. eapply (RA _ _ _ H4 H0).
    eauto using approx_restrict.
    

  + do 2 eexists; repeat split; eauto.
    hnf; intros.
    destruct n; inv H1; inv H2. simpl.
    eapply agree_on_refl. 
    eapply RA; eauto.

    econstructor; eauto using agree_on_incl. econstructor; eauto.
    intros. inv H1. split. eauto.
    split; cset_tac; isabsurd; eauto. eapply H in H4. cset_tac; intuition.
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
  | srdSimI (E EI:env val) L s (DL:list (option (set var))) (G:set var)
  (SRD:srd DL G s)
  (RA:rd_agree DL L E)
  (A: AIR2 approx' DL L)
  (PM:params_match L s)
  (AG:agree_on G E EI)
  : srdSim (L, E, s) (strip L, EI,s).

Lemma srdSim_sim σ1 σ2
  : srdSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; inv SRD; simpl; try provide_invariants_2; try params_match_tac.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto. eapply live_exp_sound_incl; eauto.
    eapply live_freeVars.
    eapply srdSim_sim; econstructor; 
    eauto using agree_on_update_any_same, approx_restrict, rd_agree_update.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite <- exp_eval_live in def; eauto. congruence.
    eapply live_exp_sound_incl; eauto using live_freeVars.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor. rewrite <- AG; eauto.
    eapply srdSim_sim; econstructor; eauto.
    eapply simS; try eapply plusO.
    eapply F.stepIfF; eauto. 
    rewrite AG in H4; eauto.
    eapply I.stepIfF; eauto. 
    eapply srdSim_sim; econstructor; eauto.
  + eapply simE; try eapply star_refl; simpl; eauto; try stuck.
    rewrite AG; eauto.
  + eapply simS; try eapply plusO.
    econstructor; eauto.
    pose proof (map_get_1 stripB H2).
    econstructor; eauto. eauto.
    eapply srdSim_sim. rewrite drop_strip.  
    simpl. simpl counted in *.
    specialize (H4 _ H5); dcr. rewrite H3 in H8.
    econstructor; simpl; eauto using approx_restrict.
    eapply rd_agree_update_list; eauto.
    eapply (RA _ _ _ H2 H0).

    simpl; unfold updE. 
    erewrite lookup_list_agree; eauto using agree_on_incl.
    eapply update_with_list_agree. rewrite union_comm. rewrite union_minus_remove.
    pose proof (RA _ _ G' H2 H0); dcr. simpl in *.
    eapply agree_on_sym. eapply agree_on_incl; eauto using incl_minus.
    eapply agree_on_trans; eauto. eapply agree_on_sym. hnf in RA.
    eapply agree_on_incl; eauto.
    rewrite lookup_list_length; eauto.

  + eapply simS; try (eapply plusO; econstructor).
    eapply srdSim_sim; econstructor; eauto.
    hnf; intros.
    destruct n; inv H3; inv H4. simpl.
    eapply agree_on_refl. 
    eapply RA; eauto. 

    econstructor; eauto using agree_on_incl. econstructor; eauto.
    intros. inv H3. split. eauto.
    split; cset_tac; isabsurd; eauto. eapply H in H6. cset_tac; intuition.
Qed.

Lemma srd_implies_invariance G s
: params_match nil s -> srd nil G s -> invariant s.
Proof.
  intros. hnf; intros. eapply srdSim_sim. 
  econstructor; eauto using AIR2; isabsurd; reflexivity.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)