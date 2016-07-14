Require Import CSet Util Get Drop Var Map OptionR AllInRel OUnion MoreList.

Set Implicit Arguments.

Definition restr (G:set var) (o:option (set var)) :=
  match o with
    | None => None
    | Some G' => if [G' ⊆ G] then Some G' else None
  end.

Lemma restr_iff G o G'
  : restr G o = Some G' <-> G' ⊆ G /\ o = Some G'.
Proof.
  unfold restr; destruct o; intros.
  cases; split; intros A; inv A; isabsurd; eauto.
  split; intros; dcr; congruence.
Qed.

Lemma restr_idem G o G'
  : G' ⊆ G -> restr G' (restr G o) = restr G' o.
Proof.
  unfold restr; destruct o; eauto. repeat cases; eauto.
  intros. exfalso. eapply NOTCOND. rewrite <- H. eauto.
Qed.

Lemma restr_comm o G G'
  : restr G' (restr G o) = restr G (restr G' o).
Proof.
  destruct o; unfold restr; eauto.
  repeat cases; eauto.
  exfalso; eauto.
Qed.

Instance restr_morphism
  : Proper (Equal ==> option_eq Equal ==> option_eq Equal) restr.
Proof.
  unfold Proper, respectful; intros.
  destruct x0,y0; unfold restr;
  repeat cases; try econstructor;
  inv H0; eauto; cset_tac.
Qed.

Instance restr_morphism_eq
  : Proper (Equal ==> eq ==> eq) restr.
Proof.
  unfold Proper, respectful; intros.
  destruct x0,y0; unfold restr;
  repeat cases; try econstructor;
  eauto; cset_tac.
Qed.

Instance restr_m2
  : Proper (Equal ==> pointwise_relation _ eq) restr.
Proof.
  unfold Proper, respectful, pointwise_relation, restr; intros; subst.
  repeat cases; eauto.
  - exfalso. eapply NOTCOND. rewrite <- H. eauto.
  - exfalso. eapply NOTCOND. rewrite H. eauto.
Qed.

Lemma restr_comp_meet G o G'
  : restr G' (restr G o) = restr (G ∩ G') o.
Proof.
  unfold restr; destruct o; eauto.
  repeat cases; eauto.
  - exfalso. eapply NOTCOND. cset_tac.
  - exfalso. rewrite COND0 in NOTCOND. eapply NOTCOND. cset_tac.
  - rewrite COND in NOTCOND. exfalso; eapply NOTCOND. cset_tac.
Qed.

Lemma restrict_comp_meet DL G G'
  : restr G' ⊝ (restr G ⊝ DL) = restr (G ∩ G') ⊝ DL.
Proof.
  rewrite map_map.
  setoid_rewrite restr_comp_meet. reflexivity.
Qed.

Lemma restrict_idem DL G G'
  : G ⊆ G' -> restr G ⊝ (restr G' ⊝ DL) = restr G ⊝ DL.
Proof.
  rewrite restrict_comp_meet; intros.
  rewrite meet_comm, <- incl_meet; eauto.
Qed.

(*
Instance restrict_morphism
  : Proper (PIR2 (option_eq Equal) ==>
                    Equal ==> PIR2 (option_eq Equal)) (restrict.
Proof.
  unfold Proper, respectful; intros.
  general induction H; simpl; try econstructor; eauto.
  rewrite pf, H0. reflexivity.
Qed.

Instance restrict_morphism_eq
  : Proper (eq ==> Equal ==> eq) restrict.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y; simpl; try econstructor; eauto.
  f_equal. rewrite H0; reflexivity. eauto.
Qed.
 *)

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
  subst.
  general induction y; simpl; eauto.
  destruct a; simpl in *; cset_tac; intuition.
Qed.

Instance bounded_morphism
  : Proper (eq ==> Equal ==> iff) bounded.
Proof.
  unfold Proper, respectful, impl; intros; split; intros; subst;
  eapply double_inclusion in H0; dcr.
  rewrite <- H; eauto.
  rewrite <- H2; eauto.
Qed.

Instance bounded_instance_1 DL
  : Proper (Equal ==> flip impl) (bounded DL).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  rewrite H; eauto.
Qed.

Lemma bounded_get DL G G' n
  : bounded DL G -> get DL n (Some G') -> G' ⊆ G.
Proof.
  intros. general induction H0; simpl in *; eauto.
  destruct x'; eapply IHget; intuition.
Qed.

Lemma bounded_restrict DL G' G
  : G' ⊆ G -> bounded (restr G' ⊝ DL) G.
Proof.
  general induction DL; simpl; eauto.
  case_eq (restr G' a); intros; try split; eauto.
  eapply restr_iff in H0; cset_tac; intuition.
Qed.

Lemma bounded_restrict_eq DL G' G
  : G ⊆ G' -> bounded DL G -> restr G' ⊝ DL = DL.
Proof.
  general induction DL; simpl; eauto.
  case_eq (restr G' a); intros; try split; eauto.
  - eapply restr_iff in H1; dcr; simpl in *.
    subst; dcr.
    f_equal. eauto.
  - destruct a; unfold restr in H1; dcr.
    + exfalso. cases in H1; isabsurd.
      simpl in H0; dcr. cset_tac.
    + f_equal. eauto.
Qed.

Lemma restrict_subset2 DL DL' G G'
: PIR2 (fstNoneOrR (flip Subset)) DL DL'
  -> G ⊆ G'
  -> PIR2 (fstNoneOrR (flip Subset)) (restr G ⊝ DL) (restr G' ⊝ DL').
Proof.
  intros. induction H; simpl; econstructor; eauto.
  - inv pf.
    + simpl. econstructor.
    + unfold restr. repeat cases; try econstructor; eauto.
      exfalso. unfold flip in H1. rewrite H0 in COND. cset_tac.
Qed.


Lemma restrict_subset DL DL' G G'
: PIR2 (fstNoneOrR Equal) DL DL'
  -> G ⊆ G'
  -> PIR2 (fstNoneOrR Equal) (restr G ⊝ DL) (restr G' ⊝ DL').
Proof.
   intros. induction H; simpl; econstructor; eauto.
  - inv pf.
    + simpl. econstructor.
    + unfold restr. repeat cases; try econstructor; eauto.
      cset_tac.
Qed.

Definition lookup_seto (ϱ:var->var) (x:option (set var)) : option (set var):=
  match x with
    | None => None
    | Some x => Some (lookup_set ϱ x)
  end.

Lemma lookup_seto_restr G s ϱ
  : lookup_seto ϱ (restr G ⎣ s ⎦) =
    if [ s ⊆ G ] then Some (lookup_set ϱ s) else None.
Proof.
  unfold restr; cases; reflexivity.
Qed.

Definition live_global (p:set var * list var) := Some (fst p \ of_list (snd p)).

Lemma bounded_map_lookup G (ϱ: var -> var) DL
  : bounded DL G -> bounded (lookup_seto ϱ ⊝ DL) (lookup_set ϱ G).
Proof.
  general induction DL; simpl; eauto.
  destruct a; simpl in *; dcr; eauto using lookup_set_incl.
Qed.

Lemma restrict_incl_ext DL G G' D
:  bounded DL D
   -> G ∩ D [=] G' ∩ D
   -> restr G ⊝ DL = restr G' ⊝ DL.
Proof.
  intros.
  general induction DL; simpl in *; try destruct a; dcr; eauto.
  f_equal; eauto.
  - unfold restr. repeat cases; eauto.
    exfalso. eapply NOTCOND. eapply meet_incl_eq in H0; eauto.
    rewrite meet_comm in H0. rewrite <- incl_meet in H0; eauto.
    rewrite H0. eapply meet_incl; reflexivity.
    exfalso. eapply NOTCOND. eapply meet_incl_eq in H0; eauto. symmetry in H0.
    rewrite meet_comm in H0. rewrite <- incl_meet in H0; eauto.
    rewrite H0. eapply meet_incl; reflexivity.
  - f_equal; eauto.
Qed.

Lemma list_eq_special DL ϱ A B A'
: A ⊆ B
  -> lookup_set ϱ A ⊆ A'
  -> PIR2 (fstNoneOrR Equal)
         (lookup_seto ϱ ⊝ (restr A ⊝ DL))
         (restr A' ⊝ (lookup_seto ϱ ⊝ (restr B ⊝ DL))).
Proof.
  intros. general induction DL; simpl. econstructor.
  unfold restr. unfold lookup_seto.
  destruct a; repeat cases; eauto using PIR2, @fstNoneOrR.
  - exfalso. eapply NOTCOND. lset_tac; eauto. eapply H0; lset_tac.
  - exfalso. eapply NOTCOND; rewrite <- H. eauto.
Qed.

Lemma list_eq_fstNoneOrR_incl DL ϱ A B
: A ⊆ B ->
  PIR2 (fstNoneOrR Equal)
       (lookup_seto ϱ ⊝ (restr A ⊝ DL))
       (lookup_seto ϱ ⊝ (restr B ⊝ DL)).
Proof.
  intros. general induction DL; simpl.
  - econstructor.
  - unfold restr; destruct a; repeat cases;
      simpl; econstructor; eauto; try econstructor; eauto.
    exfalso. cset_tac; intuition.
Qed.

Lemma bounded_app L L' s
: bounded (L++L') s <-> bounded L s /\ bounded L' s.
Proof.
  general induction L; simpl.
  - intuition.
  - destruct a; edestruct (IHL L' s); eauto. intuition.
Qed.


Inductive fstNoneOrR' {X Y:Type} (R:X->Y->Prop)
  : option X -> Y -> Prop :=
| fstNone' (y:Y) : fstNoneOrR' R None y
| bothR' (x:X) (y:Y) : R x y -> fstNoneOrR' R (Some x) y
.

Definition eqReq := (fstNoneOrR' (fun (s : set var) (t : set var * list var) =>
                                   s [=] fst t \ of_list (snd t))).

Lemma restrict_eqReq DL DL' G
: PIR2 eqReq DL DL'
  -> PIR2 eqReq (restr G ⊝ DL) DL'.
Proof.
  intros. induction H; simpl; econstructor; eauto.
  unfold restr. destruct pf. constructor.
  cases; eauto. subst. constructor; eauto. constructor.
Qed.

Lemma restrict_get DL lv n s
: get (restr lv ⊝ DL) n ⎣ s ⎦
  -> get DL n (Some s) /\ s ⊆ lv.
Proof.
  intros. general induction H.
  - destruct DL; simpl in *; isabsurd.
    inv Heql. unfold restr in H0. destruct o; isabsurd.
    + cases in H0.
      eauto using get. congruence.
  - destruct DL; simpl in *; isabsurd.
    inv Heql. edestruct IHget; eauto.
    eauto using get.
Qed.

Lemma get_bounded L D
: (forall n x, get L n (Some x) -> x ⊆ D)
  -> bounded L D.
Proof.
  general induction L; simpl; isabsurd; eauto.
  destruct a; eauto 50 using get.
Qed.

Lemma bounded_incl DL G G'
: bounded DL G
  -> G ⊆ G'
  -> bounded DL G'.
Proof.
  intros. rewrite <- H0; eauto.
Qed.

Lemma restrict_disj (DL : 〔؟⦃var⦄〕) (s t : ⦃var⦄)
  : (forall n u, get DL n (Some u) -> disj (s ∩ t) u)
    -> restr (s \ t) ⊝ DL = restr s ⊝ DL.
Proof.
  general induction DL; simpl; eauto.
  rewrite IHDL; eauto using get.
  unfold restr. destruct a; eauto.
  exploit H; eauto using get.
  repeat cases; eauto.
  - exfalso. rewrite COND in NOTCOND. cset_tac.
  - exfalso. eapply NOTCOND.
    intros a aIns.
    cset_tac. eapply H0; eauto. cset_tac.
Qed.


Hint Resolve bounded_incl.


Lemma PIR2_restrict A B s
:  A ≿ B
   -> restr s ⊝ A ≿ B.
Proof.
  intros. general induction H; simpl.
  - econstructor.
  - econstructor; eauto.
    + inv pf; simpl.
      * econstructor.
      * cases. econstructor; eauto. econstructor.
Qed.

Lemma restrict_get_Some L s t n
: get L n (Some s)
  -> s ⊆ t
  -> get (restr t ⊝ L) n (Some s).
Proof.
  intros. general induction H; simpl; eauto using get.
  - cases; eauto using get.
Qed.

Ltac inv_get_step_restrict dummy :=
  first [
         match goal with
         | [ H : get (restr ?G ⊝ ?DL) ?n (Some ?lv) |- _ ] =>
           eapply (@restrict_get DL G n lv) in H; destruct H as [H ?]
         end | inv_get_step ].

Tactic Notation "inv_get_step" := inv_get_step_restrict idtac.
Tactic Notation "inv_get" := inv_get' inv_get_step_restrict.

Lemma restrict_ifFstR B (R:⦃var⦄->B->Prop) DL GL G
: PIR2 (ifFstR R) DL GL
  -> PIR2 (ifFstR R) (restr G ⊝ DL) GL.
Proof.
  intros. induction H; simpl; eauto using PIR2, @ifFstR.
  unfold restr. destruct pf.
  - eauto using @PIR2, @ifFstR.
  - cases; eauto using PIR2, @ifFstR.
Qed.

Lemma PIR2_ifFstR_refl A (R:A->A->Prop) `{Reflexive _ R} L
  : PIR2 (ifFstR R) (Some ⊝ L) L.
Proof.
  eapply PIR2_get; intros; inv_get; eauto using @ifFstR with len.
Qed.
