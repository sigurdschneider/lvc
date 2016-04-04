Require Import CSet Util Get Drop Var Map Infra.Relations AllInRel.

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
  destruct if; split; intros A; inv A; isabsurd; eauto.
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
  : Proper (PIR2 (option_eq Equal) ==>
                    Equal ==> PIR2 (option_eq Equal)) restrict.
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
  eapply restr_iff in H0; cset_tac; intuition.
Qed.

Lemma bounded_restrict_eq DL G' G
  : G ⊆ G' -> bounded DL G -> restrict DL G' = DL.
Proof.
  general induction DL; simpl; eauto.
  case_eq (restr G' a); intros; try split; eauto.
  - eapply restr_iff in H1; dcr; simpl in *.
    subst; dcr.
    f_equal. eauto.
  - destruct a; unfold restr in H1; dcr.
    + exfalso. destruct if in H1; isabsurd.
      simpl in H0; dcr. eapply n. cset_tac.
    + f_equal. eapply IHDL; eauto.
Qed.

Lemma restrict_subset2 DL DL' G G'
: PIR2 (fstNoneOrR (flip Subset)) DL DL'
  -> G ⊆ G'
  -> PIR2 (fstNoneOrR (flip Subset)) (restrict DL G) (restrict DL' G').
Proof.
  intros. induction H; simpl; econstructor; eauto.
  - inv pf.
    + simpl. econstructor.
    + unfold restr. repeat destruct if; try econstructor; eauto.
      exfalso. eapply n. transitivity G; eauto. rewrite <- s; eauto.
Qed.


Lemma restrict_subset DL DL' G G'
: PIR2 (fstNoneOrR Equal) DL DL'
  -> G ⊆ G'
  -> PIR2 (fstNoneOrR Equal) (restrict DL G) (restrict DL' G').
Proof.
   intros. induction H; simpl; econstructor; eauto.
  - inv pf.
    + simpl. econstructor.
    + unfold restr. repeat destruct if; try econstructor; eauto.
      exfalso. eapply n. transitivity G; eauto. rewrite <- s; eauto.
      rewrite H1; reflexivity.
Qed.


Lemma restr_comp_meet G o G'
  : restr G' (restr G o) = restr (G ∩ G') o.
Proof.
  unfold restr; destruct o.
  repeat destruct if; eauto; isabsurd.
  - cset_tac; intuition.
  - exfalso; eapply n. rewrite s1. cset_tac; intuition.
  - exfalso; eapply n. rewrite s0. cset_tac; intuition.
  - eauto.
Qed.

Lemma restrict_comp_meet DL G G'
  : restrict (restrict DL G) G' = restrict DL (G ∩ G').
Proof.
  general induction DL; simpl; eauto.
  f_equal; eauto using restr_comp_meet.
Qed.

Definition lookup_set_option (ϱ:var->var) (x:option (set var)) : option (set var):=
  match x with
    | None => None
    | Some x => Some (lookup_set ϱ x)
  end.

Definition map_lookup (ϱ:var -> var) := List.map (lookup_set_option ϱ).

Definition live_global (p:set var * list var) := Some (fst p \ of_list (snd p)).
Definition live_globals (Lv:list (set var * list var)) := List.map live_global Lv.

Lemma bounded_map_lookup G (ϱ: var -> var) DL
  : bounded DL G -> bounded (map_lookup ϱ DL) (lookup_set ϱ G).
Proof.
  general induction DL; simpl; eauto.
  destruct a; simpl in *; dcr; eauto using lookup_set_incl.
Qed.

Lemma restrict_incl_ext DL G G' D
:  bounded DL D
   -> G ∩ D [=] G' ∩ D
   -> restrict DL G = restrict DL G'.
Proof.
  intros.
  general induction DL; simpl in *; try destruct a; dcr; eauto.
  f_equal; eauto.
  unfold restr. repeat destruct if; eauto.
  exfalso. eapply n. eapply meet_incl_eq in H0; eauto.
  rewrite meet_comm in H0. rewrite <- incl_meet in H0; eauto.
  rewrite H0. eapply meet_incl; reflexivity.
  exfalso. eapply n. eapply meet_incl_eq in H0; eauto. symmetry in H0.
  rewrite meet_comm in H0. rewrite <- incl_meet in H0; eauto.
  rewrite H0. eapply meet_incl; reflexivity.
  f_equal; eauto.
Qed.

Lemma list_eq_special DL ϱ A B A'
: A ⊆ B
  -> lookup_set ϱ A ⊆ A'
  -> PIR2 (fstNoneOrR Equal)
         (map_lookup ϱ (restrict DL A))
         (restrict (map_lookup ϱ (restrict DL B)) A').
Proof.
  intros. general induction DL; simpl. econstructor.
  unfold restr. unfold lookup_set_option.
  destruct a; repeat destruct if;econstructor; eauto; try econstructor; eauto.
  - exfalso. eapply n. lset_tac. eapply H0. eapply lookup_set_incl; lset_tac.
  - exfalso. eapply n. cset_tac.
Qed.

Lemma list_eq_fstNoneOrR_incl DL ϱ A B
: A ⊆ B ->
  PIR2 (fstNoneOrR Equal)
       (map_lookup ϱ (restrict DL A))
       (map_lookup ϱ (restrict DL B)).
Proof.
  intros. general induction DL; simpl.
  - econstructor.
  - unfold restr; destruct a; repeat destruct if;
      simpl; econstructor; eauto; try econstructor; eauto.
    exfalso. cset_tac; intuition.
Qed.

Lemma restrict_app L L' s
: restrict (L++L') s = restrict L s ++ restrict L' s.
Proof.
  general induction L; simpl; eauto using f_equal.
Qed.

Lemma restrict_length L s
: length (restrict L s) = length L.
Proof.
  unfold restrict. rewrite map_length; eauto.
Qed.

Lemma bounded_app L L' s
: bounded (L++L') s <-> bounded L s /\ bounded L' s.
Proof.
  general induction L; simpl; (try destruct a); (try edestruct IHL); eauto; intuition.
  eapply H; eauto. eapply H; eauto.
  Grab Existential Variables. eapply s. eapply L'.
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
  : (forall n u, get DL n 「u」 -> disj (s ∩ t) u)
    -> restrict DL (s \ t) = restrict DL s.
Proof.
  general induction DL; simpl; eauto.
  rewrite IHDL; eauto using get.
  unfold restr. destruct a; eauto.
  exploit H; eauto using get.
  repeat destruct if; eauto.
  - exfalso. rewrite s1 in n. cset_tac.
  - exfalso. eapply n.
    intros a aIns.
    cset_tac. eapply H0; eauto. cset_tac.
Qed.


Hint Resolve bounded_incl.
