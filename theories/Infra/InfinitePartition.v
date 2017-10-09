Require Import Util CSet NaturalRep FreshNR StableFresh Even.
Require Import InfiniteSubset SafeFirstInfiniteSubset Take TakeSet.

Set Implicit Arguments.

Record inf_partition  X `{OrderedType X}  :=
  { part_1 : inf_subset X;
    part_2 : inf_subset X;
    part_disj : forall x, part_1 x -> part_2 x -> False;
    part_cover : forall x, part_1 x + part_2 x;
  }.

Arguments inf_partition X {H}.

Lemma part_dich  X `{OrderedType X}  (p:inf_partition X) x
  : (part_1 p x /\ (part_2 p x -> False)) \/ (part_2 p x /\ (part_1 p x -> False)).
Proof.
  destruct (part_cover p x);
    pose proof (part_disj p x); cset_tac.
Qed.

Definition even_part : inf_partition nat.
Proof.
  refine (Build_inf_partition even_inf_subset odd_inf_subset _ _).
  - intros.
    unfold even_inf_subset in H. simpl in H.
    unfold odd_inf_subset in H0. simpl in H0.
    unfold odd in H0. unfold negb in H0. cases in H0; eauto.
  - intros.
    unfold even_inf_subset, odd_inf_subset, odd, negb; simpl.
    cases; eauto.
Qed.

Definition even_part_pos : inf_partition positive.
Proof.
  refine (Build_inf_partition even_inf_subset_pos odd_inf_subset_pos _ _).
  - intros.
    unfold even_inf_subset in H. simpl in H.
    unfold odd_inf_subset in H0. simpl in H0.
    unfold odd in H0. unfold negb in H0. cases in H0; eauto.
  - intros.
    unfold even_inf_subset, odd_inf_subset, odd, negb; simpl.
    rewrite <- even_pos_fast_correct.
    eapply even_or_odd.
Qed.

Require Import SafeFirst.

Lemma fresh_variable_always_exists_in_inf_subset X `{NaturalRepresentationSucc X}
      `{@NaturalRepresentationMax X H H0}
      (lv:set X) (p:inf_subset X) n
: safe (fun x => x ∉ lv /\ p x) n.
Proof.
  - decide (_lt (SetInterface.fold max lv (ofNat 0)) n).
    + decide (p n).
      * econstructor. split; eauto.
        intro. cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
      * edestruct (inf_subset_inf p n); dcr. cbn in *.
        eapply (@safe_antitone _ _ _ _ _ _ _ x); eauto.
        econstructor; split; eauto.
        intro. cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
    + decide (p (succ (SetInterface.fold max lv (ofNat 0)))).
      * eapply safe_antitone. eauto.
        instantiate (1:=succ (SetInterface.fold max lv (ofNat 0))).
        econstructor. split; eauto. intro.
        cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        simpl in *. nr. omega.
      * edestruct (inf_subset_inf p (succ (fold max lv (ofNat 0))));
          dcr.
        eapply (@safe_antitone _ _ _ _ _ _ _ x).
        econstructor; split; eauto.
        cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. clear H6. nr. omega.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. clear H6. nr. omega.
        simpl in *. clear H6. nr. omega.
        Grab Existential Variables. eauto. eauto.
Qed.

(*
Lemma fresh_variable_always_exists_in_inf_subset' X `{OrderedType X}
      (lv:set X) (p:inf_subset X) n
: SafeFirstInfiniteSubset.safe p (fun x => x ∉ lv /\ p x) n.
Proof.
  - decide (_lt (SetInterface.fold OrderedTypeMax.nr_max lv (proj1_sig (inf_subset_least p))) n).
    + decide (p n).
      * econstructor; eauto. split; eauto.
        -- destr_sig; dcr; eauto.
        -- intro. cset_tac'.
           ++ eapply (@fold_max_lt X _ _ _ _) in H0; eauto.
             simpl in *. exfalso. nr. revert H0. destr_sig. dcr.
             intro. exploit H4; swap 1 2.
             etransitivity; [|eapply H3]; eauto.
             admit.
             simpl in *. omega.
           eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
           simpl in *. exfalso. nr. simpl in *. omega.
      * edestruct (inf_subset_inf p n); dcr. cbn in *.
        eapply (@safe_antitone _ _ _ _ _ _ _ x); eauto.
        econstructor; split; eauto.
        intro. cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
    + decide (p (succ (SetInterface.fold max lv (ofNat 0)))).
      * eapply safe_antitone. eauto.
        instantiate (1:=succ (SetInterface.fold max lv (ofNat 0))).
        econstructor. split; eauto. intro.
        cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H5; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        simpl in *. nr. omega.
      * edestruct (inf_subset_inf p (succ (fold max lv (ofNat 0))));
          dcr.
        eapply (@safe_antitone _ _ _ _ _ _ _ x).
        econstructor; split; eauto.
        cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. nr. omega.
        eapply (@fold_max_lt X _ _ _ _) in H8; eauto.
        simpl in *. exfalso. clear H6. nr. omega.
        simpl in *. clear H6. nr. omega.
        Grab Existential Variables. eauto. eauto.
Qed.
*)

Definition least_fresh_P X `{NaturalRepresentationSucc X}
      `{@NaturalRepresentationMax X H H0}
           (p:inf_subset X) (lv:set X) : X.
  refine (@safe_first X H _ _ (fun x => x ∉ lv /\ p x) _
                                              (proj1_sig (inf_subset_least p)) _).
  - eapply fresh_variable_always_exists_in_inf_subset; eauto.
Defined.

(*Definition least_fresh_P' X `{OrderedType X}
           (p:inf_subset X) (lv:set X) : X.
  refine (@SafeFirstInfiniteSubset.safe_first X H p (fun x => x ∉ lv /\ p x) _
                                              (proj1_sig (inf_subset_least p)) _).
  - eapply fresh_variable_always_exists_in_inf_subset; eauto.
Defined.*)

Lemma least_fresh_P_full_spec X `{NaturalRepresentationSucc X}
      `{@NaturalRepresentationMax X H H0}
      p (G:set X)
  : least_fresh_P p G ∉ G
    /\ (forall m, p m ->  _lt m (least_fresh_P p G) -> m ∈ filter p G)
    /\ p (least_fresh_P p G).
Proof.
  unfold least_fresh_P.
  eapply safe_first_spec with
  (I:= fun n => forall m, p m -> _lt m n -> m ∈ filter p G).
  - intros. rewrite de_morgan_dec, <- in_dneg in H4.
    destruct H4.
    + decide (m === n); subst; eauto.
      * cset_tac.
      * exploit (H3 m); eauto.
        assert (asNat m <> asNat n). intro. eapply n0.
        eapply asNat_inj; eauto.
        nr. omega.
    + decide (m === n); subst; eauto.
      * exfalso. eapply H4. rewrite <- e. eauto.
      * exploit (H3 m); eauto.
        assert (asNat m <> asNat n). intro. eapply n0.
        eapply asNat_inj; eauto.
        nr. omega.
  - intros. cset_tac.
  - intros. exfalso. nr.
    revert H4. destr_sig. intros. destruct a.
    nr. eapply H6 in H3.
    destruct H3. omega. rewrite H3 in *. omega.
Qed.

Lemma least_fresh_P_ext  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p (G G' : ⦃X⦄)
  : G [=] G' -> least_fresh_P p G = least_fresh_P p G'.
Proof.
  intros. unfold least_fresh_P; eauto.
  eapply safe_first_ext. intros. rewrite H3. reflexivity.
Qed.

Lemma least_fresh_P_p X
      `{NaturalRepresentationSucc X}
      `{@NaturalRepresentationMax X H H0} (p:inf_subset X) G
  : p (least_fresh_P p G).
Proof.
  eapply least_fresh_P_full_spec.
Qed.

Definition stable_fresh_P  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (isub:inf_subset X) : StableFresh X.
  refine (Build_StableFresh (fun lv _ => least_fresh_P isub lv) _ _).
  - intros. eapply least_fresh_P_full_spec.
  - intros. eapply least_fresh_P_ext; eauto.
Defined.

Lemma semantic_branch (P Q:Prop) `{Computable Q}
  : P \/ Q -> ((~ Q /\ P) \/ Q).
Proof.
  decide Q; clear H; intros; intuition.
Qed.

Definition least_fresh_part X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) (G:set X) x :=
  if part_1 p x then least_fresh_P (part_1 p) G
  else least_fresh_P (part_2 p) G.

Lemma least_fresh_part_fresh X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p G x
  : least_fresh_part p G x ∉ G.
Proof.
  unfold least_fresh_part; cases; eauto.
  - eapply least_fresh_P_full_spec.
  - eapply least_fresh_P_full_spec.
Qed.

Lemma least_fresh_part_1 X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) G x
  : part_1 p x
    -> part_1 p (least_fresh_part p G x).
Proof.
  unfold least_fresh_part; intros; cases.
  eapply least_fresh_P_full_spec.
Qed.

Lemma least_fresh_part_2  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) G x
  : part_2 p x
    -> part_2 p (least_fresh_part p G x).
Proof.
  unfold least_fresh_part; intros. cases.
  - exfalso. eapply (part_disj p); eauto.
  - eapply least_fresh_P_full_spec.
Qed.


Lemma least_fresh_part_p1 X `{OrderedType X}
      (NR:NaturalRepresentation X)
      (NRS:@NaturalRepresentationSucc X _ NR)
      (NRM:@NaturalRepresentationMax X _ NR)
      (p:inf_partition X) G x
  : part_1 p (least_fresh_part p G x) -> part_1 p x.
Proof.
  intros. edestruct part_cover; eauto.
  eapply least_fresh_part_2 in i.
  exfalso. eapply part_disj in H0; eauto.
Qed.

Lemma least_fresh_part_p2 X `{OrderedType X}
      (NR:NaturalRepresentation X)
      (NRS:@NaturalRepresentationSucc X _ NR)
      (NRM:@NaturalRepresentationMax X _ NR)
      (p:inf_partition X) G x
  : part_2 p (least_fresh_part p G x) -> part_2 p x.
Proof.
  intros. edestruct part_cover; eauto.
  eapply least_fresh_part_1 in i.
  exfalso. eapply part_disj in H0; eauto.
Qed.

Lemma least_fresh_part_ext  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p (G G' : ⦃X⦄) x
  : G [=] G' -> least_fresh_part p G x = least_fresh_part p G' x.
Proof.
  intros. unfold least_fresh_part; cases; eauto using least_fresh_P_ext.
Qed.

Definition stable_fresh_part  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) : StableFresh X.
  refine (Build_StableFresh (least_fresh_part p) _ _).
  - intros. eapply least_fresh_part_fresh.
  - intros. eapply least_fresh_part_ext; eauto.
Defined.

Lemma least_fresh_list_part_ext  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p n G G'
  : G [=] G'
    -> fst (fresh_list_stable (stable_fresh_part p) G n)
      = fst (fresh_list_stable (stable_fresh_part p) G' n).
Proof.
  eapply fresh_list_stable_ext.
  intros. eapply least_fresh_part_ext; eauto.
Qed.

Lemma fresh_list_stable_P_ext  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p G L L'
  : ❬L❭ = ❬L'❭
    -> of_list (fst (fresh_list_stable (stable_fresh_P p) G L))
              ⊆ of_list (fst (fresh_list_stable (stable_fresh_P p) G L')).
Proof.
  intros. hnf; intros ? In.
  general induction H3; simpl in *.
  - cset_tac.
  - revert In. repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl; eauto.
    cset_tac.
Qed.

Lemma fresh_list_stable_P_ext_eq  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p G L L'
  : ❬L❭ = ❬L'❭
    -> of_list (fst (fresh_list_stable (stable_fresh_P p) G L))
              [=] of_list (fst (fresh_list_stable (stable_fresh_P p) G L')).
Proof.
  split; intros.
  - eapply fresh_list_stable_P_ext; eauto.
  - eapply fresh_list_stable_P_ext; [symmetry|]; eauto.
Qed.


Lemma least_fresh_part_1_back  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) G x
  : part_1 p (least_fresh_part p G x) -> part_1 p x.
Proof.
  intros.
  decide (part_1 p x); eauto.
  destruct (part_cover p x); eauto.
  eapply least_fresh_part_2 in i.
  edestruct (part_disj p); eauto.
Qed.

Lemma least_fresh_part_2_back  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} (p:inf_partition X) G x
  : part_2 p (least_fresh_part p G x) -> part_2 p x.
Proof.
  intros.
  decide (part_2 p x); eauto.
  destruct (part_cover p x); eauto.
  eapply least_fresh_part_1 in i.
  edestruct (part_disj p); eauto.
Qed.

Lemma cardinal_filter_part  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p G Z
      (UNIQ:NoDupA _eq Z)
  : cardinal (filter (part_1 p)
                     (of_list (fst (fresh_list_stable (stable_fresh_part p) G Z))))
    = cardinal (filter (part_1 p) (of_list Z)).
Proof.
  general induction Z; simpl.
  - reflexivity.
  -  repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl.
    decide (part_1 p a).
    + rewrite filter_add_in; eauto using least_fresh_part_1.
      rewrite filter_add_in; eauto.
      rewrite !add_cardinal_2; eauto.
      * intro. inv UNIQ. cset_tac.
      * exploit (fresh_list_stable_spec (stable_fresh_part p));
        eauto using least_fresh_part_fresh.
        cset_tac'.
        eapply H3; cset_tac.
    + rewrite filter_add_notin; eauto.
      rewrite filter_add_notin; eauto.
      eauto using least_fresh_part_1_back.
Qed.

Lemma cardinal_smaller  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0}
      p n (G:set X) (Z:list X) x
      (GET:get Z n x) (P1:part_1 p x) (ND: NoDupA _eq Z)
  : SetInterface.cardinal
    (filter (part_1 p)
       (of_list
          (take n
             (fst
                (fresh_list_stable (stable_fresh_part p) G Z)))))
    < SetInterface.cardinal (filter (part_1 p) (of_list Z)).
Proof.
  general induction Z; simpl;
    let_pair_case_eq; simpl_pair_eqs; subst; simpl; destruct n; simpl.
  - inv GET.
    + rewrite filter_incl; eauto. rewrite empty_cardinal.
      rewrite filter_add_in; eauto.
      rewrite add_cardinal_2. omega. inv ND.
      rewrite filter_incl; eauto.
  - inv GET.
    + decide (part_1 p a).
      * rewrite filter_add_in; eauto using least_fresh_part_1.
        rewrite filter_add_in; eauto.
        rewrite !add_cardinal_2.
        -- eapply lt_n_S.
           eapply IHZ; eauto.
        -- rewrite filter_incl; eauto.
        -- rewrite filter_incl, take_list_incl; eauto.
           hnf; intro IN.
           eapply fresh_list_stable_spec in IN. cset_tac.
      * rewrite filter_add_notin; eauto using least_fresh_part_1.
        rewrite filter_add_notin; eauto.
        intro; eapply n0. eapply least_fresh_part_p1; eauto.
Qed.