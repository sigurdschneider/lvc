Require Import Util CSet Fresh.

Set Implicit Arguments.

Record inf_subset X `{OrderedType X}  :=
  {
    inf_subset_P :> X -> bool;
    inf_subset_inf : forall x, exists y, inf_subset_P y /\ _lt x y;
    inf_subset_proper :> Proper (_eq ==> eq) inf_subset_P
  }.

Hint Resolve inf_subset_inf.

Record inf_partition  X `{OrderedType X}  :=
  { part_1 : inf_subset;
    part_2 : inf_subset;
    part_disj : forall x, part_1 x -> part_2 x -> False;
    part_cover : forall x, part_1 x + part_2 x;
  }.


Arguments inf_subset X {H}.
Arguments inf_partition X {H}.


Instance inf_subset_X X `{OrderedType X} (p : inf_subset X)
  :  Proper (_eq ==> eq) p.
Proof.
  eapply p.
Qed.

Hint Resolve inf_subset_X.

Lemma part_dich  X `{OrderedType X}  (p:inf_partition X) x
  : (part_1 p x /\ (part_2 p x -> False)) \/ (part_2 p x /\ (part_1 p x -> False)).
Proof.
  destruct (part_cover p x);
    pose proof (part_disj p x); cset_tac.
Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => even n
  end.

Lemma even_or_successor x
  : even x \/ even (1 + x).
Proof.
  induction x; eauto.
  destruct IHx; eauto.
Qed.

Definition even_inf_subset : inf_subset nat.
Proof.
  refine (@Build_inf_subset _ _ even _ _).
  - intros. cbn. destruct (even_or_successor (S x)); eauto.
Defined.

Definition odd := (fun x => negb (even x)).

Lemma even_or_odd (x:nat)
  : even x + odd x.
Proof.
  unfold odd. destruct (even x); eauto.
Qed.

Lemma even_not_even x
  : even x = negb (even (S x)).
Proof.
  general induction x; eauto.
  - simpl even at 2.
    destruct (even x); destruct (even (S x)); simpl in *; intuition.
Qed.

Definition odd_inf_subset : inf_subset nat.
Proof.
  refine (@Build_inf_subset _ _ odd _ _).
  - cbn. unfold odd. intros.
    destruct (even_or_successor x); eauto.
    + eexists (S x). rewrite <- even_not_even.
      split; eauto.
    + eexists (S (S x)); simpl.
      rewrite even_not_even in H. eauto.
Defined.

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


Definition even_inf_subset_pos : inf_subset positive.
Proof.
  refine (@Build_inf_subset _ _ (fun x => even (asNat x)) _ _).
  - intros. cbn. destruct (even_or_successor (S (asNat x))); eauto.
    + exists (ofNat (S (asNat x))). nr. split; eauto.
      change (_lt x (ofNat (S (asNat x)))).
      rewrite <- (@order_respecting' positive _). nr. omega.
    + exists (ofNat (S (S (asNat x)))). nr. split; eauto.
      change (_lt x (ofNat (S (S (asNat x))))).
      rewrite <- (@order_respecting' positive _). nr. omega.
Defined.

Definition odd_inf_subset_pos : inf_subset positive.
Proof.
  refine (@Build_inf_subset _ _ (fun x => odd (asNat x)) _ _).
  - cbn. unfold odd. intros.
    destruct (even_or_successor (asNat x)); eauto.
    + eexists (ofNat (S (asNat x))). nr. rewrite <- even_not_even.
      split; eauto. change (_lt x (ofNat (S (asNat x)))).
      eapply order_respecting'.
      nr. omega.
    + eexists (ofNat (S (S (asNat x)))); simpl.
      rewrite even_not_even in H. nr.  split; eauto.
      change (_lt x (ofNat (S (S (asNat x))))).
      eapply order_respecting'. nr. omega.
Defined.


Definition even_part_pos : inf_partition positive.
Proof.
  refine (Build_inf_partition even_inf_subset_pos odd_inf_subset_pos _ _).
  - intros.
    unfold even_inf_subset in H. simpl in H.
    unfold odd_inf_subset in H0. simpl in H0.
    unfold odd in H0. unfold negb in H0. cases in H0; eauto.
  - intros.
    unfold even_inf_subset, odd_inf_subset, odd, negb; simpl.
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
        eapply (@safe_antitone _ _ _ _ _ _ _ x).
        econstructor; split; eauto.
        intro. cset_tac'.
        eapply (@fold_max_lt X _ _ _ _) in H7; eauto.
        simpl in *. exfalso. nr. simpl in *. omega.
        eapply (@fold_max_lt X _ _ _ _) in H7; eauto.
        simpl in *. exfalso. nr. simpl in *. omega. eauto.
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
        eapply (@fold_max_lt X _ _ _ _) in H7; eauto.
        simpl in *. exfalso. nr. omega.
        eapply (@fold_max_lt X _ _ _ _) in H7; eauto.
        simpl in *. exfalso. nr. omega.
        simpl in *. nr. omega.
        Grab Existential Variables. eauto. eauto.
Qed.

Definition least_fresh_P X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0}
           (p:inf_subset X) (lv:set X) : X.
  refine (@safe_first _ _ _ _ (fun x => x ∉ lv /\ p x) _ (ofNat 0) _).
  - eapply fresh_variable_always_exists_in_inf_subset; eauto.
Defined.

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
  - intros. exfalso. nr. omega.
Qed.

Lemma least_fresh_P_ext  X `{NaturalRepresentationSucc X}
           `{@NaturalRepresentationMax X H H0} p (G G' : ⦃X⦄)
  : G [=] G' -> least_fresh_P p G = least_fresh_P p G'.
Proof.
  intros. unfold least_fresh_P; eauto.
  eapply safe_first_ext. intros. rewrite H3. reflexivity.
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
