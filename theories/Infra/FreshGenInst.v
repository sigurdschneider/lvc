Require Import Util CSet MapInjectivity NaturalRep FreshGen FreshNR Even.

Set Implicit Arguments.

Definition FG_fast_pos : FreshGen positive positive :=
  @Build_FreshGen positive _ positive
                  (fun n _ => (n,  succ n))
                  (fun n Z => (range succ n ❬Z❭, (Util.iter ❬Z❭ n succ)))
                  (fun n => vars_up_to n)
                  (fun n s => max n (succ (fold max s (ofNat 0))))
                  (ofNat 0).


Local Arguments succ : simpl never.
Local Arguments max : simpl never.

Lemma vars_up_to_in (x i:positive)
  : (asNat x < asNat i) <-> x ∈ vars_up_to i.
Proof.
  rewrite <- VarsUpTo.vars_up_to_in.
  unfold asNat; simpl.
  nr.
  exploit (Pos2Nat.is_pos x).
  exploit (Pos2Nat.is_pos i).
  omega.
Qed.

Lemma FGS_fast_pos : FreshGenSpec FG_fast_pos.
  econstructor.
  - intros. simpl. cset_tac'.
    rewrite <- vars_up_to_in in H. nr. omega.
  - simpl. intros. cset_tac'.
    + rewrite <- vars_up_to_in. nr. omega.
    + revert H0. setoid_rewrite <- vars_up_to_in. nr. omega.
  - intros; hnf; intros.
    eapply vars_up_to_in in H. nr.
    eapply (@in_range_x positive _ _ NaturalRepresentationSuccPositive) in H0 as [? ?].
    nr. omega.
  - simpl. intros. cset_tac'.
    + eapply (@in_range_x positive _ _ NaturalRepresentationSuccPositive) in H0 as [? ?].
      setoid_rewrite <- vars_up_to_in.
      nr. omega.
    + rewrite <- vars_up_to_in in *.
      nr. omega.
  - intros. eapply range_nodup.
  - intros.
    unfold fresh_list. simpl.
    eauto with len.
  - simpl. cset_tac'.
    + rewrite <- vars_up_to_in.
      nr.
      rewrite <- Max.le_max_r.
      eapply fold_max_lt in H0; eauto.
      eapply order_respecting' in H0. nr. eauto.
    + eapply vars_up_to_in in H0.
      eapply vars_up_to_in. nr.
      rewrite <- Max.le_max_l. eauto.
      Grab Existential Variables.
      eauto with typeclass_instances.
Qed.

Lemma NoDup_inj A `{OrderedType A} B `{OrderedType B} (L:list A) (f:A -> B)
      `{Proper _ (_eq ==> _eq) f}
  : NoDupA _eq L
    -> injective_on (of_list L) f
    -> NoDupA _eq (f ⊝ L).
Proof.
  intros ND INJ.
  general induction ND; simpl in *; eauto using NoDupA.
  econstructor; eauto using injective_on_incl with cset.
  intro. eapply InA_in in H3.
  eapply H0. eapply of_list_map in H3; eauto. cset_tac'.
  eapply INJ in H4; eauto with cset.
Qed.

Lemma asNat_iter_plus_plus N `{NaturalRepresentationSucc N} n i
  : asNat (iter n i (fun x => succ (succ x))) = 2 * n + asNat i.
Proof.
  general induction n; simpl; eauto.
  rewrite IHn. nr. omega.
Qed.

Lemma in_range_x  V `{NaturalRepresentationSucc V} x k n
  : x ∈ of_list (range (fun x => succ (succ x)) k n) ->
                 asNat x >= asNat k /\ asNat k+2*n > asNat x.
Proof.
  general induction n; simpl in *; dcr.
  - cset_tac.
  - decide (x === k); subst; try omega;
      cset_tac'; nr; try omega.
    eapply IHn in H3; nr; omega.
    eapply IHn in H3; nr; omega.
Qed.

Lemma range_nodup V `{NaturalRepresentationSucc V} i d
  : NoDupA _eq (range (fun x => succ (succ x)) i d).
Proof.
  general induction d; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro.
  rewrite InA_in in H2.
  eapply in_range_x in H2. nr. omega.
Qed.


Definition FG_even_fast_pos : FreshGen positive {n : positive | even (asNat n)}.
  refine
    (@Build_FreshGen positive _ {n :positive| even (asNat n)}
                  (fun n _ => (proj1_sig n, exist _ (succ (succ (proj1_sig n))) _))
                  (fun n Z => let z := ❬Z❭ in
                             (range (fun x => succ (succ x)) (proj1_sig n)  ❬Z❭,
                              exist _ (iter z (proj1_sig n) (fun x => succ (succ x))) _))
                  (fun n => (vars_up_to (proj1_sig n)))
                  (fun n s =>
                     exist _ (max (proj1_sig n) (next_even_pos (succ (fold max s (ofNat 0))))) _)
                  (exist _ (ofNat 0) _)).
  - simpl. nr. destruct n. eauto.
  - destruct n. subst z.
    rewrite asNat_iter_plus_plus.
    eapply even_add; eauto.
    eapply even_mult2.
  - destruct n. nr. eapply even_max; eauto using next_even_pos_even.
  - simpl. eauto.
Defined.

Lemma FGS_even_fast_pos : FreshGenSpec FG_even_fast_pos.
  econstructor; simpl.
  - intros. destruct i.
    cset_tac'. simpl in *. rewrite <- vars_up_to_in in H.
    omega.
  - intros [] _; simpl. nr. cset_tac'.
    + rewrite <- vars_up_to_in. nr. omega.
    + rewrite <- vars_up_to_in in H0.
      rewrite <- vars_up_to_in. nr. omega.
  - intros; hnf; intros. cset_tac'.
    eapply vars_up_to_in in H. destruct i; simpl in *.
    eapply in_range_x in H0. dcr. omega.
  - intros. destruct i; simpl in *. cset_tac'.
    + eapply in_range_x in H0. dcr.
      eapply vars_up_to_in.
      rewrite asNat_iter_plus_plus. omega.
    + rewrite <- vars_up_to_in in *.
      rewrite asNat_iter_plus_plus. omega.
  - intros. change eq with (@_eq positive _).
    eapply range_nodup.
  - intros. eauto with len.
  - simpl. cset_tac'.
    + rewrite <- vars_up_to_in. nr.
      rewrite <- Max.le_max_r. unfold next_even_pos.
      eapply (@fold_max_lt positive _ _ _ _) in H0.
      cases; eauto.
      * eapply order_respecting' in H0. eauto.
      * eapply order_respecting' in H0. nr. omega.
    + eapply vars_up_to_in in H0. destruct i; simpl in *.
      eapply vars_up_to_in.
      nr.
      rewrite <- Max.le_max_l. eauto.
Qed.

Inductive FreshGenSingle (V:Type) `{OrderedType V} (Fi : Type) :=
  {
    fresh :> Fi -> V -> V * Fi;
    domain : Fi -> set V;
    domain_add : Fi -> set V -> Fi;
    empty_domain : Fi
  }.

Arguments FreshGenSingle V {H} Fi.

Inductive FreshGenSingleSpec V `{OrderedType V} Fi (FG:FreshGenSingle V Fi) : Prop :=
  {
    fresh_spec : forall i x, fst (fresh FG i x) ∉ domain FG i;
    fresh_domain_spec : forall i x, {fst (fresh FG i x); (domain FG i)}
                                 ⊆ domain FG (snd (fresh FG i x));
    domain_add_spec : forall i G, G ∪ domain FG i ⊆ domain FG (domain_add FG i G)
  }.


Section FreshList_FreshGenSingle.
  Variable V : Type.
  Context `{OrderedType V}.
  Variable Fi : Type.
  Context `{FG:@FreshGenSingle V H Fi}.
  Context `{FGS:@FreshGenSingleSpec V H Fi FG}.

  Fixpoint fresh_list_stable (G:Fi) (xl:list V) : list V * Fi :=
    match xl with
      | nil => (nil, G)
      | x::xl => let (y,G') := fresh FG G x in
                let (Y,G'') := fresh_list_stable G' xl in
                (y::Y,G'')
    end.

  Lemma fresh_list_stable_length G xl
  : length (fst (fresh_list_stable G xl)) = length xl.
  Proof.
    general induction xl; simpl; repeat let_pair_case_eq; subst; simpl; eauto.
  Qed.

  Lemma fresh_list_stable_spec
    : forall G L, disj (of_list (fst (fresh_list_stable G L))) (domain FG G).
  Proof.
    intros. revert G.
    induction L; simpl; intros;
      repeat let_pair_case_eq; subst; simpl; intros; eauto.
    - hnf; intros. eapply add_iff in H0 as [A|A].
      + rewrite <- A in H1. eapply fresh_spec in H1; eauto.
      + eapply IHL; eauto. rewrite <- fresh_domain_spec. cset_tac. eauto.
  Qed.

  Lemma fresh_list_stable_nodup G L
    : NoDupA _eq (fst (fresh_list_stable G L)).
  Proof.
    revert G.
    induction L; intros G; simpl; repeat let_pair_case_eq; subst; eauto.
    econstructor; eauto. intro.
    eapply (@fresh_list_stable_spec (snd (fresh FG G a)) L).
    eapply InA_in. eapply H0.
    rewrite <- fresh_domain_spec.
    cset_tac; eauto. eauto.
  Qed.

  Lemma fresh_list_stable_G G L
    : of_list (fst (fresh_list_stable G L)) ∪ domain FG G
              ⊆ domain FG (snd (fresh_list_stable G L)).
  Proof.
    revert G.
    induction L; intros G; simpl; repeat let_pair_case_eq; subst; simpl;
      eauto with cset.
    rewrite <- IHL. rewrite <- fresh_domain_spec. clear_all. cset_tac. eauto.
  Qed.

End FreshList_FreshGenSingle.


Definition mkFreshGenFromSingle V `{OrderedType V} Fi
           (FG:FreshGenSingle V Fi) : FreshGen V Fi :=
  @Build_FreshGen V _ Fi (@fresh _ _ _ FG)
                  (@fresh_list_stable _ _ _ FG)
                  (@domain _ _ _ FG)
                  (@domain_add _ _ _ FG)
                  (@empty_domain _ _ _ FG).

Lemma mkFreshGenFromSingleSpec V `{OrderedType V} Fi
      (FG:FreshGenSingle V Fi) (FGS:@FreshGenSingleSpec V _ Fi FG)
  : @FreshGenSpec V _ Fi (mkFreshGenFromSingle FG).
Proof.
  econstructor.
  - eapply fresh_spec; eauto.
  - eapply fresh_domain_spec; eauto.
  - symmetry. eapply (@fresh_list_stable_spec V _ Fi FG); eauto.
  - intros. pose proof (@fresh_list_stable_G V _ Fi FG FGS).
    unfold FreshGen.domain. simpl. eauto.
  - intros. eapply fresh_list_stable_nodup. eauto.
  - intros. simpl.
    rewrite fresh_list_stable_length; eauto.
  - eapply domain_add_spec; eauto.
Qed.

Definition FG_fast_pres' : FreshGenSingle positive positive :=
  @Build_FreshGenSingle positive _ positive
                  (fun n x => if [ even_pos_fast x = even_pos_fast n ] then
                               (n, succ n)
                             else (succ n, succ (succ n)))
                  (fun n => vars_up_to n)
                  (fun n s => max n (succ (fold max s (ofNat 0))))
                  (ofNat 0).

Lemma FGS_fast_pres' : FreshGenSingleSpec FG_fast_pres'.
  econstructor.
  - intros. simpl. cases.
    + cset_tac'. simpl in *; subst. rewrite <- vars_up_to_in in H. nr. omega.
    + simpl. cset_tac'. rewrite <- vars_up_to_in in H.
      nr. omega.
  - simpl. intros. cset_tac'.
    + cases; simpl.
      * rewrite <- vars_up_to_in. nr. omega.
      * rewrite <- vars_up_to_in. nr. omega.
    + revert H0. setoid_rewrite <- vars_up_to_in. intros.
      cases; simpl; nr; eauto.
  - simpl. cset_tac'.
    + rewrite <- vars_up_to_in.
      nr.
      rewrite <- Max.le_max_r.
      eapply fold_max_lt in H0; eauto.
      eapply order_respecting' in H0. nr. eauto.
    + eapply vars_up_to_in in H0.
      eapply vars_up_to_in. nr.
      rewrite <- Max.le_max_l. eauto.
      Grab Existential Variables.
      eauto with typeclass_instances.
Qed.

Definition FG_fast_pres := mkFreshGenFromSingle  FG_fast_pres'.
Definition FGS_fast_pres := mkFreshGenFromSingleSpec FGS_fast_pres'.