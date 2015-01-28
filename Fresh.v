Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map.
Require Import Env EnvTy IL InjectiveMapping.

Set Implicit Arguments.

Instance le_comp (a b: nat) : Computable (a < b).
eapply lt_dec.
Defined.

(*Definition max a b := if [ a < b ] then b else a.
Definition min a b := if [ a < b ] then a else b.*)

Section PolyIter.
  Variable A : Type.

  Fixpoint iter n (s:A) (f: nat -> A-> A) :=
    match n with
        | 0 => s
        | S n => iter n (f n s) f
    end.

End PolyIter.

Definition fresh (s : set var) : var :=
  S(fold max s 0).

Lemma fresh_spec' (G:set var)
  : forall (x:var), x ∈ G -> x <= fold max G 0.
Proof.
  pattern G. pattern (fold max G 0). eapply fold_rec; intros.
  fsetdec.
  eapply H1 in H3. destruct H3.
  pattern (fold max s'' 0). rewrite fold_2; eauto.
  rewrite H3. pose proof (Max.le_max_l x0 (fold max s' 0)).
  eapply H4.
  intuition.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x1).
  rewrite Max.max_assoc. reflexivity.
  pattern (fold max s'' 0). rewrite fold_2; eauto; try intuition.
  pose proof (Max.le_max_r x (fold max s' 0)).
  specialize (H2 _ H3). unfold max in H2. rewrite <- H4. eapply H2.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x1).
  rewrite Max.max_assoc. reflexivity.
Qed.

Lemma fresh_spec G : fresh G ∉ G.
Proof.
  intro. unfold fresh in H.
  pose proof (fresh_spec' H). omega.
Qed.

Definition least_fresh (lv:set var) : var :=
  let mx := S (fold max lv 0) in
  let vx := iter (1 + cardinal lv)
                 mx
                 (fun n x => if [n ∈ lv] then x else n) in
  vx.

Lemma least_fresh_spec' G k mx
: mx ∉ G
  -> iter k mx (fun n x => if [n ∈ G] then x else n) ∉ G.
Proof.
  intros; intro.
  general induction k; simpl in *.
  - cset_tac; intuition.
  - eapply IHk; try eapply H0; eauto.
    destruct if; eauto.
Qed.

Lemma least_fresh_spec G
: least_fresh G ∉ G.
Proof.
  eapply least_fresh_spec'.
  intro.
  pose proof (fresh_spec' H). omega.
Qed.


Definition fresh_stable (lv:set var) (x:var) : var :=
  if [x ∉ lv] then x else
    fresh lv.

Lemma fresh_stable_spec G x
      : fresh_stable G x ∉ G.
Proof.
  unfold fresh_stable. destruct if; eauto using fresh_spec.
Qed.

Section FreshList.

  Variable fresh : set var -> var.

  Fixpoint fresh_list (G:set var) (n:nat) : list var :=
    match n with
      | 0 => nil
      | S n => let x := fresh G in x::fresh_list (G ∪ {{x}}) n
    end.

  Lemma fresh_list_length (G:set var) n
  : length (fresh_list G n) = n.
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G, fresh G ∉ G.

  Definition fresh_set (G:set var) (n:nat) : set var :=
    of_list (fresh_list G n).

  Lemma fresh_list_spec : forall (G:set var) n, (of_list (fresh_list G n)) ∩ G [=] ∅.
  Proof.
    intros. general induction n; simpl; split; intros; try now (cset_tac; intuition).
    - cset_tac; intuition.
      + invc H; eauto.
      + specialize (H0 (G ∪ {{fresh G}})).
        intuition (cset_tac; eauto).
  Qed.

  Lemma fresh_set_spec
  : forall (G:set var) n, (fresh_set G n) ∩ G [=] ∅.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_unique (G: set var) n
    : unique (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    split; eauto. intro.
    eapply (not_in_empty (fresh G)).
    eapply fresh_list_spec.
    cset_tac. eapply InA_in; eauto.
    cset_tac; eauto.
  Qed.
End FreshList.

Definition notincl {X} `{OrderedType X} (s t: set X) := forall x, x ∈ s -> x ∉ t.

Lemma inverse_on_update_fresh (D:set var) (Z Z':list var) (ϱ ϱ' : var -> var)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> unique Z'
  -> length Z = length Z'
  -> notincl (of_list Z') (lookup_set ϱ (D \ of_list Z))
  -> inverse_on D (update_with_list Z Z' ϱ)
                 (update_with_list Z' Z ϱ').
Proof.
  intros. eapply length_length_eq in H1.
  hnf; intros. lud. decide(x ∈ of_list Z).
  general induction H1; simpl in *; eauto; dcr. cset_tac; exfalso; eauto.
  lud. eapply add_iff in i. destruct i; eauto.
  assert (y ∈ of_list YL). rewrite e.
  eapply update_with_list_lookup_in; eauto using length_eq_length.
  exfalso. eapply (@fresh_of_list _ _ YL y H4 H9).
  exfalso; eauto.
  eapply add_iff in i; destruct i; isabsurd.
  eapply IHlength_eq; try eassumption.
  hnf; intros. exfalso; cset_tac; eauto.
  hnf; intros. intro. eapply lookup_set_spec in H11.
  destruct H11; cset_tac; eauto. intuition.

  erewrite update_with_list_no_update; eauto.
  erewrite update_with_list_no_update; eauto.
  eapply H; eauto. cset_tac ; eauto.
  erewrite update_with_list_no_update; eauto. intro.
  eapply H2; eauto.
  eapply lookup_set_spec; cset_tac; intuition.
  eexists x; eauto.
Qed.

Lemma inverse_on_update_fresh_list (D:set var) (Z:list var) (ϱ ϱ' : var -> var)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto.
  eapply fresh_list_unique, fresh_spec.
  rewrite fresh_list_length; eauto.
  hnf; intros. intro. eapply (not_in_empty x).
  eapply fresh_list_spec; eauto using fresh_spec. cset_tac; eauto.
Qed.

Hint Extern 20 (Subset (?a \ _) ?a) => eapply minus_incl.
Hint Extern 20 (Subset (?a \ _) ?a') => (is_evar a ; fail 1)
                                        || (has_evar a ; fail 1)
                                        || (is_evar a' ; fail 1)
                                        || (has_evar a'; fail 1)
                                        || eapply minus_incl.
Hint Extern 20 => match goal with
                   | [ H: ?a /\ ?b |- ?b ] => eapply H
                   | [ H: ?a /\ ?b |- ?a ] => eapply H
                 end.

Section MapUpdate.
  Open Scope fmap_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Lemma update_unique_commute `{OrderedType Y} (XL:list X) (VL:list Y) E D x y
  : length XL = length VL
    -> unique (x::XL)
    -> agree_on _eq D (E [x <- y] [XL <-- VL]) (E [XL <-- VL] [x <- y]).
  Proof.
    intros. eapply length_length_eq in H1.
    general induction H1; simpl. reflexivity.
    hnf; intros. lud. hnf in H2; simpl in *.
    dcr. exfalso. eapply H8. econstructor. eapply H5.
    exploit (IHlength_eq H _ E {x1} x0 y0). simpl in *; intuition.
    hnf; intros. eapply H9. econstructor 2; eauto.
    exploit X0. cset_tac; reflexivity. rewrite X1. lud.
    exploit (IHlength_eq H _ E {x1} x0 y0). simpl in *; intuition.
    hnf; intros. eapply H8. econstructor 2; eauto.
    exploit X0. cset_tac; reflexivity. rewrite X1. lud.
  Qed.

  Lemma injective_on_agree `{OrderedType Y} D (ϱ ϱ': X -> Y)
  : injective_on D ϱ
    -> agree_on _eq D ϱ ϱ'
    -> injective_on D ϱ'.
  Proof.
    intros. hnf; intros. eapply H1; eauto.
    exploit H2; eauto. rewrite X0.
    exploit H2; try eapply H3. rewrite X1. eauto.
  Qed.

End MapUpdate.

Lemma injective_on_fresh_list X `{OrderedType X} Y `{OrderedType Y} XL YL (ϱ: X -> Y) `{Proper _ (_eq ==> _eq) ϱ} lv
: injective_on lv ϱ
  -> length XL = length YL
  -> (of_list YL) ∩ (lookup_set ϱ lv) [=] ∅
  -> unique XL
  -> unique YL
  -> injective_on (lv ∪ of_list XL) (ϱ [XL <-- YL]).
Proof.
  intros. eapply length_length_eq in H3.
  general induction H3; simpl in * |- * ; eauto.
  - eapply injective_on_incl; eauto. cset_tac; intuition.
  - eapply injective_on_agree.
    assert (lv ∪ { x; of_list XL} [=] {{x}} ∪ lv ∪ of_list XL) by (cset_tac; intuition; eauto).
    rewrite H7. eapply IHlength_eq; auto.
    Focus 2.
    eapply injective_on_fresh. instantiate (1:=ϱ); eauto.
    eapply injective_on_incl; eauto. instantiate (1:=y).
    intro. eapply lookup_set_spec in H8. dcr.
    eapply (not_in_empty (ϱ x0)). rewrite <- H4. cset_tac; intuition.
    eapply lookup_set_spec; eauto. eapply H1.
    hnf; intros. lud; eauto; try now exfalso; eauto.
    dcr. cset_tac; intuition.
    eapply lookup_set_spec in H12; dcr. lud.
    eapply H8. rewrite <- H14; eauto. eapply InA_in; eauto.
    cset_tac; intuition.
    eapply H4. split. right; eauto.
    eapply lookup_set_spec. eauto. eexists; eauto.
    hnf; intros. lud; eauto; try now exfalso; eauto.
    eapply update_unique_commute; eauto using length_eq_length.
Qed.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
