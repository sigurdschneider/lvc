Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map.
Require Import Env EnvTy IL.
 
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

Definition least_fresh (lv:set var) : var :=
  let mx := fold max lv 0 in 
  let vx := iter (cardinal lv + 1) 
                 mx 
                 (fun n x => if [n ∈ lv] then x else n) in
  vx.

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

Definition fresh_stable (lv:set var) (x:var) : var :=
  if [x ∉ lv] then x else
    fresh lv.

Lemma fresh_stable_spec G x
      : fresh_stable G x ∉ G.
Proof.
  unfold fresh_stable. destruct if; eauto using fresh_spec.
Qed.


Fixpoint fresh_list (G:set var) (n:nat) : list var :=
  match n with
    | 0 => nil
    | S n => let x := fresh G in x::fresh_list (G ∪ {{x}}) n
  end.

Definition fresh_set (G:set var) (n:nat) : set var := 
  of_list (fresh_list G n).

Lemma fresh_list_spec : forall (G:set var) n, (of_list (fresh_list G n)) ∩ G [=] ∅.
Proof.
  intros. general induction n; simpl; split; intros.
  cset_tac; eauto. exfalso; cset_tac; eauto.  
  cset_tac; intuition.
  rewrite <- H in H1. eapply fresh_spec; eauto. 
  specialize (IHn (G ∪ {{fresh G}})). intuition (cset_tac; eauto).
  exfalso; cset_tac; eauto.
Qed.

Lemma fresh_list_length (G:set var) n
  : length (fresh_list G n) = n.
Proof.
  general induction n; eauto. simpl. f_equal; eauto.
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

Fixpoint fresh_stable_list (G:set var) (Z:list var) : list var :=
  match Z with
    | nil => nil
    | x::Z' => let x' := fresh_stable (G ∪ of_list Z') x in x'::fresh_stable_list (G ∪ {{x'}}) Z'
  end.

Lemma fresh_stable_list_length (G:set var) Z
  : length (fresh_stable_list G Z) = length Z.
Proof.
  general induction Z; eauto. simpl. f_equal; eauto.
Qed.

Lemma fresh_stable_list_spec 
: forall (G:set var) Z, (of_list (fresh_stable_list G Z)) ∩ G [=] ∅.
Proof.
  intros. general induction Z; simpl; split; intros.
  - cset_tac; eauto. 
  - exfalso; cset_tac; eauto.  
  - cset_tac; intuition.
    + hnf in H; subst.
      assert (fresh_stable (G ∪ of_list Z) a ∈ G ∪ of_list Z).
      cset_tac; intuition.
      eapply fresh_stable_spec; eauto.
    + eapply (not_in_empty a0). rewrite <- IHZ.
      intuition (cset_tac; eauto).
      intuition (cset_tac; eauto).
  - exfalso; cset_tac; auto.
Qed.

Lemma fresh_stable_list_unique (G: set var) n
  : unique (fresh_stable_list G n).
Proof.
  general induction n; simpl; eauto.
  split; eauto. intro.
  eapply (not_in_empty (fresh_stable (G ∪ of_list n) a)).
  eapply fresh_stable_list_spec.
  cset_tac. eapply InA_in; eauto. 
  cset_tac; eauto.
Qed.

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
  eexists x; eauto. cset_tac; eauto.
Qed.

Lemma inverse_on_update_fresh_list (D:set var) (Z:list var) (ϱ ϱ' : var -> var)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list (lookup_set ϱ (D \ of_list Z)) (length Z)) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto.
  eapply fresh_list_unique.
  rewrite fresh_list_length; eauto.
  hnf; intros. intro. eapply (not_in_empty x).
  eapply fresh_list_spec. cset_tac; eauto.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
