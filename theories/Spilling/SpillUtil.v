Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.



(* move somewhere *)
Lemma setTopAnn_setTopAnn
      (X : Type)
      (x x' : X)
      (a : ann X)
  :
    setTopAnn (setTopAnn a x') x = setTopAnn a x.
Proof.
  induction a; simpl; eauto.
Qed.




Lemma tl_list_incl
      (X : Type) `{OrderedType X}
      (L : list X)
  :
    of_list (tl L) ⊆ of_list L
.
Proof.
  general induction L; simpl; eauto with cset.
Qed.


Lemma tl_set_incl
      (X : Type) `{OrderedType X}
      (s : set X)
  :
    of_list (tl (elements s)) ⊆ s
.
Proof.
  rewrite tl_list_incl.
  hnf. intros. eapply elements_iff. cset_tac.
Qed.



Definition sub_spill
           (sl' sl : ann (set var * set var * option (list (set var * set var))))
  :=
    sl' = setTopAnn sl (getAnn sl') (*Note that rm=rm' *)
    /\ fst (fst (getAnn sl')) ⊆ fst (fst (getAnn sl))
    /\ snd (fst (getAnn sl')) ⊆ snd (fst (getAnn sl))
    /\ snd (getAnn sl') = snd (getAnn sl)
.


Function count
         (sl : ann (set var * set var * option (list (set var * set var))))
  := cardinal (fst (fst (getAnn sl))) + cardinal (snd (fst (getAnn sl))).



Lemma count_reduce_L
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n m : nat)
  :
    count sl = S n
    -> cardinal (snd (fst (getAnn sl))) = S m
    -> count (setTopAnn sl (fst (fst (getAnn sl)),
                           of_list (tl (elements (snd (fst (getAnn sl))))),
                           snd (getAnn sl)))
      = n
.
Proof.
  intros count_sl card_L.
  unfold count in *.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite cardinal_set_tl with (n:=m).
  - omega.
  - rewrite of_list_elements. assumption.
Qed.





Definition merge := List.map (fun (RM : set var * set var)
                                  => fst RM ∪ snd RM).


Lemma count_reduce_Sp
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n m : nat)
  :
    count sl = S n
    -> cardinal (fst (fst (getAnn sl))) = S m
    -> count (setTopAnn sl (of_list (tl (elements (fst (fst (getAnn sl))))),
                           snd (fst (getAnn sl)),
                           snd (getAnn sl)))
      = n
.
Proof.
  intros count_sl card_Sp.
  unfold count in *.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite cardinal_set_tl with (n:=m).
  - omega.
  - rewrite of_list_elements. assumption.
Qed.


(* TODO move somewhere *)
Lemma get_get_eq
      (X : Type)
      (L : list X)
      (n : nat)
      (x x' : X)
  :
    get L n x -> get L n x' -> x = x'
.
Proof.
  intros get_x get_x'.
  induction get_x; inversion get_x'.
  - reflexivity.
  - apply IHget_x. assumption.
Qed.


Lemma sub_spill_refl sl
  :
    sub_spill sl sl
.
Proof.
  unfold sub_spill.
  repeat split.
    simpl; eauto.
  - unfold setTopAnn.
    destruct sl; destruct a; destruct p;
      simpl; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* TODO move somewher *)





Lemma of_list_tl_hd
      (L : list var)
  :
    L <> nil
    ->  of_list L [=] of_list (tl L) ∪ singleton (hd 0 L)
.
Proof.
  intro N.
  induction L; simpl; eauto.
  - isabsurd.
  - cset_tac.
Qed.


Lemma tl_hd_set_incl
      (s t : ⦃var⦄)
  :
    s \ of_list (tl (elements t)) ⊆ s \ t ∪ singleton (hd 0 (elements t))
.
Proof.
  hnf.
  intros a H.
  apply diff_iff in H.
  destruct H as [in_s not_in_tl_t].
  apply union_iff.
  decide (a ∈ t).
  - right.
    rewrite <- of_list_elements in i.
    rewrite of_list_tl_hd in i.
    + apply union_iff in i.
      destruct i.
      * contradiction.
      * eauto.
    + intro N.
      apply elements_nil_eset in N.
      rewrite of_list_elements in i.
      rewrite N in i.
      isabsurd.
  - left.
    cset_tac.
Qed.

Lemma map_singleton
      (f : var -> var)
      (x : var)
  :
    map f (singleton x) [=] singleton (f x)
.
Proof.
  apply set_incl.
  - hnf.
    intros a a_in_f.
    rewrite singleton_iff in a_in_f.
    rewrite <- a_in_f.
    apply map_1; eauto.
  - hnf.
    intros a a_in_map.
    apply map_2 in a_in_map; eauto.
    destruct a_in_map as [a' [in_x a_eq]].
    rewrite singleton_iff in in_x.
    rewrite <- in_x in a_eq.
    rewrite a_eq.
    cset_tac.
Qed.



Lemma nth_zip
      (X Y Z : Type)
      (L : list X)
      (L': list Y)
      (x : X)
      (x' : Y)
      (d : Z)
      (f : X -> Y -> Z)
      n
  :
    get L n x
    -> get L' n x'
    -> nth n (f ⊜ L L') d = f x x'
.
Proof.
  intros get_x get_x'.
  general induction n; destruct L, L';
    simpl; eauto; isabsurd;
      inv get_x;
      inv get_x'.
  - reflexivity.
  - apply IHn; eauto.
Qed.


(* not needed anymore *)
Lemma injective_ann
      (X : Type)
      (a b : ann X)
  :
    a = b
    -> match a,b with
      | ann0 an, ann0 bn => an = bn
      | ann1 an a', ann1 bn b' => an = bn /\ a' = b'
      | ann2 an a1 a2, ann2 bn b1 b2 => an = bn /\ a1 = b1 /\ a2 = b2
      | annF an aF a', annF bn bF b' => an = bn /\ aF = bF /\ a' = b'
      | _,_ => True
      end
.
Proof.
  revert b;
    induction a;
    intros b eq_ab;
    induction b;
    eauto;
    try split;
    inversion eq_ab;
    eauto.
Qed.
