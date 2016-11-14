Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SpillSound.


(* this file is way too big *)


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
           (sl' sl : spilling)
  :=
    sl' = setTopAnn sl (getAnn sl') (*Note that rm=rm' *)
    /\ fst (fst (getAnn sl')) ⊆ fst (fst (getAnn sl))
    /\ snd (fst (getAnn sl')) ⊆ snd (fst (getAnn sl))
    /\ snd (getAnn sl') = snd (getAnn sl)
.


Function count
         (sl : spilling)
  := cardinal (fst (fst (getAnn sl))) + cardinal (snd (fst (getAnn sl))).



Lemma count_reduce_L
      (sl : spilling)
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




(* the name should be changed *)


Lemma count_reduce_Sp
      (sl : spilling)
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



Lemma disj_incl
      (X : Type)
      `{OrderedType X}
      (D1 D1' D2 D2' : ⦃X⦄)
  :
    disj D1 D2
    -> D1' ⊆ D1
    -> D2' ⊆ D2
    -> disj D1' D2'
.
Proof.
  intros.
  eapply disj_1_incl; eauto.
  eapply disj_2_incl; eauto.
Qed.



Lemma count_zero_Empty_Sp
      (sl : spilling)
  :
    count sl = 0
    -> Empty (getSp sl)
.
Proof.
  intro count_zero.
  apply cardinal_Empty.
  unfold count in count_zero.
  omega.
Qed.

Lemma count_zero_cardinal_Sp
      (sl : spilling)
  :
    count sl = 0
    -> cardinal (getSp sl) = 0
.
Proof.
  intro count_zero.
  unfold count in count_zero.
  omega.
Qed.




Lemma count_zero_cardinal_L
      (sl : spilling)
  :
    count sl = 0
    -> cardinal (getL sl) = 0
.
Proof.
  intro count_zero.
  unfold count in count_zero.
  omega.
Qed.


Lemma count_zero_Empty_L
      (sl : spilling)
  :
    count sl = 0
    -> Empty (getL sl)
.
Proof.
  intro count_zero.
  apply cardinal_Empty.
  unfold count in count_zero.
  omega.
Qed.


Lemma Empty_Sp_L_count_zero
      (sl : spilling)
  :
    Empty (getSp sl)
    -> Empty (getL sl)
    -> count sl = 0
.
Proof.
  intros Empty_Sp Empty_L.
  apply cardinal_Empty in Empty_Sp.
  apply cardinal_Empty in Empty_L.
  unfold count.
  omega.
Qed.



Definition clear_L
           (sl : spilling)
  :=
    setTopAnn sl (getSp sl, ∅, getRm sl)
.

Lemma count_clearL
      (sl : spilling)
  :
    count (clear_L sl) = cardinal (getSp sl)
.
Proof.
  unfold count.
  unfold clear_L.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite empty_cardinal.
  omega.
Qed.



Lemma getAnn_als_EQ_merge_rms
      (Lv : 〔⦃var⦄〕)
      (als : 〔ann ⦃var⦄〕)
      (Λ : 〔⦃var⦄ * ⦃var⦄〕)
      (pir2 : PIR2 Equal (merge ⊝ Λ) Lv)
      (rms : 〔⦃var⦄ * ⦃var⦄〕)
      (H23 : PIR2 Equal (merge ⊝ rms) (getAnn ⊝ als))
  :
    PIR2 Equal (merge ⊝ (rms ++ Λ)) (getAnn ⊝ als ++ Lv)
.
Proof.
  rewrite List.map_app. apply PIR2_app; eauto.
Qed.


(* the following lemmata & definitions could be extracted *)
Definition clear_SpL
           (sl : spilling)
  :=
    setTopAnn sl (∅,∅,snd (getAnn sl))
.


Definition reduce_Sp
           (sl : spilling)
  :=
    setTopAnn sl (of_list (tl (elements (getSp sl))), getL sl, snd (getAnn sl))
.


Definition reduce_L
           (sl : spilling)
  :=
    setTopAnn sl (getSp sl, of_list (tl (elements (getL sl))), snd (getAnn sl))
.


Lemma count_clear_zero
      (sl : spilling)
  :
    count (clear_SpL sl) = 0
.
Proof.
  unfold count.
  unfold clear_SpL.
  rewrite getAnn_setTopAnn.
  simpl.
  apply empty_cardinal.
Qed.

Definition clear_Sp
           (sl : spilling)
  :=
    setTopAnn sl (∅,getL sl,getRm sl)
.


Lemma count_clearSp
      (sl : spilling)
  :
    count (clear_Sp sl) = cardinal (getL sl)
.
Proof.
  unfold count.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite empty_cardinal.
  reflexivity.
Qed.


Lemma getSp_clearSp
      (sl : spilling)
  :
    getSp clear_Sp sl = ∅
.
Proof.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.

Lemma getL_clearSp
      (sl : spilling)
  :
    getL clear_Sp sl = getL sl
.
Proof.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.



Lemma getSp_clear
      (sl : spilling)
  :
    getSp clear_SpL sl = ∅
.
Proof.
  unfold clear_SpL.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.

Lemma getL_clear
      (sl : spilling)
  :
    getL clear_SpL sl = ∅
.
Proof.
  unfold clear_SpL.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.


Lemma getRm_clear
      (sl : spilling)
  :
    getRm clear_SpL sl = getRm sl
.
Proof.
  unfold clear_SpL.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.




Lemma getRm_clearSp
      (sl : spilling)
  :
    getRm clear_Sp sl = getRm sl
.
Proof.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.

Definition setSp
           (sl : spilling)
           (Sp : ⦃var⦄)
  : spilling
  :=
    setTopAnn sl (Sp,getL sl,getRm sl)
.


Lemma clear_clearSp
      (sl : spilling)
  :
    clear_SpL (clear_Sp sl) = clear_SpL sl
.
Proof.
  unfold clear_SpL.
  unfold clear_Sp.
  rewrite setTopAnn_setTopAnn.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.


Lemma clearSp_clearSp
      (sl : spilling)
  :
    clear_Sp (clear_Sp sl) = clear_Sp sl
.
Proof.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  rewrite setTopAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.



Lemma setSp_getSp
      (sl : spilling)
  :
    setSp sl (getSp sl) = sl
.
Proof.
  unfold setSp.
  unfold setTopAnn.
  destruct sl;
    destruct a;
    destruct p;
    simpl;
    reflexivity.
Qed.


Lemma getSp_setSp
      (sl : spilling)
      (Sp : ⦃var⦄)
  :
    getSp (setSp sl Sp) = Sp
.
Proof.
  unfold setSp.
  rewrite getAnn_setTopAnn.
  simpl.
  reflexivity.
Qed.
