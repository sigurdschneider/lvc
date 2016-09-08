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