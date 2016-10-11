Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined SetUtil.


(* move somewhere to of_list or maybe generalize to symmetric relations ? *)
Lemma elem_eq_sym_proof
      (X Y : Type)
      `{OrderedType X}
      `{OrderedType Y}
      (f : list X -> list Y)
  :
    (forall (xl xl' : list X),
      of_list xl ⊆ of_list xl' -> of_list (f xl) ⊆ of_list (f xl'))
    -> (forall (xl xl' : list X),
          elem_eq xl xl' -> elem_eq (f xl)  (f xl'))
.
Proof.
  intros.
  unfold elem_eq in H2.
  unfold elem_eq.
  apply eq_incl in H2 as [incl1 incl2].
  eapply H1 in incl1.
  eapply H1 in incl2.
  apply incl_eq; eauto.
Qed.


(* move somewhere to Op.freeVars *)
Lemma op_freeVars_elem_eq_ext
      (Y Y' : args)
  :
    elem_eq Y Y'
    -> elem_eq (Op.freeVars ⊝ Y) (Op.freeVars ⊝ Y')
.
Proof.
  apply elem_eq_sym_proof.
  intros.
  unfold elem_eq.
  general induction xl;
    simpl in *; eauto.
  - cset_tac.
  - rewrite IHxl with (xl':=xl');
      simpl; eauto.
    + assert (a ∈ of_list xl') as a_in.
      {
        rewrite <- H.
        clear; cset_tac.
      }
      enough (Op.freeVars a ∈ of_list (Op.freeVars ⊝ xl')) as sla_in.
      {
        apply incl_singleton in sla_in.
        rewrite add_union_singleton.
        rewrite sla_in.
        clear; cset_tac.
      }
      apply of_list_1.
      apply of_list_1 in a_in.
      clear H.
      general induction a_in;
        simpl; eauto.
      rewrite H.
      econstructor; eauto.
      econstructor; eauto.
    + rewrite <- H.
      eauto with cset.
Qed.




(* move somewhere to renamedApart *)
Lemma renamedApart_incl
      (s : stmt)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    renamedApart s ra
    -> match ra with
      | ann1 (D, D') an
        => union_fs (getAnn an) ⊆ D ∪ D'
      | ann2 (D, D') ans ant
        => union_fs (getAnn ans) ⊆ D ∪ D'
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | annF (D, D') anF ant
        => (forall (ans : ann (⦃var⦄ * ⦃var⦄)) n,
              get anF n ans
              -> union_fs (getAnn ans) ⊆ D ∪ D')
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | _ => True
      end
.
Proof.
  intros.
  invc H; simpl; unfold union_fs; eauto.
  - invc H4.
    simpl.
    rewrite H7.
    rewrite H8.
    rewrite H3.
    clear; cset_tac.
  - invc H5; invc H6.
    simpl.
    rewrite H9.
    rewrite H10.
    rewrite H11.
    rewrite H12.
    rewrite <- H2.
    split; clear; cset_tac.
  - invc H5.
    split.
    + intros; inv_get.
      exploit H2; eauto.
      destruct H8 as [A [B [C E]]].
      rewrite A.
      rewrite <- H6.
      enough (snd (getAnn ans0) ∪ of_list (fst x) ⊆ list_union (defVars ⊜ F ans))
        as enouf.
      {
        rewrite union_assoc.
        rewrite union_comm.
        rewrite union_assoc.
        rewrite enouf.
        simpl.
        clear; cset_tac.
      }
      eapply incl_list_union.
      apply zip_get; eauto.
      rewrite union_comm.
      reflexivity.
    + rewrite H9.
      rewrite H10.
      rewrite <- H6.
      simpl.
      clear; cset_tac.
Qed.




(* to be moved to list_union *)
Lemma list_union_elem_eq_ext
      (X : Type)
      `{OrderedType X}
      (L L' : list ⦃X⦄)
  :
    elem_eq L L'
    -> list_union L [=] list_union L'
.
Proof.
  enough (forall (l l' : list ⦃X⦄),
                    of_list l ⊆ of_list l'
                    -> list_union l ⊆ list_union l') as enouf.
  {
    unfold elem_eq.
    intros.
    apply eq_incl in H0 as [incl1 incl2].
    apply incl_eq; eauto.
  }
  intros.
  clear L L'.
  general induction l;
    simpl in *; eauto.
  - cset_tac.
  - rewrite list_union_start_swap.
    rewrite add_union_singleton in H0.
    apply union_incl_split2 in H0 as [a_ofl l_ofl].
    assert (a ⊆ list_union l') as a_sub.
    {
      apply in_singleton in a_ofl.
      apply of_list_list_union; eauto.
    }
    rewrite a_sub.
    rewrite IHl with (l':=l'); eauto.
    clear; cset_tac.
Qed.





(* to be moved to lookup_set / map *)
Lemma injective_on_map_inter
      (X : Type)
      `{OrderedType X}
      (D s t : ⦃X⦄)
      (f : X -> X)
  :
    Proper (_eq ==> _eq) f
    -> injective_on D f
    -> s ⊆ D
    -> t ⊆ D
    -> map f (s ∩ t) [=] map f s ∩ map f t
.
Proof.
  intros.
  apply incl_eq.
  - hnf; intros.
    apply inter_iff in H4 as [a_s a_t].
    apply map_iff in a_s as [b [b_s b_eq]]; eauto.
    apply map_iff in a_t as [c [c_s c_eq]]; eauto.
    unfold injective_on in H1.
    rewrite b_eq in c_eq.
    assert (b ∈ D) as b_D by cset_tac.
    assert (c ∈ D) as c_D by cset_tac.
    apply (H1 b c) in b_D; eauto.
    apply map_iff; eauto.
    exists b.
    rewrite <- b_D in c_s.
    split; eauto.
    cset_tac.
  - hnf; intros.
    apply map_iff in H4 as [b [b_s b_eq]]; eauto.
    apply inter_iff in b_s as [b_s b_t].
    apply inter_iff; split; eauto.
    + eapply map_iff; eauto.
    + eapply map_iff; eauto.
Qed.
