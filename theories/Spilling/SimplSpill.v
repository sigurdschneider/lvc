Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.
Require Import Spilling.
Require Import Take.


Instance ge_computable a b : Computable (a >= b).
Proof.
eapply ge_dec.
Qed.

Fixpoint simplSpill (k : nat) (R : set var) (s : stmt) (Lv : ann (set var))
: ann (set var * set var * option (list (set var * set var))) :=
match s,Lv with

| stmtLet x e s, ann1 LV lv
  => let Fv_e := Exp.freeVars e in
     let Lv_s := getAnn lv in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e : set var  := R \ K ∪ L in

     let K_x  := if [(cardinal R_e) >= k]
                 (*if [cardinal R >= k /\ cardinal L >= k]*)
                      then singleton (hd 0 (elements R_e))
                      else ∅ in
     let Sp   := Lv_s ∩ (K ∪ K_x) in
     let R_s  := {x; R_e \ K_x} in

     ann1 (Sp,L,None) (simplSpill k R_s s lv)


| _,_ => ann0 (∅, ∅, None)
end.

Lemma minus_minus X `{OrderedType X} (s t : set X) : s \ (s \ t) [=] s ∩ t.
Proof.
cset_tac.
Qed.

Lemma incl_minus X `{OrderedType X} (s t u : set X) : s ⊆ t -> u \ t ⊆ u \ s.
cset_tac.
Qed.

Lemma incl_add_eq X `{OrderedType X}(s t : set X ) (a : X) : {a; t} ⊆ s <-> a ∈ s /\ t ⊆ s.
Proof.
split; intros H0.
- split.
  + rewrite add_union_singleton in H0; unfold Subset in H0. apply H0; cset_tac.
  + rewrite <- H0. cset_tac.
- destruct H as [ain yx]. decide (a ∈ t); cset_tac.
Qed.



Lemma add_cardinal X `{OrderedType X} (s : set X) x
  : cardinal {x; s} <= S (cardinal s).
Proof.
decide (x ∈ s);
  [apply add_cardinal_1 in i; rewrite i
  |apply add_cardinal_2 in n; rewrite n]; cset_tac.
Qed.

Lemma take_list_incl X `{OrderedType X} (n : nat) (L:list X) :
        of_list (take n L) ⊆ of_list L.
Proof.
  general induction L; destruct n; simpl; eauto with cset.
  rewrite IHL. reflexivity.
Qed.

Lemma take_set_incl X `{OrderedType X} (n : nat) (s : set X) :
        of_list (take n (elements s)) ⊆ s.
Proof.
  rewrite take_list_incl.
  hnf; intros. eapply elements_iff. cset_tac.
Qed.


Lemma elements_length  X `{OrderedType X} (s : set X)
: length (elements s) = cardinal s.
Proof.
  rewrite SetInterface.cardinal_1. reflexivity.
Qed.

Lemma card_in_of_list X `{OrderedType X} ( l: list X) :
  NoDupA _eq l -> cardinal (of_list l) = length l.
Proof.
induction l; intro noDup; simpl; eauto.
- rewrite add_cardinal_2.
  + inversion_clear noDup. apply IHl in H1. rewrite H1. eauto.
  + inversion_clear noDup. intro no. apply <- InA_in in no. contradiction.
Qed.

Lemma elements_of_list_size X `{OrderedType X} ( l : list X) :
  NoDupA _eq l -> length (elements (of_list l)) = length l.
intro noDup. rewrite elements_length. apply card_in_of_list.
exact noDup.
Qed.

Lemma hd_in_list  X `{OrderedType X} ( l : list X)  x :
 l <> nil -> InA _eq (hd x l) l.
intro nonNil.
destruct l.
- isabsurd.
- constructor. simpl. eauto.
Qed.


Lemma hd_in_elements X `{OrderedType X} ( s : set X) x:
 ~ s [=] ∅ -> hd x (elements s) ∈ s.
intro nonEmpty.
apply elements_iff.
apply hd_in_list.
rewrite <- elements_nil_eset.
eauto with cset.
Qed.

Lemma take_dupFree_list X `{OrderedType X} ( l : list X ) (n : nat) :
NoDupA _eq l -> NoDupA _eq (take n l).
Proof.
intro noDup.
induction l; inversion_clear noDup.
- rewrite take_nil. constructor.
- induction n.
  + simpl. constructor.
  + simpl. constructor.
    * admit.
    * apply IHl in H1. admit.
Admitted.

Lemma take_dupFree X `{OrderedType X} ( s : set X ) (n:nat) :
NoDupA _eq (take n (elements s)).
assert (NoDupA _eq (elements s)). { apply elements_3w. }
decide (n <= length (elements s)).
- induction (elements s).
  + rewrite take_nil. constructor.
  + induction n; inversion H0; simpl.
    * constructor.
    * constructor.
      -- intro H5. inversion H4.
         ++ rewrite <- H6 in H5. rewrite take_nil in H5. isabsurd.
         ++ admit.
      -- admit.
- admit.
Admitted.


Lemma of_list_elements (X : set var) : of_list (elements X) [=] X.
Proof.
cset_tac; [apply of_list_1 in H; rewrite elements_iff
          |apply of_list_1; rewrite <- elements_iff] ; eauto.
Qed.


Lemma simplSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var)
  (Λ : list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> cardinal R' <= k
-> getAnn alv ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
(*-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv*)
-> spill_sound k ZL Λ (R,M) s (simplSpill k R' s alv).

Proof.
intros kgeq1 ReqR' RleqK fvRM fvBound lvSound (*pir2*).
general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt
       |k0 f0 Y0
       |k0 Z0 s0 t0 fvBs fvBt];
   simpl in *.



- assert (R \ (R \ Exp.freeVars e) ∪ Exp.freeVars e \ R' [=] Exp.freeVars e)
      as seteq. {
    rewrite minus_minus. rewrite <- ReqR'. clear. cset_tac.
    decide (a ∈ R).
    * left. split; eauto with cset.
    * right. split; eauto with cset.
  }


  assert ((Exp.freeVars e)
            ⊆
            (R' \
              of_list (
                take
                  (cardinal (Exp.freeVars e \ R'))
                  (elements (R' \ Exp.freeVars e))
              ) ∪ Exp.freeVars e \ R')) as fTake.
  {
    assert (
           of_list (
             take
               (cardinal ( Exp.freeVars e \ R'))
               (elements ( R' \ Exp.freeVars e))
           )
           ⊆ R' \ Exp.freeVars e
         ) as takeIncl. { rewrite take_set_incl. eauto with cset. }
         apply incl_minus with (u:=R') in takeIncl.
         rewrite <- seteq at 1.
         rewrite <- ReqR' in takeIncl at 1 2.
         eauto with cset.
  }

  set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  assert (cardinal (R' \ K ∪ Exp.freeVars e \ R') <= k) as rke.
  {
    clear - fTake fvBcard RleqK ReqR' kgeq1.

      decide (cardinal (Exp.freeVars e \ R') <= cardinal (R' \ Exp.freeVars e)).
      * assert (cardinal K = cardinal (Exp.freeVars e \ R')) as crdKL.
        { subst K. rewrite <- elements_length.
          rewrite elements_of_list_size.
          + rewrite take_length_le; eauto. rewrite elements_length. eauto.
          + apply take_dupFree.
        }
        rewrite union_cardinal_le. rewrite cardinal_difference'.
        + rewrite crdKL.
          decide (cardinal (Exp.freeVars e \ R') <= cardinal R').
          - rewrite plus_comm. rewrite <- le_plus_minus; eauto.
          - rewrite not_le_minus_0.
            ** simpl. rewrite cardinal_difference. eauto.
            ** eauto.
        + subst K. rewrite take_set_incl. eauto with cset.
      * apply not_le in n. subst K. rewrite take_eq_ge.
        -- rewrite of_list_elements. rewrite minus_minus.
           enough (R' ∩ Exp.freeVars e ∪ Exp.freeVars e \ R' [=] Exp.freeVars e).
           { rewrite H. eauto. }
           clear. cset_tac. decide (a ∈ R'); cset_tac.
        -- clear - n. rewrite elements_length. omega.
  }

  decide (cardinal (R' \ K ∪ Exp.freeVars e \ R') >= k).
  { rename g into sizeRL.

    set (K_x:=singleton (hd 0 (elements (
                        R' \ K ∪ Exp.freeVars e \ R' )))).

    assert (cardinal {x; (R' \ K ∪ Exp.freeVars e \ R') \ K_x} <= k) as rkk.
    {
      clear - RleqK fvBcard rke kgeq1 sizeRL.
      rewrite add_cardinal. rewrite cardinal_difference'.
      - subst K_x. rewrite singleton_cardinal.
        remember (cardinal (R' \ K ∪ Exp.freeVars e \ R')).
        destruct (cardinal (R' \ K ∪ Exp.freeVars e \ R')).
        + omega.
        + rewrite Heqn. simpl. omega.
      - subst K_x. apply incl_singleton.
        apply hd_in_elements. intro no.
        assert (k >= 1) as geq. { omega. }
        assert (cardinal (R' \ K ∪ Exp.freeVars e \ R') = 0) as emptRE.
        { rewrite no. apply empty_cardinal. }
        rewrite emptRE in sizeRL. omega.
    }

    eapply SpillLet with (K:= K) (Kx := K_x); eauto.

    + eapply IHlvSound; try rewrite ReqR'; eauto.

      * unfold Subset; intro a. decide (a = x); [cset_tac|].
        intro aInAnn. rewrite union_iff.

      decide (   a ∈ K
              \/ a ∈ K_x
              \/ a ∈ M
             ).
      -- right. cset_tac.
      -- left. apply not_or_dist in n0. destruct n0 as [nK nM].
         decide (a = x).
         ++ cset_tac.
         ++ apply add_iff. right.
            unfold Subset in H0. specialize (H0 a).
            unfold Subset in fvRM. specialize (fvRM a).
            assert (a ∈ (getAnn al \ (singleton x))). { cset_tac. }
            assert (a ∈ R'). { cset_tac. rewrite <- ReqR'. eauto. }
            assert (a ∈ R' \ K).
            { cset_tac. } cset_tac.

    + rewrite ReqR'. exact fTake.
    + rewrite ReqR'. exact rke.

    + rewrite ReqR'. exact rkk.
  }

  {
  rename n into sizeRL.


  assert (cardinal (Exp.freeVars e) < k) as leqK.
  { apply not_ge in sizeRL.
    apply subset_cardinal in fTake.
    rewrite <- fTake in sizeRL. exact sizeRL. }

  eapply SpillLet with
            (K:= of_list (take
                            (cardinal (Exp.freeVars e \ R'))
                            (elements (R' \ Exp.freeVars e))
                          )
            )
            (Kx := ∅).
  + eapply IHlvSound; eauto.
    * rewrite ReqR'. cset_tac.
    * clear - sizeRL. rewrite add_cardinal. apply not_ge in sizeRL.
      rewrite minus_empty. omega.
    * rewrite ReqR'. clear - H0 fvRM ReqR'. unfold Subset. intros a aIn.
      apply union_iff.
      decide (a ∈ of_list (take
                            (cardinal (Exp.freeVars e \ R'))
                            (elements (R' \ Exp.freeVars e))
                          )
              \/ a ∈ M
             ).
      -- right. cset_tac.
      -- left. apply not_or_dist in n. destruct n as [nK nM].
         decide (a = x).
         ++ cset_tac.
         ++ apply add_iff. right.
            unfold Subset in H0. specialize (H0 a).
            unfold Subset in fvRM. specialize (fvRM a).
            assert (a ∈ (getAnn al \ (singleton x))). { cset_tac. }
            rewrite minus_empty.
            assert (a ∈ R). { cset_tac. } rewrite ReqR' in H1. cset_tac.

  + rewrite ReqR'. eauto.
  + subst K... rewrite ReqR'. exact rke.
  + rewrite minus_empty. rewrite add_cardinal. apply not_ge in sizeRL.
    rewrite ReqR'. clear - sizeRL. subst K... omega.
  }
- admit.
- admit.
- admit.
- admit.