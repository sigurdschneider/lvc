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
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e : set var  := R \ K ∪ L in

     let K_x  := if [(cardinal R_e) >= k]
                 (*if [cardinal R >= k /\ cardinal L >= k]*)
                      then singleton (hd 0 (elements R_e))
                      else ∅ in
     let Sp   := getAnn lv ∩ (K ∪ K_x) in
     let R_s  := {x; R_e \ K_x} in

     ann1 (Sp,L,None) (simplSpill k R_s s lv)

| stmtReturn e, _
  => let Fv_e := Exp.freeVars e in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e  := R \ K ∪ L in
     let Sp   := ∅ in

     ann0 (Sp,L,None)

| stmtIf e s1 s2, ann2 LV lv1 lv2
  => let Fv_e := Exp.freeVars e in
     let L    := Fv_e \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_e))) in
     let R_e  := R \ K ∪ L in
     let Sp   := (getAnn lv1 ∪ getAnn lv2) ∩ K in

     ann2 (Sp,L,None) (simplSpill k R_e s1 lv1)
                      (simplSpill k R_e s2 lv2)

| stmtApp f Y, _
  => let Fv_Y := list_union (Exp.freeVars ⊝ Y) in
     let L    := Fv_Y \ R in
     let K    := of_list (take (cardinal L) (elements (R \ Fv_Y))) in
     let Sp   := R in (* to avoid spilling R we would have to keep track on Λ *)
     let R_e  := R \ K ∪ L in

     ann0 (Sp,L,None)

| stmtFun F t, annF LV als lv_t
  => annF (R, ∅, Some ((fun lv => (∅, lv)) ⊝ (List.map getAnn als)))
                      ((fun Zs lv => simplSpill k ∅ (snd Zs) lv) ⊜ F als)
                      (simplSpill k ∅ t lv_t)


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

Lemma in_take_list X `{OrderedType X} (l: list X) (n: nat) (x:X) :
InA _eq x (take n l) -> InA _eq x l.
Proof.
revert n.
induction l; destruct n; simpl; eauto; intros G.
- inv G.
- inv G.
  + constructor; eauto.
  + apply InA_cons_tl. eauto.
Qed.

Lemma take_dupFree_list X `{OrderedType X} ( l : list X ) (n : nat) :
NoDupA _eq l -> NoDupA _eq (take n l).
Proof.
intro noDup. revert n.
induction noDup; destruct n; simpl; eauto using NoDupA.
econstructor; eauto.
- intros no. apply in_take_list in no. contradiction.
Qed.

Lemma take_dupFree X `{OrderedType X} ( s : set X ) (n:nat) :
NoDupA _eq (take n (elements s)).
Proof.
apply take_dupFree_list. apply elements_3w.
Qed.



Lemma of_list_elements X `{OrderedType X} (s : set X)
 : of_list (elements s) [=] s.
Proof.
cset_tac; [apply of_list_1 in H0; rewrite elements_iff
          |apply of_list_1; rewrite <- elements_iff] ; eauto.
Qed.

(**********************************************************************)

Lemma seteq X `{OrderedType X} (s t : set X)
:  s \ (s \ t) ∪ t \ s [=] t.
Proof.
rewrite minus_minus. clear. cset_tac.
decide (a ∈ s).
* left. split; eauto with cset.
* right. split; eauto with cset.
Qed.

Lemma seteq_1 X `{OrderedType X} s t u1 u2 v w :
          s ∪ t ∪ (u1 ∩ v ∪ w)⊆ s ∪ t ∪ (u1 ∪ u2 ∩ v ∪ w).
Proof.
cset_tac.
Qed.

Lemma seteq_2 X `{OrderedType X} s t u1 u2 v w :
          s ∪ t ∪ (u2 ∩ v ∪ w) ⊆ s ∪ t ∪ (u1 ∪ u2 ∩ v ∪ w).
Proof.
cset_tac.
Qed.


Lemma fTake (s t : set var)
 : (t)
            ⊆
            (s \
              of_list (
                take
                  (cardinal (t \ s))
                  (elements (s \ t))
              ) ∪ t \ s).
Proof.
    assert (
           of_list (
             take
               (cardinal ( t \ s))
               (elements ( s \ t))
           )
           ⊆ s \ t
         ) as takeIncl. { rewrite take_set_incl. eauto with cset. }
         apply incl_minus with (u:=s) in takeIncl.
         rewrite <- takeIncl.
         rewrite seteq at 1.
         reflexivity.
Qed.

Lemma rke (s t: set var) (k : nat)
: cardinal s <= k ->
cardinal (t) <= k ->  cardinal (s \
of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  )
 ∪ t \ s) <= k.
Proof.
set (K := of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  )) in *.

decide (cardinal (t \ s) <= cardinal (s \ t)).
* assert (cardinal K = cardinal (t \ s)) as crdKL.
  { subst K. rewrite <- elements_length.
    rewrite elements_of_list_size.
    + rewrite take_length_le; eauto. rewrite elements_length. eauto.
    + apply take_dupFree.
  }
 rewrite union_cardinal_le. rewrite cardinal_difference'.
  + rewrite crdKL.
    decide (cardinal (t \ s) <= cardinal s).
    - rewrite plus_comm.
      rewrite <- le_plus_minus; eauto. (* uses RleqK *)
    - rewrite not_le_minus_0.
      ** simpl. rewrite cardinal_difference. eauto.
      ** eauto.
  + subst K. rewrite take_set_incl. eauto with cset.
* apply not_le in n. subst K. rewrite take_eq_ge.
  + rewrite of_list_elements. rewrite minus_minus.
    enough (s ∩ t ∪ t \ s [=] t).
    { rewrite H. eauto. }
    clear. cset_tac. decide (a ∈ s); cset_tac.
  + clear - n. rewrite elements_length. omega.
Qed.


Lemma rkk (s t  : set var) (k : nat) (x : var)
: let K :=  of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  ) in
  let  K_x := singleton (hd 0 (elements (
                        s \ K ∪ t \ s ))) in
   cardinal s <= k
-> cardinal (t) <= k
-> k > 0
-> cardinal (s \ K ∪ t \ s) >= k

-> cardinal {x; (s \ K ∪ t \ s) \ K_x} <= k.
Proof.
intros K K_x RleqK fvBcard kgeq1 sizeRL.
rewrite add_cardinal. rewrite cardinal_difference'.
- subst K_x. rewrite singleton_cardinal.
  assert (rke := rke s t k RleqK fvBcard).
  remember (cardinal (s \ K ∪ t \ s)).
  destruct n.
  + omega. (*uses kgt0*)
  + simpl.
    enough (S n <= k). { omega. } rewrite Heqn. subst. exact rke.
- subst K_x. apply incl_singleton.
  apply hd_in_elements. intro no.
  assert (k >= 1) as geq. { omega. }
  assert (cardinal (s \ K ∪ t \ s) = 0) as emptRE.
  { rewrite no. apply empty_cardinal. }
  rewrite emptRE in sizeRL. omega.
Qed.

Lemma al_in_rkl (s t u : set var) (e : exp) (al : ann (set var)) (x : var) :
let K :=  of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                  ) in
getAnn al ⊆ s ∪ u ->
 getAnn al
   [<=] (s \
         of_list
           (take (cardinal (t \ s))
              (elements (s \ t))) ∪ t \ s)
        ∪ (getAnn al ∩ K ∪ u).
Proof.
intros K annRM a aIn.
apply union_iff.
decide (a ∈ of_list (take
                       (cardinal (t \ s))
                       (elements (s \ t))
                    )
        \/ a ∈ u).
- right. cset_tac.
- left. apply not_or_dist in n. destruct n as [nK nM].
  assert (a ∈ s) as aInR.
  { clear - nM annRM aIn. unfold Subset in annRM.
    specialize (annRM a aIn). cset_tac. }
  cset_tac.
Qed.

(**********************************************************************)

Lemma simplSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var)
  (Λ : list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> cardinal R' <= k
-> getAnn alv ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv
-> spill_sound k ZL Λ (R,M) s (simplSpill k R' s alv).

Proof.
intros kgeq1 ReqR' RleqK fvRM fvBound lvSound pir2.

general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt
       |k0 f0 Y0
       |k0 Z0 s0 t0 fvBs fvBt];
   simpl in *.



- assert (rke := rke R' (Exp.freeVars e) k RleqK fvBcard).
  assert (fTake := fTake R' (Exp.freeVars e)).
  set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  decide (cardinal (R' \ K ∪ Exp.freeVars e \ R') >= k).
  { rename g into sizeRL.
    set (K_x:=singleton (hd 0 (elements (
                        R' \ K ∪ Exp.freeVars e \ R' )))).

    assert (rkk := rkk R' (Exp.freeVars e) k x).

    eapply SpillLet with (K:= K) (Kx := K_x); eauto.

    + eapply IHlvSound; try rewrite ReqR'; eauto.

      * unfold Subset; intro a. decide (a = x); [cset_tac|].
        intro aInAnn. rewrite union_iff.
        (** this can be simplified using al_in_rkl **)
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
    + rewrite ReqR'. apply fTake.
    + rewrite ReqR'. apply rke.

    + rewrite ReqR'. apply rkk; eauto.
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
    * rewrite ReqR'. clear - H0 fvRM ReqR'.

      (** This can be simplified using al_in_rkl **)
      unfold Subset. intros a aIn.
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
- set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  eapply SpillIf with (K:= K);
  [rewrite ReqR'; apply fTake
  | rewrite ReqR'; apply rke; eauto
  | eapply IHlvSound1
  | eapply IHlvSound2 ];
  try rewrite ReqR'; eauto;
  [ apply rke ; eauto  | | apply rke; eauto | ];
  [ rewrite <- seteq_1 | rewrite <- seteq_2 ];
  subst K; apply al_in_rkl; eauto;
  rewrite <- ReqR'; eauto with cset.
- set (K := of_list (take
                       (cardinal (list_union (Exp.freeVars ⊝ Y) \ R'))
                       (elements (R' \ list_union (Exp.freeVars ⊝ Y)))
                  )) in *.
  eapply PIR2_nth_2 with (l:=counted l) in pir2; eauto using zip_get.
  destruct pir2 as [[R_f M_f] [pir2_get [pir2_R pir2_M]]]. simpl in *.

  eapply SpillApp with (K:= K); try rewrite ReqR'; eauto.
  + subst K. apply rke; eauto.
  + subst K. apply fTake; eauto.
  + rewrite pir2_R. clear. cset_tac.
  + rewrite pir2_M. rewrite H1. rewrite fvRM. rewrite ReqR'. cset_tac.
- set (K := of_list (take
                       (cardinal (Exp.freeVars e \ R'))
                       (elements (R' \ Exp.freeVars e))
                  )) in *.
  eapply SpillReturn with (K:= K); try rewrite ReqR'; eauto.
  + apply fTake.
  + apply rke; eauto.
- eapply SpillFun with (K:=∅); eauto.
  + assert (forall s:set var, s \ ∅ ∪ ∅ [=] s) as seteq'. { cset_tac. }
    rewrite (seteq' R). rewrite ReqR'. apply RleqK.
  + intros ; inv_get. simpl. rewrite empty_cardinal. omega.
  + intros ; inv_get. eapply H1; eauto with cset.
    * rewrite empty_cardinal. omega.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. simpl. split; eauto with cset.
  + eapply IHlvSound; eauto.
    * cset_tac.
c    * rewrite <- ReqR'. rewrite H3. rewrite fvRM. clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. simpl. split; eauto with cset.