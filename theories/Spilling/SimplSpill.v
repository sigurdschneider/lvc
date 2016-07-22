Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.
Require Import Spilling.
Require Import Take Sublist.


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
     let Sp   := Lv_s ∩ K in 
     let R_e : set var  := R \ K ∪ L in

     let K_x  := if [(cardinal R) >= k] 
                      then singleton (hd 0 (elements R_e))
                      else ∅ in 
     let R_s  := {x; R_e \ K_x} in 
     
     ann1 (Sp,L,None) (simplSpill k R_s s lv)


| _,_ => ann0 (∅, ∅, None)
end.

Lemma minus_minus (X Y : set var) : X \ (X \ Y) [=] X ∩ Y.
Proof.
cset_tac.
Qed.

Lemma incl_add_eq (X Y : set var ) (a : var) : {a; Y} ⊆ X <-> a ∈ X /\ Y ⊆ X.
Proof.
split; intros H.
- split. 
  + rewrite add_union_singleton in H; unfold Subset in H. apply H; cset_tac.
  + rewrite <- H. cset_tac.
- destruct H as [ain yx]. decide (a ∈ Y); cset_tac.
Qed.



Lemma subList_fact (l:var) (L1 L2 : list var) (*(m : nat)*)
 : subList L1 L2 0 (*m*) -> subList (l::L1) L2 (S (0 (*m*))).
Proof.
(*induction m.*)
- clear. intros. induction H.
  + constructor. 
  + constructor; eauto. constructor. exact H.
(*-*)
Qed.



Lemma take_list_incl (n: nat) (xs : list var)
 :  subList xs (take n xs) 0.
Proof.
decide (n < length xs). 
{
  revert n l. induction xs; intros n leq.
  - rewrite take_nil. constructor.
  - induction n; simpl.
    + constructor.
    + constructor.
      * constructor.
      * apply subList_fact. apply IHxs. simpl in leq. omega.
} {
  apply not_lt in n0. 
  rewrite take_eq_ge ; [apply subList_refl | eauto].
}
Qed.


Lemma take_set_incl (n : nat) (X : set var) : 
        of_list (take n (elements X)) ⊆ X.
Proof.

assert (subList (elements X) (take n (elements X)) 0).
{ apply take_list_incl. }
induction H.
- eauto with cset.
- simpl. apply incl_add_eq. split; eauto.
  + remember (elements X). induction H.
    * apply elements_iff. rewrite <- Heql0. eauto. 
    * clear - H Heql0. apply IHget. inversion_clear H.
- eauto with cset.
- simpl. apply incl_add_eq. split.
  + apply elements_iff.
    admit.
  + induction H1. 
    * eauto with cset. 
    * simpl. apply incl_add_eq. split.
      -- 

assert 
  (forall ys Y, exists k, subList ys (elements Y) k -> Y ⊆ X-> of_list (take n ys) ⊆ X).
- intros ys. induction ys.
  + rewrite take_nil. eauto with cset.
  + induction n.
    * simpl. eauto with cset.
    * intro Y. exists n. intros sub yx.
      simpl. rewrite incl_add_eq. eapply IHys. ays yx.
intro Y. 
assert (elements Y) as ys.
induction ys.
- eauto with cset.
- simpl. cset_tac. unfold take. unfold of_list. unfold fold_right.
induction n; simpl; intros Y yx; eauto with cset.
remember (elements Y). revert Y yx Heql. induction (elements Y) ; eauto with cset.
- subst l. eauto with cset.
- 
rewrite <- yx.
inducti); simpl; intros Y yx.
+ rewrite take_nil. eauto with cset. 
+ remember (elements X). induction (elements X).
  * decide (n > 0). 
    -- simpl. rewrite Heql; eauto with cset.
  * unfold take in IHn. apply IHn. 




Lemma simplSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var) 
  (Λ : list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> getAnn alv ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv
-> spill_sound k ZL Λ (R,M) s (simplSpill k R' s alv).

Proof.
intros kgeq1 ReqR' fvRM fvBound lvSound pir2. 
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
  decide (cardinal (R \ Exp.freeVars e) >= cardinal (Exp.freeVars e \ R));
  decide (cardinal R < k);
  eapply SpillLet with (K:= R \ Exp.freeVars e) (Kx := ∅).
  + eapply IHlvSound; eauto.
    * rewrite seteq.
      assert ((R' \
        of_list
          (take (cardinal (Exp.freeVars e \ R'))
             (elements (R' \ Exp.freeVars e))) ∪ Exp.freeVars e \ R') \
       (if [cardinal R' >= k] then singleton (hd 0
                                      (elements
                                         (R' \
                                          of_list
                                            (take
                                               (cardinal (Exp.freeVars e \ R'))
                                               (elements (R' \ Exp.freeVars e)))
                                          ∪ Exp.freeVars e \ R'))) else 
        {}) [=] Exp.freeVars e) as seteq2. {
        clear - ReqR' seteq. cset_tac.
        - decide (cardinal (R \ Exp.freeVars e) >= cardinal (Exp.freeVars e \R)).
          + assert (of_list (take (cardinal (Exp.freeVars e \ R')) 
                                 (elements (R' \ Exp.freeVars e))) 
                    ⊆ R' \ Exp.freeVars e) as subs. {
              rewrite <- take_length_le.
(*take_length_le*)
      }
      rewrite seteq2. 
  + rewrite seteq. eauto.
  + rewrite seteq. eauto with cset.
  + rewrite seteq. union_cardinal. 