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
     let Sp   := Lv_s ∩ K in
     let R_e : set var  := R \ K ∪ L in

     let K_x  := if [(cardinal R_e) >= k]
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

Lemma incl_minus (X Y Z : set var) : X ⊆ Y -> Z \ Y ⊆ Z \ X.
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

Lemma set_fact (X Y Z : set var)
 : Y ⊆ X \ Z -> X ∩ Z ⊆ X \ Y ∪ Z \ X.
Proof.

Lemma take_list_incl X `{OrderedType X} (n : nat) (L:list X) :
        of_list (take n L) ⊆ of_list L.
Proof.
  general induction L; destruct n; simpl; eauto with cset.
  rewrite IHL. reflexivity.
Qed.

Lemma take_set_incl X `{OrderedType X} (n : nat) (s : set var) :
        of_list (take n (elements s)) ⊆ s.
Proof.
  rewrite take_list_incl.
  hnf; intros. eapply elements_iff. cset_tac.
Qed.

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

  (*decide (cardinal (R \ Exp.freeVars e) >= cardinal (Exp.freeVars e \ R));*)
  decide (cardinal R < k);
  eapply SpillLet with (K:= R \ Exp.freeVars e) (Kx := ∅).
  + eapply IHlvSound; eauto.
    * rewrite seteq.
      enough (
        Exp.freeVars e \ ∅ [=]
        (
          R'\ of_list (
            take (cardinal (Exp.freeVars e \ R'))(elements (R' \ Exp.freeVars e))
          )
          ∪ Exp.freeVars e \ R'
        )
        \
        (
          if [cardinal R' >= k]
          then singleton (
            hd 0 (
              elements (
                R' \ of_list (
                  take (
                    cardinal (Exp.freeVars e \ R')
                  )
                  (elements (R' \ Exp.freeVars e))
                )
                ∪ Exp.freeVars e \ R'
              )
            )
          )
          else {}
        )
      ) as seteq2. (*proof is broken because of fix in simplSpill*)
      { rewrite <- seteq2. eauto with cset. }
      clear - ReqR' kgeq1 fvBs fvBcard seteq.
      decide (cardinal R' >= k).
      -- admit.
      -- apply incl_eq.
         ++ assert (Exp.freeVars e \ ∅ [=] Exp.freeVars e ∪ Exp.freeVars e).
            { cset_tac. } rewrite H. rewrite minus_empty.
            apply incl_union_lr.
            ** assert (
                  of_list (
                    take
                      (cardinal ( Exp.freeVars e \ R'))
                      (elements ( R' \ Exp.freeVars e))
                  )
                  ⊆ R' \ Exp.freeVars e
                ) as takeIncl. { rewrite take_set_incl. eauto with cset. }
                assert (R' \ (R' \ Exp.freeVars e) ⊆ Exp.freeVars e) as rree.
                { rewrite <- ReqR'. rewrite <- seteq at 2. cset_tac. }
                apply incl_minus with (Z:=R') in takeIncl.
                admit.
            ** cset_tac.
         ++ assert (
               of_list (
                 take
                   (cardinal ( Exp.freeVars e \ R'))
                   (elements ( R' \ Exp.freeVars e))
               )
               ⊆ R' \ Exp.freeVars e
             ) as takeIncl. { rewrite take_set_incl. eauto with cset. }
             apply incl_minus with (Z:=R') in takeIncl.
             assert (Exp.freeVars e \ ∅ [=] Exp.freeVars e) as seteq2.
             { cset_tac. }
             rewrite seteq2. rewrite <- seteq at 1.
             rewrite <- ReqR' in takeIncl at 1 2. rewrite minus_empty.
             eauto with cset.

(*
              rewrite erewrite <- takeIncl. { rewrite take_set_incl. eauto with cset. }
  (of_list (take
                              (cardinal (Exp.freeVars e \ R'))
                              (elements (R' \ Exp.freeVars e ))))
                  (R' \ Exp.freeVars e)
                  ).
rewrite incl_minus.
            ---
 apply not_ge in n.
               enough ( kladerradatsch ⊆ Exp.freeVars e \ R' rewrite take_set_incl.
         ++ enough (* WRONG!!! *)
             (
               Exp.freeVars e ∩ R' ⊆
                 R' \ of_list (
                   take
                     (cardinal (Exp.freeVars e \ R'))
                     (elements (R' \ Exp.freeVars e))
                 )
             )  as ErT.
             { replace (Exp.freeVars e \ ∅) with (Exp.freeVars e). {
              rewrite <- TE at 1.

        clear - ReqR' seteq. cset_tac.
        - decide (cardinal (R \ Exp.freeVars e) >= cardinal (Exp.freeVars e \R)).
          + assert (of_list (take (cardinal (Exp.freeVars e \ R'))
                                 (elements (R' \ Exp.freeVars e)))
                    ⊆ R' \ Exp.freeVars e) as subs. {
            apply take_set_incl. }
            apply seteq.
              rewrite <- take_length_le.
(*take_length_le*)
      }*)
    * admit.
  + rewrite seteq. eauto.
  + rewrite seteq. eauto with cset. (*until here it did work out*)
  + rewrite seteq. union_cardinal. (*for this we need the decision on R_e*)