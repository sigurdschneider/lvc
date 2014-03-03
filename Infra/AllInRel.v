Require Import Coq.Arith.Lt Coq.Arith.Plus Coq.Classes.RelationClasses List.
Require Import Util Get Drop.

(** * AllInRel: Inductive characterization of lists which are element-wise in relation *)

Set Implicit Arguments.

Section AIR2.
  Variable X Y : Type.
  Variable R : list X -> Y -> Prop.
  
  Inductive AIR2 
    : list X -> list Y -> Prop :=
  | AIR2_nil : AIR2 nil nil
  | AIR2_cons x XL y (pf:R (x::XL) y)
    (YL:list Y) :
    AIR2 XL YL ->
    AIR2 (x::XL) (y::YL).

  Lemma AIR2_nth LT L l blkt : 
    AIR2 LT L 
    -> get LT l blkt
    -> exists blk:Y,
      get L l blk /\ R (drop l LT) blk.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHAIR2 as [blk [A B]]; eauto.
    eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR2_drop LT L n 
    : AIR2 LT L -> AIR2 (drop n LT) (drop n L).
  Proof.
    general induction n; simpl; eauto.
    destruct L; inv H; simpl; eauto using AIR2.
  Qed.
  
End AIR2.


Ltac provide_invariants_2 := 
match goal with 
  | [ H : AIR2 ?R ?A ?B, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in 
    destruct (AIR2_nth H H') as [? [? X]]; eauto; inv X;
    repeat get_functional; (try subst);
    let X'' := fresh H in pose proof (AIR2_drop n H) as X'';
    match goal with
      | [ H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
        (try rewrite <- H'' in X'');
          let X' := fresh H in
          pose proof (get_drop_eq H' H'') as X'; inv X'; try clear X'
    end
end.


Section AIR3.
  Variable X Y Z : Type.
  Variable R : list X -> Y -> Z -> Prop.
  
  Inductive AIR3 
    : list X -> list Y -> list Z -> Prop :=
  | AIR3_nil : AIR3 nil nil nil
  | AIR3_cons x XL y z (pf:R (x::XL) y z)
    (YL:list Y) (ZL:list Z) :
    AIR3 XL YL ZL ->
    AIR3 (x::XL) (y::YL) (z::ZL).

  Lemma AIR3_nth LT L L' l blkt : 
    AIR3 LT L L' 
    -> get LT l blkt
    -> exists blk:Y, exists blk':Z,
      get L l blk /\ get L' l blk' /\ R (drop l LT) blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. do 2 eexists.
    split; eauto using get.
    edestruct IHAIR3 as [blk [blk' [A [B C]]]]; eauto.
    do 2 eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR3_nth2 LT L L' l blk : 
    AIR3 LT L L' 
    -> get L l blk
    -> exists blkt, exists blk':Z,
      get LT l blkt /\ get L' l blk' /\ R (drop l LT) blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eauto using get. 
    edestruct IHAIR3 as [blkt [blk' [A [B C]]]]; eauto.
    eauto 20 using get.
  Qed.

  Lemma AIR3_nth3 LT L L' l blk : 
    AIR3 LT L L' 
    -> get L' l blk
    -> exists blkt, exists blk':Y,
                      get LT l blkt /\ get L l blk' /\ R (drop l LT) blk' blk.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eauto using get. 
    edestruct IHAIR3 as [blkt [blk' [A [B C]]]]; eauto.
    eauto 20 using get.
  Qed.

  Lemma AIR3_drop LT L L' n 
    : AIR3 LT L L' -> AIR3 (drop n LT) (drop n L) (drop n L').
  Proof.
    general induction n; simpl; eauto.
    destruct L,L'; inv H; simpl; eauto using AIR3.
  Qed.
  
End AIR3.


Ltac provide_invariants_3 := 
match goal with 
  | [ H : AIR3 ?R ?A ?B ?C, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in 
    destruct (AIR3_nth H H') as [? [? [? [? X]]]]; try eassumption; inversion X; try subst;
    repeat get_functional; (try subst);
    let X'' := fresh H in pose proof (AIR3_drop n H) as X'';
    match goal with
      | [ H' : get ?A ?n ?b, H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
         (try rewrite <- H'' in X'');
          let X' := fresh H in
         pose proof (get_drop_eq H' H'') as X'; inversion X'; try subst; try clear X'
    end 
  | [ H : AIR3 ?R ?A ?B ?C, H' : get ?B ?n ?b |- _ ] =>
    match goal with 
      | [ H'' : get A ?n ?b |- _ ] => fail 1
      | _ => destruct (AIR3_nth2 H H') as [? [? [? [? ?]]]]; dcr; provide_invariants_3
    end
  | [ H : AIR3 ?R ?A ?B ?C, H' : get ?C ?n ?b |- _ ] =>
    match goal with 
      | [ H'' : get A ?n ?b |- _ ] => fail 1
      | _ => destruct (AIR3_nth3 H H') as [? [? [? [? ?]]]]; dcr; provide_invariants_3
    end
end.
(*
match goal with 
  | [ H : AIR3 ?R ?A ?B ?C, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in 
    destruct (AIR3_nth H H') as [? [? [? [? X]]]]; try eassumption; inversion X; try subst;
    repeat get_functional; (try subst);
    let X'' := fresh H in pose proof (AIR3_drop n H) as X'';
    match goal with
      | [ H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
        (try rewrite <- H'' in X'');
          let X' := fresh H in
          pose proof (get_drop_eq H' H'') as X'; inversion X'; try subst; try clear X'
    end
  | [ H : AIR3 ?R ?A ?B ?C, H' : get ?B ?n ?b |- _ ] =>
    match goal with 
      | [ H'' : get A ?n ?b |- _ ] => fail 1
      | _ => destruct (AIR3_nth2 H H') as [? [? [? [? ?]]]]; dcr; provide_invariants_3
    end
end.
*)



Section AIR4.
  Variable W X Y Z : Type.
  Variable R : list W -> list X -> Y -> Z -> Prop.
  
  Inductive AIR4 
    : list W -> list X -> list Y -> list Z -> Prop :=
  | AIR4_nil : AIR4 nil nil nil nil
  | AIR4_cons (w:W) (WL:list W) x XL y z (pf:R (w::WL) (x::XL) y z)
    (YL:list Y) (ZL:list Z) :
    AIR4 WL XL YL ZL ->
    AIR4 (w::WL) (x::XL) (y::YL) (z::ZL).

  Lemma AIR4_nth WL LT L L' l blkw blkt : 
    AIR4 WL LT L L' 
    -> get WL l blkw
    -> get LT l blkt
    -> exists blk:Y, exists blk':Z,
      get L l blk /\ get L' l blk' /\ R (drop l WL) (drop l LT) blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. inv H1. eexists. eexists. 
    split; eauto using get.
    inv H1.
    edestruct IHAIR4 as [blk [blk' [A [B C]]]]; eauto.
    eexists; eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR4_drop WL LT L L' n 
    : AIR4 WL LT L L' -> AIR4 (drop n WL) (drop n LT) (drop n L) (drop n L').
  Proof.
    general induction n; simpl; eauto.
    destruct L,L'; inv H; simpl; eauto using AIR3.
  Qed.

  Lemma AIR4_length WL LT L L'
        : AIR4 WL LT L L' -> length WL = length LT /\ length LT = length L /\ length L = length L'.
  Proof.
    intros. general induction H; eauto; simpl; dcr; repeat split; congruence.
  Qed.
End AIR4.


Ltac provide_invariants_4 :=
    match goal with 
      | [ H : AIR4 ?R ?A ?A' ?B ?C, H' : get ?A ?n ?b, I : get ?A' ?n ?b' |- _ ] => 
        let X := fresh H in 
        destruct (AIR4_nth H H' I) as [? [? [? [? X]]]]; eauto; inv X;
        repeat get_functional; (try subst);
        let X'' := fresh H in pose proof (AIR4_drop n H) as X'';
                             match goal with
                               | [ H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
                                 (try rewrite <- H'' in X'');
                                   let X' := fresh H in
                                   pose proof (get_drop_eq H' H'') as X'; inv X'; try clear X'
                             end 
    end.


Section AIR5.
  Variable U W X Y Z : Type.
  Variable R : list U -> list W -> X -> Y -> Z -> Prop.
  
  Inductive AIR5 
    : list U -> list W -> list X -> list Y -> list Z -> Prop :=
  | AIR5_nil : AIR5 nil nil nil nil nil
  | AIR5_cons (u:U) (UL:list U) (w:W) (WL:list W) x XL y z 
              (pf:R (u::UL) (w::WL) x y z)
              (YL:list Y) (ZL:list Z) :
      AIR5 UL WL XL YL ZL ->
      AIR5 (u::UL) (w::WL) (x::XL) (y::YL) (z::ZL).

  Lemma AIR5_nth UL WL LT L L' l blkw blkt : 
    AIR5 UL WL LT L L' 
    -> get UL l blkw
    -> get WL l blkt
    -> exists lt:X, exists blk:Y, exists blk':Z, 
      get LT l lt /\ get L l blk /\ get L' l blk'
      /\ R (drop l UL) (drop l WL) lt blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. inv H1. do 3 eexists. 
    split; eauto using get.
    inv H1.
    edestruct IHAIR5 as [lt' [blk [blk' [A [B [C D]]]]]]; eauto.
    do 3 eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR5_drop UL WL LT L L' n 
    : AIR5 UL WL LT L L' 
      -> AIR5 (drop n UL) (drop n WL) (drop n LT) (drop n L) (drop n L').
  Proof.
    general induction n; simpl; eauto.
    destruct L,L'; inv H; simpl; eauto.
  Qed.

  Lemma AIR5_length UL WL LT L L'
        : AIR5 UL WL LT L L' 
          -> length UL = length WL
          /\ length WL = length LT 
          /\ length LT = length L 
          /\ length L = length L'.
  Proof.
    intros. general induction H; eauto; simpl; dcr; repeat split; congruence.
  Qed.
End AIR5.


Section PIR2.
  Variable X Y : Type.
  Variable R : X -> Y -> Prop.
  
  Inductive PIR2 
    : list X -> list Y -> Prop :=
  | PIR2_nil : PIR2 nil nil
  | PIR2_cons x XL y (pf:R x y)
    (YL:list Y) :
    PIR2 XL YL ->
    PIR2 (x::XL) (y::YL).

  Lemma PIR2_nth (L:list X) (L':list Y) l blk : 
    PIR2 L L'
    -> get L l blk
    -> exists blk':Y,
      get L' l blk' /\ R blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHPIR2 as [blk' [A B]]; eauto.
    eexists; repeat split; eauto using get.
  Qed.

  Lemma PIR2_nth_2 (L:list X) (L':list Y) l blk : 
    PIR2 L L'
    -> get L' l blk
    -> exists blk',
      get L l blk' /\ R blk' blk.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHPIR2 as [blk' [A B]]; eauto.
    eexists; repeat split; eauto using get.
  Qed.


  Lemma PIR2_drop LT L n 
    : PIR2 LT L -> PIR2 (drop n LT) (drop n L).
  Proof.
    general induction n; simpl; eauto.
    destruct L; inv H; simpl; auto.
  Qed.

End PIR2.

Lemma PIR2_app X Y (R:X->Y->Prop) L1 L2 L1' L2'
: PIR2 R (L1) (L1')
  -> PIR2 R (L2) (L2')
  -> PIR2 R (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. general induction H; eauto using PIR2.
Qed.

Lemma PIR2_get X Y (R:X->Y->Prop) L L'
: (forall n x x', get L n x -> get L' n x' -> R x x')
  -> length L = length L'
  -> PIR2 R L L'.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; eauto 20 using PIR2, get.
Qed.

Ltac provide_invariants_P2 := 
match goal with 
  | [ H : PIR2 ?R ?A ?B, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in 
    destruct (PIR2_nth H H') as [? [? X]]; eauto; inv X;
    repeat get_functional; (try subst) ;
    let X'' := fresh H in pose proof (PIR2_drop n H) as X''
end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)