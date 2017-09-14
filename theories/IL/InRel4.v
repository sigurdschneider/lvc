Require Import Util LengthEq AllInRel Map Envs IL AutoIndTac MoreList.
Require Export DecSolve BlockType.

Set Implicit Arguments.
Inductive mutual_block {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
: nat -> list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C -> Prop :=
  | CS_nil n : mutual_block R n nil nil nil nil nil nil
  | CS_cons a1 a2 a3 a4 b c n AL1 AL2 AL3 AL4 L L' :
      mutual_block R (S n) AL1 AL2 AL3 AL4 L L'
      -> n = block_n b
      -> n = block_n c
      -> R a1 a2 a3 a4 b c
      -> mutual_block R n (a1::AL1) (a2::AL2) (a3::AL3) (a4::AL4) (b::L) (c::L').


Lemma mutual_block_zero {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b i
: mutual_block R i AL1 AL2 AL3 AL4 L L' -> get L n b -> block_n b = (n+i).
Proof.
  intros. general induction H2. inv H1; eauto.
  inv H1; eauto. erewrite IHget; eauto. omega.
Qed.

Lemma mutual_block_length {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L1:list B) (L2:list C) i
: mutual_block R i AL1 AL2 AL3 AL4 L1 L2 -> ❬AL1❭ = ❬L1❭ /\ ❬AL2❭ = ❬L1❭ /\ ❬AL3❭ = ❬L1❭  /\ ❬AL4❭ = ❬L1❭ /\ ❬L2❭ = ❬L1❭.
Proof.
  intros. general induction H1; dcr; simpl; eauto.
  repeat split; omega.
Qed.

Lemma mutual_block_get {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L1:list B) (L2:list C) i n b
: mutual_block R i AL1 AL2 AL3 AL4 L1 L2 -> get L1 n b ->
  exists a1 a2 a3 a4 c, get AL1 n a1 /\ get AL2 n a2 /\ get AL3 n a3 /\ get AL4 n a4
                   /\ get L2 n c /\ R a1 a2 a3 a4 b c.
Proof.
  intros. general induction H2; inv H1; eauto 20 using get.
  edestruct IHget; dcr; eauto 20 using get.
Qed.

Lemma mutual_block_get_A1 {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L1:list B) (L2:list C) i n a1
: mutual_block R i AL1 AL2 AL3 AL4 L1 L2 -> get AL1 n a1 ->
  exists a2 a3 a4 b c, get AL2 n a2 /\ get AL3 n a3 /\ get AL4 n a4 /\
                   get L1 n b /\ get L2 n c /\ R a1 a2 a3 a4 b c.
Proof.
  intros. general induction H2; inv H1; eauto 20 using get.
  edestruct IHget; dcr; eauto 20 using get.
Qed.

Lemma mutual_approx k {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 AL1' AL2' AL3' AL4' F1 F2 L1 L2
  : length AL1' = length F1
    -> length AL1' = length AL2'
    -> length AL2' = length AL3'
    -> length AL3' = length AL4'
    -> length F1 = length F2
    -> (forall n a1 a2 a3 a4 b b', get AL1' n a1 -> get AL2' n a2 -> get AL3' n a3 -> get AL4' n a4
                             -> get F1 n b -> get F2 n b' -> R AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b b')
    -> (forall i b, get F1 i b -> k + i = block_n b)
    -> (forall i b, get F2 i b -> k + i = block_n b)
    -> mutual_block (R AL1 AL2 AL3 AL4 L1 L2) k AL1' AL2' AL3' AL4' F1 F2.
Proof.
  intros. length_equify.
  general induction H1; eauto using @mutual_block.
  econstructor; eauto using get. eapply IHlength_eq; eauto 20 using get.
  intros. exploit H7. econstructor 2. eauto. omega.
  intros. exploit H8. econstructor 2. eauto. omega.
  exploit H7; eauto using get. omega.
  exploit H8; eauto using get. omega.
Qed.

Inductive inRel {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
          (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
             A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
: list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C -> Prop :=
  | LPM_nil : inRel R nil nil nil nil nil nil
  | LPM_app AL1 AL2 AL3 AL4 AL1' AL2' AL3' AL4' L1 L2 L1' L2' :
      inRel R AL1 AL2 AL3 AL4 L1 L2
      -> mutual_block (R (AL1'++AL1) (AL2'++AL2) (AL3'++AL3) (AL4'++AL4) (L1'++L1) (L2'++L2))
                     0 AL1' AL2' AL3' AL4' L1' L2'
      -> inRel R (AL1'++AL1) (AL2'++AL2) (AL3'++AL3) (AL4'++AL4) (L1'++L1) (L2'++L2).
Lemma inRel_less {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b
: inRel R AL1 AL2 AL3 AL4 L L' -> get L n b -> block_n b <= n.
Proof.
  intros. general induction H1.
  eapply get_app_cases in H3; destruct H3; dcr.
  erewrite mutual_block_zero; eauto. omega.
  rewrite IHinRel; try eapply H4. omega.
Qed.

Lemma inRel_drop {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b
: inRel R AL1 AL2 AL3 AL4 L L'
  -> get L n b
  -> inRel R
          (drop (n - block_n b) AL1)
          (drop (n - block_n b) AL2)
          (drop (n - block_n b) AL3)
          (drop (n - block_n b) AL4)
          (drop (n - block_n b) L)
          (drop (n - block_n b) L').
Proof.
  intros. general induction H1; simpl; eauto; isabsurd.
  - eapply get_app_cases in H3; destruct H3; dcr.
    + exploit (mutual_block_zero H2 H3); eauto.
      rewrite H4. orewrite (n - (n + 0)= 0). simpl; econstructor; eauto.
    + exploit (inRel_less H1 H4); eauto.
      exploit (mutual_block_length H2); dcr.
      specialize (IHinRel _ _ H4).
      repeat (rewrite drop_app_gen; [| omega]).
      assert (REO:forall m, block_n b <= n - ❬L1'❭ -> m = ❬L1'❭
                       -> n - block_n b - m = n - ❬L1'❭ - block_n b). {
        intros. omega.
      }
      repeat (rewrite REO; eauto).
Qed.

Lemma inRel_nth {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b
: inRel R AL1 AL2 AL3 AL4 L L' -> get L n b ->
  exists a1:A1, exists a2:A2, exists a3:A3, exists a4:A4, exists c:C,
            get AL1 n a1 /\ get AL2 n a2 /\ get AL3 n a3 /\ get AL4 n a4 /\ get L' n c
            /\ R (drop (n - block_n b) AL1) (drop (n - block_n b) AL2) (drop (n - block_n b) AL3) (drop (n - block_n b) AL4) (drop (n - block_n b) L) (drop (n - block_n b) L') a1 a2 a3 a4 b c.
Proof.
  intros. general induction H1; isabsurd.
  eapply get_app_cases in H3; destruct H3; dcr.
  - exploit (mutual_block_zero H2 H3); eauto. rewrite H4.
    orewrite (n - (n + 0) = 0). simpl.
    edestruct (mutual_block_get H2 H3); dcr.
    eauto 20 using get_app, get.
  - edestruct IHinRel; eauto; dcr.
    pose proof (mutual_block_length H2); dcr.
    do 5 eexists.
    repeat split; try (eapply get_app_right; [ | eauto ]; omega).
    exploit (inRel_less H1 H4); eauto.
    repeat (rewrite drop_app_gen; [| omega]).
    assert (REO:forall m, block_n b <= n - ❬L1'❭ -> m = ❬L1'❭
                     -> n - block_n b - m = n - ❬L1'❭ - block_n b). {
      intros. omega.
    }
    repeat (rewrite REO; eauto).
Qed.

Lemma inRel_nth_A1 {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n a1
: inRel R AL1 AL2 AL3 AL4 L L' -> get AL1 n a1 ->
  exists a2:A2, exists a3:A3, exists a4:A4, exists b:B, exists c:C,
            get AL2 n a2 /\ get AL3 n a3 /\ get AL4 n a4 /\ get L n b /\ get L' n c
            /\ R (drop (n - block_n b) AL1) (drop (n - block_n b) AL2) (drop (n - block_n b) AL3) (drop (n - block_n b) AL4) (drop (n - block_n b) L) (drop (n - block_n b) L') a1 a2 a3 a4 b c.
Proof.
  intros. general induction H1; isabsurd.
  eapply get_app_cases in H3; destruct H3; dcr.
  - edestruct (mutual_block_get_A1 H2 H3); dcr.
    exploit (mutual_block_zero H2 H8); eauto.
    eexists x, x0, x1, x2, x3.
    rewrite H4.
    orewrite (n - (n + 0) = 0). simpl.
    eauto 20 using get_app, get.
  - edestruct IHinRel; eauto; dcr.
    pose proof (mutual_block_length H2); dcr.
    do 5 eexists.
    repeat split; try (eapply get_app_right; [ | eauto ]; omega).
    exploit (inRel_less H1 H9); eauto.
    repeat (rewrite drop_app_gen; [| omega]).
    assert (REO:forall m, block_n x2 <= n - ❬AL1'❭ -> m = ❬AL1'❭
                     -> n - block_n x2 - m = n - ❬AL1'❭ - block_n x2). {
      intros. omega.
    }
    repeat (rewrite REO; eauto); try congruence.
Qed.

Tactic Notation "inRel_invs" :=
  match goal with
  | [ H : inRel ?R ?A1 ?A2 ?A3 ?A4 ?B ?C, H' : get ?A1 ?n ?b |- _ ] =>
    let InR := fresh "InR" in
    let G := fresh "G" in
    let GetL := fresh "GetL" in
    edestruct (inRel_nth_A1 H H') as [? [? [? [? [? [? [? [? [GetL [? ]]]]] ]]]]];
    let X'' := fresh "H" in
    pose proof (inRel_drop H GetL) as X'';
    repeat get_functional
  end.


Lemma mutual_block_map_A3 {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1' AL1 AL2' AL2 AL3' AL3 AL4' AL4 L1' L1 L2' L2 n (f: A3 -> A3)
      (Rf: forall AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b1 b2,
          R AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b1 b2 ->
          R AL1 AL2 (f ⊝ AL3) AL4 L1 L2 a1 a2 (f a3) a4 b1 b2 )
  : mutual_block
      (R AL1 AL2 AL3 AL4 L1 L2) n AL1' AL2' AL3' AL4' L1' L2'
    -> mutual_block (R AL1 AL2 (f ⊝ AL3) AL4 L1 L2) n AL1' AL2' (f ⊝ AL3') AL4' L1' L2'.
Proof.
  intros. general induction H1; eauto using @mutual_block.
  simpl. econstructor; eauto.
Qed.

Lemma inRel_map_A3 {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 L1 L2 (f: A3 -> A3)
      (Rf: forall AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b1 b2,
          R AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b1 b2 ->
          R AL1 AL2 (f ⊝ AL3) AL4 L1 L2 a1 a2 (f a3) a4 b1 b2 )
  : inRel R AL1 AL2 AL3 AL4 L1 L2
    -> inRel R AL1 AL2 (f ⊝ AL3) AL4 L1 L2.
Proof.
  intros IR.
  general induction IR; simpl in *; eauto using @inRel.
  - rewrite List.map_app. econstructor; eauto.
    rewrite <- List.map_app.
    eapply mutual_block_map_A3; eauto.
Qed.

Lemma inRel_length  {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 L1 L2
  : inRel R AL1 AL2 AL3 AL4 L1 L2 -> length AL1 = length AL2 /\ length AL2 = length AL3
                                   /\ length AL3 = length AL4 /\ length L1 = length L2.
Proof.
  intros. general induction H1; dcr; simpl; eauto.
  repeat rewrite app_length.
  exploit (mutual_block_length H2); eauto; dcr; omega.
Qed.
