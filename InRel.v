Require Import AllInRel List Map Env IL AutoIndTac MoreList.
Require Export DecSolve.

Set Implicit Arguments.

Class BlockType X := {
  block_n : X -> nat
}.

Lemma mkBlocks_I_less
      : forall (F : list (params * stmt)) (n k : nat) (b : I.block),
          get (mapi_impl I.mkBlock k F) n b -> I.block_n b <= k + length F - 1.
Proof.
  intros; inv_get. simpl. eapply get_range in H. omega.
Qed.

Lemma mkBlock_I_i F
  : forall i b, get (mapi I.mkBlock F) i b -> i = I.block_n b.
Proof.
  intros; inv_get; eauto.
Qed.

Lemma mkBlock_F_i E F
  : forall i b, get (mapi (F.mkBlock E) F) i b -> i = F.block_n b.
Proof.
  intros; inv_get; eauto.
Qed.

Instance block_type_I : BlockType (I.block) :=
  {
    block_n := I.block_n
  }.

Lemma mkBlocks_F_less
      : forall E (F : list (params * stmt)) (n k : nat) (b : F.block),
          get (mapi_impl (F.mkBlock E) k F) n b -> F.block_n b <= k + length F - 1.
Proof.
  intros; inv_get. simpl. eapply get_range in H. omega.
Qed.

Instance block_type_F : BlockType (F.block) :=
  {
    block_n := F.block_n
  }.

Inductive mutual_block {A} {B} `{BlockType B} {C} `{BlockType C} (R:A->B->C->Prop)
: nat -> list A -> list B -> list C -> Prop :=
  | CS_nil n : mutual_block R n nil nil nil
  | CS_cons a b c n AL L L' :
      mutual_block R (S n) AL L L'
      -> n = block_n b
      -> n = block_n c
      -> R a b c
      -> mutual_block R n (a::AL) (b::L) (c::L').

Lemma mutual_block_zero {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n b i
: mutual_block R i AL L L' -> get L n b -> block_n b = (n+i).
Proof.
  intros. general induction H2. inv H1; eauto.
  inv H1; eauto. erewrite IHget; eauto. omega.
Qed.

Lemma mutual_block_zero' {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n b i
: mutual_block R i AL L L' -> get L' n b -> block_n b = (n+i).
Proof.
  intros. general induction H2. inv H1; eauto.
  inv H1; eauto. erewrite (IHget _ _ _ _ _ _ _ _ H5); eauto. omega.
Qed.

Lemma mutual_block_length {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) i
: mutual_block R i AL L L' -> length AL = length L /\ length L = length L'.
Proof.
  intros. general induction H1; dcr; simpl; eauto.
Qed.

Lemma mutual_block_get {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) i n b
: mutual_block R i AL L L' -> get L n b ->
  exists a c, get AL n a /\ get L' n c /\ R a b c.
Proof.
  intros. general induction H2; inv H1; eauto using get.
  edestruct IHget as [? [? [? []]]]; try do 2 eexists; eauto using get.
Qed.


Lemma mutual_approx_impl {A} {B} `{BlockType B} {C} `{BlockType C}
      (R: list A -> list B -> list C -> A -> B -> C -> Prop)
      (AL:list A) DL (F:list (params*stmt)) AL' F' i f g L1 L2
: length AL = length F
  -> F' = drop i F
  -> AL' = drop i AL
  -> (forall n a Z s,
        get AL n a
        -> get F n (Z,s)
        -> R DL L1 L2 a (f n (Z,s)) (g n (Z,s)))
  -> (forall i b, i = block_n (f i b))
  -> (forall i b, i = block_n (g i b))
  -> mutual_block (R DL L1 L2) i AL' (mapi_impl f i F') (mapi_impl g i F').
Proof.
  intros.
  assert (length_eq AL' F').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  general induction X.
  - simpl; econstructor.
  - simpl. econstructor; eauto.
    eapply IHX; eauto using drop_shift_1.
    destruct y; eapply H4; eauto using drop_eq.
Qed.

Lemma mutual_approx {A} {B} `{BlockType B} {C} `{BlockType C}
      (R: list A -> list B -> list C -> A -> B -> C -> Prop)
      (AL:list A) DL (F:list (params*stmt)) f g L1 L2
: length AL = length F
  -> (forall n a Z s,
        get AL n a
        -> get F n (Z,s)
        -> R DL L1 L2 a (f n (Z,s)) (g n (Z,s)))
  -> (forall i b, i = block_n (f i b))
  -> (forall i b, i = block_n (g i b))
  -> mutual_block (R DL L1 L2) 0 AL (mapi_impl f 0 F) (mapi_impl g 0 F).
Proof.
  intros. eapply mutual_approx_impl; eauto.
Qed.

Lemma mutual_approx_impl2 {A} {B} `{BlockType B} {C} `{BlockType C}
      (R: list A -> list B -> list C -> A -> B -> C -> Prop)
      (AL:list A) DL F1 F2 AL' F1' F2' i L1 L2
  : length AL = length F1
    -> length F1 = length F2
    -> F1' = drop i F1
    -> F2' = drop i F2
    -> AL' = drop i AL
    -> (forall n a b b', get AL n a -> get F1 n b -> get F2 n b' -> R DL L1 L2 a b b')
    -> (forall i b, get F1 i b -> i = block_n b)
    -> (forall i b, get F2 i b -> i = block_n b)
    -> mutual_block (R DL L1 L2) i AL' F1' F2'.
Proof.
  intros LenEq1 LenEq2 LenF1' LenF2' LenAL' GET I1 I2.
  assert (LenAL1:length_eq AL' F1'). subst; eauto using drop_length_stable with len.
  assert (LenAL2:length_eq AL' F2'). subst; eauto using drop_length_stable with len.
  general induction LenAL1; inv LenAL2; eauto using @mutual_block.
  - econstructor; eauto using drop_eq.
    eapply IHLenAL1; eauto using drop_shift_1.
Qed.


Lemma mutual_approx2 {A} {B} `{BlockType B} {C} `{BlockType C}
      (R: list A -> list B -> list C -> A -> B -> C -> Prop)
      (AL:list A) DL F1 F2 L1 L2
  : length AL = length F1
    -> length F1 = length F2
    -> (forall n a b b', get AL n a -> get F1 n b -> get F2 n b' -> R DL L1 L2 a b b')
    -> (forall i b, get F1 i b -> i = block_n b)
    -> (forall i b, get F2 i b -> i = block_n b)
    -> mutual_block (R DL L1 L2) 0 AL F1 F2.
Proof.
  intros. eapply mutual_approx_impl2; eauto.
Qed.

Inductive inRel {A} {B} `{BlockType B} {C} `{BlockType C}
          (R:list A -> list B -> list C -> A -> B -> C -> Prop)
: list A -> list B -> list C -> Prop :=
  | LPM_nil : inRel R nil nil nil
  | LPM_app AL AL' L1 L2 L1' L2' :
      inRel R AL L1 L2
      -> mutual_block (R (AL'++AL) (L1'++L1) (L2'++L2)) 0 AL' L1' L2'
      -> inRel R (AL'++AL) (L1'++L1) (L2'++L2).

Lemma inRel_length {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C)
: inRel R AL L L' -> length AL = length L /\ length L = length L'.
Proof.
  intros. general induction H1; dcr; simpl; eauto.
  repeat rewrite app_length.
  exploit (mutual_block_length H2); eauto; dcr; omega.
Qed.

Lemma inRel_less {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n b
: inRel R AL L L' -> get L n b -> block_n b <= n.
Proof.
  intros. general induction H1. inv H2; eauto.
  eapply get_app_cases in H3; destruct H3; dcr.
  erewrite mutual_block_zero; eauto. omega.
  rewrite IHinRel; try eapply H4. omega.
Qed.

Lemma inRel_drop {A} {B} `{BlockType B} {C} `{BlockType C} R
      (LT:list A) (L:list B) (L':list C) n b
: inRel R LT L L'
  -> get L n b
  -> inRel R
           (drop (n - block_n b) LT)
           (drop (n - block_n b) L)
           (drop (n - block_n b) L').
Proof.
  intros. general induction H1; simpl; eauto.
  - inv H2.
  - eapply get_app_cases in H3; destruct H3; dcr.
    + exploit (mutual_block_zero H2 H3); eauto.
      rewrite H4. orewrite (n - (n + 0)= 0). simpl; econstructor; eauto.
    + exploit (inRel_less H1 H4); eauto.
      specialize (IHinRel _ _ H4).
      assert (length L1' + (n - length L1') = n) by omega.
      rewrite <- H6.
      orewrite (length L1' + (n - length L1') - block_n b
                = length L1' + (n - length L1' - block_n b)).
      exploit (mutual_block_length H2). dcr.
      Typeclasses eauto := 5.
      rewrite <- H8 at 1.
      rewrite H9 at 4.
      repeat rewrite drop_app. eauto.
Qed.

Lemma inRel_nth {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n b
: inRel R AL L L' -> get L n b ->
  exists a:A, exists c:C,
    get AL n a /\ get L' n c /\ R (drop (n - block_n b) AL) (drop (n - block_n b) L) (drop (n - block_n b) L') a b c.
Proof.
  intros. general induction H1; isabsurd.
  eapply get_app_cases in H3; destruct H3; dcr.
  - exploit (mutual_block_zero H2 H3); eauto. rewrite H4.
    orewrite (n - (n + 0) = 0). simpl.
    edestruct (mutual_block_get H2 H3) as [? [? [? []]]].
    do 2 eexists. repeat split; eauto using get_app.
  - edestruct IHinRel; eauto; dcr. do 2 eexists.
    pose proof (mutual_block_length H2); dcr.
    repeat split; try (eapply get_app_right; eauto; omega).
    orewrite (n = length L1' + (n - length L1')).
    exploit (inRel_less H1 H4).
    orewrite (length L1' + (n - length L1') - block_n b
              = length L1' + (n - length L1' - block_n b)).
    Typeclasses eauto :=10.
    rewrite <- H8 at 1. repeat rewrite drop_app. rewrite H10. rewrite drop_app.
    rewrite <- H10. eauto.
Qed.

Lemma inRel_nthA {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n a
: inRel R AL L L' -> get AL n a ->
  exists b:B, exists c:C,
    get L n b /\ get L' n c /\ R (drop (n - block_n b) AL) (drop (n - block_n b) L) (drop (n - block_n b) L') a b c.
Proof.
  intros.
  exploit (inRel_length H1); eauto; dcr.
  edestruct (get_length_eq _ H2 H4); eauto.
  edestruct (inRel_nth H1 H3); eauto; dcr.
  get_functional; subst.
  do 2 eexists; split; eauto.
Qed.

Lemma inRel_nthC {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n c
: inRel R AL L L' -> get L' n c ->
  exists a:A, exists b:B,
    get AL n a /\ get L n b /\ R (drop (n - block_n b) AL) (drop (n - block_n b) L) (drop (n - block_n b) L') a b c.
Proof.
  intros.
  exploit (inRel_length H1); eauto; dcr.
  edestruct (get_length_eq _ H2 (eq_sym H5)); eauto.
  edestruct (inRel_nth H1 H3); eauto; dcr.
  get_functional; subst.
  do 2 eexists; split; eauto.
Qed.



Lemma mutual_block_mon A B (H : BlockType B) (C : Type)
          (H0 : BlockType C)
          (R R': A -> B -> C -> Prop) AL L1 L2 n
:  mutual_block R n AL L1 L2
  -> (forall a b c, R a b c -> R' a b c)
  ->  mutual_block R' n AL L1 L2.
Proof.
  intros. general induction H1.
  - econstructor.
  - econstructor; eauto.
Qed.


Lemma inRel_mon A B (H : BlockType B) (C : Type)
          (H0 : BlockType C)
          (R R': list A -> list B -> list C -> A -> B -> C -> Prop) AL L1 L2
:  inRel R AL L1 L2
  -> (forall AL L1 L2 a b c, R AL L1 L2 a b c -> R' AL L1 L2 a b c)
  ->  inRel R' AL L1 L2.
Proof.
  intros. general induction H1.
  - econstructor.
  - econstructor; eauto using mutual_block_mon.
Qed.

Tactic Notation "inRel_invs" :=
match goal with
  | [ H : inRel ?R ?A ?B ?C, H' : get ?B ?n ?b |- _ ] =>
    let InR := fresh "InR" in let G := fresh "G" in
    edestruct (inRel_nth H H') as [? [? [? [G InR]]]]; (try eassumption); dcr; inversion InR; try subst;
    let X'' := fresh "H" in pose proof (inRel_drop H H') as X'';
    repeat get_functional; (try subst)
    (*match goal with
      | [ H' : get ?A ?n ?b, H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
         (try rewrite <- H'' in X'');
          let X' := fresh H in
         pose proof (get_drop_eq H' H'') as X'; inversion X'; try subst; try clear X'
    end *)
  | [ H : inRel ?R ?A ?B ?C, H' : get ?A ?n ?a |- _ ] =>
    let InR := fresh "InR" in let G := fresh "G" in
    edestruct (inRel_nthA H H') as [? [? [? [G InR]]]]; (try eassumption); dcr; inversion InR; try subst;
    repeat get_functional; (try subst)
    (*match goal with
      | [ H' : get ?A ?n ?b, H'' : ?x :: ?DL = drop ?n ?Lv |- _ ] =>
         (try rewrite <- H'' in X'');
          let X' := fresh H in
         pose proof (get_drop_eq H' H'') as X'; inversion X'; try subst; try clear X'
    end *)
  | [ H : inRel ?R ?A ?B ?C, H' : get ?C ?n ?c |- _ ] =>
    let InR := fresh "InR" in let G := fresh "G" in
    edestruct (inRel_nthC H H') as [? [? [? [G InR]]]]; (try eassumption); dcr; inversion InR; try subst;
    repeat get_functional; (try subst)
end.
