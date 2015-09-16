Require Import AllInRel List Map Env IL AutoIndTac MoreList.
Require Export DecSolve.

Set Implicit Arguments.

Class BlockType X := {
(*  block_s : X -> stmt;
  block_Z : X -> list var; *)
  block_n : X -> nat
(*  rename_block : env var -> X -> X; *)
(*  block_ctor : forall s Z n, { b : X | block_s b = s /\ block_Z b = Z /\ block_n b = n };
  mkBlocks : onv val -> list (params * stmt) -> list X;
  mkBlocks_closed :
    forall E F n b, get (mkBlocks E F) n b -> block_n b < length F *)
(*  rename_block_s : forall ϱ b, block_s (rename_block ϱ b) = rename ϱ (block_s b);
  rename_block_Z : forall ϱ b, block_Z (rename_block ϱ b) = lookup_list ϱ (block_Z b) *)
}.

Lemma mkBlocks_I_less
      : forall (F : list (params * stmt)) (n k : nat) (b : I.block),
          get (mapi_impl I.mkBlock k F) n b -> I.block_n b <= k + length F - 1.
Proof.
  intros. general induction F; simpl in *; inv H; simpl in *; try omega.
  rewrite IHF; eauto. omega.
Qed.

Global Instance block_type_I : BlockType (I.block) := {
(*  block_s := I.block_s;
  block_Z := I.block_Z; *)
  block_n := I.block_n
(*  mkBlocks := fun _ => I.mkBlocks *)
                                                     }.
(*  rename_block := rename_block_I
}. *)
(*+ intros. eexists (I.blockI Z s n); eauto. (*
+ intros; destruct b; eauto.
+ intros; destruct b; eauto. *)
+ intros. pose proof (@mkBlocks_I_less F n 0 b H).
  destruct F. inv H. simpl in *. omega.
Defined. *)

Lemma mkBlocks_F_less
      : forall E (F : list (params * stmt)) (n k : nat) (b : F.block),
          get (mapi_impl (F.mkBlock E) k F) n b -> F.block_n b <= k + length F - 1.
Proof.
  intros. general induction F; simpl in *; inv H; simpl in *; try omega.
  rewrite IHF; eauto. omega.
Qed.

Global Instance block_type_F : BlockType (F.block) := {
(*  block_s := F.block_s;
  block_Z := F.block_Z; *)
  block_n := F.block_n
(*  mkBlocks := F.mkBlocks *) }.
(*  rename_block := rename_block_F
}. *)
(* + intros. eexists (F.blockI (fun _ => None) Z s n); eauto. (*
+ intros; destruct b; eauto.
+ intros; destruct b; eauto. *)
+ intros. pose proof (@mkBlocks_F_less _ F n 0 b H).
  destruct F. inv H. simpl in *. omega.
Defined.*)

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


Lemma mutual_approx_impl {A} {A'} {B} `{BlockType B} {C} `{BlockType C} (R: list A-> A->B->C->Prop)
      (AL:list A') DL (F:list (params*stmt)) AL' F' i f g zipf
: length AL = length F
  -> F' = drop i F
  -> AL' = drop i AL
  -> (forall n a Z s,
        get AL n a
        -> get F n (Z,s)
        -> R DL (zipf a (Z,s)) (f n (Z,s)) (g n (Z,s)))
  -> (forall i b, i = block_n (f i b))
  -> (forall i b, i = block_n (g i b))
  -> mutual_block (R DL) i (zip zipf AL' F')
                  (mapi_impl f i F') (mapi_impl g i F').
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

Lemma mutual_approx {A} {A'} {B} `{BlockType B} {C} `{BlockType C} (R: list A-> A->B->C->Prop)
      (AL:list A') DL (F:list (params*stmt)) f g zipf
: length AL = length F
  -> (forall n a Z s,
        get AL n a
        -> get F n (Z,s)
        -> R DL (zipf a (Z,s)) (f n (Z,s)) (g n (Z,s)))
  -> (forall i b, i = block_n (f i b))
  -> (forall i b, i = block_n (g i b))
  -> mutual_block (R DL) 0 (zip zipf AL F)
                  (mapi_impl f 0 F) (mapi_impl g 0 F).
Proof.
  intros. eapply mutual_approx_impl; eauto.
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
      rewrite X. orewrite (n - (n + 0)= 0). simpl; econstructor; eauto.
    + exploit (inRel_less H1 H4); eauto.
      specialize (IHinRel _ _ H4).
      assert (length L1' + (n - length L1') = n) by omega.
      rewrite <- H3.
      orewrite (length L1' + (n - length L1') - block_n b
                = length L1' + (n - length L1' - block_n b)).
      exploit (mutual_block_length H2). dcr.
      rewrite <- H6 at 1.
      rewrite H7 at 4.
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
  - exploit (mutual_block_zero H2 H3); eauto. rewrite X.
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
  edestruct (get_length_eq _ H2 H3); eauto.
  edestruct (inRel_nth H1 H5); eauto; dcr.
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
  edestruct (get_length_eq _ H2 (eq_sym H4)); eauto.
  edestruct (inRel_nth H1 H5); eauto; dcr.
  get_functional; subst.
  do 2 eexists; split; eauto.
Qed.


(*
Lemma lpm_less {B} `{BlockType B} L n b
: labenv_parameters_match L -> get L n b -> block_n b <= n.
Proof.
  intros. general induction H0. inv H1; eauto.
  eapply get_app_cases in H3; destruct H3; dcr.
  erewrite  chainsaw_zero; eauto. omega.
  rewrite IHlabenv_parameters_match; try eapply H4. omega.
Qed.

Lemma labenv_parameters_match_get B `{BlockType B} n L (blk:B)
: labenv_parameters_match L
  -> get L n blk
  -> parameters_match (drop (n - block_n blk) L) (block_s blk)
     /\ labenv_parameters_match (drop (n - block_n blk) L).
Proof.
  intros. general induction H0. inv H1.
  eapply get_app_cases in H3; destruct H3; dcr.
  - exploit (eapply chainsaw_zero; eauto). rewrite X.
    orewrite (n - (n + 0) = 0). simpl.
    split; eauto. econstructor; eauto.
  - inv H0. inv H4.
    specialize (IHlabenv_parameters_match _ _ H4).
    assert (length L' + (n - length L') = n) by omega.
    exploit (eapply lpm_less; eauto).
    rewrite <- H8.
    orewrite (length L' + (n - length L') - block_n blk
              = length L' + (n - length L' - block_n blk)).
    rewrite drop_app. eauto.
Qed.
*)
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


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
