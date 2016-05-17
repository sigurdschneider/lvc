Require Import List paco2.
Require Export Util AutoIndTac AllInRel Sawtooth.
Require Export Equiv ProofRelations Sim SimTactics IL InRel.

Set Implicit Arguments.
Unset Printing Records.


Lemma get_drop_lab0 (L:F.labenv) l blk
:  get L (counted l) blk
   -> get (drop (labN l) L) (counted (LabI 0)) blk.
Proof.
  intros. eapply drop_get; simpl. orewrite (labN l + 0 = labN l); eauto.
Qed.

Lemma drop_get_lab0 (L:F.labenv) l blk
: get (drop (labN l) L) (counted (LabI 0)) blk
  -> get L (counted l) blk.
Proof.
  intros. eapply get_drop in H; simpl in *. orewrite (labN l + 0 = labN l) in H; eauto.
Qed.


Ltac simpl_get_drop :=
  repeat match goal with
  | [ H : get (drop (?n - _) ?L) _ _, H' : get ?L ?n ?blk, STL: sawtooth ?L |- _ ]
    => eapply get_drop in H;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X, H;
        orewrite (n - F.block_n blk + F.block_n blk = n) in H; clear X
  | [ H' : get ?L ?n ?blk, STL: sawtooth ?L |- get (drop (?n - _) ?L) _ _ ]
    => eapply drop_get;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X; simpl;
        orewrite (n - F.block_n blk + F.block_n blk = n); clear X
  end.

Lemma sim_drop_shift r l L E Y L' E' Y' blk blk' (STL:sawtooth L) (STL':sawtooth L')
  : get L (labN l) blk
  -> get L' (labN l) blk'
  -> paco2 (@sim_gen F.state _ F.state _) r
          (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
          (drop (labN l - block_n blk') L', E', stmtApp (LabI (block_n blk')) Y')
  -> paco2 (@sim_gen F.state _ F.state _) r (L, E, stmtApp l Y)
          (L', E', stmtApp l Y').
Proof.
  intros. pinversion H1; subst.
  - eapply plus2_destr_nil in H2.
    eapply plus2_destr_nil in H3.
    destruct H2; destruct H3; dcr. inv H3.
    simpl in *. inv H5; simpl in *.
    simpl_get_drop; repeat get_functional.
    simpl_minus.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  - inv H2.
    + exfalso. destruct H4 as [? [? ?]]. inv H4.
    + inv H3.
      * exfalso. destruct H5 as [? [? ?]]. inv H5.
      * inv H9; inv H12; simpl in *.
        pfold. subst yl yl0.
        simpl_get_drop; repeat get_functional.
        simpl_minus.
        econstructor; try eapply star2_plus2.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        left. pfold. econstructor 2; try eapply star2_refl; eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; simpl; eauto using star2_refl. eauto.
      stuck2. eapply H4.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_drop. eauto.
    + inv H6.
      pfold. econstructor 3; try eapply H2; eauto.
      destruct yl; isabsurd.
      simpl in *. simpl_get_drop. repeat get_functional.
      eapply (star2_silent).
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2. eapply H5.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_drop. eauto.
    + inv H8. inv H4; simpl in *.
      * pfold. subst. econstructor 3; try eapply H2; eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
      * inv H11.
        pfold. econstructor 4; try eapply H2; eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. subst.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
Qed.


Lemma simL_mon (r r0:rel2 F.state (fun _ : F.state => F.state)) A AR L1 L2 (AL:list A)
:  inRel (simB sim_progeq r AR) AL L1 L2
  -> (forall x0 x1 : F.state, r x0 x1 -> r0 x0 x1)
  ->  inRel (simB sim_progeq r0 AR) AL L1 L2.
Proof.
  intros. eapply inRel_mon. eauto.
  intros. inv H1. econstructor; eauto.
  intros. eapply paco2_mon. eapply H4; eauto. eauto.
Qed.

Lemma mutual_block_extension r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simL' sim_progeq r AR ALX L1 L2)
      (CIH: forall a
              (Z Z' : params)
              (Yv Y'v : list val) (s s' : stmt) (n : nat),
          get F1 n (Z, s) ->
          get F2 n (Z', s') ->
          get AL n a ->
          ArgRel E1 E2 a Yv Y'v ->
          r ((mapi (F.mkBlock E1) F1 ++ L1)%list, E1 [Z <-- List.map Some Yv], s)
            ((mapi (F.mkBlock E2) F2 ++ L2)%list, E2 [Z' <-- List.map Some Y'v], s'))
  :

    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteq' sim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
        BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
        ParamRel a Z Z')
    -> mutual_block
        (simB sim_progeq r AR (AL ++ ALX) (mapi (F.mkBlock E1) F1 ++ L1)%list
              (mapi (F.mkBlock E2) F2 ++ L2)%list) i AL'
        (mapi_impl (F.mkBlock E1) i F1')
        (mapi_impl (F.mkBlock E2) i F2').
Proof.
  intros.
  assert (LEN1':length_eq F1' F2').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  assert (LEN2':length_eq AL' F1').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  general induction LEN1'. inv LEN2'.
  - simpl. econstructor.
  - inv LEN2'.
    simpl. econstructor; simpl; eauto.
    + eapply IHLEN1'; eauto using drop_shift_1.
    + destruct x,y. edestruct H as [[B1 B2] [B3 B4]]; eauto using drop_eq.
      econstructor; eauto.
      intros. hnf.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H0; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H5; eauto.
      congruence. reflexivity.
      simpl. right. orewrite (i-i=0); simpl.
      eapply CIH; eauto using drop_eq.
Qed.


Lemma fix_compatible r A AR (a:A) AL F F' E E' Z Z' L L' Yv Y'v s s' n AL'
(LEN1:length F = length F') (LEN2:length AL' = length F)
  : simL' sim_progeq r AR AL L L'
    -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                             fexteq' sim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                             /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                             /\ ParamRel a Z Z')
    -> get F n (Z,s)
    -> get F' n (Z',s')
    -> get AL' n a
    -> ArgRel E E' a Yv Y'v
    -> sim'r r
              ((mapi (F.mkBlock E) F ++ L)%list, E [Z <-- List.map Some Yv], s)
              ((mapi (F.mkBlock E') F' ++ L')%list, E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto.
  hnf; intros.
  econstructor; eauto.
  - eapply simL_mon; eauto.
  - eapply mutual_block_extension; eauto.
    eapply simL_mon; eauto.
Qed.

Lemma mutual_block_extension_simple r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simL' sim_progeq r AR ALX L1 L2)
  :
    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteq' sim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
        BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
        ParamRel a Z Z')
    -> mutual_block
        (simB sim_progeq r AR (AL ++ ALX) (mapi (F.mkBlock E1) F1 ++ L1)%list
              (mapi (F.mkBlock E2) F2 ++ L2)%list) i AL'
        (mapi_impl (F.mkBlock E1) i F1')
        (mapi_impl (F.mkBlock E2) i F2').
Proof.
  intros.
  assert (LEN1':length_eq F1' F2').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  assert (LEN2':length_eq AL' F1').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  general induction LEN1'. inv LEN2'.
  - simpl. econstructor.
  - inv LEN2'.
    simpl. econstructor; simpl; eauto.
    + eapply IHLEN1'; eauto using drop_shift_1.
    + destruct x,y. edestruct H as [[B1 B2] [B3 B4]]; eauto using drop_eq.
      econstructor; eauto.
      intros. hnf.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H0; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H5; eauto.
      congruence. reflexivity.
      simpl. left. orewrite (i-i=0); simpl.
      eapply fix_compatible; eauto.
      eauto using drop_eq. eauto using drop_eq. eauto using drop_eq.
Qed.

Lemma simL_extension' r A AR (AL AL':list A) F F' E E' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
: simL' sim_progeq r AR AL L L'
  -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                         fexteq' sim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                         /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                         /\ ParamRel a Z Z')
  -> simL' sim_progeq r AR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros.
  hnf; intros.
  econstructor; eauto.
  eapply mutual_block_extension_simple; eauto.
Qed.
