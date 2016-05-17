Require Import List paco2.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export Equiv ProofRelations Sim SimTactics IL InRel.

Set Implicit Arguments.
Unset Printing Records.


Ltac simpl_get_dropI :=
  repeat match goal with
  | [ H : get (drop (?n - _) ?L) _ _, H' : get ?L ?n ?blk, STL: sawtooth ?L |- _ ]
    => eapply get_drop in H;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X, H;
        orewrite (n - I.block_n blk + I.block_n blk = n) in H; clear X
  | [ H' : get ?L ?n ?blk, STL: sawtooth ?L |- get (drop (?n - _) ?L) _ _ ]
    => eapply drop_get;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X; simpl;
        orewrite (n - I.block_n blk + I.block_n blk = n); clear X
  end.

Lemma sim_drop_shift_I r l (L:I.labenv) E Y (L':I.labenv) E' Y' blk blk' (STL:sawtooth L) (STL':sawtooth L')
  : get L (labN l) blk
  -> get L' (labN l) blk'
  -> paco2 (@sim_gen I.state _ I.state _) r
          (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
          (drop (labN l - block_n blk') L', E', stmtApp (LabI (block_n blk')) Y')
  -> paco2 (@sim_gen I.state _ I.state _) r (L, E, stmtApp l Y)
          (L', E', stmtApp l Y').
Proof.
  intros. pinversion H1; subst.
  - eapply plus2_destr_nil in H2.
    eapply plus2_destr_nil in H3.
    dcr. inv H5; simpl in *. inv H6; simpl in *.
    simpl_get_dropI. repeat get_functional.
    simpl_minus.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto. eauto.
    econstructor; eauto. eauto.
    eauto.
  - inv H2.
    + exfalso. destruct H4 as [? [? ?]]. inv H4.
    + inv H3.
      * exfalso. destruct H5 as [? [? ?]]. inv H5.
      * inv H9; inv H12; simpl in *.
        pfold. subst yl yl0.
        simpl_get_dropI; repeat get_functional.
        simpl_minus.
        econstructor; try eapply star2_plus2.
        econstructor; eauto. eauto.
        econstructor; eauto. eauto.
        left. pfold. econstructor 2; try eapply star2_refl; eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; simpl; eauto using star2_refl. eauto.
      stuck2. eapply H4.
      do 2 eexists.
      econstructor; eauto.
      simpl. simpl_get_dropI. eauto.
    + inv H6.
      pfold. econstructor 3; try eapply H2; eauto.
      destruct yl; isabsurd.
      simpl in *. simpl_get_dropI. repeat get_functional.
      eapply star2_silent.
      econstructor; eauto.
      eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2. eapply H5.
      do 2 eexists.
      econstructor; eauto.
      simpl. simpl_get_dropI. eauto.
    + inv H8. inv H4; simpl in *.
      * pfold. subst. econstructor 3; try eapply H2; eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
      * inv H11.
        pfold. econstructor 4; try eapply H2; eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto. subst.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
Qed.

Lemma mutual_block_extension_I r A (AR:ProofRelationI A) F1 F2 F1' F2' ALX AL AL' i L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simILabenv sim_progeq r AR ALX L1 L2)
      (CIH: forall a
              (Z Z' : params)
              (Yv Y'v : list val) (s s' : stmt) (n : nat) E1 E2,
          get F1 n (Z, s) ->
          get F2 n (Z', s') ->
          get AL n a ->
          ArgRelI E1 E2 a Yv Y'v ->
          r (mapi I.mkBlock F1 ++ L1, E1 [Z <-- List.map Some Yv], s)
            (mapi I.mkBlock F2 ++ L2, E2 [Z' <-- List.map Some Y'v], s'))
  : (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteqI sim_progeq AR a (AL ++ ALX) Z s Z' s' /\
        BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n) /\
        ParamRelI a Z Z')
    -> mutual_block
        (simIBlock sim_progeq r AR (AL ++ ALX) (mapi I.mkBlock F1 ++ L1)%list
              (mapi I.mkBlock F2 ++ L2)%list) i AL'
        (mapi_impl I.mkBlock i F1')
        (mapi_impl I.mkBlock i F2').
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
      edestruct RelsOKI; eauto. exploit omap_length; try eapply H0; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOKI; eauto. exploit omap_length; try eapply H5; eauto.
      congruence. reflexivity.
      simpl. right. orewrite (i-i=0); simpl.
      eapply CIH; eauto using drop_eq.
Qed.

Lemma fix_compatible_I r A (AR:ProofRelationI A) (a:A) AL F F' E E' Z Z' L L' Yv Y'v s s' n AL'
(LEN1:length F = length F') (LEN2:length AL' = length F)
  : simILabenv sim_progeq r AR AL L L'
    -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                             fexteqI sim_progeq AR a (AL' ++ AL) Z s Z' s'
                             /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n)
                             /\ ParamRelI a Z Z')
    -> get F n (Z,s)
    -> get F' n (Z',s')
    -> get AL' n a
    -> ArgRelI E E' a Yv Y'v
    -> sim'r r
              (mapi I.mkBlock F ++ L, E [Z <-- List.map Some Yv], s)
              (mapi I.mkBlock F' ++ L', E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto.
  hnf; intros.
  econstructor; eauto using simILabenv_mon.
  - eapply mutual_block_extension_I; eauto.
    eapply simILabenv_mon; eauto.
Qed.

Lemma mutual_block_extension_simple_I r A AR F1 F2 F1' F2' ALX AL AL' i L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simILabenv sim_progeq r AR ALX L1 L2)
  :
    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteqI sim_progeq AR a (AL ++ ALX) Z s Z' s' /\
        BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n) /\
        ParamRelI a Z Z')
    -> mutual_block
        (simIBlock sim_progeq r AR (AL ++ ALX) (mapi I.mkBlock F1 ++ L1)%list
              (mapi I.mkBlock F2 ++ L2)%list) i AL'
        (mapi_impl I.mkBlock i F1')
        (mapi_impl I.mkBlock i F2').
Proof.
  intros ASS.
  assert (LEN1':length_eq F1' F2') by (subst; eauto with len).
  assert (LEN2':length_eq AL' F1') by (subst; eauto with len).
  general induction LEN1'; inv LEN2'; eauto using @mutual_block.
  - simpl. econstructor; simpl; eauto using drop_shift_1.
    + destruct x,y. edestruct ASS as [[B1 B2] [B3 B4]]; eauto using drop_eq.
      econstructor; eauto.
      intros. hnf.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOKI; eauto. exploit omap_length; try eapply H; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOKI; eauto. exploit omap_length; try eapply H1; eauto.
      congruence. reflexivity.
      simpl. left. orewrite (i-i=0); simpl.
      eapply fix_compatible_I; eauto.
      eauto using drop_eq. eauto using drop_eq. eauto using drop_eq.
Qed.

Lemma simILabenv_extension r A (AR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
: simILabenv sim_progeq r AR AL L L'
  -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                         fexteqI sim_progeq AR a (AL' ++ AL) Z s Z' s'
                         /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n)
                         /\ ParamRelI a Z Z')
  -> simILabenv sim_progeq r AR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros.
  hnf; intros.
  econstructor; eauto.
  eapply mutual_block_extension_simple_I; eauto.
Qed.
