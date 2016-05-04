Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export EventsActivated StateType paco Equiv Bisim.

Set Implicit Arguments.
Unset Printing Records.

Lemma mutual_block_extension_I r A (AR:ProofRelationI A) F1 F2 F1' F2' ALX AL AL' i L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simILabenv bisim_progeq r AR ALX L1 L2)
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
        fexteqI bisim_progeq AR a (AL ++ ALX) Z s Z' s' /\
        BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n) /\
        ParamRelI a Z Z')
    -> mutual_block
        (simIBlock bisim_progeq r AR (AL ++ ALX) (mapi I.mkBlock F1 ++ L1)
              (mapi I.mkBlock F2 ++ L2)) i AL'
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
  : simILabenv bisim_progeq r AR AL L L'
    -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                             fexteqI bisim_progeq AR a (AL' ++ AL) Z s Z' s'
                             /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n)
                             /\ ParamRelI a Z Z')
    -> get F n (Z,s)
    -> get F' n (Z',s')
    -> get AL' n a
    -> ArgRelI E E' a Yv Y'v
    -> bisim'r r
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
      (SIML:simILabenv bisim_progeq r AR ALX L1 L2)
  :
    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteqI bisim_progeq AR a (AL ++ ALX) Z s Z' s' /\
        BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n) /\
        ParamRelI a Z Z')
    -> mutual_block
        (simIBlock bisim_progeq r AR (AL ++ ALX) (mapi I.mkBlock F1 ++ L1)
              (mapi I.mkBlock F2 ++ L2)) i AL'
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
: simILabenv bisim_progeq r AR AL L L'
  -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                         fexteqI bisim_progeq AR a (AL' ++ AL) Z s Z' s'
                         /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n)
                         /\ ParamRelI a Z Z')
  -> simILabenv bisim_progeq r AR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros.
  hnf; intros.
  econstructor; eauto.
  eapply mutual_block_extension_simple_I; eauto.
Qed.
