Require Import List paco2.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export Sim SimTactics IL InRel.

Set Implicit Arguments.
Unset Printing Records.

(* A proof relation is parameterized by analysis information A *)
Class ProofRelationI (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelI : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelI : onv val -> onv val -> A-> list val -> list val -> Prop;
    (* Relates environments according to analysis information *)
    IndexRelI : 〔A〕 -> nat -> nat -> Prop;
    Image : 〔A〕 -> nat;
    ArgLengthMatchI : forall E E' a Z Z' VL VL',
        ParamRelI a Z Z' -> ArgRelI E E' a VL VL' -> length Z = length VL /\ length Z' = length VL';
    IndexRelDrop : forall AL' AL n n', IndexRelI (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelI AL (n - length AL') (n' - Image AL')
}.

Definition irel := rel3 simtype (fun _ : simtype => I.state)
                       (fun (_ : simtype) (_ : I.state) => I.state).

Coercion labN : lab >-> nat.

Definition paramrel A (PR:ProofRelationI A) AL L L' :=
  forall (f f':lab) Z s i Z' s' i' a,
    IndexRelI AL f f'
    -> get AL f a
    -> get L f (I.blockI Z s i)
    -> get L' f' (I.blockI Z' s' i')
    -> ParamRelI a Z Z'.

Definition app_r t (r:irel) A (PR:ProofRelationI A) AL (L L':I.labenv) :=
  forall (f f':lab) a Z s i Z' s' i',
    IndexRelI AL f f'
    -> get AL f a
    -> get L f (I.blockI Z s i)
    -> get L' f' (I.blockI Z' s' i')
    -> forall E E' Yv Y'v Y Y',
        ArgRelI E E' a Yv Y'v
        -> omap (exp_eval E) Y = Some Yv
        -> omap (exp_eval E') Y' = Some Y'v
        -> r t (L, E, stmtApp f Y)
            (L', E', stmtApp f' Y').

Lemma app_r_mon t (r r':irel) A (PR:ProofRelationI A) AL L L'
  : app_r t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> app_r t r' PR AL L L'.
Proof.
  intros Lr LE; hnf; intros; eauto.
Qed.

Definition labenv_sim t (r:irel)
           {A} (PR:ProofRelationI A) (AL:list A) L L' :=
  length AL = length L /\
  sawtooth L' /\
  sawtooth L /\
  paramrel PR AL L L' /\
  app_r t r PR AL L L'.

Lemma labenv_sim_mon t (r r':irel) A (PR:ProofRelationI A) AL L L'
  :  labenv_sim t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> labenv_sim t r' PR AL L L'.
Proof.
  intros [LEN [STL [STL' [PAR SIM]]]] LE; hnf; repeat split; eauto.
  eapply app_r_mon; eauto.
Qed.

Definition bodies_r t (r:irel) A (PR:ProofRelationI A) AL (L1 L2 L L':I.labenv) :=
  forall f f' Z s i Z' s' i' a,
    IndexRelI AL f f'
    -> get L f (I.blockI Z s i)
    -> get L' f' (I.blockI Z' s' i')
    -> get AL f a
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r t (drop (f - i) L1, E[Z <-- List.map Some VL], s)
            (drop (f' - i') L2, E'[Z' <-- List.map Some VL'], s').

Lemma bodies_r_mon t (r r':irel) A (PR:ProofRelationI A) AL L1 L2 L L'
  : bodies_r t r PR AL L1 L2 L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> bodies_r t r' PR AL L1 L2 L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Lemma fix_compatible_bodies t A (PR:ProofRelationI A) AL L L'
  : (forall r L1 L2, app_r t (sim'r r) PR AL L1 L2
          -> bodies_r t (sim'r r) PR AL L1 L2 L L')
    -> paramrel PR AL L L'
    -> forall r, bodies_r t (sim'r r) PR AL L L' L L'.
Proof.
  intros ISIM LP r. pcofix CIH.
  eapply ISIM.
  hnf; intros.
  exploit LP; eauto.
  exploit ArgLengthMatchI; eauto; dcr.
  pone_step; simpl; eauto with len.
Qed.

Lemma stepGoto_mapi L blk Y E vl f F k
      (Ldef:get L (counted f - ❬F❭) blk)
      (len:length (I.block_Z blk) = length Y)
      (def:omap (exp_eval E) Y = Some vl) E'
      (updOk:E [I.block_Z blk <-- List.map Some vl] = E')
      (ST:smaller L) (GE: counted f >= ❬F❭) (EQ:k = counted f - ❬F❭ - block_n blk)
  : I.step (mapi I.mkBlock F ++ L, E, stmtApp f Y) EvtTau
           (drop k L,
            E', I.block_s blk).
Proof.
  subst.
  rewrite <- (mapi_length I.mkBlock).
  assert (counted f - block_n blk >= ❬mapi I.mkBlock F❭). {
    exploit (ST _ _ Ldef).
    rewrite mapi_length. simpl in *. omega.
  }
  orewrite (counted f - ❬mapi I.mkBlock F❭ - block_n blk
            =  (counted f - block_n blk) - ❬mapi I.mkBlock F❭).
  rewrite <- (drop_app_gen _ (mapi I.mkBlock F)); eauto.
  eapply I.stepGoto; eauto.
  rewrite get_app_ge. rewrite mapi_length. eauto. omega.
Qed.

Definition indexwise_r t (r:irel) A (PR:ProofRelationI A) AL' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r t (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':irel) A (PR:ProofRelationI A) AL' F F' AL L L'
  : indexwise_r t r PR AL' F F' AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition indexwise_proofrel A (PR:ProofRelationI A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelI a Z Z'.


Lemma indexwise_paramrel A (PR:ProofRelationI A) F F' AL' AL L L'
  : indexwise_proofrel PR F F' AL' AL
    -> paramrel PR AL L L'
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> length AL' = length F
    -> paramrel PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros IPR PAR Ilt Ige Img Len1.
  hnf; intros ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  eapply get_app_cases in GetFL; destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
    eauto.
  - rewrite mapi_length in *; eauto.
    exploit Ige; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len1; eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    eapply IndexRelDrop in RN; [| rewrite Len1; rewrite mapi_length in *; eauto].
    exploit (PAR (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))); eauto.
    rewrite Len1; eauto. rewrite Img; rewrite mapi_length in *; eauto.
Qed.

Definition separates A (PR:ProofRelationI A) AL' AL (F F':〔params * stmt〕) :=
  length AL' = length F
  /\ Image AL' = length F'
  /\ (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
  /\  (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F').

Lemma labenv_sim_extension' t r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : indexwise_r t (sim'r r \3/ r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
    -> indexwise_proofrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> labenv_sim t (sim'r r) PR AL L L'
    -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros SIM IPR [Len2 [Img [Ilt Ige]]] [Len1 [STL [STL' [PAR LSIM]]]].
  hnf; repeat split; eauto using sawtooth_I_mkBlocks, indexwise_paramrel with len.
  intros f f' ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (Len3:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
    exploit IPR; eauto.
    exploit (ArgLengthMatchI); eauto; dcr.
    pone_step; simpl; eauto using get_app, get_mapi; simpl; eauto with len.
    orewrite (f-f=0). orewrite (f'-f'=0). simpl.
    exploit SIM; eauto.
  - exploit Ige; eauto. rewrite mapi_length in GE; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len3; eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto; [| rewrite Len3; eauto].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len3; eauto. rewrite Img; eauto.
    exploit (PAR (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))); eauto.
    rewrite Len3; eauto. rewrite Img; eauto.
    exploit (ArgLengthMatchI); eauto; dcr.
    eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite Img in SIMR. rewrite Len3 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto using @sawtooth_smaller with len.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto using @sawtooth_smaller with len.
Qed.

(*
Lemma labenv_sim_extension' t A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : (forall r L1 L2, labenv_sim t (sim'r r) PR (AL' ++ AL) L1 L2
                -> indexwise_r t (sim'r r) PR AL' F F' AL L1 L2)
    -> indexwise_proofrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> paramrel PR AL L L'
    -> sawtooth L
    -> sawtooth L'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
        -> app_r t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros SIM IPR [Len2 [Img [Ilt Ige]]] PAR STL STL' r LSIM. pcofix CIH.
  intros f f' ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (Len1:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
    exploit IPR; eauto.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit SIM.
    repeat split; [ | | | | eapply app_r_mon; eauto];
      eauto using sawtooth_I_mkBlocks, indexwise_paramrel with len.
    hnf in LSIM; dcr; eauto with len.
    exploit H1; eauto.
    pone_step; simpl; eauto using get_app, get_mapi; simpl; eauto with len.
    left.
    orewrite (f-f=0). orewrite (f'-f'=0). simpl.
    exploit H0; eauto.
  - exploit Ige; eauto. rewrite mapi_length in GE; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len1; eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto; [| rewrite Len1; eauto].
    destruct LSIM as [Len3 [STLx [STL'x [PARx LSIM]]]].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len1; eauto. rewrite Img; eauto.
    exploit (PAR (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))); eauto.
    rewrite Len1; eauto. rewrite Img; eauto.
    exploit (ArgLengthMatchI); eauto; dcr.
    eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite Img in SIMR. rewrite Len1 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto using @sawtooth_smaller with len.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto using @sawtooth_smaller with len.
Qed.
 *)


Lemma fix_compatible_separate t A (PR:ProofRelationI A) AL' AL F F' L L'
  : (forall r,
        labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_proofrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
           -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM LP SEP r SIML. pcofix CIH.
  eapply ISIM.
  eapply labenv_sim_extension'; eauto.
  eauto using indexwise_r_mon; eauto.
  eapply labenv_sim_mon; eauto.
  intros. eapply paco3_mon; eauto.
Qed.


Lemma labenv_sim_extension t A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : (forall r,
        labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_proofrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
        -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP SEP r SIML.
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.


(* A proof relation is parameterized by analysis information A *)
Class PointwiseProofRelationI (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelIP : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelIP : onv val -> onv val -> A-> list val -> list val -> Prop;
    (* Relates environments according to analysis information *)
    ArgLengthMatchIP : forall E E' a Z Z' VL VL',
        ParamRelIP a Z Z' -> ArgRelIP E E' a VL VL' -> length Z = length VL /\ length Z' = length VL';
}.

Lemma pointwise_PR_as_PR A
  : PointwiseProofRelationI A -> ProofRelationI A.
Proof.
  intros. destruct X as [B C D].
  eapply (Build_ProofRelationI B C (fun _ => eq) (@length _) D).
  intros; eauto.
Defined.

Hint Resolve pointwise_PR_as_PR : typeclass_instances.

Coercion pointwise_PR_as_PR : PointwiseProofRelationI >-> ProofRelationI.


Lemma labenv_sim_extension_ptw t A (PR:PointwiseProofRelationI A) (AL AL':list A) F F' L L'
  : (forall r L1 L2, labenv_sim t (sim'r r) PR (AL' ++ AL) L1 L2
                -> indexwise_r t (sim'r r) PR AL' F F' AL L1 L2)
    -> indexwise_proofrel PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
        -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP Len1 Len2 r SIML.
  assert (separates PR AL' AL F F'). {
    destruct SIML; dcr.
    hnf; destruct PR; simpl; repeat split; intros; omega.
  }
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.