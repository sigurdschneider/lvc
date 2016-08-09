Require Import List paco2.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export Sim SimTactics IL BlockType.

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
    IndexRelDrop : forall AL' AL n n', IndexRelI (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelI AL (n - length AL') (n' - Image AL')
}.

Definition irel := rel3 simtype (fun _ : simtype => I.state)
                       (fun (_ : simtype) (_ : I.state) => I.state).

Coercion labN : lab >-> nat.

Definition paramrel A (PR:ProofRelationI A)  AL L L' :=
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
        -> omap (op_eval E) Y = Some Yv
        -> omap (op_eval E') Y' = Some Y'v
        -> ❬Z❭ = ❬Yv❭
        -> ❬Z'❭ = ❬Y'v❭
        -> r t (L, E, stmtApp f Y)
            (L', E', stmtApp f' Y').

Lemma app_r_mon t (r r':irel) A (PR:ProofRelationI A) AL L L'
  : app_r t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> app_r t r' PR AL L L'.
Proof.
  intros Lr LE; hnf; intros; eauto.
Qed.

Definition indexes_exists {A} (PR:ProofRelationI A) AL (L L' : I.labenv) :=
  forall n n' a b, IndexRelI AL n n' -> get AL n a -> get L n b -> exists b', get L' n' b'.

Definition indexwise_indexes_exists A (PR:ProofRelationI A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Zs a,
    IndexRelI (AL' ++ AL) n n'
    -> get AL' n a
    -> get F n Zs
    -> exists Zs', get F' n' Zs'.

Definition labenv_sim t (r:irel)
           {A} (PR:ProofRelationI A) (AL:list A) L L' :=
  length AL = length L /\
  smaller L' /\
  smaller L /\
  paramrel PR AL L L' /\
  indexes_exists PR AL L L' /\
  app_r t r PR AL L L'.

Lemma labenv_sim_nil t r A PR
  : @labenv_sim t r A PR nil nil nil.
Proof.
  do 5 (try split); hnf; intros; isabsurd.
Qed.

Hint Immediate labenv_sim_nil.

Lemma labenv_sim_mon t (r r':irel) A (PR:ProofRelationI A) AL L L'
  :  labenv_sim t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> labenv_sim t r' PR AL L L'.
Proof.
  intros [LEN [STL [STL' [PAR [IE SIM]]]]] LE; hnf; do 5 (try split); eauto.
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


Lemma bodies_r_app_r t A (PR:ProofRelationI A) AL L L' r
  : bodies_r t r PR AL L L' L L'
    -> app_r t (sim'r r) PR AL L L'.
Proof.
  intros SIM.
  hnf; intros.
  pone_step; simpl; eauto with len.
Qed.

Lemma fix_compatible_bodies t A (PR:ProofRelationI A) AL L L'
  : (forall (r:irel) L1 L2, app_r t (sim'r r) PR AL L1 L2
          -> bodies_r t (sim'r r) PR AL L1 L2 L L')
    -> forall r, bodies_r t (sim'r r) PR AL L L' L L'.
Proof.
  intros ISIM r.
  pcofix CIH;
  change (bodies_r t (sim'r r) PR AL L L' L L');
  change (bodies_r t r PR AL L L' L L') in CIH.
  eapply ISIM.
  eapply bodies_r_app_r; eauto.
Qed.

Lemma stepGoto_mapi L blk Y E vl f F k
      (Ldef:get L (counted f - ❬F❭) blk)
      (len:length (I.block_Z blk) = length Y)
      (def:omap (op_eval E) Y = Some vl) E'
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

Definition indexwise_paramrel A (PR:ProofRelationI A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelI a Z Z'.

Definition separates A (PR:ProofRelationI A) AL' AL (F F':〔params * stmt〕) :=
  length AL' = length F
  /\ Image AL' = length F'
  /\ (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
  /\  (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F').

Lemma complete_paramrel A (PR:ProofRelationI A) F F' AL' AL L L'
  : indexwise_paramrel PR F F' AL' AL
    -> paramrel PR AL L L'
    -> separates PR AL' AL F F'
    -> paramrel PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros IPR PAR [Len1 [Img [Ilt Ige]]].
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

Lemma complete_indexes_exists A (PR:ProofRelationI A) F F' AL' AL L L'
  : indexwise_indexes_exists PR F F' AL' AL
    -> indexes_exists PR AL L L'
    -> separates PR AL' AL F F'
    -> indexes_exists PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros IIE IE [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? RN GetAL GetF.
  assert (Len3:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetF. destruct GetF as [GetF| [GetFL GE]].
  + inv_get. edestruct IIE; eauto.
    eexists; eapply get_app, get_mapi; eauto.
  + eapply get_app_right_ge in GetAL; [ | rewrite Len3; eauto ].
    exploit Ige; eauto. rewrite mapi_length in *; eauto.
    eapply IndexRelDrop in RN; [| rewrite Len3; eauto].
    edestruct IE; eauto. rewrite Len3. eauto.
    rewrite Img in H0. eexists.
    eapply get_app_right; eauto. rewrite mapi_length in *. omega.
Qed.

Hint Unfold separates.

Lemma labenv_sim_extension' t r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : indexwise_r t (sim'r r \3/ r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
    -> indexwise_paramrel PR F F' AL' AL
    -> indexwise_indexes_exists PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> labenv_sim t (sim'r r) PR AL L L'
    -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros SIM IPR IIE [Len2 [Img [Ilt Ige]]] [Len1 [STL [STL' [PAR [IE LSIM]]]]].
  hnf; do 5 (try split);
    eauto 20 using smaller_I_mkBlocks, complete_paramrel, complete_indexes_exists with len.
  intros f f' ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (Len3:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
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
    eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite Img in SIMR. rewrite Len3 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto with len.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto with len.
Qed.

Lemma fix_compatible_separate t A (PR:ProofRelationI A) AL' AL F F' L L'
  : (forall r,
        labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> indexwise_indexes_exists PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
           -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM LP IE SEP r SIML. pcofix CIH.
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
    -> indexwise_paramrel PR F F' AL' AL
    -> indexwise_indexes_exists PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
        -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP IE SEP r SIML.
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
}.

Lemma pointwise_PR_as_PR A
  : PointwiseProofRelationI A -> ProofRelationI A.
Proof.
  intros. destruct X as [B C].
  eapply (Build_ProofRelationI B C (fun L n n' => eq n n') (@length _)).
  - intros; dcr; subst; eauto.
Defined.

Hint Resolve pointwise_PR_as_PR : typeclass_instances.
Coercion pointwise_PR_as_PR : PointwiseProofRelationI >-> ProofRelationI.

Lemma IndexRelIP_eq A PR L n n'
  : @IndexRelI A (pointwise_PR_as_PR PR) L n n' <-> n = n'.
Proof.
  destruct PR; simpl. reflexivity.
Qed.

Lemma IndexRelIP_refl A PR L n
  : @IndexRelI A (pointwise_PR_as_PR PR) L n n.
Proof.
  destruct PR; simpl. reflexivity.
Qed.

Hint Resolve IndexRelIP_refl.

Lemma labenv_sim_extension_ptw t A (PR:PointwiseProofRelationI A) (AL AL':list A) F F' L L'
  : (forall r ,
        labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim'r r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> indexwise_indexes_exists PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r, labenv_sim t (sim'r r) PR AL L L'
        -> labenv_sim t (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP IE Len1 Len2 r SIML.
  assert (separates PR AL' AL F F'). {
    destruct SIML; dcr.
    hnf; destruct PR; simpl; repeat split; intros; omega.
  }
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.

Lemma labenv_sim_app i A (PR:ProofRelationI A) AL L L' r V V' Y Y' (f f':lab) a
  : labenv_sim i (sim'r r) PR AL L L'
    -> get AL f a
    -> IndexRelI AL f f'
    -> (forall Z s n Z' s' n',
         get L f (I.blockI Z s n)
         -> get L' f' (I.blockI Z' s' n')
         -> ParamRelI a Z Z'
         -> (forall Yv, omap (op_eval V) Y = ⎣ Yv ⎦ -> ❬Z❭ = ❬Yv❭
                 -> exists Y'v, omap (op_eval V') Y' = ⎣ Y'v ⎦ /\
                          ❬Z'❭ = ❬Y'v❭ /\ ArgRelI V V' a Yv Y'v)
           /\ (i = Bisim -> omap (op_eval V) Y = None -> omap (op_eval V') Y' = None)
           /\ (i = Bisim -> ❬Z❭ <> ❬Y❭ -> ❬Z'❭ <> ❬Y'❭))
    -> sim'r r i (L, V, stmtApp f Y) (L', V', stmtApp f' Y').
Proof.
  intros LSIM GetAL RN ALL.
  edestruct LSIM as [Len1 [STL [STL' [PAR [IE SIM]]]]]; eauto; dcr.
  inv_get. edestruct IE; eauto.
  destruct x as [Z s n], x0 as [Z' s' n'].
  exploit PAR; eauto.
  edestruct ALL as [A1 [A2 A3]]; eauto; dcr.
  case_eq (omap (op_eval V) Y); intros.
  - decide (❬Z❭ = ❬Y❭).
    + edestruct A1; dcr; eauto with len.
    + destruct i.
      * exploit A3; eauto. pno_step.
      * perr.
  - destruct i.
    + exploit A2; eauto. pno_step.
    + perr.
Qed.
