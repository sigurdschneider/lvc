Require Import List paco2.
Require Export Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Export Sim SimTactics IL BlockType.

Set Implicit Arguments.
Unset Printing Records.

(** * A Framework for Simulation Proofs by Induction: Imperative Version *)

(** ** Proof Relation *)
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

(** ** Parameter Relation and Separation *)

Definition paramrel A (PR:ProofRelationI A)  AL L L' :=
  forall (f f':lab) Z s i Z' s' i' a,
    IndexRelI AL f f'
    -> get AL f a
    -> get L f (I.blockI Z s i)
    -> get L' f' (I.blockI Z' s' i')
    -> ParamRelI a Z Z'.

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

Definition indexes_exists {A} (PR:ProofRelationI A) AL (L L' : I.labenv) :=
  forall n n' a b, IndexRelI AL n n' -> get AL n a -> get L n b -> exists b', get L' n' b'.

Lemma complete_indexes_exists A (PR:ProofRelationI A) F F' AL' AL L L'
  : indexes_exists PR AL L L'
    -> separates PR AL' AL F F'
    -> indexes_exists PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros IE [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? RN GetAL GetF.
  assert (Len3:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetF. destruct GetF as [GetF| [GetFL GE]].
  + inv_get. exploit Ilt; eauto using get_range.
    edestruct get_in_range; eauto.
    eexists; eapply get_app, get_mapi; eauto.
  + eapply get_app_right_ge in GetAL; [ | rewrite Len3; eauto ].
    exploit Ige; eauto. rewrite mapi_length in *; eauto.
    eapply IndexRelDrop in RN; [| rewrite Len3; eauto].
    edestruct IE; eauto. rewrite Len3. eauto.
    rewrite Img in H0. eexists.
    eapply get_app_right; eauto. rewrite mapi_length in *. omega.
Qed.

(** ** Application Relation *)

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

(** ** Label Environment Relation *)

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

Hint Unfold separates.

Lemma labenv_sim_extension' t r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : indexwise_r t (sim r \3/ r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> labenv_sim t (sim r) PR AL L L'
    -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros SIM IPR [Len2 [Img [Ilt Ige]]] [Len1 [STL [STL' [PAR [IE LSIM]]]]].
  hnf; do 5 (try split);
    eauto 20 using smaller_I_mkBlocks, complete_paramrel, complete_indexes_exists with len.
  intros f f' ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (Len3:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
    pone_step. simpl.
    orewrite (f-f=0). orewrite (f'-f'=0). simpl.
    exploit SIM; eauto.
  - intros. exploit Ige; eauto. rewrite mapi_length in GE; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len3; eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto; [| rewrite Len3; eauto].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len3; eauto. rewrite Img; eauto.
    assert (EQf:f=LabI (❬mapi I.mkBlock F❭+(f-❬mapi I.mkBlock F❭))). {
      len_simpl. destruct f; f_equal. simpl in *. omega.
    }
    assert (EQf':f'=LabI (❬mapi I.mkBlock F'❭+(f'-❬mapi I.mkBlock F'❭))). {
      len_simpl. destruct f'; f_equal. simpl in *. omega.
    }
    rewrite EQf, EQf'.
    eapply sim_app_shift_I; eauto. len_simpl.
    rewrite Img, Len3 in *. eauto.
Qed.

(** ** Key Lemmata *)

(** *** Fix Compatibility *)

Lemma fix_compatible_separate t A (PR:ProofRelationI A) AL' AL F F'
  : (forall r L L',
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r L L', labenv_sim t (sim r) PR AL L L'
           -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM LP SEP r L L' SIML. pcofix CIH.
  eapply ISIM.
  eapply labenv_sim_extension'; eauto.
  eauto using indexwise_r_mon; eauto.
  eapply labenv_sim_mon; eauto.
Qed.

(** *** Extension Lemma *)

Lemma labenv_sim_extension t A (PR:ProofRelationI A) (AL AL':list A) F F'
  : (forall r L L',
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r L L', labenv_sim t (sim r) PR AL L L'
        -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP SEP r L L' SIML.
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.

(** *** Fun Compatibility *)


Lemma sim_fun t A (PR:ProofRelationI A) (AL AL':list A) F F' V V' s s'
  : (forall r L L', labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
               -> (sim r \3/ r) t (mapi I.mkBlock F ++ L, V, s) (mapi I.mkBlock F' ++ L', V', s'))
    -> (forall r L L',
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r L L', labenv_sim t (sim r) PR AL L L'
                -> sim r t (L, V, stmtFun F s) (L', V', stmtFun F' s').
Proof.
  intros SIM_s ISIM IP SEP r L L' SIML.
  pone_step.
  eapply SIM_s.
  eapply labenv_sim_extension; eauto.
Qed.


(** *** Specialized Version if function bindings are not changed *)

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

Arguments pointwise_PR_as_PR : simpl never.

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

Lemma labenv_sim_extension_ptw t A (PR:PointwiseProofRelationI A) (AL AL':list A) F F'
  : (forall r L L',
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
        -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r L L', labenv_sim t (sim r) PR AL L L'
        -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP Len1 Len2 r L L' SIML.
  assert (separates PR AL' AL F F'). {
    destruct SIML; dcr.
    hnf; destruct PR; simpl; repeat split; intros; omega.
  }
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.

Lemma sim_fun_ptw t A (PR:PointwiseProofRelationI A) (AL AL':list A) F F' V V' s s'
  : (forall r L L', labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> (sim r \3/ r) t (mapi I.mkBlock F ++ L, V, s) (mapi I.mkBlock F' ++ L', V', s'))
    -> (forall r L L',
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r L L', labenv_sim t (sim r) PR AL L L'
           -> sim r t (L, V, stmtFun F s) (L', V', stmtFun F' s').
Proof.
  intros SIM_s ISIM IP Len1 Len2 r L L' SIML.
  pone_step.
  eapply SIM_s.
  eapply labenv_sim_extension_ptw; eauto.
Qed.

Lemma labenv_sim_app i A (PR:ProofRelationI A) AL L L' r V V' Y Y' (f f':lab) a
  : labenv_sim i (sim r) PR AL L L'
    -> get AL f a
    -> IndexRelI AL f f'
    -> (forall Z s n Z' s' n',
         get L f (I.blockI Z s n)
         -> get L' f' (I.blockI Z' s' n')
         -> ParamRelI a Z Z'
         -> (forall Yv, omap (op_eval V) Y = ⎣ Yv ⎦ -> ❬Z❭ = ❬Yv❭
                 -> exists Y'v, omap (op_eval V') Y' = ⎣ Y'v ⎦ /\
                          ❬Z'❭ = ❬Y'v❭ /\ ArgRelI V V' a Yv Y'v)
           /\ (if isBisim i then
                (omap (op_eval V) Y = None -> omap (op_eval V') Y' = None)
                /\ (❬Z❭ <> ❬Y❭ -> ❬Z'❭ <> ❬Y'❭)
              else True))
    -> sim r i (L, V, stmtApp f Y) (L', V', stmtApp f' Y').
Proof.
  intros LSIM GetAL RN ALL.
  edestruct LSIM as [Len1 [STL [STL' [PAR [IE SIM]]]]]; eauto; dcr.
  inv_get. edestruct IE; eauto.
  destruct x as [Z s n], x0 as [Z' s' n'].
  exploit PAR; eauto.
  edestruct ALL as [A1 A2]; eauto; dcr.
  case_eq (omap (op_eval V) Y); intros.
  - decide (❬Z❭ = ❬Y❭).
    + edestruct A1; dcr; eauto with len.
    + destruct i; simpl in *; dcr.
      * exploit H4; eauto.
        pno_step.
      * perr.
      * perr.
  - destruct i; simpl in *; dcr.
    + exploit H3; eauto. pno_step.
    + perr.
    + perr.
Qed.

(** *** A small study on IL fixed-points in general *)

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
    -> app_r t (sim r) PR AL L L'.
Proof.
  intros SIM.
  hnf; intros.
  pone_step; simpl; eauto with len.
Qed.

Lemma fix_compatible_bodies t A (PR:ProofRelationI A) AL L L'
  : (forall (r:irel) L1 L2, app_r t (sim r) PR AL L1 L2
          -> bodies_r t (sim r) PR AL L1 L2 L L')
    -> forall r, bodies_r t (sim r) PR AL L L' L L'.
Proof.
  intros ISIM r.
  pcofix CIH;
  change (bodies_r t (sim r) PR AL L L' L L');
  change (bodies_r t r PR AL L L' L L') in CIH.
  eapply ISIM.
  eapply bodies_r_app_r; eauto.
Qed.

Lemma stmtApp_sim_tl S `{StateType S} (σ:S) r L E cont C
  : sim r Bisim σ (L, E, stmtApp (LabI cont) nil)
    -> smaller L
    -> sim r Bisim σ (C :: L, E, stmtApp (LabI (1 + cont)) nil).
Proof.
  intros.
  destruct (get_dec L cont) as [[? ?]|].
  - decide (length (block_Z x) = 0).
    + eapply sim_Y_right; eauto; swap 1 2.
      * econstructor; eauto using get. reflexivity.
      * exploit H1; eauto. change (LabI (1 + cont):nat) with (1 + cont).
        simpl in H2.
        orewrite (1 + cont - I.block_n x = 1 + (cont - I.block_n x)).
        simpl. econstructor; eauto. reflexivity. reflexivity.
    + eapply (sim_stuck_exchange _ H0); eauto.
      * stuck. inv H2. simpl in *. inv def. simpl in *. inv_get. congruence.
      * stuck. inv H2. simpl in *. inv def. simpl in *. repeat inv_get. congruence.
  - eapply (sim_stuck_exchange _ H0); eauto.
      * stuck. inv H2. simpl in *. inv def. simpl in *. inv_get.
      * stuck. inv H2. simpl in *. inv def. simpl in *. inv_get.
Qed.
