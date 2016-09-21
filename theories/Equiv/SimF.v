Require Import List paco2.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export Sim SimTactics IL BlockType.

Set Implicit Arguments.
Unset Printing Records.

(* A proof relation is parameterized by analysis information A *)
Class ProofRelationF (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelF : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelF : A -> list val -> list val -> Prop;
    (* Relates environments according to analysis information *)
    IndexRelF : 〔A〕 -> nat -> nat -> Prop;
    Image : 〔A〕 -> nat;
    IndexRelDrop : forall AL' AL n n', IndexRelF (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelF AL (n - length AL') (n' - Image AL')
}.

Definition frel := rel3 simtype (fun _ : simtype => F.state)
                       (fun (_ : simtype) (_ : F.state) => F.state).

Definition paramrel A (PR:ProofRelationF A) AL L L' :=
  forall (f f':lab) E Z s i E' Z' s' i' a,
    IndexRelF AL f f'
    -> get AL f a
    -> get L f (F.blockI E Z s i)
    -> get L' f' (F.blockI E' Z' s' i')
    -> ParamRelF a Z Z'.

Definition app_r t (r:frel) A (PR:ProofRelationF A) AL L L' :=
  forall (f f':lab) a E Z s i E' Z' s' i',
    IndexRelF AL f f'
    -> get AL f a
    -> get L f (F.blockI E Z s i)
    -> get L' f' (F.blockI E' Z' s' i')
    -> forall E E' Yv Y'v Y Y',
        ArgRelF a Yv Y'v
        -> omap (op_eval E) Y = Some Yv
        -> omap (op_eval E') Y' = Some Y'v
        -> ❬Z❭ = ❬Yv❭
        -> ❬Z'❭ = ❬Y'v❭
        -> r t (L, E, stmtApp f Y)
            (L', E', stmtApp f' Y').

Lemma app_r_mon t (r r':frel) A (PR:ProofRelationF A) AL L L'
  : app_r t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> app_r t r' PR AL L L'.
Proof.
  intros Lr LE; hnf; intros; eauto.
Qed.

Definition indexes_exists {A} (PR:ProofRelationF A) AL (L L' : F.labenv) :=
  forall n n' a b, IndexRelF AL n n' -> get AL n a -> get L n b -> exists b', get L' n' b'.

Definition labenv_sim t (r:frel)
           {A} (PR:ProofRelationF A) (AL:list A) L L' :=
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

Lemma labenv_sim_mon t (r r':frel) A (PR:ProofRelationF A) AL L L'
  :  labenv_sim t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> labenv_sim t r' PR AL L L'.
Proof.
  intros [LEN [STL [STL' [PAR [IE SIM]]]]] LE; hnf; do 5 (try split); eauto.
  eapply app_r_mon; eauto.
Qed.

Definition bodies_r t (r:frel) A (PR:ProofRelationF A) AL (L1 L2 L L':F.labenv) :=
  forall f f' E Z s i E' Z' s' i' a,
    IndexRelF AL f f'
    -> get L f (F.blockI E Z s i)
    -> get L' f' (F.blockI E' Z' s' i')
    -> get AL f a
    -> forall VL VL',
        ArgRelF a VL VL'
        -> r t (drop (f - i) L1, E[Z <-- List.map Some VL], s)
            (drop (f' - i') L2, E'[Z' <-- List.map Some VL'], s').

Lemma bodies_r_mon t (r r':frel) A (PR:ProofRelationF A) AL L1 L2 L L'
  : bodies_r t r PR AL L1 L2 L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> bodies_r t r' PR AL L1 L2 L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.


Lemma bodies_r_app_r t A (PR:ProofRelationF A) AL L L' r
  : bodies_r t r PR AL L L' L L'
    -> app_r t (sim r) PR AL L L'.
Proof.
  intros SIM.
  hnf; intros.
  pone_step; simpl; eauto with len.
Qed.

Lemma fix_compatible_bodies t A (PR:ProofRelationF A) AL L L'
  : (forall (r:frel) L1 L2, app_r t (sim r) PR AL L1 L2
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

Lemma stepGoto_mapi L blk Y E E'' vl f F k
      (Ldef:get L (counted f - ❬F❭) blk)
      (len:length (F.block_Z blk) = length Y)
      (def:omap (op_eval E) Y = Some vl) E'
      (updOk:F.block_E blk [F.block_Z blk <-- List.map Some vl] = E')
      (ST:smaller L) (GE: counted f >= ❬F❭) (EQ:k = counted f - ❬F❭ - block_n blk)
  : F.step (mapi (F.mkBlock E'') F ++ L, E, stmtApp f Y) EvtTau
           (drop k L,
            E', F.block_s blk).
Proof.
  subst.
  rewrite <- (mapi_length (F.mkBlock E'')).
  assert (counted f - block_n blk >= ❬mapi (F.mkBlock E'') F❭). {
    exploit (ST _ _ Ldef).
    rewrite mapi_length. simpl in *. omega.
  }
  orewrite (counted f - ❬mapi (F.mkBlock E'') F❭ - block_n blk
            =  (counted f - block_n blk) - ❬mapi (F.mkBlock E'') F❭).
  rewrite <- (drop_app_gen _ (mapi (F.mkBlock E'') F)); eauto.
  eapply F.StepGoto; eauto.
  rewrite get_app_ge. rewrite mapi_length. eauto. omega.
Qed.

Definition indexwise_r t (r:frel) A (PR:ProofRelationF A) AL' E E' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRelF (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall VL VL',
        ArgRelF a VL VL'
        -> r t (mapi (F.mkBlock E) F ++ L, E[Z <-- List.map Some VL], s)
            (mapi (F.mkBlock E') F' ++ L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':frel) A (PR:ProofRelationF A) AL' E E' F F' AL L L'
  : indexwise_r t r PR AL' E E' F F' AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' E E' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition indexwise_paramrel A (PR:ProofRelationF A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelF (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelF a Z Z'.

Definition separates A (PR:ProofRelationF A) AL' AL (F F':〔params * stmt〕) :=
  length AL' = length F
  /\ Image AL' = length F'
  /\ (forall n n', IndexRelF (AL' ++ AL) n n' -> n < length F -> n' < length F')
  /\  (forall n n', IndexRelF (AL' ++ AL) n n' -> n >= length F -> n' >= length F').

Lemma complete_paramrel A (PR:ProofRelationF A) E E' F F' AL' AL L L'
  : indexwise_paramrel PR F F' AL' AL
    -> paramrel PR AL L L'
    -> separates PR AL' AL F F'
    -> paramrel PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros IPR PAR [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
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

Lemma complete_indexes_exists A (PR:ProofRelationF A) E E' F F' AL' AL L L'
  : indexes_exists PR AL L L'
    -> separates PR AL' AL F F'
    -> indexes_exists PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros IE [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? RN GetAL GetF.
  assert (Len3:forall E, ❬AL'❭ = ❬mapi (F.mkBlock E) F❭) by eauto with len.
  eapply get_app_cases in GetF. destruct GetF as [GetF| [GetFL GE]].
  + inv_get. exploit Ilt; eauto using get_range.
    edestruct get_in_range; eauto.
    eexists; eapply get_app, get_mapi; eauto.
  + eapply get_app_right_ge in GetAL; [ | erewrite Len3; eauto ].
    exploit Ige; eauto. rewrite mapi_length in *; eauto.
    eapply IndexRelDrop in RN; [| erewrite Len3; eauto].
    edestruct IE; eauto. erewrite Len3. eauto.
    rewrite Img in H0. eexists.
    eapply get_app_right; eauto. rewrite mapi_length in *. omega.
Qed.

Hint Unfold separates.

Lemma labenv_sim_extension' t r A (PR:ProofRelationF A) (AL AL':list A) E E' F F' L L'
  : indexwise_r t (sim r \3/ r) PR AL' E E' F F' AL L L'
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> labenv_sim t (sim r) PR AL L L'
    -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros SIM IPR [Len2 [Img [Ilt Ige]]] [Len1 [STL [STL' [PAR [IE LSIM]]]]].
  hnf; do 5 (try split);
    eauto 20 using smaller_F_mkBlocks, complete_paramrel, complete_indexes_exists with len.
  intros f f' ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (Len3:forall E, ❬AL'❭ = ❬mapi (F.mkBlock E) F❭) by eauto with len.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto. eapply get_range in GetFL'.
    rewrite mapi_length in GetFL'; eauto.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto ].
    inv_get. destruct x0 as [Z s], x as [Z' s']. simpl in *. clear EQ0 EQ.
    pone_step; simpl; eauto using get_app, get_mapi; simpl; eauto with len.
    orewrite (f-f=0). orewrite (f'-f'=0). simpl.
    exploit SIM; eauto.
  - exploit Ige; eauto. rewrite mapi_length in GE; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite (Len3 E); eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto; [| rewrite (Len3 E); eauto].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len2; eauto. rewrite Img; eauto.
    eapply (@sim_Y_left F.state _ F.state _).
    eapply (@sim_Y_right F.state _ F.state _).
    rewrite Img in SIMR. rewrite Len2 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto with len.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply stepGoto_mapi; simpl in *; eauto with len.
    erewrite <- Len3, Len2; eauto.
Qed.

Lemma fix_compatible_separate t A (PR:ProofRelationF A) AL' AL E E' F F' L L'
  : (forall r,
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
        -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> indexwise_r t (sim r) PR AL' E E' F F' AL L L'.
Proof.
  intros ISIM LP SEP r SIML. pcofix CIH.
  eapply ISIM.
  eapply labenv_sim_extension'; eauto.
  eauto using indexwise_r_mon; eauto.
  eapply labenv_sim_mon; eauto.
  intros. eapply paco3_mon; eauto.
Qed.


Lemma labenv_sim_extension t A (PR:ProofRelationF A) (AL AL':list A) E E' F F' L L'
  : (forall r,
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
        -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros ISIM IP SEP r SIML.
  eapply labenv_sim_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto. eauto.
Qed.

Lemma sim_fun t A (PR:ProofRelationF A) (AL AL':list A) E E' F F' L L' s s'
  : (forall r, labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> (sim r \3/ r) t (mapi (F.mkBlock E) F ++ L, E, s) (mapi (F.mkBlock E') F' ++ L', E', s'))
    -> (forall r,
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> sim r t (L, E, stmtFun F s) (L', E', stmtFun F' s').

Proof.
  intros SIM_s ISIM IP SEP r SIML.
  pone_step.
  eapply SIM_s.
  eapply labenv_sim_extension; eauto.
Qed.


(* A proof relation is parameterized by analysis information A *)
Class PointwiseProofRelationF (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelFP : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelFP :  A -> list val -> list val -> Prop;
    (* Relates environments according to analysis information *)
}.

Lemma pointwise_PR_as_PR A
  : PointwiseProofRelationF A -> ProofRelationF A.
Proof.
  intros. destruct X as [B C].
  eapply (Build_ProofRelationF B C (fun L n n' => eq n n') (@length _)).
  - intros; dcr; subst; eauto.
Defined.

Arguments pointwise_PR_as_PR : simpl never.

Hint Resolve pointwise_PR_as_PR : typeclass_instances.
Coercion pointwise_PR_as_PR : PointwiseProofRelationF >-> ProofRelationF.

Lemma IndexRelFP_eq A PR L n n'
  : @IndexRelF A (pointwise_PR_as_PR PR) L n n' <-> n = n'.
Proof.
  destruct PR; simpl. reflexivity.
Qed.

Lemma IndexRelFP_refl A PR L n
  : @IndexRelF A (pointwise_PR_as_PR PR) L n n.
Proof.
  destruct PR; simpl. reflexivity.
Qed.

Hint Resolve IndexRelFP_refl.

Lemma labenv_sim_extension_ptw t A (PR:PointwiseProofRelationF A) (AL AL':list A) E E' F F' L L'
  : (forall r ,
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
        -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> indexwise_paramrel PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
        -> labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
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

Lemma sim_fun_ptw t A (PR:PointwiseProofRelationF A) (AL AL':list A) F F' L L' E E' s s'
  : (forall r, labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> (sim r \3/ r) t (mapi (F.mkBlock E) F ++ L, E, s) (mapi (F.mkBlock E') F' ++ L', E', s'))
    -> (forall r,
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> indexwise_paramrel PR F F' AL' AL
    -> length AL' = length F
    -> length F = length F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> sim r t (L, E, stmtFun F s) (L', E', stmtFun F' s').
Proof.
  intros SIM_s ISIM IP Len1 Len2 r SIML.
  pone_step.
  eapply SIM_s.
  eapply labenv_sim_extension_ptw; eauto.
Qed.

Lemma labenv_sim_app i A (PR:ProofRelationF A) AL L L' r V V' Y Y' (f f':lab) a
  : labenv_sim i (sim r) PR AL L L'
    -> get AL f a
    -> IndexRelF AL f f'
    -> (forall E Z s n E' Z' s' n',
         get L f (F.blockI E Z s n)
         -> get L' f' (F.blockI E' Z' s' n')
         -> ParamRelF a Z Z'
         -> (forall Yv, omap (op_eval V) Y = ⎣ Yv ⎦ -> ❬Z❭ = ❬Yv❭
                 -> exists Y'v, omap (op_eval V') Y' = ⎣ Y'v ⎦ /\
                          ❬Z'❭ = ❬Y'v❭ /\ ArgRelF a Yv Y'v)
           /\ (if isBisim i then
                (omap (op_eval V) Y = None -> omap (op_eval V') Y' = None)
                /\ (❬Z❭ <> ❬Y❭ -> ❬Z'❭ <> ❬Y'❭)
              else True))
    -> sim r i (L, V, stmtApp f Y) (L', V', stmtApp f' Y').
Proof.
  intros LSIM GetAL RN ALL.
  edestruct LSIM as [Len1 [STL [STL' [PAR [IE SIM]]]]]; eauto; dcr.
  inv_get. edestruct IE; eauto.
  destruct x as [E Z s n], x0 as [E' Z' s' n'].
  exploit PAR; eauto.
  edestruct ALL as [A1 A2]; eauto; dcr.
  case_eq (omap (op_eval V) Y); intros.
  - decide (❬Z❭ = ❬Y❭).
    + edestruct A1; dcr; eauto with len.
    + destruct i; simpl in *; dcr.
      * exploit H4; eauto.
        pno_step.
      * perr.
  - destruct i; simpl in *; dcr.
    + exploit H3; eauto. pno_step.
    + perr.
Qed.
