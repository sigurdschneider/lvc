Require Import List paco2.
Require Export Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Export Sim SimTactics IL BlockType Sawtooth.

Set Implicit Arguments.
Unset Printing Records.

(** * A Framework for Simulation Proofs by Induction: Functional Version *)

(** ** Proof Relation *)
(* A proof relation is parameterized by analysis information A *)

Class ProofRelationF (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelF : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelF : onv val -> onv val -> A -> list val -> list val -> Prop;
    (* Relates environments according to analysis information *)
    IndexRelF : 〔A〕 -> nat -> nat -> Prop;
    Image : 〔A〕 -> nat;
    IndexRelDrop : forall AL' AL n n', IndexRelF (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelF AL (n - length AL') (n' - Image AL')
}.

Definition frel := rel3 simtype (fun _ : simtype => F.state)
                       (fun (_ : simtype) (_ : F.state) => F.state).

(** ** Parameter Relation and Separation *)

Definition paramrel A (PR:ProofRelationF A) AL L L' :=
  forall (f f':lab) E Z s i E' Z' s' i' a,
    IndexRelF AL f f'
    -> get AL f a
    -> get L f (F.blockI E Z s i)
    -> get L' f' (F.blockI E' Z' s' i')
    -> ParamRelF a Z Z'.

Definition separates A (PR:ProofRelationF A) AL' AL X (F F':〔X〕) :=
  length AL' = length F
  /\ Image AL' = length F'
  /\ (forall n n', IndexRelF (AL' ++ AL) n n' -> n < length F -> n' < length F')
  /\  (forall n n', IndexRelF (AL' ++ AL) n n' -> n >= length F -> n' >= length F').

Hint Unfold separates.

Lemma paramrel_app A (PR:ProofRelationF A) AL' L1 L2 AL L L'
  : paramrel PR (AL' ++ AL) L1 L2
    -> paramrel PR AL L L'
    -> separates PR AL' AL L1 L2
    -> paramrel PR (AL' ++ AL) (L1 ++ L) (L2 ++ L').
Proof.
  intros IPR PAR [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  eapply get_app_cases in GetFL; destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto.
    eapply get_app_lt_1 in GetL'; [| eauto with len].
    inv_get.
    eapply IPR; eauto.
    eapply get_app; eauto.
  - exploit Ige; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len1; eauto ].
    eapply get_app_right_ge in GetL'; [ | eauto ].
    eapply IndexRelDrop in RN; [| rewrite Len1; eauto].
    exploit (PAR (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))); eauto.
    rewrite Len1; eauto. rewrite Img; eauto.
Qed.

Definition indexes_exists {A} (PR:ProofRelationF A) AL (L L' : F.labenv) :=
  forall n n' a b, IndexRelF AL n n' -> get AL n a -> get L n b -> exists b', get L' n' b'.

Lemma complete_indexes_exists A (PR:ProofRelationF A) L1 L2 AL' AL L L'
  : indexes_exists PR AL L L'
    -> separates PR AL' AL L1 L2
    -> indexes_exists PR (AL' ++ AL) (L1 ++ L) (L2 ++ L').
Proof.
  intros IE [Len1 [Img [Ilt Ige]]].
  hnf; intros ? ? ? ? RN GetAL GetF.
  eapply get_app_cases in GetF. destruct GetF as [GetF| [GetFL GE]].
  + inv_get. exploit Ilt; eauto using get_range.
    edestruct get_in_range; eauto.
    eexists; eapply get_app; eauto.
  + eapply get_app_right_ge in GetAL; [ | omega ].
    exploit Ige; eauto.
    eapply IndexRelDrop in RN; [| omega ].
    rewrite <- Len1 in *.
    edestruct IE; eauto.
    eexists.
    eapply get_app_right; eauto. omega.
Qed.

(** ** Application Relation *)

Definition app_r t (r:frel) A (PR:ProofRelationF A) AL L L' :=
  forall (f f':lab) a E Z s i E' Z' s' i',
    IndexRelF AL f f'
    -> get AL f a
    -> get L f (F.blockI E Z s i)
    -> get L' f' (F.blockI E' Z' s' i')
    -> forall V V' Yv Y'v Y Y',
        ArgRelF E E' a Yv Y'v
        -> omap (op_eval V) Y = Some Yv
        -> omap (op_eval V') Y' = Some Y'v
        -> ❬Z❭ = ❬Yv❭
        -> ❬Z'❭ = ❬Y'v❭
        -> r t (L, V, stmtApp f Y)
            (L', V', stmtApp f' Y').

Lemma app_r_mon t (r r':frel) A (PR:ProofRelationF A) AL L L'
  : app_r t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> app_r t r' PR AL L L'.
Proof.
  intros Lr LE; hnf; intros; eauto.
Qed.

(** ** Label Environment Relation *)

Definition labenv_sim t (r:frel)
           {A} (PR:ProofRelationF A) (AL:list A) L L' :=
  length AL = length L /\
  sawtooth L' /\
  sawtooth L /\
  paramrel PR AL L L' /\
  indexes_exists PR AL L L' /\
  app_r t r PR AL L L'.

Lemma labenv_sim_nil t r A PR
  : @labenv_sim t r A PR nil nil nil.
Proof.
  do 5 (try split); hnf; intros; isabsurd. econstructor. econstructor.
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
        ArgRelF E E' a VL VL'
        -> r t (drop (f - i) L1, E[Z <-- List.map Some VL], s)
            (drop (f' - i') L2, E'[Z' <-- List.map Some VL'], s').

Lemma bodies_r_mon t (r r':frel) A (PR:ProofRelationF A) AL L1 L2 L L'
  : bodies_r t r PR AL L1 L2 L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> bodies_r t r' PR AL L1 L2 L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Lemma labenv_sim_extension_cases t r A (PR:ProofRelationF A) (AL AL':list A) L1 L2 L L'
  : bodies_r t (sim r \3/ r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L') L1 L2
    -> paramrel PR (AL' ++ AL) L1 L2
    -> separates PR AL' AL L1 L2
    -> labenv_sim t (sim r) PR AL L L'
    -> sawtooth L1 -> sawtooth L2
    -> labenv_sim t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L').
Proof.
  intros SIM IPR [Len2 [Img [Ilt Ige]]] [Len1 [STL [STL' [PAR [IE LSIM]]]]] SM1 SM2.
  hnf; do 5 (try split);
    eauto 20 using sawtooth_app, paramrel_app, complete_indexes_exists with len.
  intros f f' ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  eapply get_app_cases in GetFL. destruct GetFL as [GetFL'| [GetFL GE]].
  - exploit Ilt; eauto.
    inv_get.
    intros.
    pone_step; simpl; eauto using get_app, get_mapi; simpl; eauto with len.
    exploit SIM; eauto using IndexRelDrop, get_app.
  - intros. exploit Ige; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len2; eauto ].
    eapply get_app_right_ge in GetL'; [ | eauto ].
    eapply IndexRelDrop in RN; eauto; [| rewrite Len2; eauto].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len2; eauto. rewrite Img; eauto.
    destruct f, f'; simpl in *.
    orewrite (n = ❬L1❭ + (n - ❬L1❭)).
    orewrite (n0 = ❬L2❭ + (n0 - ❬L2❭)).
    eapply sim_app_shift_F; eauto using sawtooth_smaller.
    rewrite Len2 in *; rewrite Img in *. eauto.
Qed.

Definition indexwise_r t (r:frel) A (PR:ProofRelationF A) AL' E E' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRelF (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall VL VL',
        ArgRelF E E' a VL VL'
        -> r t (mapi (F.mkBlock E) F ++ L, E[Z <-- List.map Some VL], s)
            (mapi (F.mkBlock E') F' ++ L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':frel) A (PR:ProofRelationF A) AL' E E' F F' AL L L'
  : indexwise_r t r PR AL' E E' F F' AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' E E' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Lemma indexwise_r_bodies_r r t A (PR:ProofRelationF A) AL' AL E E' F F' L L' (Len:❬AL'❭ = ❬F❭)
  : indexwise_r t r PR AL' E E' F F' AL L L'
    <-> bodies_r t r PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
               (mapi (F.mkBlock E) F) (mapi (F.mkBlock E') F').
Proof.
  split; intros; hnf; intros.
  - inv_get. destruct x,x0. simpl in *. exploit H; eauto.
    orewrite (i - i = 0).   orewrite (i' - i' = 0). eauto.
  - eapply (@mapi_get_1 0 _ _ _ (F.mkBlock E)) in H1.
    eapply (@mapi_get_1 0 _ _ _ (F.mkBlock E')) in H2.
    exploit H; eauto using get_app.
    simpl in *.
    orewrite (n - n = 0) in H5.
    orewrite (n' - n' = 0) in H5. eauto.
Qed.

(** ** Key Lemmata *)

(** ***  Fix Compatibility *)

Lemma fix_compatible_separate t A (PR:ProofRelationF A) AL' AL E E' F F' L L'
  : (forall r,
        labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
        -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    -> paramrel PR (AL'++ AL) (mapi (F.mkBlock E) F) (mapi (F.mkBlock E') F')
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> indexwise_r t (sim r) PR AL' E E' F F' AL L L'.
Proof.
  intros ISIM LP SEP r SIML. pcofix CIH.
  eapply ISIM.
  eapply labenv_sim_extension_cases; eauto.
  eapply indexwise_r_bodies_r; eauto. eapply SEP.
  eauto using indexwise_r_mon; eauto.
  hnf; intros. len_simpl. eauto.
  eapply labenv_sim_mon; eauto.
Qed.

Lemma fix_compatible_separate2 t A (PR:ProofRelationF A) AL' AL L1 L2 L L'
  : (forall r,
        labenv_sim t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L')
        -> bodies_r t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L') L1 L2)
    -> paramrel PR (AL' ++ AL) L1 L2
    -> separates PR AL' AL L1 L2
    -> sawtooth L1 -> sawtooth L2
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> bodies_r t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L') L1 L2.
Proof.
  intros ISIM LP SEP r SIML SM1 SM2. pcofix CIH.
  eapply ISIM.
  eapply labenv_sim_extension_cases; eauto.
  hnf. intros. right. eapply CIH; eauto.
  eapply labenv_sim_mon; eauto.
Qed.

(** *** Extension Lemma *)


Definition indexwise_paramrel A (PR:ProofRelationF A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelF (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelF a Z Z'.

Lemma indexwise_paramrel_paramrel A (PR:ProofRelationF A) (F F':〔params * stmt〕) AL' AL E E' (Len:❬AL'❭ = ❬F❭)
  : indexwise_paramrel PR F F' AL' AL
    <-> paramrel PR (AL'++ AL) (mapi (F.mkBlock E) F) (mapi (F.mkBlock E') F').
Proof.
  split; intros; hnf; intros; inv_get.
  - destruct x,x0. exploit H; eauto.
  - eapply (@mapi_get_1 0 _ _ _ (F.mkBlock E)) in H1.
    eapply (@mapi_get_1 0 _ _ _ (F.mkBlock E')) in H2.
    exploit (H (LabI n) (LabI n')); eauto using get_app.
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
  eapply indexwise_paramrel_paramrel in IP; [| eapply SEP].
  eapply labenv_sim_extension_cases; eauto.
  eapply indexwise_r_bodies_r. eapply SEP.
  eapply indexwise_r_mon.
  eapply fix_compatible_separate; eauto.
  eauto.
  hnf; len_simpl; eauto.
Qed.

(** *** Fun Compatibility *)

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

(** *** Specialized Version if function bindings are not changed *)

(* A proof relation is parameterized by analysis information A *)
Class PointwiseProofRelationF (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelFP : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelFP :  onv val -> onv val -> A -> list val -> list val -> Prop;
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
  eapply labenv_sim_extension; eauto.
Qed.


Lemma labenv_sim_extension_ptw' t A (PR:PointwiseProofRelationF A) (AL AL':list A) L1 L2 L L'
  : (forall r ,
        labenv_sim t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L')
        -> bodies_r t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L') L1 L2)
    -> paramrel PR (AL' ++ AL) L1 L2
    -> length AL' = length L1
    -> length L1 = length L2
    -> sawtooth L1 -> sawtooth L2
    -> forall r, labenv_sim t (sim r) PR AL L L'
        -> labenv_sim t (sim r) PR (AL' ++ AL) (L1 ++ L) (L2 ++ L').
Proof.
  intros ISIM IP Len1 Len2 SM1 SM2 r SIML.
  assert (separates PR AL' AL L1 L2). {
    edestruct SIML; dcr.
    hnf; destruct PR; simpl; repeat split; intros; omega.
  }
  eapply labenv_sim_extension_cases; eauto.
  eapply bodies_r_mon.
  eapply fix_compatible_separate2; eauto. eauto.
Qed.


Lemma sim_fun_ptw t A (PR:PointwiseProofRelationF A) (AL AL':list A) F F' L L' E E' s s'
  : (forall r, labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> (sim r \3/ r) t (mapi (F.mkBlock E) F ++ L, E, s) (mapi (F.mkBlock E') F' ++ L', E', s'))
    -> (forall r,
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L')
          -> indexwise_r t (sim r) PR AL' E E' F F' AL L L')
    ->  indexwise_paramrel PR F F' AL' AL
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
                          ❬Z'❭ = ❬Y'v❭ /\ ArgRelF E E' a Yv Y'v)
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
      * perr.
  - destruct i; simpl in *; dcr.
    + exploit H3; eauto. pno_step.
    + perr.
    + perr.
Qed.

(** *** A small study on IL fixed-points in general *)

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
