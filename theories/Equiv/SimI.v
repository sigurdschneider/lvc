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
    eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite Img in SIMR. rewrite Len3 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply I.StepGoto_mapi; simpl in *; eauto with len.
    rewrite mapi_length. exploit STL; eauto. simpl in *. omega.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply I.StepGoto_mapi; simpl in *; eauto with len.
    rewrite mapi_length. exploit STL'; eauto. simpl in *. omega.
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


(*Require Import TraceEquiv.

Definition pfx' (t:simtype) (σ σ':I.state) := forall L, prefix σ L -> prefix σ' L.
Definition pfx
           (r:rel3 simtype (fun _ : simtype => I.state) (fun (_ : simtype) (_ : I.state) => I.state))
           (t:simtype) := pfx'.


Inductive prefix_n {S} `{StateType S} : nat -> S -> list extevent -> Prop :=
  | producesPrefixSilent n (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> prefix_n n σ' L
      -> prefix_n (1+ n) σ L
  | producesPrefixExtern n (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> prefix_n n σ' L
      -> prefix_n (1+ n) σ (EEvtExtern evt::L)
  | producesPrefixTerm n (σ:S) (σ':S) r
    : result σ' = r
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> prefix_n n σ (EEvtTerminate r::nil)
  | producesPrefixPrefix n (σ:S)
    : prefix_n n σ nil.

Definition preincl n
           {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S') :=
  forall L,  prefix_n n σ L -> prefix σ' L.

Lemma prefix_prefix_n {S} `{StateType S} σ L
  : prefix σ L -> exists n, prefix_n n σ L.
Proof.
  intros P.
  general induction P; try destruct IHP.
  - exists (1+x). eauto 20 using @prefix_n.
  - exists (1+x). eauto 20 using @prefix_n.
  - exists 0. eauto 20 using @prefix_n.
  - eexists 0. eauto 20 using @prefix_n.
Qed.

Lemma prefix_n_prefix {S} `{StateType S} σ L n
  : prefix_n n σ L -> prefix σ L.
Proof.
  intros P.
  general induction P; eauto using @prefix.
Qed.

Lemma preincl_prefix_incl {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : (forall n, preincl n σ σ') -> forall L, prefix σ L -> prefix σ' L.
Proof.
  intros. eapply prefix_prefix_n in H2 as [? ?]. eapply H1; eauto.
Qed.

Definition pic n {S} `{StateType S} {S'} `{StateType S'}
           (t:simtype) (σ:S) (σ':S') := preincl n σ σ'.

Lemma pic_silent_step t n {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2 σ2':S')
  : pic n t σ1' σ2'
    -> step σ1 EvtTau σ1'
    -> step σ2 EvtTau σ2'
    -> pic (1+ n) t σ1 σ2.
Proof.
  intros. hnf; intros.
  inv H4. relsimpl. eapply H1 in H7.
  econstructor; eauto.
  relsimpl. relsimpl.
  assert (prefix_n n σ1' (EEvtTerminate (result σ') :: nil)) by eauto using @prefix_n.
  eapply H1 in H5. econstructor; eauto.
  econstructor. eauto. econstructor 4.
Qed.

Lemma labenv_sim_extension'' n t A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
  : indexwise_r t (pic n) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> labenv_sim t (pic n) PR AL L L'
    -> labenv_sim t (pic (S n)) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
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
    eapply pic_silent_step; only 2-3: single_step.
    simpl.
    orewrite (f-f=0). orewrite (f'-f'=0). simpl.
    exploit SIM; eauto.
  - intros. exploit Ige; eauto. rewrite mapi_length in GE; eauto.
    eapply get_app_right_ge in GetAL; [ | rewrite Len3; eauto ].
    eapply get_app_right_ge in GetL'; [ | rewrite mapi_length; eauto ].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto; [| rewrite Len3; eauto].
    exploit (LSIM (LabI  (f - ❬AL'❭)) (LabI (f' - Image AL'))) as SIMR; eauto.
    rewrite Len3; eauto. rewrite Img; eauto.
    eapply pic_silent_step; only 2-3: single_step.
    Focus 2. eapply get_app_right; eauto. len_simpl. omega.
    Focus 3. eapply get_app_right; eauto. len_simpl. omega.
    simpl.
    admit.
    simpl; eauto with len. simpl; eauto with len.
    (*eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite Img in SIMR. rewrite Len3 in SIMR.
    eapply paco3_mon; [| eauto].
    eapply SIMR; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    eapply I.StepGoto_mapi; simpl in *; eauto with len.
    rewrite mapi_length. exploit STL; eauto. simpl in *. omega.
    econstructor; simpl; eauto. simpl. eauto with len.
    eapply I.StepGoto_mapi; simpl in *; eauto with len.
    rewrite mapi_length. exploit STL'; eauto. simpl in *. omega.*)
Admitted.

Definition pic' {S} `{StateType S} {S'} `{StateType S'}
           (t:simtype) (σ:S) (σ':S') := forall L, prefix σ L -> prefix σ' L.

Lemma pic_pic' t A (PR:ProofRelationI A) AL' AL F F' L L'
  : (forall n, (labenv_sim t (pic n) PR AL L L' -> indexwise_r t (pic n) PR AL' F F' AL L L'))
    -> labenv_sim t pic' PR AL L L' -> indexwise_r t pic' PR AL' F F' AL L L'.
Proof.
  intros. hnf; intros.
  hnf; intros.
  eapply prefix_prefix_n in H6 as [? ?].
  eapply H; eauto.
  hnf; intros. edestruct H0. dcr.
  split; eauto. split; eauto. split; eauto. split; eauto.
  split; eauto. hnf; intros. hnf; intros.
  eapply H14; eauto. eapply prefix_n_prefix; eauto.
Qed.

(*

Lemma pic'_pic t A (PR:ProofRelationI A) AL' AL F F' L L'
  : (labenv_sim t pic' PR AL L L' -> indexwise_r t pic' PR AL' F F' AL L L')
    -> (forall n, (labenv_sim t (pic n) PR AL L L' -> indexwise_r t (pic n) PR AL' F F' AL L L')).
Proof.
  intros. hnf; intros.
  hnf; intros.
  eapply prefix_n_prefix in H6.
  eapply H; eauto.
  hnf; intros. edestruct H0. dcr.
  split; eauto. split; eauto. split; eauto. split; eauto.
  split; eauto. hnf; intros. hnf; intros.
  eapply H14; eauto. eapply prefix_prefix_n in H22 as [? ?]. eauto.
Qed.
*)



Lemma fix_compatible_separate' t A (PR:ProofRelationI A) AL' AL F F' L L'
  : (forall n, (labenv_sim t (pic n) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
           -> indexwise_r t (pic n) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')))
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> (forall n, labenv_sim t (pic n) PR AL L L'
    -> indexwise_r t (pic n) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')).
Proof.
  intros ISIM LP SEP k SIML. general induction k.
  - intros. hnf; intros. hnf; intros.
    inv H4; eauto using @prefix.
    eapply ISIM; eauto using @prefix.
    admit.
  - eapply ISIM; eauto.
    eapply labenv_sim_extension''; eauto.
    Focus 2.
    eapply labenv_sim_mon; eauto. admit.
    eapply IHk; eauto.
    eapply labenv_sim_mon; eauto. admit.
Admitted.
 *)

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

(*
Lemma sim_fun t A (PR:ProofRelationI A) (AL AL':list A) F F' L L' V V' s s'
  : (forall r, labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> (sim r \3/ r) t (mapi I.mkBlock F ++ L, V, s) (mapi I.mkBlock F' ++ L', V', s'))
    -> (forall r,
          labenv_sim t (sim r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> indexwise_r t (sim r) PR AL' F F' AL (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L'))
    -> indexwise_paramrel PR F F' AL' AL
    -> separates PR AL' AL F F'
    -> forall r, labenv_sim t (sim r) PR AL L L'
           -> sim r t (L, V, stmtFun F s) (L', V', stmtFun F' s').
Proof.
  intros SIM_s ISIM IP SEP r SIML.
  pone_step.
  eapply SIM_s.
  eapply labenv_sim_extension; eauto.
Qed.
 *)

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
  - destruct i; simpl in *; dcr.
    + exploit H3; eauto. pno_step.
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


Definition trivs (f:external) :=
  stmtLet default_var (Call f nil) (stmtReturn (Con default_val)).

Definition trivL (b:I.block) (f:external) :=
  match b with
  | I.blockI Z s n => I.blockI Z (trivs f) n
  end.

Lemma triv_sat t A (PR:PointwiseProofRelationI A) AL L L' XF r (Len:❬XF❭= ❬L❭) (Len2:❬L❭=❬L'❭)
  : labenv_sim t (sim r) PR AL L L'
    -> labenv_sim t (sim bot3) PR AL (trivL ⊜ L XF) (trivL ⊜ L' XF).
Proof.
  intros. hnf; intros.
  destruct H; dcr. len_simpl.
  split; eauto.
  split. {
    hnf; intros; inv_get. destruct x; simpl. exploit H1; eauto.
  }
  split. {
    hnf; intros; inv_get. destruct x; simpl. exploit H3; eauto.
  }
  split. {
    hnf; intros; inv_get. destruct x,x1; simpl in *; clear_trivial_eqs.
    exploit H2; eauto.
  }
  split. hnf; intros; inv_get. edestruct H4; eauto. inv_get.
  eexists; eapply zip_get; eauto.
  hnf; intros. pone_step. inv_get. simpl.
  destruct x,x1; simpl in *; clear_trivial_eqs. unfold trivs.
  assert (f=f'). hnf in H0. destruct PR. simpl in *. destruct f, f'; simpl in *. congruence.
  rewrite H15. subst. inv_get.
  left. pextern_step; eauto.
  hnf; intros. eexists; eauto. eexists. econstructor. simpl. reflexivity.
  hnf; intros. eexists; eauto. eexists. econstructor. simpl. reflexivity.
  left. pno_step.
  left. pno_step.
  Grab Existential Variables.
  eapply default_val.
  eapply default_val.
Qed.

Require Import Sawtooth.

Lemma drop_le n X (L L':list X)
      (LE:n <= ❬L❭)
  : drop n (L ++ L') = drop n L ++ L'.
Proof.
  general induction L; simpl in *.
  - invc LE. reflexivity.
  - destruct n; simpl; eauto.
    rewrite IHL; eauto. omega.
Qed.

Lemma drop_app n X (L L':list X)
  : drop n (L ++ L') = drop n L ++ drop (n - ❬L❭) L'.
Proof.
  general induction L; simpl in *.
  - rewrite drop_nil. orewrite (n - 0 = n). reflexivity.
  - destruct n; simpl; eauto.
Qed.

Lemma trivL_step_tau_inv (L1:〔I.block〕) L XF E s σ
  : step (L1 ++ trivL ⊜ L XF, E, s) EvtTau σ
    -> (exists k L2 E' s', σ = (drop k (L2 ++ L1 ++ trivL ⊜ L XF), E', s') /\
                     step (L1 ++ L, E, s) EvtTau (drop k (L2 ++ L1 ++ L), E', s')
                     /\ k <= ❬L1❭ + ❬L2❭)
      \/ exists f Y, s = stmtApp f Y /\ f >= ❬L1❭.
Proof.
  intros.
  inv H;
    try now (left; eexists 0, nil; do 2 eexists; (split; [try reflexivity|split;[try single_step|simpl; omega]])).
  - eapply get_app_cases in Ldef as [|[? ?]].
    + left. eexists (l - I.block_n blk), nil.
      do 2 eexists; (split; [try reflexivity|split;[try single_step|simpl; try omega]]).
      simpl. eauto using get_app.
      eapply get_range in H0. omega.
    + right. eauto.
  - left. eexists 0, (mapi I.mkBlock s0). simpl.
    do 2 eexists; (split; [try reflexivity|split;[try single_step|simpl; try omega]]).
Qed.

Definition externalsE (e:exp) :=
  match e with
  | Operation _ => {}
  | Call f _ => singleton f
  end.

Fixpoint externals (s:stmt) : set var :=
  match s with
  | stmtLet x e s0 => externalsE e ∪ externals s0
  | stmtIf e s1 s2 => externals s1 ∪ externals s2
  | stmtApp l Y => {}
  | stmtReturn e => {}
  | stmtFun F t => list_union ((fun Zs => externals (snd Zs)) ⊝ F) ∪ externals t
  end.

Definition bexternals (b:I.block) :=
  externals (I.block_s b).

Lemma trivL_step_tau_inv' (L1:〔I.block〕) L XF E s σ (STL:sawtooth (L1 ++ L))
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
  : step (L1 ++ trivL ⊜ L XF, E, s) EvtTau σ
    -> (exists L2 E' s', σ = (L2 ++ trivL ⊜ L XF, E', s') /\
                   step (L1 ++ L, E, s) EvtTau (L2 ++ L, E', s') /\ sawtooth (L2 ++ L) /\
                   disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
      \/ exists f Y vl Z n s' xf, s = stmtApp f Y /\ f >= ❬L1❭ /\
                      omap (op_eval E) Y = Some vl /\
                      get XF (f - ❬L1❭) xf  /\
                      get L (f - ❬L1❭) (I.blockI Z s' n) /\
                 σ = (drop ((f - ❬L1❭)- n) (trivL ⊜ L XF), E[Z <-- Some ⊝ vl], trivs xf) /\
                 step (L1 ++ L, E, s) EvtTau (drop ((f - ❬L1❭) - n) L, E[Z <-- Some ⊝ vl], s').
Proof.
  intros.
  inv H; simpl in *;
    try now (
          left; eexists L1; do 2 eexists;
          (split; [try reflexivity
                  |split; [try single_step
                          |split; [eassumption|eapply disj_2_incl; eauto with cset]]])
        ).
  - eapply get_app_cases in Ldef as [|[? ?]].
    + left. eexists (drop (l - I.block_n blk) L1).
      rewrite <- !drop_le; eauto.
      do 2 eexists; (split; [try reflexivity|split; try single_step]).
      eapply get_app; eauto.
      split.
      eapply sawtooth_drop'; eauto using get_app.
      rewrite drop_map. rewrite list_union_drop_incl.
      eapply disj_2_incl; eauto.
      eapply union_incl_split; eauto with cset.
      rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
      cset_tac.
      eapply get_range in H0. omega.
      eapply get_range in H0. omega.
    + right.
      inv_get. destruct x as [Z s' n].
      do 7 eexists; split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto. simpl.
      rewrite drop_app_gen.
      admit. admit.
  - left. eexists (mapi I.mkBlock s0 ++ L1). rewrite <- !app_assoc.
    do 2 eexists; (split; [try reflexivity|try single_step]).
Admitted.


Lemma trivs_star_inv (L:〔I.block〕) E xf σ n
  :  star2n step n (L, E, trivs xf) nil σ
     -> n = 0 /\ σ = (L, E, trivs xf).
Proof.
  intros. inv H; eauto.
  exfalso. inv H1. isabsurd.
Qed.

Lemma trivL_plus_step_tau_inv L1 (L:〔I.block〕) XF E s σ n
      (STEP:star2n step n (L1 ++ trivL ⊜ L XF, E, s) nil σ) (STL:sawtooth (L1 ++ L))
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
  : ((exists σ' L2 E' s',
         star2n step n (L1 ++ L, E, s) nil σ' /\
         sawtooth (L2 ++ L) /\ σ = (L2 ++ trivL ⊜ L XF, E', s') /\
         σ' = (L2 ++ L, E', s') /\
         disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
     \/ ( exists σ' E' f Y vl Z n' s' xf,
           star2n step n (L1 ++ L, E, s) nil σ' /\
           omap (op_eval E') Y = Some vl /\
           get XF f xf  /\
           get L f (I.blockI Z s' n') /\
           σ = (drop (f - n') (trivL ⊜ L XF), E'[Z <-- Some ⊝ vl], trivs xf) /\
           σ' = (drop (f - n') L, E'[Z <-- Some ⊝ vl], s'))).
Proof.
  intros. general induction STEP.
  - left.
    eexists.
    eexists L1; do 2 eexists; eauto 20 using star2n.
  - destruct y, yl; isabsurd.
    edestruct trivL_step_tau_inv'; eauto.
    + dcr. subst. simpl in *; clear_trivial_eqs.
      exploit IHSTEP as IH; eauto.
      destruct IH as [[? ?]|[? ?]]; dcr; subst.
      * left. do 4 eexists. split.
        -- eapply S_star2n with (y:=EvtTau) (yl:=nil); eauto.
        -- eauto.
      * right.
        do 9 eexists. split.
        -- eapply S_star2n with (y:=EvtTau) (yl:=nil); eauto.
        -- eauto.
    + destruct H0; dcr; subst.
      edestruct trivs_star_inv; eauto; subst.
      right.
      do 9 eexists. split.
      * eapply S_star2n with (y:=EvtTau) (yl:=nil); eauto.
        econstructor.
      * eauto.
Qed.

Lemma normal2_labenv_I E s (L L':I.labenv)
  : normal2 step (L, E, s)
    -> (forall n b b', get L n b -> get L' n b' -> block_Z b = block_Z b')
    -> ❬L'❭ = ❬L❭
    -> normal2 step (L', E, s).
Proof.
  intros. hnf; intros. eapply H.
  destruct H2 as [? [? ?]].
  eexists x.
  inv H2; simpl in *; inv_get; eexists; try single_step.
  econstructor; eauto. exploit H0; eauto. rewrite H4. eauto.
Qed.

Lemma event_inversion t (L:I.labenv) E xf L' E' s'
  : (forall evt σ1'', step (L, E, trivs xf) evt σ1'' -> exists σ2'',
          step (L', E', s') evt σ2'' /\ sim bot3 t σ1'' σ2'')
    -> exists x s'', s' = stmtLet x (Call xf nil) s''.
Proof.
  intros.
  edestruct H.
  - hnf. eapply I.StepExtern with (v:=default_val). reflexivity.
  - dcr. inv H1. destruct Y; simpl in *; eauto.
    monad_inv def.
Qed.


Lemma trivs_inversion (L:I.labenv) XF E s L' E' xf n s' x L2
      (GET:get XF n xf) (Len:❬XF❭ = ❬L❭) (ND:NoDupA eq XF)
      (NOTIN1:xf ∉ externals s) (NOTIN2:xf ∉ list_union (bexternals ⊝ L2))
  (Step:step (L2 ++ trivL ⊜ L XF, E, s) EvtTau (L', E', stmtLet x (Call xf nil) s'))
  : exists Y b vl, s = stmtApp (LabI (❬L2❭ + n)) Y
         /\ get L n b
         /\ ❬Y❭ = ❬I.block_Z b❭
         /\ omap (op_eval E) Y = Some vl.
Proof.
  inv Step; simpl in *;
    try now (exfalso; cset_tac).
  eapply get_app_cases in Ldef as [?|[? ?]].
  - exfalso. eapply NOTIN2. rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
    unfold bexternals. rewrite H5. simpl. cset_tac.
  - destruct blk; simpl in *. subst.
    inv_get. destruct x0. simpl in *. unfold trivs in EQ. invc EQ.
    decide (n = l - ❬L2❭).
    + rewrite e. do 3 eexists.
      split. f_equal. destruct l. f_equal. simpl in *. omega.
      eauto.
    + exfalso.
      eapply NoDupA_get_neq in GET; eauto. congruence.
Qed.

Lemma star2n_trans_silent (X : Type) (R : X -> event -> X -> Prop) n m x y z
  : star2n R n x nil y
    -> star2n R m y nil z
    -> star2n R (n + m) x nil z.
Proof.
  intros A B.
  general induction A; simpl; eauto.
  econstructor; eauto.
  destruct y, yl; isabsurd.
  eapply IHA; eauto.
Qed.

Lemma star2n_decomp_right (X : Type) (R : X -> event -> X -> Prop) n x y
  : star2n R (S n) x nil y
    -> exists z, star2n R n x nil z /\ R z EvtTau y.
Proof.
  general induction n.
  - repeat invtc star2n.
    destruct y0; isabsurd.
    eauto using star2n.
  - invtc star2n.
    destruct y0, yl; isabsurd.
    eapply IHn in H4; dcr.
    eauto using star2n.
Qed.

Lemma labenv_lift r t A (PR:PointwiseProofRelationI A) XF AL L1 L2 L L' E E' s s'
      (Len:❬XF❭=❬L❭) (Len2:❬L❭=❬L'❭)
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
      (DISJ':disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
  (LAB:labenv_sim t (sim r) PR AL L L')
  (SIMbot:sim bot3 t (L1 ++ trivL ⊜ L XF, E, s) (L2 ++ trivL ⊜ L' XF, E', s'))
  (STL1:sawtooth (L1 ++ L))
  (STL2: sawtooth (L2 ++ L'))
  : sim r t (L1 ++ L, E, s) (L2 ++ L', E', s').
Proof.
  revert_all. pcofix CIH; intros.
  pinversion SIMbot; subst.
  - eapply plus2_star2n in H. eapply plus2_star2n in H0. dcr.
    edestruct (trivL_plus_step_tau_inv _ _ _ H2); eauto. dcr.
    destruct H4; dcr; subst.
    + edestruct (trivL_plus_step_tau_inv _ _ _ H0); eauto. dcr.
      destruct H6; dcr; subst.
      * eapply star2n_plus2 in H3.
        eapply star2n_plus2 in H4.
        pfold.
        econstructor 1; eauto.
      * eapply star2n_plus2 in H4.
        eapply sim_activated in H1 as [? [? [? ?]]]; dcr.
        destruct x1 as [[? ?] ?].
        eapply event_inversion in H11 as [? [? ?]]. subst. clear H12.
        eapply star2_star2n in H. dcr.
        eapply star2n_trans_silent in H10; eauto. simpl in *.
        eapply trivL_plus_step_tau_inv in H10 as [? [? ?]]; eauto.
        destruct H10.
        exfalso; dcr. subst. invc H11. simpl in *.
        eapply H15. eapply get_in_of_list; eauto.
        clear. cset_tac. dcr. subst. invc H14. inv_get.
        eapply star2n_star2 in H.
        eapply plus2_star2 in H4.
        admit.
        -- hnf. do 2 eexists; econstructor. reflexivity.
    + admit.
  - admit.
  - eapply star2_star2n in H0. dcr.
    edestruct (trivL_plus_step_tau_inv _ _ _ H2); eauto. dcr.
    destruct H4; dcr; subst.
    + eapply star2n_star2 in H3.
      pfold.
      eapply SimErr; try eapply H3; eauto.
      eapply normal2_labenv_I; eauto with len.
      clear. intros.
      eapply get_app_cases in H as [?|[? ?]]; inv_get; eauto.
      eapply get_app_ge in H0; eauto.
      destruct x; inv_get; reflexivity.
    + exfalso. eapply H1.
      hnf. do 2 eexists. econstructor. reflexivity.
  - eapply star2_star2n in H0. eapply star2_star2n in H1. dcr.
    edestruct (trivL_plus_step_tau_inv _ _ _ H4); eauto. dcr.
    edestruct (trivL_plus_step_tau_inv _ _ _ H1); eauto. dcr.
    pfold.
    eapply star2n_star2 in H5. eapply star2n_star2 in H7.
    destruct H6; dcr; subst.
    + destruct H8; dcr; subst.
      * eapply SimTerm; try eapply H5; try eapply H7; eauto.
        eapply normal2_labenv_I; eauto with len.
        clear. intros.
        eapply get_app_cases in H as [?|[? ?]]; inv_get; eauto.
        eapply get_app_ge in H0; eauto.
        destruct x; inv_get; reflexivity.
        eapply normal2_labenv_I; eauto.
        clear. intros.
        eapply get_app_cases in H as [?|[? ?]]; inv_get; eauto.
        eapply get_app_ge in H0; eauto.
        destruct x; inv_get; reflexivity.
        len_simpl. rewrite Len. rewrite min_l; eauto.
        omega.
      * exfalso. eapply H2.
        hnf. do 2 eexists. econstructor. reflexivity.
    + exfalso. eapply H3.
      hnf. do 2 eexists. econstructor. reflexivity.
Qed.


Lemma key t A (PR:PointwiseProofRelationI A) AL' AL F F'
  : (forall L L', ❬L❭=❬L'❭ -> labenv_sim t (sim bot3) PR AL L L' -> indexwise_r t (sim bot3) PR AL' F F' AL L L')
    -> (forall r L L', ❬L❭=❬L'❭-> (labenv_sim t (sim r) PR AL L L' -> indexwise_r t (sim r) PR AL' F F' AL L L')).
Proof.
  intros. hnf; intros.
  assert (XFE:exists XF:list external, ❬XF❭ = ❬L❭) by admit.
  destruct XFE as [XF XFlen].
  exploit (H (trivL ⊜ L XF) (trivL ⊜ L' XF)).
  eauto with len.
  eapply (triv_sat PR XF XFlen H0 H1); eauto.
  exploit H7; eauto.
  eapply labenv_lift with (L1:=nil) (L2:=nil); eauto.
Qed.
  clear H.

(*
  hnf; intros.
  eapply prefix_n_prefix in H6.
  eapply H; eauto.
  hnf; intros. edestruct H0. dcr.
  split; eauto. split; eauto. split; eauto. split; eauto.
  split; eauto. hnf; intros. hnf; intros.
  eapply H14; eauto. eapply prefix_prefix_n in H22 as [? ?]. eauto.
Qed.
 *)
Admitted.