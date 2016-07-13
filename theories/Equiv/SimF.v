Require Import List paco2.
Require Export Util Var Val Exp MoreExp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export Sim SimTactics IL InRel.

Set Implicit Arguments.
Unset Printing Records.

(* A proof relation is parameterized by analysis information A *)
Class ProofRelation (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRel : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRel : A -> list val -> list val -> Prop;
    (* Relates blocks according to analysis information *)
    BlockRel : A -> F.block -> F.block -> Prop;
    (* Relates environments according to analysis information *)
    IndexRel : 〔A〕 -> nat -> nat -> Prop;
    Image : 〔A〕 -> nat;
    ArgLengthMatchI : forall a Z Z' VL VL',
        ParamRel a Z Z' -> ArgRel a VL VL' -> length Z = length VL /\ length Z' = length VL';
    IndexRelDrop : forall AL' AL n n', IndexRel (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRel AL (n - length AL') (n' - Image AL')
(*    IndexRelApp : forall AL AL' n n', IndexRelI AL n n' -> IndexRelI (AL' ++ AL) (❬AL'❭ + n) n' *)
}.

Definition frel := rel3 simtype (fun _ : simtype => F.state)
                       (fun (_ : simtype) (_ : F.state) => F.state).

Definition indexwise_r t (r:frel) A (PR:ProofRelation A) AL' E E' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRel (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall VL VL',
        ArgRel a VL VL'
        -> r t (mapi (F.mkBlock E) F ++ L, E[Z <-- List.map Some VL], s)
            (mapi (F.mkBlock E') F' ++ L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':frel) A (PR:ProofRelation A) AL' E E' F F' AL L L'
  : indexwise_r t r PR AL' E E' F F' AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' E E' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition simLabenv t (r:frel)
           {A} (PR:ProofRelation A) (AL:list A) L L' :=
  (length AL = length L /\ sawtooth L' /\ sawtooth L) /\
  forall f f' a V Z s n V' Z' s' n',
    IndexRel AL (counted f) (counted f')
    -> get AL (counted f) a
    -> get L (counted f) (F.blockI V Z s n)
    -> get L' (counted f') (F.blockI V' Z' s' n')
    -> (ParamRel a Z Z' /\ BlockRel a (F.blockI V Z s n) (F.blockI V' Z' s' n'))
      /\ (forall E E' Yv Y'v Y Y',
            ArgRel a Yv Y'v
            -> omap (exp_eval E) Y = Some Yv
            -> omap (exp_eval E') Y' = Some Y'v
            -> sim'r r t (L, E, stmtApp f Y)
                    (L', E', stmtApp f' Y')).

Lemma simLabenv_mon t (r r':frel) A (PR:ProofRelation A) AL L L'
  : simLabenv t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> simLabenv t r' PR AL L L'.
Proof.
  intros [[? ?] SIM] LE; hnf; intros; split; eauto.
  intros. edestruct SIM as [[? ?] SIM']; eauto.
  split; eauto. intros.
  eapply paco3_mon. eapply SIM; eauto. eauto.
Qed.

Definition indexwise_proofrel A (PR:ProofRelation A) E E' (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRel (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRel a Z Z' /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n').


Lemma stepGoto_mapi L blk Y E vl f F V
      (Ldef:get L (counted f - ❬F❭) blk)
      (len:length (F.block_Z blk) = length Y)
      (def:omap (exp_eval V) Y = Some vl) E'
      (updOk:F.block_E blk [F.block_Z blk <-- List.map Some vl] = E')
      (ST:sawtooth L) (GE: counted f >= ❬F❭)
  : F.step (mapi (F.mkBlock E) F ++ L, V, stmtApp f Y) EvtTau
           (drop (counted f - ❬F❭ - block_n blk) L,
            E', F.block_s blk).
Proof.
  rewrite <- (mapi_length (F.mkBlock E)).
  assert (counted f - block_n blk >= ❬mapi (F.mkBlock E) F❭). {
    exploit (sawtooth_smaller ST Ldef).
    rewrite mapi_length. simpl in *. omega.
  }
  orewrite (counted f - ❬mapi (F.mkBlock E) F❭ - block_n blk
            =  (counted f - block_n blk) - ❬mapi (F.mkBlock E) F❭).
  rewrite <- (drop_app_gen _ (mapi (F.mkBlock E) F)); eauto.
  eapply F.stepGoto; eauto.
  rewrite get_app_ge. rewrite mapi_length. eauto. omega.
Qed.

Lemma simLabenv_extension' t (r:frel) A (PR:ProofRelation A) (AL AL':list A) E E' F F' L L'
      (LEN1:length AL' = length F)
  : indexwise_r t (sim'r r \3/ r) PR AL' E E' F F' AL L L'
    -> indexwise_proofrel PR E E' F F' AL' AL
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> simLabenv t r PR AL L L'
    -> simLabenv t r PR (AL' ++ AL)
                (mapi (F.mkBlock E) F ++ L)
                (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros ISIM IP Ilt Ige Img SIML.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_F_mkBlocks.
  econstructor; eauto. eapply tooth_F_mkBlocks.
  intros f f' ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi (F.mkBlock E) F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL as [GetAL'|GetAL].
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. simpl in *. clear EQ.
    exploit Ilt; eauto using get_range.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto with len ].
    inv_get. destruct x as [Z' s']; simpl in *; clear EQ.
    split; eauto.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr. eapply IP; eauto.
    pone_step; eauto using get_app, get_mapi; eauto; simpl; eauto with len.
    orewrite (labN f - labN f = 0); simpl.
    orewrite (labN f' - labN f' = 0); simpl.
    eapply ISIM; eauto.
  - destruct SIML; dcr.
    eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    exploit Ige; eauto; try congruence.
    eapply get_app_right_ge in GetL'; [ | eauto with len; rewrite mapi_length; eauto].    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto.
    edestruct (H1 (LabI (counted f - ❬AL'❭)) (LabI (counted f' - Image AL')))
      as [[? ?] SIM]; simpl; eauto.
    rewrite H; eauto. rewrite Img; eauto.
    split; eauto.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    eapply (@sim_Y_left F.state _ F.state _).
    eapply (@sim_Y_right F.state _ F.state _).
    rewrite Img in SIM. rewrite H in SIM.
    eapply SIM; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    Focus 2.
    econstructor; simpl; eauto. simpl. eauto with len.
    simpl.
    eapply (stepGoto_mapi _ _ _ _ _ GetL'); simpl; eauto with len.
    eapply (stepGoto_mapi _ _ _ _ _ GetFL); simpl; eauto with len.
    simpl in *; omega.
Qed.

Lemma fix_compatible_I t A (PR:ProofRelation A) AL F F' E E' L L' AL'
(LEN2:length AL' = length F)
  : (forall r, simLabenv t r PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L)
                     (mapi (F.mkBlock E') F' ++ L')
            -> indexwise_r t (sim'r r) PR AL' E E' F F' AL L L')
    -> indexwise_proofrel PR E E' F F' AL' AL
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, simLabenv t r PR AL L L'
           -> indexwise_r t (sim'r r) PR AL' E E' F F' AL L L'.
Proof.
  intros ISIM IP Ilt Ige Img r SIML; pcofix CIH.
  eapply ISIM; eauto.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split.
  econstructor; eauto. eapply tooth_F_mkBlocks.
  econstructor; eauto. eapply tooth_F_mkBlocks.
  eapply simLabenv_extension'; eauto using simLabenv_mon, indexwise_r_mon.
Qed.

Lemma simILabenv_extension t A (PR:ProofRelation A) (AL AL':list A) E E' F F' L L'
      (LEN1:length AL' = length F)
  : (forall r, simLabenv t r PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L)
                     (mapi (F.mkBlock E') F' ++ L')
          -> indexwise_r t (sim'r r) PR AL' E E' F F' AL L L')
    -> indexwise_proofrel PR E E' F F' AL' AL
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRel (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, simLabenv t r PR AL L L'
           -> simLabenv t r PR (AL' ++ AL)
                       (mapi (F.mkBlock E) F ++ L)
                       (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros. eapply simLabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.

Lemma simLabenv_extension_len t A (PR:ProofRelation A) (AL AL':list A)
      E E' F F' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
      (IDX:forall AL n n', IndexRel AL n n' = (n = n'))
  : (forall r, simLabenv t r PR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L)
                     (mapi (F.mkBlock E') F' ++ L')
          -> indexwise_r t (sim'r r) PR AL' E E' F F' AL L L')
    -> indexwise_proofrel PR E E' F F' AL' AL
    -> Image AL' = length F'
    -> forall r, simLabenv t r PR AL L L'
           -> simLabenv t r PR (AL' ++ AL)
                       (mapi (F.mkBlock E) F ++ L)
                       (mapi (F.mkBlock E') F' ++ L').
Proof.
  assert (forall n n', IndexRel (AL' ++ AL) n n' -> n < length F -> n' < length F').
  intros. rewrite IDX in H. subst; omega.
  assert (forall n n', IndexRel (AL' ++ AL) n n' -> n >= length F -> n' >= length F').
  intros. rewrite IDX in H0. subst; omega.
  intros. eapply simLabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.
