Require Import List paco2.
Require Export Util Var Val Exp MoreExp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
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
    (* Relates blocks according to analysis information *)
    BlockRelI : A -> I.block -> I.block -> Prop;
    (* Relates environments according to analysis information *)
    IndexRelI : 〔A〕 -> nat -> nat -> Prop;
    Image : 〔A〕 -> nat;
    ArgLengthMatchI : forall E E' a Z Z' VL VL',
        ParamRelI a Z Z' -> ArgRelI E E' a VL VL' -> length Z = length VL /\ length Z' = length VL';
    IndexRelDrop : forall AL' AL n n', IndexRelI (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelI AL (n - length AL') (n' - Image AL')
(*    IndexRelApp : forall AL AL' n n', IndexRelI AL n n' -> IndexRelI (AL' ++ AL) (❬AL'❭ + n) n' *)
}.

Definition irel := rel3 simtype (fun _ : simtype => I.state)
                       (fun (_ : simtype) (_ : I.state) => I.state).

Definition indexwise_r t (r:irel) A (PR:ProofRelationI A) AL' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r t (mapi I.mkBlock F ++ L, E[Z <-- List.map Some VL], s)
            (mapi I.mkBlock F' ++ L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':irel) A (PR:ProofRelationI A) AL' F F' AL L L'
  : indexwise_r t r PR AL' F F' AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition simILabenv t (r:irel)
           {A} (PR:ProofRelationI A) (AL:list A) L L' :=
  (length AL = length L /\ sawtooth L' /\ sawtooth L) /\
  forall f f' a Z s n Z' s' n',
    IndexRelI AL f f'
    -> get AL f a
    -> get L f (I.blockI Z s n)
    -> get L' f' (I.blockI Z' s' n')
    -> (ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n'))
      /\ (forall E E' Yv Y'v Y Y',
            ArgRelI E E' a Yv Y'v
            -> omap (exp_eval E) Y = Some Yv
            -> omap (exp_eval E') Y' = Some Y'v
            -> sim'r r t (drop (f  - n) L, E, stmtApp (LabI n) Y)
                    (drop (f'  - n') L', E', stmtApp (LabI n') Y')).

Lemma simILabenv_mon t (r r':irel) A (PR:ProofRelationI A) AL L L'
  : simILabenv t r PR AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> simILabenv t r' PR AL L L'.
Proof.
  intros [[? ?] SIM] LE; hnf; intros; split; eauto.
  intros. edestruct SIM as [[? ?] SIM']; eauto.
  split; eauto. intros.
  eapply paco3_mon. eapply SIM; eauto. eauto.
Qed.

Definition indexwise_proofrel A (PR:ProofRelationI A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n').

Lemma simILabenv_extension' t (r:irel) A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : indexwise_r t (sim'r r \3/ r) PR AL' F F' AL L L'
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> simILabenv t r PR AL L L'
    -> simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP Ilt Ige Img SIML.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  intros ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL as [GetAL'|GetAL].
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. simpl in *. clear EQ.
    orewrite (n - n = 0). simpl.
    exploit Ilt; eauto using get_range.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto with len ].
    inv_get. destruct x as [Z' s']; simpl in *; clear EQ.
    split; eauto.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr. eapply IP; eauto.
    exploit (omap_length _ _ _ _ _ H2).
    exploit (omap_length _ _ _ _ _ H3).
    pone_step; eauto using get_app, get_mapi; eauto; simpl; try congruence.
    orewrite (n' - n' = 0); simpl.
    eapply get_app. eapply mapi_get_1; eauto.
    simpl. congruence.
    orewrite (n - n = 0); simpl.
    orewrite (n' - n' = 0); simpl.
    eapply ISIM; eauto.
  - destruct SIML; dcr.
    eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    exploit Ige; eauto; try congruence.
    eapply get_app_right_ge in GetL'; [ | eauto with len; rewrite mapi_length; eauto].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto.
    edestruct H1 as [[? ?] SIM]; eauto. rewrite H; eauto. rewrite Img; eauto.
    split; eauto.
    intros.
    assert (f - n >= ❬mapi I.mkBlock F❭). {
      exploit (sawtooth_smaller H7 GetFL).
      rewrite <- H in *. rewrite mapi_length. simpl in *. omega.
    }
    assert (f' - n' >= ❬mapi I.mkBlock F'❭). {
      exploit (sawtooth_smaller H6 GetL').
      rewrite mapi_length in *.
      simpl in *. omega.
    }
    rewrite (drop_app_gen _ (mapi I.mkBlock F)); eauto.
    rewrite (drop_app_gen _ (mapi I.mkBlock F')); eauto.
    repeat rewrite mapi_length. rewrite H in SIM. rewrite Img in SIM.
    orewrite (f - n - ❬F❭ = f - ❬F❭ - n).
    orewrite (f' - n' - ❬F'❭ = f' - ❬F'❭ - n').
    eapply paco3_mon. eapply SIM; eauto. eauto.
Qed.

Lemma fix_compatible_I t A (PR:ProofRelationI A) AL F F' L L' AL'
(LEN2:length AL' = length F)
  : (forall r, simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L)
                     (mapi I.mkBlock F' ++ L')
            -> indexwise_r t (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, simILabenv t r PR AL L L'
           -> indexwise_r t (sim'r r) PR AL' F F' AL L L'.
Proof.
  intros ISIM IP Ilt Ige Img r SIML; pcofix CIH.
  eapply ISIM; eauto.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  eapply simILabenv_extension'; eauto using simILabenv_mon, indexwise_r_mon.
Qed.

Lemma simILabenv_extension t A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : (forall r, simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L)
                     (mapi I.mkBlock F' ++ L')
          -> indexwise_r t (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, simILabenv t r PR AL L L'
           -> simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros. eapply simILabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.

Lemma renILabenv_extension_len t A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
      (IDX:forall AL n n', IndexRelI AL n n' = (n = n'))
  : (forall r, simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L)
                     (mapi I.mkBlock F' ++ L')
          -> indexwise_r t (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> Image AL' = length F'
    -> forall r, simILabenv t r PR AL L L'
           -> simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  assert (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F').
  intros. rewrite IDX in H. subst; omega.
  assert (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F').
  intros. rewrite IDX in H0. subst; omega.
  intros. eapply simILabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.
