Require Import CSet Util Fresh Filter MoreExp Take MoreList OUnion.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness.
Require Import Sim SimTactics.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint countSome X (L:list (؟ X)) :=
  match L with
  | nil => 0
  | Some _ ::xs => 1 + countSome xs
  | None :: xs => countSome xs
  end.

Lemma countSome_app X (L L':list (؟ X))
  : countSome (L ++ L') = countSome L + countSome L'.
Proof.
  intros. induction L; simpl; eauto.
  destruct a; eauto. omega.
Qed.

Definition compileF (compile : forall (LV:list (؟ (set var) * params)) (s:stmt) (a:ann (؟(set var))), stmt)
(LV:list (؟ (set var) * params)) :=
  fix f (F:〔params * stmt〕) (ans:list (ann (؟⦃var⦄))) :=
    match F, ans with
    | (Z,s)::F, a::ans =>
      match getAnn a with
      | Some lv => (List.filter (fun x => B[x ∈ lv]) Z,
                  compile LV s a) :: f F ans
      | None => f F ans
      end
    | _, _ => nil
    end.

Fixpoint compile (LV:list (؟ (set var) * params)) (s:stmt) (a:ann (؟(set var))) :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      if [x ∈ oget (getAnn an)]
      then stmtLet x e (compile LV s an)
      else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [exp2bool e = Some true] then
        (compile LV s ans)
      else if [ exp2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtApp f Y, ann0 _ =>
      let lvZ := nth (counted f) LV (None, nil) in
      stmtApp (LabI (countSome (fst ⊝ (take (counted f) LV))))
              (filter_by (fun y => B[y ∈ oget (fst lvZ)]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile LV s an)
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (compileF compile LV' F ans)
              (compile LV' t ant)
    | s, _ => s
  end.

Lemma compileF_get LV F n ans Zs a lv
  : ❬F❭ = ❬ans❭
    -> get F n Zs
    -> get ans n a
    -> getAnn a = Some lv
    -> get (compileF compile LV F ans) (countSome (getAnn ⊝ (take n ans)))
          (List.filter (fun x => B[x ∈ lv]) (fst Zs), compile LV (snd Zs) a).
Proof.
  intros LEN GetF GetAns. length_equify.
  general induction LEN.
  - isabsurd.
  - destruct x as [Z s]; inv GetF; inv GetAns.
    + simpl. rewrite H.
      * eauto using get.
    + simpl. cases; simpl; eauto using get.
Qed.

Lemma compileF_get_inv LV F ans Z' s' n'
  : ❬F❭ = ❬ans❭
    -> get (compileF compile LV F ans) n' (Z', s')
    -> exists Zs a n lv, get F n Zs
      /\ get ans n a
      /\ getAnn a = Some lv
      /\ Z' = List.filter (fun x => B[x ∈ lv]) (fst Zs)
      /\ s' = compile LV (snd Zs) a
      /\ n' = countSome (getAnn ⊝ (take n ans)).
Proof.
  intros LEN Get. length_equify.
  general induction LEN; simpl in *.
  - isabsurd.
  - destruct x as [Z s]. case_eq (getAnn y); [ intros ? EQ | intros EQ].
    + rewrite EQ in *. inv Get.
      * eexists (Z,s), y, 0, s0; eauto 20 using get.
      * clear Get. edestruct IHLEN as [Zs [a [n' [lv ?]]]]; eauto; dcr; subst.
        exists Zs, a, (S n'), lv. simpl; rewrite EQ. eauto 20 using get.
    + rewrite EQ in *. edestruct IHLEN as [Zs [a [n [lv ?]]]]; eauto; dcr; subst.
      exists Zs, a, (S n), lv. simpl; rewrite EQ. eauto 20 using get.
Qed.

Lemma compileF_length LV F ans
  : length F = length ans
    -> length (compileF compile LV F ans) = countSome (getAnn ⊝ ans).
Proof.
  intros. length_equify.
  general induction H; simpl; eauto.
  cases; subst. cases; simpl; eauto.
Qed.

Lemma getAnn_eq X Y Y' (F:list (Y * Y')) (als:list (ann X))
  : ❬F❭ = ❬als❭
    -> getAnn ⊝ als = fst ⊝ pair ⊜ (getAnn ⊝ als) (fst ⊝ F).
Proof.
  intros LEN.
  rewrite map_zip.
  rewrite zip_map_fst; eauto with len.
Qed.

Lemma getAnn_take_eq X Y Y' (F:list (Y * Y')) (als:list (ann X)) k a LV
  : ❬F❭ = ❬als❭
    -> get als k a
    -> getAnn ⊝ take k als = fst ⊝ take k (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ LV).
Proof.
  intros LEN Get.
  rewrite take_app_lt; eauto with len.
  repeat rewrite map_take.
  rewrite map_zip.
  rewrite zip_map_fst; eauto with len.
Qed.

Lemma DVE_isCalled LV s lv n
  : true_live_sound Imperative LV s lv
    -> trueIsCalled s (LabI n)
    -> isCalled (compile LV s lv) (LabI (countSome (fst ⊝ take n LV))).
Proof.
  intros Live IC. general induction IC; invt true_live_sound; simpl.
  - cases; eauto using isCalled.
  - repeat cases; eauto using isCalled. congruence.
  - repeat cases; eauto using isCalled. congruence.
  - eauto using isCalled.
  - eauto using isCalled.
  - edestruct get_length_eq as [a GetA]; eauto.
    edestruct true_live_sound_trueIsCalled as [lv [Z ?]]; eauto.
    rewrite get_app_lt in H1; eauto with len. simpl in *. inv_get.
    + exploit compileF_get; eauto.
      econstructor; eauto.
      * rewrite compileF_length; eauto.
        rewrite (take_eta k (getAnn ⊝ als)). rewrite countSome_app.
        rewrite map_take. erewrite <- get_eq_drop; eauto.
        rewrite <- H2. simpl. omega.
      * exploit IHIC1 as IH; eauto; try reflexivity; simpl.
        rewrite compileF_length; eauto with len.
        rewrite take_app_ge in IH; eauto 20 with len.
        rewrite map_app in IH.
        rewrite <- getAnn_eq in IH; eauto. rewrite countSome_app in IH; eauto.
        rewrite zip_length2 in IH; eauto with len.
        rewrite map_length in IH. orewrite (❬F❭ + n - ❬als❭ = n) in IH. eauto.
      * exploit IHIC2 as IH; eauto. erewrite <- getAnn_take_eq in IH; eauto.
  - eapply IsCalledLet.
    exploit IHIC; eauto; try reflexivity.
    rewrite compileF_length; eauto.
    rewrite take_app_ge in H; eauto 20 with len.
    rewrite zip_length2 in H; eauto with len.
    rewrite map_length in H.
    orewrite (❬F❭ + n - ❬als❭ = n) in H. simpl.
    rewrite map_app in H. rewrite countSome_app in H.
    rewrite <- getAnn_eq in H; eauto.
Qed.

Lemma DVE_noUnreachableCode LV s lv
  : true_live_sound Imperative LV s lv
    -> noUnreachableCode (compile LV s lv).
Proof.
  intros Live. induction Live; simpl; repeat cases; eauto using noUnreachableCode.
  - subst. econstructor; eauto using noUnreachableCode.
    + intros. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' [lv' ?]]]]; eauto; dcr; subst; simpl.
      eapply H3; eauto.
    + intros.
      edestruct get_in_range as [Zs ?]; eauto. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' [lv' ?]]]]; eauto; dcr; subst; simpl.
      exploit H0; eauto. rewrite <- H8.
      eauto using zip_get, map_get_1.
      exploit DVE_isCalled as IH; eauto.
      erewrite <- getAnn_take_eq in IH; eauto.
Qed.

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

Definition indexwise_r (r:rel2 I.state (fun _ => I.state)) A (PR:ProofRelationI A) AL' F F' AL L L' :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r (mapi I.mkBlock F ++ L, E[Z <-- List.map Some VL], s)
            (mapi I.mkBlock F' ++ L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon (r r':rel2 I.state (fun _ => I.state)) A (PR:ProofRelationI A) AL' F F' AL L L'
  : indexwise_r r PR AL' F F' AL L L'
    -> (forall x y, r x y -> r' x y)
    -> indexwise_r r' PR AL' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition renILabenv r
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
            -> sim'r r (drop (f  - n) L, E, stmtApp (LabI n) Y)
                    (drop (f'  - n') L', E', stmtApp (LabI n') Y')).

Lemma renILabenv_mon (r r':rel2 I.state (fun _ => I.state)) A (PR:ProofRelationI A) AL L L'
  : renILabenv r PR AL L L'
    -> (forall x y, r x y -> r' x y)
    -> renILabenv r' PR AL L L'.
Proof.
  intros [[? ?] SIM] LE; hnf; intros; split; eauto.
  intros. edestruct SIM as [[? ?] SIM']; eauto.
  split; eauto. intros.
  eapply paco2_mon. eapply SIM; eauto. eauto.
Qed.

Definition indexwise_proofrel A (PR:ProofRelationI A) (F F':〔params * stmt〕) AL' AL :=
  forall n n' Z s Z' s' a,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> get AL' n a
    -> ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n').

Lemma renILabenv_extension' r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : indexwise_r (sim'r r \2/ r) PR AL' F F' AL L L'
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> renILabenv r PR AL L L'
    -> renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
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
    eapply paco2_mon. eapply SIM; eauto. eauto.
Qed.

Lemma fix_compatible_I A (PR:ProofRelationI A) AL F F' L L' AL'
(LEN2:length AL' = length F)
  : (forall r, renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
            -> indexwise_r (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, renILabenv r PR AL L L'
           -> indexwise_r (sim'r r) PR AL' F F' AL L L'.
Proof.
  intros ISIM IP Ilt Ige Img r SIML; pcofix CIH.
  eapply ISIM; eauto.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  eapply renILabenv_extension'; eauto using renILabenv_mon, indexwise_r_mon.
Qed.

(*
Definition indexwise_r' (r:rel2 I.state (fun _ => I.state)) A (PR:ProofRelationI A) AL L L' :=
  forall f f' a Z s n Z' s' n',
    IndexRelI AL f f'
    -> get AL f a
    -> get L f (I.blockI Z s n)
    -> get L' f' (I.blockI Z' s' n')
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r (drop (f - n) L, E[Z <-- List.map Some VL], s)
            (drop (f' - n') L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon' (r r':rel2 I.state (fun _ => I.state)) A (PR:ProofRelationI A) AL' F F' AL L L'
  : indexwise_r r PR AL' F F' AL L L'
    -> (forall x y, r x y -> r' x y)
    -> indexwise_r r' PR AL' F F' AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition indexwise_proofrel' A (PR:ProofRelationI A) AL L L' :=
  forall f f' Z s n Z' s' n' a,
    IndexRelI AL f f'
    -> get L f (I.blockI Z s n)
    -> get L' f' (I.blockI Z' s' n')
    -> get AL f a
    -> ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n').

Lemma fix_compatible_I' A (PR:ProofRelationI A) AL L L'
(LEN2:length AL = length L)
  : (forall r, renILabenv r PR AL L L' -> indexwise_r' (sim'r r) PR AL L L')
    -> indexwise_proofrel' PR AL L L'
    -> sawtooth L
    -> sawtooth L'
    -> forall r, indexwise_r' (sim'r r) PR AL L L'.
Proof.
  intros ISIM IP STL STL' r; pcofix CIH.
  eapply ISIM; eauto.
  split; eauto.
  intros. split; eauto.
  intros. exploit IP; eauto; dcr.
  exploit ArgLengthMatchI; eauto; dcr.
  pone_step.
  eapply (sawtooth_get STL H1). simpl. eapply omap_length in H4. congruence.
  eapply (sawtooth_get STL' H2). simpl. eapply omap_length in H5. congruence.
  simpl. right. orewrite (n - n = 0). orewrite (n' - n' = 0). simpl.
  eapply CIH; eauto.
Qed.

Lemma fix_compatible_I'' A (PR:ProofRelationI A) AL F F' L L' AL'
(LEN2:length AL' = length F)
  : (forall r, renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
            -> indexwise_r (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, renILabenv r PR AL L L'
           -> renILabenv (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros ISIM IP Ilt Ige Img r SIML.
  destruct SIML as [[? ?] SIM].
  exploit fix_compatible_I'; eauto using @sawtooth, tooth_I_mkBlocks with len.
  intros.




  eapply ISIM; eauto.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  eapply renILabenv_extension'; eauto using renILabenv_mon, indexwise_r_mon.
Qed.


Lemma renILabenv_extension' A (PR:ProofRelationI A) (AL:list A) L L'
      (LEN1:length AL' = length F)
  : (forall r, renILabenv r PR AL L L' -> indexwise_r' (sim'r r) PR AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, renILabenv r PR AL L L'
           -> renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros. eapply renILabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.


(*
Lemma indexrel_extend A (PR:ProofRelationI A) AL F F' L L' AL'
(LEN2:length AL' = length F)
  : (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, renILabenv r PR AL L L'
           -> indexwise_r (sim'r r) PR AL' F F' AL L L'
           -> indexwise_r' (sim'r r) PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros Ilt Ige Img r SIML IW.
  hnf. intros ? ? ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL as [GetAL'|GetAL].
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. simpl in *. clear EQ.
    orewrite (n - n = 0). simpl.
    exploit Ilt; eauto using get_range.
    eapply get_app_lt_1 in GetL'; [| rewrite mapi_length; eauto with len ].
    inv_get. destruct x as [Z' s']. simpl in *. clear EQ.
    orewrite (n' - n' = 0); simpl.
    eapply IW; eauto.
  - destruct SIML; dcr.
    exploit Ige; eauto; try congruence.
    eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    eapply get_app_right_ge in GetL'; [ | eauto with len; rewrite mapi_length; eauto].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto.
    edestruct H1 as [[? ?] SIM]; eauto. rewrite H; eauto. rewrite Img; eauto.
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
    eapply sim'_expansion_closed. eapply SIM; eauto.

Admitted.
 *)

*)


Lemma renILabenv_extension A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : (forall r, renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L')
          -> indexwise_r (sim'r r) PR AL' F F' AL L L')
    -> indexwise_proofrel PR F F' AL' AL
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> forall r, renILabenv r PR AL L L'
           -> renILabenv r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros. eapply renILabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
Qed.

Module I.

  Definition ArgRel (V V':onv val) (G:؟(set var) * params) (VL VL': list val) : Prop :=
      VL' = (filter_by (fun x => B[x ∈ oget (fst G)]) (snd G) VL) /\
      length (snd G) = length VL /\
      agree_on eq (oget (fst G) \ of_list (snd G)) V V'.


  Definition ParamRel (G:option (set var) * params) (Z Z' : list var) : Prop :=
    Z' = (List.filter (fun x => B[x ∈ oget (fst G)]) Z) /\ snd G = Z.

Instance SR : ProofRelationI (؟(set var) * params) := {
   ParamRelI := ParamRel;
   ArgRelI := ArgRel;
   BlockRelI := fun lvZ b b' => True;
   Image AL := countSome (List.map fst AL);
   IndexRelI AL n n' :=
     n' = countSome (fst ⊝ (take n AL)) /\ exists lv Z, get AL n (Some lv, Z)
}.
- intros. hnf in H, H0; dcr; subst.
  erewrite filter_filter_by_length; eauto.
- intros AL' AL n n' [H H']; subst.
  split. clear H' H.
  + general induction AL'; simpl.
    * orewrite (n - 0 = n). omega.
    * destruct n; simpl; eauto. cases; simpl; eauto.
  + destruct H' as [? [? ?]]. rewrite get_app_ge in H0; eauto.
Defined.


Lemma inv_extend s L L' LV als lv Z f
(LEN: ❬s❭ = ❬als❭)
(H: forall (f : nat) (lv : ⦃var⦄) (Z : params),
       get LV f (⎣ lv ⎦, Z) ->
       exists b b' : I.block, get L f b /\ get L' (countSome (fst ⊝ take f LV)) b')
(Get : get (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV) f (⎣ lv ⎦, Z))
  :  exists b b' : I.block, get (mapi I.mkBlock s ++ L) f b /\
                       get (mapi I.mkBlock (compileF compile (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV) s als) ++ L') (countSome (fst ⊝ take f (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV))) b'.
Proof.
  get_cases Get; inv_get.
  - exploit compileF_get; eauto.
    do 2 eexists; split; eauto using get_app, mapi_get_1.
    eapply get_app. eapply mapi_get_1.
    erewrite <- getAnn_take_eq; eauto.
  - edestruct H as [b [b' [? ?]]]; eauto.
    exists b, b'; split.
    eapply get_app_right; eauto.
    rewrite mapi_length. rewrite zip_length2; eauto with len.
    rewrite map_length.
    rewrite zip_length2 in H1; eauto with len.
    rewrite map_length in H1. omega.
    eapply get_app_right; eauto.
    rewrite take_app_ge; eauto. rewrite map_app.
    rewrite countSome_app.
    rewrite mapi_length.
    rewrite compileF_length; eauto.
    rewrite <- getAnn_eq; eauto.
Qed.


Lemma sim_I r L L' V V' s LV lv
: agree_on eq (oget (getAnn lv)) V V'
-> true_live_sound Imperative LV s lv
-> renILabenv r SR LV L L'
-> (forall (f:nat) lv Z,
      get LV f (Some lv, Z)
      -> exists (b b' : I.block),
        get L f b /\
        get L' (countSome (fst ⊝ (take f LV))) b')
-> sim'r r (L,V, s) (L',V', compile LV s lv).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + cases.
      *  pone_step. instantiate (1:=v).
         erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
         left. eapply (IH s); eauto. eapply agree_on_update_same. reflexivity.
         eapply agree_on_incl; eauto.
      *  eapply sim'_expansion_closed;
           [ | eapply star2_silent;
               [ econstructor; eauto | eapply star2_refl ]
             | eapply star2_refl].
         eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
         eapply agree_on_incl; eauto. rewrite <- H10. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
      eapply H11; congruence.
      eapply star2_silent.
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s2); eauto. eapply agree_on_incl; eauto.
      eapply star2_silent.
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      eapply H9. case_eq (exp2bool e); intros; try destruct b; congruence.
      destruct o. case_eq (val2bool v); intros.
      pfold; econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. reflexivity.
      left; eapply (IH s1); eauto using agree_on_incl.
      pfold; econstructor; try eapply plus2O.
      econstructor 3; eauto. reflexivity.
      econstructor 3; eauto. reflexivity.
      left; eapply (IH s2); eauto using agree_on_incl.
      pfold. econstructor 3; try eapply star2_refl; eauto.
      stuck.
  - edestruct H2 as [? [? [GetL GetL']]]; eauto.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    rewrite (get_nth (None, nil) H5); eauto; simpl.
    destruct o.
    + destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      hnf in H1; dcr.
      exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z Heqo); eauto.
      exploit omap_exp_eval_live_agree; eauto.
      intros. eapply argsLive_liveSound; eauto.
      edestruct H4 as [[? ?] SIM]; eauto. hnf; eauto.
      hnf in H12; dcr; subst.
      eapply (@sim_Y_left I.state _ I.state _).
      eapply (@sim_Y_right I.state _ I.state _).
      eapply SIM; [ | eapply Heqo | eapply H9 ].
      hnf; simpl. split; eauto.
      exploit (omap_length _ _ _ _ _ Heqo); eauto. split. congruence.
      eauto using agree_on_incl.
      Focus 4. econstructor; eauto.
      Focus 2. econstructor; eauto. simpl.
      eapply filter_filter_by_length; eauto.
      * simpl.
        eapply (stepGoto' _ _ GetL'); eauto; simpl.
        eapply filter_filter_by_length; eauto.
      * simpl.
        eapply (stepGoto' _ _ GetL); eauto.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.

  - pno_step.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    + pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
    + pno_step.
  - pone_step. left. eapply IH; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + eapply renILabenv_extension; eauto. eauto with len.
      * intros. hnf; intros.
        hnf in H4. dcr.
        rewrite get_app_lt in H16; eauto using get_range.
        inv_get.
        exploit (compileF_get ((pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV) )); eauto.
        erewrite <- getAnn_take_eq in H10; eauto.
        get_functional. clear EQ0.
        hnf in H14; dcr; subst.
        eapply IH; eauto.
        rewrite EQ. simpl.
        eapply agree_on_update_filter'; eauto.
        exploit H7; eauto using zip_get.
        rewrite <- EQ. eapply zip_get; eauto using map_get.
        exploit H9; eauto.
        intros.
        eapply inv_extend; eauto.
      * hnf; intros.
        hnf in H3. dcr.
        rewrite get_app_lt in H14; eauto with len.
        inv_get. simpl; unfold ParamRel; simpl.
        exploit (compileF_get ((pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV) )); eauto.
        erewrite <- getAnn_take_eq in H6; eauto.
        get_functional. eauto.
      * intros. rewrite compileF_length; eauto.
        hnf in H3; dcr; subst.
        rewrite get_app_lt in H10;
          [| rewrite zip_length2; eauto with len; rewrite map_length; omega].
        inv_get.
        erewrite <- getAnn_take_eq; eauto.
        rewrite map_take.
        erewrite (take_eta n (getAnn ⊝ als)) at 2.
        rewrite countSome_app.
        erewrite <- get_eq_drop; eauto using map_get_1.
        rewrite EQ1. simpl; omega.
      * intros. rewrite compileF_length; eauto.
        hnf in H3; dcr; subst.
        rewrite map_take. rewrite map_app.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
        rewrite take_app_ge. rewrite countSome_app. omega.
        rewrite map_length. omega.
      * simpl. rewrite compileF_length; eauto.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
    + intros; eapply inv_extend; eauto.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative nil s lv
-> @sim I.state _ I.state _ (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply sim_I; eauto. hnf. econstructor.
Qed.

End I.


Definition ArgRel (V V:onv val) (G:option (set var * params)) (VL VL': list val) : Prop :=
  match G with
  | Some G => VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\ length (snd G) = length VL
  | None => VL' = VL
  end.

Definition ParamRel (G:(؟(set var * params))) (Z Z' : list var) : Prop :=
  match G with
  | Some G => Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z
  | None => True
  end.

Instance SR : ProofRelationI (؟(set var * params)) :=
  {
    ParamRelI := ParamRel;
    ArgRelI := ArgRel;
    BlockRelI := fun lvZ b b' => True;
    IndexRelI D n n' := True
  }.
Proof.
intros. hnf in H, H0. destruct a; dcr. subst.
erewrite filter_filter_by_length; eauto.
Admitted.


Fixpoint compile_live (s:stmt) (a:ann (set var)) (G:set var) : ann (set var) :=
  match s, a with
    | stmtLet x e s, ann1 lv an as a =>
      if [x ∈ getAnn an] then ann1 (G ∪ lv) (compile_live s an {x})
                         else compile_live s an G
    | stmtIf e s t, ann2 lv ans ant =>
      if [exp2bool e = Some true] then
        compile_live s ans G
      else if [exp2bool e = Some false ] then
        compile_live t ant G
      else
        ann2 (G ∪ lv) (compile_live s ans ∅) (compile_live t ant ∅)
    | stmtApp f Y, ann0 lv => ann0 (G ∪ lv)
    | stmtReturn x, ann0 lv => ann0 (G ∪ lv)
    | stmtExtern x f Y s, ann1 lv an as a =>
      ann1 (G ∪ lv) (compile_live s an {x})
    | stmtFun F t, annF lv ans ant =>
      let ans' := zip (fun Zs a => let a' := compile_live (snd Zs) a ∅ in
                               setTopAnn a' (getAnn a' ∪ of_list (List.filter (fun x => B[x ∈ getAnn a]) (fst Zs)))) F ans in
      annF (G ∪ lv) ans' (compile_live t ant ∅)
    | _, a => a
  end.


Lemma compile_live_incl G i LV s lv
  : true_live_sound i LV s lv
    -> getAnn (compile_live s lv G) ⊆ G ∪ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity.
    + etransitivity; eauto. rewrite <- H2. eauto. congruence.
    + etransitivity; eauto.  rewrite <- H3; eauto.
Qed.

Lemma compile_live_incl_empty i LV s lv
  : true_live_sound i LV s lv
    -> getAnn (compile_live s lv ∅) ⊆ getAnn lv.
Proof.
  intros.
  eapply compile_live_incl in H.
  rewrite H. cset_tac; intuition.
Qed.

Lemma incl_compile_live G i LV s lv
  : true_live_sound i LV s lv
    -> G ⊆ getAnn (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity. cset_tac; intuition.
    rewrite <- IHtrue_live_sound. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity; eauto.
Qed.

Definition compile_LV (LV:list (set var *params)) :=
  List.map (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                      (fst lvZ, Z')) LV.

Lemma dve_live i LV s lv G
  : true_live_sound i LV s lv
    -> live_sound i (compile_LV LV) (compile LV s lv) (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - cases; eauto. econstructor; eauto.
    + eapply live_exp_sound_incl; eauto. eauto.
    + rewrite compile_live_incl; eauto.
      rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - repeat cases; eauto.
    + econstructor; eauto; try rewrite compile_live_incl; eauto.
      eapply live_exp_sound_incl. eapply incl_right.
      eapply H1. case_eq (exp2bool e); intros; try destruct b; congruence.
      cset_tac; intuition.
      cset_tac; intuition.
  - econstructor.
    + eapply (map_get_1 (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                                   (fst lvZ, Z')) H); eauto.
    + simpl. destruct i; simpl in * |- *; eauto.
      rewrite <- H0. rewrite minus_inter_empty. eapply incl_right.
      cset_tac; intuition. eapply filter_incl2; eauto.
      eapply filter_in; eauto. intuition. hnf. cases; eauto.
      rewrite <- H0. rewrite minus_inter_empty. eapply incl_right.
      cset_tac; intuition. eapply filter_incl2; eauto.
      eapply filter_in; eauto. intuition. hnf. cases; eauto.
    + simpl. eapply get_nth in H. erewrite H. simpl.
      erewrite filter_filter_by_length. reflexivity. congruence.
    + intros. eapply get_nth in H. erewrite H in H3. simpl in *.
      edestruct filter_by_get as [? [? [? []]]]; eauto; dcr.
      eapply live_exp_sound_incl. eapply incl_right.
      eapply argsLive_live_exp_sound; eauto. simpl in *.
      decide (x0 ∈ blv); intuition.
  - econstructor; eauto.
    eapply live_exp_sound_incl; eauto using incl_right.
  - econstructor; eauto.
    + intros; eapply live_exp_sound_incl; eauto using incl_right.
    + rewrite compile_live_incl; eauto. rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - econstructor; simpl in *; eauto with len.
    + eapply live_sound_monotone.
      eapply IHtrue_live_sound.
      unfold compile_LV. rewrite map_app. eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. rewrite of_list_filter.
      split; cset_tac.
    + intros; inv_get.
      eapply live_sound_monotone.
      eapply live_sound_monotone2; eauto. eapply H2; eauto.
      unfold compile_LV. rewrite map_app. eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. rewrite of_list_filter.
      split; cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      rewrite of_list_filter.
      clear_all; cset_tac.
    + rewrite compile_live_incl; eauto with cset.
Qed.

Lemma sim_DVE' r L L' V V' s LV lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional LV s lv
-> simL' sim_progeq r SR LV L L'
-> sim'r r (L,V, s) (L',V', compile LV s lv).
Proof.
  unfold simL', sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros. cases.
    + pone_step.
      instantiate (1:=v). erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
      left. eapply (IH s); eauto. eapply agree_on_update_same; eauto with cset.
    + eapply sim'_expansion_closed;
      [ | eapply S_star2 with (y:=EvtTau);
          [ econstructor; eauto | eapply star2_refl ]
        | eapply star2_refl].
      eapply (IH s); eauto. eapply agree_on_update_dead; eauto with cset.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
      eapply H10; congruence.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s2); eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      eapply H8. case_eq (exp2bool e); intros; try destruct b; congruence.
      destruct o. case_eq (val2bool v); intros.
      pone_step. left. eapply IH; eauto with cset.
      pone_step. left; eapply (IH s2); eauto with cset.
      pno_step.
  - destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    + remember (omap (exp_eval V) Y). symmetry in Heqo.
      rewrite (get_nth (∅, nil) H4); simpl.
      destruct o.
      * exploit omap_filter_by; eauto.
        unfold simL' in H1. inRel_invs. simpl in *.
        hnf in H17; dcr; subst; simpl in *.
        eapply sim_drop_shift; eauto.
        eapply (inRel_sawtooth H1). eapply (inRel_sawtooth H1). eapply H19. eauto.
        eapply omap_exp_eval_live_agree; eauto.
        eapply argsLive_liveSound; eauto.
        hnf; split; eauto. simpl. exploit omap_length; try eapply Heqo; eauto.
        congruence.
      * pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
  - pno_step; simpl. erewrite <- exp_eval_live_agree; eauto; symmetry; eauto.
  - remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    + pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
    + pno_step.
  - pone_step. left. eapply IH; eauto with cset.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto with len.
      * intros. inv_get; simpl. split. hnf; intros; simpl.
        unfold ParamRel, ArgRel. intuition.
        eapply (IH s1); eauto. subst.
        eapply agree_on_update_filter'; eauto.
        eapply agree_on_incl; eauto. simpl.
        exploit H8; eauto.
        exploit H6; eauto.
        unfold ParamRel. intuition.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional nil s lv
-> @sim F.state _ F.state _ (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply sim_DVE'; eauto. hnf. econstructor.
Qed.
