Require Import AllInRel Util Map Env EnvTy Exp IL Bisim DecSolve MoreList InRel Sublist.

Set Implicit Arguments.
Unset Printing Records.

(** Pull all definitions to the top.
    [D] at index f holds the new index of function f
    n is the number of pulled-up defintions so far (n >= length D),
    not neccessarily equal
    yields the transformed statement and the global definitions
*)

Definition egalize_funs (egalize:list nat -> nat -> stmt -> stmt * list (params * stmt))
           (D':list nat) (n:nat) (F:list (params * stmt)) :=
  fold_right (fun f nF' =>
                       let '(n, F1, F2) := nF' in
                       let (s, F'') := egalize D' n (snd f) in
                       let n' := n + length F'' in
                       (n', (fst f, s)::F1, F2 ++ F'')) (n, nil, nil) F.

Definition plus' n i (Z:params * stmt) := n + i.
Definition extend n (F:list (params * stmt)) D := mapi (fun i _ => i+n) F ++ D.

Fixpoint egalize (D:list nat) (n:nat) (s:stmt) : stmt * list (params * stmt) :=
  match s with
    | stmtLet x e s =>
      let (s', F) := egalize D n s in
      (stmtLet x e s', F)
    | stmtExtern x f Y s =>
      let (s', F) := egalize D n s in
      (stmtExtern x f Y s', F)
    | stmtIf x s1 s2 =>
      let (s1', F1) := egalize D n s1 in
      let (s2', F2) := egalize D (n + length F1) s2 in
      (stmtIf x s1' s2', F1 ++ F2)
    | stmtApp l Y => (stmtApp (LabI (nth (counted l) D 0)) Y, nil)
    | stmtReturn x => (stmtReturn x, nil)
    | stmtFun F s =>
      (* entries for definitions in F: they are put to the bottom of the stack *)
      let D' := mapi (plus' n) F ++  D in
      let '(n', F1, F2) := egalize_funs egalize D' (length F + n) F in
      let (s', F'') := egalize D' n' s in
      (s', F1 ++ F2 ++ F'')
  end.

Lemma egalize_funs_length1 f D n F
      : length (snd (fst (egalize_funs f D n F))) = length F.
Proof.
  induction F; intros; simpl; eauto.
  erewrite <- IHF. unfold egalize_funs.
  repeat let_pair_case_eq; subst; simpl.
  repeat f_equal.
Qed.

Lemma egalize_funs_length2 f D n F
      : length (snd (egalize_funs f  D n F)) + n = fst (fst (egalize_funs f  D n F)).
Proof.
  revert n. induction F; intros; simpl; eauto.
  repeat let_pair_case_eq; subst; simpl.
  rewrite app_length. rewrite <- IHF. omega.
Qed.

Lemma egalize_funs_get F f Zb sb n D s p
: get F f (Zb, sb)
-> get (snd (fst (egalize_funs egalize D n F))) f (p, s)
-> let nF := egalize_funs egalize D n (drop (f+1) F) in
    fst (egalize D (fst (fst nF)) sb) = s /\ p = Zb.
Proof.
  intros GetF GetE nF.
  general induction F.
  - inv GetF.
  - simpl in *. subst nF. inv GetF.
    + simpl in *.
      repeat let_case_eq. subst. simpl in *. inv GetE. rewrite eq1; eauto.
    + inv GetE. simpl. eapply IHF; eauto.
      repeat let_case_eq; subst; simpl in *; eauto.
      inv H; eauto.
Qed.

Lemma mapi_app X Y (f:nat -> X -> Y) n L L'
: mapi_impl f n (L++L') = mapi_impl f n L ++ mapi_impl f (n+length L) L'.
Proof.
  general induction L; simpl; eauto.
  - orewrite (n + 0 = n); eauto.
  - f_equal. rewrite IHL. f_equal; f_equal. omega.
Qed.

Lemma drop_app_eq X (L L' : list X) n
: length L = n
  -> drop n (L ++ L') = L'.
Proof.
  intros; subst. orewrite (length L = length L + 0) . eapply drop_app.
Qed.

Lemma egalize_funs_get2 D n' F L' f Zb sb
  : get F f (Zb, sb)
    -> exists L'',
      let h := egalize_funs egalize D n' in
      drop (length (snd (h (drop (f + 1) F))))
           (mapi_impl I.mkBlock n' (snd (h F))
                      ++ L') =
      mapi_impl I.mkBlock (length (snd (h (drop (f + 1) F))) + n')
                (snd (egalize D
                              (length (snd (h (drop (f + 1) F))) + n') sb)) ++
                L''.
Proof.
  intros. general induction f. inv H.
  - simpl in *.
    repeat let_pair_case_eq; subst; simpl.
    rewrite <- egalize_funs_length2.
    rewrite mapi_app.
    simpl in *.
    rewrite <- app_assoc.
    erewrite (drop_app_eq). eexists. rewrite Plus.plus_comm. reflexivity.
    rewrite mapi_length; eauto.
  - inv H; simpl in *.
    repeat let_pair_case_eq; subst; simpl.
    edestruct (IHf D) with (n':=n'); eauto.
    eexists. rewrite mapi_app. rewrite <- app_assoc.
    eapply H0.
Qed.

Lemma app_drop X (L L' L'':list X)
 : L = L' ++ L''
   -> drop (length L') L = L''.
Proof.
  general induction L'; simpl; eauto.
Qed.

Require Import BisimI.


Ltac simpl_get_dropI :=
  repeat match goal with
  | [ H : get (drop (?n - _) ?L) _ _, H' : get ?L ?n ?blk, STL: sawtooth ?L |- _ ]
    => eapply get_drop in H;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X, H;
        orewrite (n - I.block_n blk + I.block_n blk = n) in H; clear X
  | [ H' : get ?L ?n ?blk, STL: sawtooth ?L |- get (drop (?n - _) ?L) _ _ ]
    => eapply drop_get;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X; simpl;
        orewrite (n - I.block_n blk + I.block_n blk = n); clear X
  end.

Lemma sawtooth_app B `{BlockType B} L L'
  : sawtooth L -> sawtooth L' -> sawtooth (L ++ L').
Proof.
  intros H1 H2. general induction H1; eauto.
  rewrite <- app_assoc. econstructor; eauto.
Qed.

Ltac not_activated H :=
  let STEP := fresh "STEP" in
  destruct H as [? [? STEP]]; inv STEP.

Ltac not_normal H :=
  destruct H; econstructor; eexists; econstructor; eauto.

Lemma bisim_drop_shift_left r l (L:I.labenv) E Y
      blk (STL:sawtooth L) sigma
  : get L (labN l) blk
    -> paco2 (@bisim_gen I.state _ I.state _) r
            (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
            sigma
    -> paco2 (@bisim_gen I.state _ I.state _) r
            (L, E, stmtApp l Y)
            sigma.
Proof.
  intros GetL SIM. pinversion SIM; subst.
  - eapply plus2_destr_nil in H. destruct H as [? [? ?]].
    invt step. clear H. simpl in *.
    eapply get_drop in Ldef. exploit (sawtooth_smaller STL GetL); eauto.
    simpl in *.
    assert (l_eq:labN l - I.block_n blk + I.block_n blk = labN l). omega.
    rewrite l_eq in *. get_functional.
    orewrite (I.block_n blk - I.block_n blk = 0) in H2. simpl in *.
    pfold.
    econstructor 1.
    eapply star2_plus2. econstructor; eauto. eapply H2. eauto. eauto.
  - inv H.
    + exfalso. not_activated H1.
    + invt step. clear H6. simpl in *.
      eapply get_drop in Ldef. exploit (sawtooth_smaller STL GetL); eauto.
      simpl in *.
      assert (l_eq:labN l - I.block_n blk + I.block_n blk = labN l). omega.
      rewrite l_eq in *. get_functional. subst.
      orewrite (I.block_n blk - I.block_n blk = 0) in H8. simpl in *.
      pfold.
      econstructor 2.
      eapply star2_silent. econstructor; eauto. eapply H8. eauto. eauto. eauto.
      eauto. eauto.
  - inv H0.
    + assert ( get (drop (labN l - block_n blk) L) (counted (LabI (block_n blk))) blk). {
        eapply drop_get. simpl.
        exploit (sawtooth_smaller STL); eauto. simpl in *.
        orewrite (labN l - I.block_n blk + I.block_n blk = labN l). eauto.
      }
      decide (❬I.block_Z blk❭ = ❬Y❭).
      case_eq (omap (exp_eval E) Y); intros.
      not_normal H2.
      pfold. econstructor 3. Focus 2. eapply star2_refl. eauto. eauto.
      stuck2. eauto.
      pfold. econstructor 3. Focus 2. eapply star2_refl. eauto. eauto.
      stuck2. eauto.
    + invt step. clear H5. simpl in *.
      eapply get_drop in Ldef. exploit (sawtooth_smaller STL GetL); eauto.
      simpl in *.
      assert (l_eq:labN l - I.block_n blk + I.block_n blk = labN l). omega.
      rewrite l_eq in *. get_functional. subst.
      orewrite (I.block_n blk - I.block_n blk = 0) in H7. simpl in *.
      pfold. econstructor 3. Focus 2.
      eapply star2_silent. econstructor; eauto. eapply H7. eauto. eauto. eauto.
      eauto.
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
    ArgLengthMatchI : forall E E' a Z Z' VL VL',
        ParamRelI a Z Z' -> ArgRelI E E' a VL VL' -> length Z = length VL /\ length Z' = length VL';
    IndexRelDrop : forall k AL n n', IndexRelI AL n n' -> k <= n -> IndexRelI (drop k AL) (n - k) n'
(*    IndexRelApp : forall AL AL' n n', IndexRelI AL n n' -> IndexRelI (AL' ++ AL) (❬AL'❭ + n) n' *)
}.

Inductive simIBlock (SIM:ProgramEquivalence I.state I.state)
          (r:I.state -> I.state -> Prop)
          {A} (AR:ProofRelationI A)
  : list A -> I.labenv -> I.labenv -> A -> I.block -> I.block -> Prop :=
| simIBlockI a L L' Z Z' s s' n n' bn' AL
  : ParamRelI a Z Z'
    -> BlockRelI a (I.blockI Z s n) (I.blockI Z' s' bn')
    -> IndexRelI AL n n'
    -> (forall E E' Yv Y'v Y Y',
          omap (exp_eval E) Y = Some Yv
          -> omap (exp_eval E') Y' = Some Y'v
          -> ArgRelI E E' a Yv Y'v
          -> progeq r (L, E, stmtApp (LabI n) Y)
                   (L', E', stmtApp (LabI n') Y'))
          -> simIBlock SIM r AR AL L L' a (I.blockI Z s n) (I.blockI Z' s' bn').


Definition renILabenv (SIM:ProgramEquivalence I.state I.state) r
           {A} AR (AL:list A) L L' :=
  (length AL = length L /\ tooth 0 L' /\ sawtooth L) /\
  forall n n' a b b', IndexRelI AL n n' -> get AL n a -> get L n b -> get L' n' b'
               -> simIBlock SIM r AR
                           (drop (n - I.block_n b) AL)
                           (drop (n - I.block_n b) L)
                           L'
                           a b b' .

Definition fexteqI (SIM:ProgramEquivalence I.state I.state)
           {A} (PR:ProofRelationI A) (a:A) (AL:list A) L L' Z s Z' s' :=
  ParamRelI a Z Z' /\
  forall E E' VL VL' (r:rel2 I.state (fun _ : I.state => I.state)),
    ArgRelI E E' a VL VL'
    -> renILabenv SIM r PR AL L L'
    -> progeq r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').

Lemma fix_compatible_I r A (PR:ProofRelationI A) (a:A) AL F E E' Z Z' L L' Yv Y'v s s' n n' AL' bn
(LEN2:length AL' = length F)
  : renILabenv bisim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a bn, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                              -> get L' n' (I.blockI Z' s' bn) -> get AL' n a ->
                             fexteqI bisim_progeq PR a (AL' ++ AL) (mapi I.mkBlock F ++ L) L' Z s Z' s'
                             /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' bn)
                             /\ ParamRelI a Z Z')
    -> get F n (Z,s)
    -> IndexRelI (AL' ++ AL) n n'
    -> get L' n' (I.blockI Z' s' bn)
    -> get AL' n a
    -> ArgRelI E E' a Yv Y'v
    -> tooth 0 L'
    -> sawtooth L
    -> bisim'r r
              (mapi I.mkBlock F ++ L, E [Z <-- List.map Some Yv], s)
              (L', E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto. clear H2 H3 H4 H5 H6. clear s s' Z Z' n n' a bn.
  hnf. split.
  destruct H0; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  intros ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL.
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. destruct b' as [Z' s' bn]. simpl.
    assert (bn = n'). {
      exploit (tooth_index H7 GetL'); eauto. simpl in *. omega.
    }
    subst bn.
    orewrite (n - n = 0). simpl.
    exploit H1; eauto; dcr.
    eapply simIBlockI; eauto. simpl.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit (omap_length _ _ _ _ _ H3).
    exploit (omap_length _ _ _ _ _ H5).
    pone_step; eauto using get_app, get_mapi; eauto; simpl.
    congruence. congruence.
    orewrite (n - n = 0); simpl.
    right.
    orewrite (n' - n' = 0); simpl.
    eapply CIH; eauto.
  - destruct H0.
    dcr. eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    assert (n - I.block_n b >= ❬mapi I.mkBlock F❭). {
      exploit (sawtooth_smaller H8 GetFL). rewrite <- H in *. simpl in *. omega.
    }
    exploit H3. instantiate (2:=n-❬mapi I.mkBlock F❭). instantiate (1:=n').
    eapply IndexRelDrop in RN. instantiate (1:=❬AL'❭) in RN.
    rewrite drop_length_eq in RN. rewrite <- H. eauto. omega.
    rewrite <- H. eauto. eauto. eauto.
    rewrite (drop_app_gen _ (mapi I.mkBlock F)); eauto.
    assert (EQ:n - ❬mapi I.mkBlock F❭ - I.block_n b = n - I.block_n b - ❬mapi I.mkBlock F❭)
      by omega.
    rewrite <- EQ.
    inv H6. econstructor; eauto. simpl in *.
    rewrite (drop_app_gen _ AL'); eauto.
    rewrite H. rewrite <- EQ. eauto. omega.
    intros. eapply progeq_mon; eauto.
Qed.


Lemma renILabenv_extension r A (PR:ProofRelationI A) (AL AL':list A) F L L'
      (LEN1:length AL' = length F)
  : renILabenv bisim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a bn, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                              -> get L' n' (I.blockI Z' s' bn) -> get AL' n a ->
                              fexteqI bisim_progeq PR a (AL' ++ AL) (mapi I.mkBlock F ++ L) L' Z s Z' s'
                              /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' bn)
                              /\ ParamRelI a Z Z')
  -> renILabenv bisim_progeq r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) L'.
Proof.
  intros. destruct H.
  split. dcr. split. eauto with len.
  split; eauto. econstructor; eauto using tooth_I_mkBlocks.
  intros ? ? ? ? ? RN GetAL GetL GetL'.
  assert (ALLEN:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL.
  - eapply get_app_lt_1 in GetL; [| rewrite <- ALLEN; eauto using get_range].
    inv_get. destruct x, b'.
    exploit H0; eauto. simpl in *. dcr.
    destruct H4. orewrite (n - n = 0); simpl.
    econstructor; eauto. intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit (omap_length _ _ _ _ _ H5).
    exploit (omap_length _ _ _ _ _ H10).
    pone_step; eauto using get_app, get_mapi; simpl; eauto with len.
    left. orewrite (n - n = 0); simpl.
    exploit (tooth_index H8 GetL'); eauto. simpl in *.
    orewrite (n' + 0 = n') in H16. subst; simpl in *.
    orewrite (n' - n' = 0); simpl.
    eapply fix_compatible_I; eauto.
    split; eauto.
  - dcr.
    eapply get_app_right_ge in GetL; [ | rewrite <- ALLEN; eauto].
    assert (n - I.block_n b >= ❬mapi I.mkBlock F❭). {
      exploit (sawtooth_smaller H7 GetL). rewrite <- ALLEN in *. simpl in *. omega.
    }
    rewrite (drop_app_gen _ (mapi I.mkBlock F)); eauto.
    rewrite (drop_app_gen _ AL'); [ | rewrite ALLEN; eauto ].
    assert (EQ:n - ❬mapi I.mkBlock F❭ - I.block_n b = n - I.block_n b - ❬mapi I.mkBlock F❭)
      by omega.
    rewrite ALLEN. rewrite <- EQ.
    eapply H1; eauto.
    eapply IndexRelDrop in RN. instantiate (1:= ❬mapi I.mkBlock F❭) in RN.
    rewrite <- ALLEN in RN. rewrite drop_length_eq in RN.
    rewrite ALLEN in RN. eauto. rewrite <- ALLEN. omega.
    rewrite <- ALLEN. eauto.
Qed.

Lemma nth_drop X (L:list X) n m x
: nth n (drop m L) x = nth (n+m) L x.
Proof.
  general induction m; simpl. orewrite (n + 0 = n); eauto.
  rewrite IHm; eauto. orewrite (n + S m = S (n + m)); eauto.
  destruct L; simpl; eauto. destruct (n + m); eauto.
Qed.

Instance PR : ProofRelationI (params * nat) :=
  {
    ParamRelI G Z Z' := Z = Z' /\ fst G = Z;
    ArgRelI V V' G VL VL' := VL = VL' /\ length VL = length (fst G) /\ V = V';
    BlockRelI G b b' := length (I.block_Z b) = length (fst G)
                           /\ length (I.block_Z b') = length (fst G);
    IndexRelI D n n' := exists a, get D n a /\ snd a = n'

  }.
intros. dcr; repeat subst. eauto.
intros. destruct H; dcr; subst.
eexists x; split; eauto.
eapply drop_get. orewrite (k + (n - k) = n); eauto.
Defined.


Definition R D n n' := n' = get D n n'.

Inductive approx (L':list I.block) (Z:params) (D:list nat)
  : nat -> I.block -> I.block -> Prop :=
  Approx s n m s' F f
  : egalize D m s = (s', F)
    -> approx L' Z D f (I.blockI Z s n) (I.blockI Z s' f).

Require Import LabelsDefined.

Lemma renestSim_sim r L L' E s n D L'' ZL
      (SL:forall (f f': nat),
          get D f f'
          -> exists (b b' : I.block) Z,
            get L f b /\
            get L' f' b' /\
            get ZL f Z /\
            approx L' Z (drop (f - block_n b) D) f' b b')
      (DEF:labelsDefined s (length D))
      (SIM:renILabenv bisim_progeq r PR (zip pair ZL D) L L')
      (DROP:drop n L' = mapi_impl I.mkBlock n (snd (egalize D n s)) ++ L'')
      (LEN1:length L = length D) (LEN2:length L = length ZL)
  : bisim'r r (L, E, s) (L', E, fst (egalize D n s)).
Proof.
  revert_except s.
  sind s; intros; destruct s; simpl in *; invt labelsDefined;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - case_eq (exp_eval E e); intros.
    + pone_step. left. eapply IH; eauto.
    + pno_step.
  - case_eq (exp_eval E e); [ intros | intros; pno_step ].
    rewrite mapi_app in DROP. rewrite <- app_assoc in DROP.
    case_eq (val2bool v); intros.
    + pone_step. left. eapply IH; eauto.
    + pone_step. left. eapply IH; eauto.
      eapply app_drop in DROP. rewrite mapi_length in DROP.
      rewrite drop_drop in DROP. rewrite plus_comm.
      rewrite DROP. rewrite plus_comm. eauto.
  - edestruct SIM as [SIM1 SIM2].
    edestruct (get_in_range D H2) as [f' GetD].
    edestruct SL as [b [b' [Z ?]]]; eauto; dcr; eauto. invt approx.
    destruct l as [f]; simpl in *.
    repeat let_case_eq; repeat let_pair_case_eq; simpl in * |- *; subst.
    decide (length Z = length Y).
    + case_eq (omap (exp_eval E) Y); [ intros | intros; pno_step; eauto ].
      exploit SIM2; eauto using zip_get.
      simpl. orewrite (f' + 0 = f'). eauto.
      simpl in *. inv H8. unfold progeq in H22. simpl in *. unfold bisim'r.
      destruct H21; dcr; subst. inv_get. inv SIM. dcr.
      exploit (sawtooth_smaller H16 H0); eauto.
      simpl in *. assert (f_eq: f = f - n0 + n0) by omega. rewrite <- f_eq in *.
      repeat get_functional.
      erewrite get_nth; eauto using zip_get.
      eapply bisim_drop_shift_left; eauto. simpl.
      eapply H22; eauto. exploit omap_length; eauto. split; eauto. split; congruence.
    + pno_step; simpl in *.
      erewrite get_nth in Ldef; eauto. get_functional. eauto.
  - pno_step.
  - case_eq (omap (exp_eval E) Y); [intros | intros; pno_step ].
    pextern_step.
    + left. eapply IH; eauto.
    + left. eapply IH; eauto.
  - rename s into F. eapply bisim'_expansion_closed;
                       [ | eapply star2_silent; [ econstructor | eapply star2_refl ]
                         | eapply star2_refl].
    assert (SL': forall f f' : nat,
               get (mapi (plus' n) F ++ D) f f' ->
               exists (b b' : I.block) (Z : params),
                 get (mapi I.mkBlock F ++ L) f b /\
                 get L' f' b' /\
                 get (fst ⊝ F ++ ZL) f Z /\ approx L' Z (drop (f - I.block_n b) (mapi (plus' n) F ++ D)) f' b b'). {
      intros. eapply get_app_cases in H. destruct H as [H|[H ?]].
      - inv_get. destruct x as [Z s].
        exploit (@get_in_range _ (snd (fst (egalize_funs egalize (mapi (plus' n) F ++ D) (❬F❭ + n) F)))
                               f).
        rewrite egalize_funs_length1; eauto using get_range. destruct X as [[Z' s'] ?].
        do 2 eexists. eexists Z.
        split; eauto using get_app, mapi_get_1.
        split. unfold plus'. eapply get_drop.
        rewrite DROP. repeat rewrite mapi_app. rewrite <- app_assoc.
        eapply get_app. eapply mapi_get_1; eauto.
        split. eapply get_app. eapply (map_get_1 fst H).
        simpl. edestruct (egalize_funs_get _ _ H g); eauto; subst.
        eapply Approx. simpl. orewrite (f - f = 0). simpl.
        eapply pair_eta.
      -
        edestruct SL as [b [b' [Z ?]]]; eauto.
        eexists b, b', Z.
        unfold mapi in H0. rewrite mapi_length in H0.
        repeat rewrite get_app_ge. unfold mapi. rewrite mapi_length.
        rewrite map_length.
        unfold mapi in H2. rewrite mapi_length in H2. dcr.
        split; eauto. split; eauto. split; eauto.
        destruct SIM; dcr.
        pose proof (sawtooth_smaller H12 H4).
        rewrite drop_app_gen. rewrite mapi_length.
        simpl in *.
        orewrite (f - I.block_n b - ❬F❭ = f - ❬F❭ - I.block_n b).
        eauto. rewrite mapi_length. simpl in *. omega.
        rewrite map_length; eauto. unfold mapi.
        rewrite mapi_length. eauto.
    }
    eapply IH; eauto.
    + unfold mapi. rewrite app_length, mapi_length; eauto.
    + rewrite zip_app; eauto with len.
      eapply renILabenv_extension; eauto 10 with len.
      intros ? ? ? ? ? ? ? ? GetF RN GetL' GetA. simpl. inv_get.
      destruct RN as [? [? ?]]; subst. simpl.
      rewrite get_app_lt in H; eauto 20 using get_range with len.
      inv_get; simpl in *. unfold plus' in GetL'.
      eapply drop_get in GetL'.
      rewrite DROP in GetL'. repeat rewrite mapi_app in GetL'.
      repeat rewrite <- app_assoc in GetL'.
      rewrite get_app_lt in GetL';
        [| rewrite mapi_length, egalize_funs_length1; eauto 20 using get_range].
      inv_get. clear EQ.
      destruct x as [Z' s']; simpl.
      destruct (egalize_funs_get _ _ GetF GetL'); eauto; subst.
      split; [|eauto].
      split; [ hnf; eauto|].
      intros ? ? ? ? ? [? [B ?]] SIM'; subst; simpl in *.
      rewrite <- zip_app in SIM'.
      edestruct (@egalize_funs_get2 (mapi (plus' n) F ++ D) (❬F❭ + n) F) as [LX EQ]; eauto;
        simpl in *.
      eapply IH; eauto. simpl in *.
      * unfold mapi. rewrite app_length, mapi_length. exploit H1; eauto.
      * instantiate (1:=LX).
        rewrite <- egalize_funs_length2.
        rewrite <- drop_drop.
        rewrite <- EQ.
        repeat rewrite mapi_app in DROP.
        repeat rewrite <- app_assoc in DROP.
        eapply app_drop with (L:=drop n L') in DROP.
        repeat rewrite mapi_length in DROP.
        rewrite egalize_funs_length1 in DROP.
        rewrite drop_drop in DROP.
        rewrite DROP. f_equal. f_equal. rewrite plus_comm. eauto.
      * eauto with len.
      * eauto with len.
      * eauto with len.
    + rewrite <- egalize_funs_length2 at 1. simpl.
      repeat rewrite mapi_app in DROP.
      repeat rewrite <- app_assoc in DROP.
      eapply app_drop with (L:=drop n L') in DROP.
      repeat rewrite mapi_length in DROP.
      rewrite egalize_funs_length1 in DROP.
      eapply app_drop in DROP. repeat rewrite mapi_length in DROP.
      repeat rewrite drop_drop in DROP. simpl. rewrite Plus.plus_assoc.
      rewrite DROP. simpl.
      rewrite <- egalize_funs_length2. f_equal. f_equal. omega.
    + eauto with len.
    + eauto with len.
Qed.
