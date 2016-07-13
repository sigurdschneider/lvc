Require Import paco2 AllInRel Util Map Env Exp IL SimI DecSolve MoreList Sawtooth InRel Sublist.

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
    rewrite mapi_impl_length; eauto.
  - inv H; simpl in *.
    repeat let_pair_case_eq; subst; simpl.
    edestruct (IHf D) with (n':=n'); eauto.
    eexists. rewrite mapi_app. rewrite <- app_assoc.
    eapply H0.
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
    IndexRelDrop : forall AL' AL n n', IndexRelI (AL' ++ AL) n n' ->
                                  n >= length AL'
                                  -> IndexRelI AL (n - length AL') (n')
(*    IndexRelApp : forall AL AL' n n', IndexRelI AL n n' -> IndexRelI (AL' ++ AL) (❬AL'❭ + n) n' *)
}.

Definition irel := rel3 simtype (fun _ : simtype => I.state)
                       (fun (_ : simtype) (_ : I.state) => I.state).


Definition simILabenv t (r:irel)
           {A} (PR:ProofRelationI A) (AL:list A) L L' :=
  (length AL = length L /\ tooth 0 L' /\ sawtooth L) /\
  forall f f' a Z s n Z' s' n',
    IndexRelI AL (counted f) (counted f')
    -> get AL (counted f) a
    -> get L (counted f) (I.blockI Z s n)
    -> get L' (counted f') (I.blockI Z' s' n')
    -> (ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n'))
      /\ (forall E E' Yv Y'v Y Y',
            ArgRelI E E' a Yv Y'v
            -> omap (exp_eval E) Y = Some Yv
            -> omap (exp_eval E') Y' = Some Y'v
            -> sim'r r t (L, E, stmtApp f Y)
                    (L', E', stmtApp f' Y')).

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

Definition indexwise_r t (r:irel) A (PR:ProofRelationI A) AL' F AL L L' :=
  forall n n' Z s Z' s' a i,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get L' n' (I.blockI Z' s' i)
    -> get AL' n a
    -> forall E E' VL VL',
        ArgRelI E E' a VL VL'
        -> r t (mapi I.mkBlock F ++ L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').

Lemma indexwise_r_mon t (r r':irel) A (PR:ProofRelationI A) AL' F AL L L'
  : indexwise_r t r PR AL' F AL L L'
    -> (forall t x y, r t x y -> r' t x y)
    -> indexwise_r t r' PR AL' F AL L L'.
Proof.
  intros Idx LE; hnf; intros; eauto.
Qed.

Definition indexwise_proofrel A (PR:ProofRelationI A) (F:〔params * stmt〕) AL' L' AL :=
  forall n n' Z s Z' s' a i,
    IndexRelI (AL' ++ AL) n n'
    -> get F n (Z,s)
    -> get L' n' (I.blockI Z' s' i)
    -> get AL' n a
    -> ParamRelI a Z Z' /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' i).

Lemma simILabenv_extension' t (r:irel) A (PR:ProofRelationI A) (AL AL':list A) F L L'
      (LEN1:length AL' = length F)
  : indexwise_r t (sim'r r \3/ r) PR AL' F AL L L'
    -> indexwise_proofrel PR F AL' L' AL
    -> simILabenv t r PR AL L L'
    -> simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) L'.
Proof.
  intros ISIM IP SIML.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  intros f f' ? ? ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL as [GetAL'|GetAL].
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. simpl in *. clear EQ.
    split; eauto.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr. eapply IP; eauto.
    pone_step; eauto using get_app, get_mapi; eauto; simpl; eauto with len.
    destruct SIML; dcr.
    exploit (tooth_index H9 GetL'); eauto; simpl in *; subst.
    orewrite (labN f' + 0 = labN f'); simpl.
    orewrite (labN f - labN f = 0); simpl.
    orewrite (labN f' - labN f' = 0); simpl.
    eapply ISIM; eauto.
  - destruct SIML; dcr.
    eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    rewrite mapi_length in *.
    eapply IndexRelDrop in RN; eauto.
    edestruct (H1 (LabI (counted f - ❬AL'❭)) (LabI (counted f')))
      as [[? ?] SIM]; simpl; eauto.
    rewrite H; eauto.
    split; eauto.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    eapply (@sim_Y_left I.state _ I.state _).
    eapply (@sim_Y_right I.state _ I.state _).
    rewrite H in SIM.
    eapply SIM; eauto.
    econstructor; simpl; eauto with len. simpl. eauto with len.
    Focus 2.
    econstructor; simpl; eauto. simpl. eauto with len.
    simpl.
    eapply (I.stepGoto _ _ _ GetL'); simpl; eauto with len.
    eapply (stepGoto_mapi _ _ _ _ GetFL); simpl; eauto with len.
    simpl in *; omega.
Qed.

Lemma fix_compatible_I t A (PR:ProofRelationI A) AL F L L' AL'
(LEN2:length AL' = length F)
  : (forall r, simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) L'
            -> indexwise_r t (sim'r r) PR AL' F AL L L')
    -> indexwise_proofrel PR F AL' L' AL
    -> forall r, simILabenv t r PR AL L L'
           -> indexwise_r t (sim'r r) PR AL' F AL L L'.
Proof.
  intros ISIM IP r SIML; pcofix CIH.
  eapply ISIM; eauto.
  hnf. split.
  destruct SIML; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  eapply simILabenv_extension'; eauto using simILabenv_mon, indexwise_r_mon.
Qed.

Lemma simILabenv_extension t A (PR:ProofRelationI A) (AL AL':list A) F L L'
      (LEN1:length AL' = length F)
  : (forall r, simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) L'
          -> indexwise_r t (sim'r r) PR AL' F AL L L')
    -> indexwise_proofrel PR F AL' L' AL
    -> forall r, simILabenv t r PR AL L L'
           -> simILabenv t r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) L'.
Proof.
  intros. eapply simILabenv_extension'; eauto.
  eapply indexwise_r_mon.
  eapply fix_compatible_I; eauto. eauto.
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
eapply get_app_ge; eauto.
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
      (SIM:simILabenv Bisim r PR (zip pair ZL D) L L')
      (DROP:drop n L' = mapi_impl I.mkBlock n (snd (egalize D n s)) ++ L'')
      (LEN1:length L = length D) (LEN2:length L = length ZL)
  : sim'r r Bisim (L, E, s) (L', E, fst (egalize D n s)).
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
      eapply app_drop in DROP. rewrite mapi_impl_length in DROP.
      rewrite drop_drop in DROP. rewrite plus_comm.
      rewrite DROP. rewrite plus_comm. eauto.
  - edestruct SIM as [SIM1 SIM2].
    edestruct (get_in_range D H2) as [f' GetD].
    edestruct SL as [b [b' [Z ?]]]; eauto; dcr; eauto. invt approx.
    repeat let_case_eq; repeat let_pair_case_eq; simpl in * |- *; subst.
    decide (length Z = length Y).
    + case_eq (omap (exp_eval E) Y); [ intros | intros; pno_step; eauto ].
      exploit (SIM2 l (LabI f')); eauto using zip_get.
      simpl in *. dcr; subst.
      erewrite get_nth; [| eauto].
      eapply H10; try eassumption. eauto with len.
    + pno_step; simpl in *.
      erewrite get_nth in Ldef; eauto. get_functional. eauto.
  - pno_step.
  - case_eq (omap (exp_eval E) Y); [intros | intros; pno_step ].
    pextern_step.
    + left. eapply IH; eauto.
    + left. eapply IH; eauto.
  - rename s into t. eapply sim'_expansion_closed;
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
        rewrite mapi_length in H0.
        repeat rewrite get_app_ge. rewrite mapi_length.
        rewrite map_length.
        rewrite mapi_length in H2. dcr.
        split; eauto. split; eauto. split; eauto.
        destruct SIM; dcr.
        pose proof (sawtooth_smaller H12 H4).
        rewrite drop_app_gen. rewrite mapi_length.
        simpl in *.
        orewrite (f - I.block_n b - ❬F❭ = f - ❬F❭ - I.block_n b).
        eauto. rewrite mapi_length. simpl in *. omega.
        rewrite map_length; eauto.
        rewrite mapi_length. eauto.
    }
    eapply IH; eauto with len.
    + rewrite app_length, mapi_length; eauto.
    + rewrite zip_app; eauto with len.
      eapply simILabenv_extension; eauto 10 with len.
      intros.
      intros ? ? ? ? ? ? ? ? RN GetF GetL' GetA. simpl.
      inv_get. simpl in *; dcr; subst.
      destruct RN; dcr. subst.
      rewrite get_app_lt in H2; eauto 20 using get_range with len.
      inv_get; simpl in *. unfold plus' in GetL'.
      eapply drop_get in GetL'.
      rewrite DROP in GetL'. repeat rewrite mapi_app in GetL'.
      repeat rewrite <- app_assoc in GetL'.
      rewrite get_app_lt in GetL';
        [| rewrite mapi_impl_length, egalize_funs_length1; eauto 20 using get_range].
      inv_get. clear EQ.
      destruct x as [Z' s']; simpl.
      destruct (egalize_funs_get _ _ GetF GetL'); eauto; subst.
      edestruct (@egalize_funs_get2 (mapi (plus' n) F ++ D) (❬F❭ + n) F) as [LX EQ]; eauto;
        simpl in *.
      eapply IH; eauto with len. simpl in *.
      * rewrite app_length, mapi_length. exploit H1; eauto.
      * instantiate (1:=LX).
        rewrite <- egalize_funs_length2.
        rewrite <- drop_drop.
        rewrite <- EQ.
        repeat rewrite mapi_app in DROP.
        repeat rewrite <- app_assoc in DROP.
        eapply app_drop with (L:=drop n L') in DROP.
        repeat rewrite mapi_impl_length in DROP.
        rewrite egalize_funs_length1 in DROP.
        rewrite drop_drop in DROP.
        rewrite DROP. f_equal. f_equal. rewrite plus_comm. eauto.
      * hnf; intros. simpl.
        inv_get. simpl. destruct H; dcr.
        rewrite get_app_lt in H4; eauto 20 using get_range with len.
        inv_get. simpl in *. unfold plus' in H2.
        eapply drop_get in H2.
        rewrite DROP in H2. repeat rewrite mapi_app in H2.
        repeat rewrite <- app_assoc in H2.
        rewrite get_app_lt in H2;
          [| rewrite mapi_impl_length, egalize_funs_length1; eauto 20 using get_range].
        inv_get. clear EQ.
        destruct x as [Z' s']; simpl.
        destruct (egalize_funs_get _ _ H0 H2); eauto; subst. eauto.
    + rewrite <- egalize_funs_length2 at 1. simpl.
      repeat rewrite mapi_app in DROP.
      repeat rewrite <- app_assoc in DROP.
      eapply app_drop with (L:=drop n L') in DROP.
      repeat rewrite mapi_impl_length in DROP.
      rewrite egalize_funs_length1 in DROP.
      eapply app_drop in DROP. repeat rewrite mapi_impl_length in DROP.
      repeat rewrite drop_drop in DROP. simpl. rewrite Plus.plus_assoc.
      rewrite DROP. simpl.
      rewrite <- egalize_funs_length2. f_equal. f_equal. omega.
Qed.
