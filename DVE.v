Require Import CSet Le.
Require Import Plus Util AllInRel Map.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Sim Fresh Filter Liveness TrueLiveness Filter MoreExp OUnion Take MoreList.

Set Implicit Arguments.
Unset Printing Records.

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

Lemma compileF_length LV F ans
  : length F = length ans
    -> length (compileF compile LV F ans) = countSome (getAnn ⊝ ans).
Proof.
  intros. length_equify.
  general induction H; simpl; eauto.
  cases; subst. cases; simpl; eauto.
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

Inductive simIBlock (SIM:ProgramEquivalence I.state I.state)
          (r:I.state -> I.state -> Prop)
          {A} (AR:ProofRelationI A)
  : list A -> I.labenv -> I.labenv -> A -> I.block -> I.block -> Prop :=
| simIBlockI a L L' Z Z' s s' n n' AL
  : ParamRelI a Z Z'
    -> BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n')
    -> IndexRelI AL n n'
    -> (forall E E' Yv Y'v Y Y',
          omap (exp_eval E) Y = Some Yv
          -> omap (exp_eval E') Y' = Some Y'v
          -> ArgRelI E E' a Yv Y'v
          -> progeq r (L, E, stmtApp (LabI n) Y)
                   (L', E', stmtApp (LabI n') Y'))
          -> simIBlock SIM r AR AL L L' a (I.blockI Z s n) (I.blockI Z' s' n').


Definition renILabenv (SIM:ProgramEquivalence I.state I.state) r
           {A} AR (AL:list A) L L' :=
  (length AL = length L /\ sawtooth L' /\ sawtooth L) /\
  forall n n' a b b', IndexRelI AL n n' -> get AL n a -> get L n b -> get L' n' b'
               -> simIBlock SIM r AR
                           (drop (n  - I.block_n b) AL)
                           (drop (n  - I.block_n b) L)
                           (drop (n' - I.block_n b') L')
                           a b b' .

Definition fexteqI (SIM:ProgramEquivalence I.state I.state)
           {A} (PR:ProofRelationI A) (a:A) (AL:list A) L L' Z s Z' s' :=
  ParamRelI a Z Z' /\
  forall E E' VL VL' (r:rel2 I.state (fun _ : I.state => I.state)),
    ArgRelI E E' a VL VL'
    -> renILabenv SIM r PR AL L L'
    -> progeq r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').

Lemma fix_compatible_I r A (PR:ProofRelationI A) (a:A) AL F F' E E' Z Z' L L' Yv Y'v s s' n n' AL'
(LEN2:length AL' = length F)
  : renILabenv sim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                              -> get F' n' (Z',s') -> get AL' n a ->
                              fexteqI sim_progeq PR a
                                      (AL' ++ AL)
                                      (mapi I.mkBlock F ++ L)
                                      (mapi I.mkBlock F' ++ L') Z s Z' s'
                              /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n')
                              /\ ParamRelI a Z Z')
    -> get F n (Z,s)
    -> get F' n' (Z',s')
    -> IndexRelI (AL' ++ AL) n n'
    -> get AL' n a
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> ArgRelI E E' a Yv Y'v
    -> sim'r r
              (mapi I.mkBlock F ++ L, E [Z <-- List.map Some Yv], s)
              (mapi I.mkBlock F' ++ L', E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto. clear H2 H3 H4 H5 H9. clear s s' Z Z' n n' a.
  hnf. split.
  destruct H0; dcr; split; eauto with len. split; eauto.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  econstructor; eauto. eapply tooth_I_mkBlocks.
  intros ? ? ? ? ? RN GetAL GetFL GetL'.
  assert (❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL.
  - eapply get_app_lt_1 in GetFL; [| rewrite <- H; eauto using get_range].
    inv_get. destruct x as [Z s]. destruct b' as [Z' s' bn]. simpl.
    orewrite (n - n = 0). simpl.
    exploit H6; eauto using get_range.
    eapply get_app_lt_1 in GetL'; [| unfold mapi; rewrite mapi_length; eauto ].
    inv_get. destruct x as [Z' s']; simpl in *; clear EQ.
    exploit H1; eauto; dcr.
    eapply simIBlockI; eauto. simpl.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit (omap_length _ _ _ _ _ H4).
    exploit (omap_length _ _ _ _ _ H9).
    pone_step; eauto using get_app, get_mapi; eauto; simpl.
    congruence.
    orewrite (bn - bn = 0); simpl.
    eapply get_app. eapply mapi_get_1; eauto.
    simpl. congruence.
    right.
    orewrite (n - n = 0); simpl.
    orewrite (bn - bn = 0); simpl.
    eapply CIH; eauto.
  - destruct H0.
    dcr. eapply get_app_right_ge in GetFL; [ | rewrite <- H; eauto].
    exploit H7; eauto. unfold mapi in H. rewrite mapi_length in H. omega.
    eapply get_app_right_ge in GetL'; [ | unfold mapi; rewrite mapi_length; eauto].
    assert (n - I.block_n b >= ❬mapi I.mkBlock F❭). {
      exploit (sawtooth_smaller H11 GetFL). rewrite <- H in *. simpl in *. omega.
    }
    assert (n' - I.block_n b' >= ❬mapi I.mkBlock F'❭). {
      exploit (sawtooth_smaller H10 GetL').
      unfold mapi in *. rewrite mapi_length in *.
      simpl in *. omega.
    }
    rewrite (drop_app_gen _ (mapi I.mkBlock F)); eauto.
    rewrite (drop_app_gen _ (mapi I.mkBlock F')); eauto.
    rewrite (drop_app_gen _ AL'); eauto.
    unfold mapi in *; rewrite mapi_length in *. rewrite mapi_length.
    rewrite H.
    orewrite (n - I.block_n b - ❬F❭ = n - ❬F❭ - I.block_n b).
    orewrite (n' - I.block_n b' - ❬F'❭ = n' - ❬F'❭ - I.block_n b').
    exploit H3; eauto. eapply IndexRelDrop in RN. rewrite H8 in RN. eauto.
    eauto.
    rewrite H. eauto. rewrite <- H.
    inv H13. econstructor; eauto. intros.
    eapply progeq_mon; eauto. rewrite H. eauto.
Qed.


Lemma renILabenv_extension r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : renILabenv sim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                           -> get F' n' (Z',s') -> get AL' n a ->
                           fexteqI sim_progeq PR a
                                   (AL' ++ AL)
                                   (mapi I.mkBlock F ++ L)
                                   (mapi I.mkBlock F' ++ L') Z s Z' s'
                           /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n')
                           /\ ParamRelI a Z Z')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n < length F -> n' < length F')
    -> (forall n n', IndexRelI (AL' ++ AL) n n' -> n >= length F -> n' >= length F')
    -> Image AL' = length F'
    -> renILabenv sim_progeq r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros SimL ASS I1 I2. destruct SimL.
  split. dcr. split. eauto with len.
  split; eauto.
  econstructor; eauto using tooth_I_mkBlocks.
  econstructor; eauto using tooth_I_mkBlocks.
  intros ? ? ? ? ? RN GetAL GetL GetL'.
  assert (ALLEN:❬AL'❭ = ❬mapi I.mkBlock F❭) by eauto with len.
  eapply get_app_cases in GetAL. destruct GetAL.
  - eapply get_app_lt_1 in GetL; [| rewrite <- ALLEN; eauto using get_range].
    inv_get. destruct x as [Z s]. destruct b' as [Z' s' bn]. simpl.
    orewrite (n - n = 0). simpl.
    exploit I1; eauto using get_range.
    eapply get_app_lt_1 in GetL'; [| unfold mapi; rewrite mapi_length; eauto ].
    inv_get. destruct x as [Z' s']; simpl in *; clear EQ.
    orewrite (bn - bn = 0). simpl.
    exploit ASS; eauto; dcr.
    eapply simIBlockI; eauto. simpl.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit (omap_length _ _ _ _ _ H).
    exploit (omap_length _ _ _ _ _ H6).
    pone_step; eauto using get_app, get_mapi; eauto; simpl.
    congruence. congruence.
    left.
    orewrite (n - n = 0); simpl.
    orewrite (bn - bn = 0); simpl.
    eapply fix_compatible_I; eauto.
    split; eauto.
  - dcr.
    eapply get_app_right_ge in GetL; [ | rewrite <- ALLEN; eauto].
    assert (n - I.block_n b >= ❬mapi I.mkBlock F❭). {
      exploit (sawtooth_smaller H7 GetL). rewrite <- ALLEN in *. simpl in *. omega.
    }
    exploit I2; eauto. unfold mapi in *; rewrite mapi_length in *. rewrite <- ALLEN. eauto.
    eapply get_app_right_ge in GetL'; [ | unfold mapi; rewrite mapi_length; eauto ].
    assert (n' - I.block_n b' >= ❬mapi I.mkBlock F'❭). {
      exploit (sawtooth_smaller H6 GetL'). rewrite ALLEN in *.
      unfold mapi in *. rewrite mapi_length in *. simpl in *. omega.
    }
    rewrite (drop_app_gen _ (mapi I.mkBlock F)); eauto.
    rewrite (drop_app_gen _ (mapi I.mkBlock F')); eauto.
    rewrite (drop_app_gen _ AL'); [ | rewrite ALLEN; eauto ].
    rewrite LEN1. unfold mapi in *. rewrite mapi_length in *. rewrite mapi_length.
    orewrite (n - I.block_n b - ❬F❭ = n - ❬F❭ - I.block_n b).
    orewrite (n' - I.block_n b' - ❬F'❭ = n' - ❬F'❭ - I.block_n b').
    eapply H0; eauto. eapply IndexRelDrop in RN. rewrite H1 in RN.
    rewrite <- ALLEN. eauto. eauto.
    rewrite <- ALLEN. eauto.
Qed.

Module I.

  Require Import SimI.

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

Lemma map_take X Y (f:X -> Y) (L:list X) n
  : f ⊝ take n L = take n (f ⊝ L).
Proof.
  general induction n; simpl; eauto.
  destruct L; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma take_app_lt n X (L L':list X)
  : n < length L
    -> take n (L ++ L') = take n L.
Proof.
  intros. general induction n; simpl; eauto.
  destruct L; isabsurd; simpl.
  rewrite IHn; eauto. simpl in *; omega.
Qed.

Lemma take_app_ge n X (L L':list X)
  : n >= length L
    -> take n (L ++ L') = L ++ take (n - length L) L'.
Proof.
  intros. general induction n; simpl; eauto.
  - destruct L; simpl in *; eauto. exfalso; omega.
  - destruct L; simpl in *; eauto.
    rewrite IHn; eauto. omega.
Qed.

Lemma zip_map_fst X Y (L:list X) (L':list Y)
  : length L = length L'
    -> zip (fun x _ => x) L L' = L.
Proof.
  intros. length_equify.
  general induction H; eauto; simpl in *.
  f_equal; eauto.
Qed.

Lemma take_eq_ge n X (L:list X)
  : n >= ❬L❭ -> take n L = L.
Proof.
  intros. general induction n; destruct L; simpl in *; eauto.
  - exfalso; omega.
  - rewrite IHn; eauto. omega.
Qed.


Lemma sim_I r L L' V V' s LV lv
: agree_on eq (oget (getAnn lv)) V V'
-> true_live_sound Imperative LV s lv
-> renILabenv sim_progeq r SR LV L L'
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
           [ | eapply S_star2 with (y:=EvtTau);
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
    + hnf in H1; dcr. exploit H4; eauto. split. reflexivity. eauto.
      destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      invc H1. simpl in *. dcr; subst; simpl in *.
      hnf in H20; dcr. subst. simpl in *.
      exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z Heqo); eauto.
      eapply sim_Y_left. eapply sim_Y_right.
      eapply H24. eapply Heqo. eapply H1.
      hnf. simpl. split; eauto. split; eauto.
      exploit (omap_length _ _ _ _ _ Heqo); eauto. congruence.
      Focus 4. econstructor; eauto.
      Focus 2. econstructor; eauto. simpl.
      eapply filter_filter_by_length; eauto.
      eapply omap_exp_eval_live_agree; eauto.
      eapply argsLive_liveSound; eauto. simpl.


      eapply H15. eauto. eauto. hnf. simpl. admit.
      pone_step. simpl.
      eapply filter_filter_by_length; eauto.
      eapply omap_exp_eval_live_agree; eauto.
      eapply argsLive_liveSound; eauto.
      simpl. left.
      hnf in H15. dcr; simpl in *; clear_trivial_eqs; subst.
      eapply sim_drop_shift_I. eapply (inRel_sawtooth H1).
      eapply (inRel_sawtooth H1). eauto. eauto.
      simpl. eapply H18; eauto.
      eapply omap_exp_eval_live_agree; eauto.
      inv H0.
      eapply argsLive_liveSound; eauto.
      hnf; split; eauto. simpl. split.
      exploit omap_length; try eapply Heqo; eauto. congruence.
      eapply agree_on_incl; eauto.
      admit.
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
    + eapply renILabenv_extension. eauto with len.  eauto.
      * intros.
        hnf in H3. dcr.
        rewrite get_app_lt in H13; eauto using get_range.
        inv_get.
        exploit (compileF_get ((pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ LV) )); eauto.
        rewrite map_take in H5. rewrite map_app in H5.
        rewrite map_zip in H5. simpl in H5.
        rewrite zip_map_fst in H5; eauto with len.
        rewrite take_app_lt in H5.
        rewrite map_take in H9. get_functional. clear EQ0. simpl.
        unfold ParamRel, ArgRel. simpl. split; eauto.
        hnf. simpl. unfold ParamRel, ArgRel. simpl.
        split; [eauto|].
        intros. dcr. subst. simpl. eapply IH; eauto.
        rewrite EQ. simpl.
        eapply agree_on_update_filter'; eauto.
        exploit H6; eauto using zip_get.
        rewrite <- EQ. eapply zip_get; eauto using map_get.
        exploit H8; eauto. rewrite map_length. eauto using get_range.
      * intros. rewrite compileF_length; eauto.
        hnf in H2; dcr; subst.
        rewrite map_take. rewrite map_app.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
        rewrite take_app_lt; [|rewrite map_length; eauto; omega ].
        erewrite (take_eta n (getAnn ⊝ als)) at 2.
        rewrite countSome_app.
        rewrite get_app_lt in H9;
          [| rewrite zip_length2; eauto with len; rewrite map_length; omega].
        inv_get. erewrite <- get_eq_drop; eauto using map_get_1.
        simpl. rewrite EQ1. omega.
      * intros. rewrite compileF_length; eauto.
        hnf in H2; dcr; subst.
        rewrite map_take. rewrite map_app.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
        rewrite take_app_ge. rewrite countSome_app. omega.
        rewrite map_length. omega.
      * simpl. rewrite compileF_length; eauto.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
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
