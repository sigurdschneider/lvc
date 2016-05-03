Require Import CSet Le.
Require Import Plus Util AllInRel Map.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Sim Fresh Filter Liveness TrueLiveness Filter MoreExp OUnion.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint compile (LV:list (؟ (set var) * params)) (s:stmt) (a:ann (؟(set var))) :=
  match s, a with
    | stmtLet x e s, ann1 lv an =>
      if [x ∈ getOAnn an] then stmtLet x e (compile LV s an)
                         else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [exp2bool e = Some true] then
        (compile LV s ans)
      else if [ exp2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtApp f Y, ann0 lv =>
      let lvZ := nth (counted f) LV (None, nil) in
      stmtApp f (filter_by (fun y => B[y ∈ oget (fst lvZ)]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile LV s an)
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (zip (fun Zs a => (List.filter (fun x => B[x ∈ getOAnn a]) (fst Zs),
                              compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.


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
                   (L', E', stmtApp (LabI bn') Y'))
          -> simIBlock SIM r AR AL L L' a (I.blockI Z s n) (I.blockI Z' s' bn').


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

Lemma sawtooth_get_drop {B} `{BlockType B} L f b
: sawtooth L
  -> get L f b
  -> get (drop (f - block_n b) L) (block_n b) b.
Proof.
    intros. general induction H0; simpl; isabsurd.
    get_cases H2.
    - exploit tooth_index; eauto.
      rewrite H3.
      orewrite (f + 0 = f).
      orewrite (f - f = 0).
      simpl. eapply get_app; eauto.
    - exploit (sawtooth_smaller H0 H2).
      specialize (IHsawtooth _ _ H2).
      orewrite (f - block_n b
                = length L + (f - length L - block_n b)).
      rewrite drop_app; eauto.
Qed.

Lemma fix_compatible_I r A (PR:ProofRelationI A) (a:A) AL F F' E E' Z Z' L L' Yv Y'v s s' n n' AL' bn
(LEN2:length AL' = length F)
  : renILabenv sim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a bn, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                              -> get (mapi I.mkBlock F' ++ L') n' (I.blockI Z' s' bn) -> get AL' n a ->
                              fexteqI sim_progeq PR a
                                      (AL' ++ AL)
                                      (mapi I.mkBlock F ++ L)
                                      (mapi I.mkBlock F' ++ L') Z s Z' s'
                              /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' bn)
                              /\ ParamRelI a Z Z')
    -> get F n (Z,s)
    -> IndexRelI (AL' ++ AL) n n'
    -> get (mapi I.mkBlock F' ++ L') n' (I.blockI Z' s' bn)
    -> get AL' n a
    -> ArgRelI E E' a Yv Y'v
    -> sim'r r
              (mapi I.mkBlock F ++ L, E [Z <-- List.map Some Yv], s)
              (mapi I.mkBlock F' ++ L', E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto. clear H2 H3 H4 H5 H6. clear s s' Z Z' n n' a bn.
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
    exploit H1; eauto; dcr.
    eapply simIBlockI; eauto. simpl.
    intros.
    exploit (ArgLengthMatchI); eauto; dcr.
    exploit (omap_length _ _ _ _ _ H3).
    exploit (omap_length _ _ _ _ _ H5).
    pone_step; eauto using get_app, get_mapi; eauto; simpl.
    congruence. assert (sawtooth (mapi I.mkBlock F' ++ L')).
    econstructor. eapply H0. eapply tooth_I_mkBlocks.
    eapply (sawtooth_get_drop H13 GetL'). simpl. omega.
    right. simpl.
    orewrite (n - n = 0); simpl.
    orewrite (bn - bn = 0); simpl.
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


Lemma renILabenv_extension r A (PR:ProofRelationI A) (AL AL':list A) F F' L L'
      (LEN1:length AL' = length F)
  : renILabenv sim_progeq r PR AL L L'
    -> (forall n n' Z s Z' s' a bn, get F n (Z,s) -> IndexRelI (AL' ++ AL) n n'
                              -> get (mapi I.mkBlock F' ++ L') n' (I.blockI Z' s' bn) -> get AL' n a ->
                              fexteqI sim_progeq PR a
                                      (AL' ++ AL)
                                      (mapi I.mkBlock F ++ L)
                                      (mapi I.mkBlock F ++ L') Z s Z' s'
                              /\ BlockRelI a (I.blockI Z s n) (I.blockI Z' s' bn)
                              /\ ParamRelI a Z Z')
  -> renILabenv sim_progeq r PR (AL' ++ AL) (mapi I.mkBlock F ++ L) (mapi I.mkBlock F' ++ L').
Proof.
  intros. destruct H.
  split. dcr. split. eauto with len.
  split; eauto.
  econstructor; eauto using tooth_I_mkBlocks.
  econstructor; eauto using tooth_I_mkBlocks.
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
   IndexRelI a b c := True
}.
intros. hnf in H, H0; dcr; subst.
erewrite filter_filter_by_length; eauto.
intros. admit.
Admitted.

Lemma sim_I r L L' V V' s LV lv
: agree_on eq (getOAnn lv) V V'
-> true_live_sound Imperative LV s lv
-> renILabenv sim_progeq r SR LV L L'
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
         eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
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
  - destruct (get_dec L (counted l)) as [[[bZ bs]]|].
    + remember (omap (exp_eval V) Y). symmetry in Heqo.
      rewrite (get_nth (None, nil) H4); eauto; simpl.
      destruct o.
      * exploit omap_filter_by; eauto.
        (*hnf in H1; dcr. exploit H6; eauto.
        hnf in H15. dcr; simpl in *; clear_trivial_eqs; subst.
        eapply sim_drop_shift_I. eapply (inRel_sawtooth H1).
        eapply (inRel_sawtooth H1). eauto. eauto.
        simpl. eapply H18; eauto.
        eapply omap_exp_eval_live_agree; eauto.
        inv H0.
        eapply argsLive_liveSound; eauto.
        hnf; split; eauto. simpl. split.
        exploit omap_length; try eapply Heqo; eauto. congruence.
        eapply agree_on_incl; eauto.*)
        admit.
      * pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
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
    + eapply renILabenv_extension.
      * intros. inv_get; simpl. split. hnf; intros; simpl.
        unfold ParamRel, ArgRel. intuition.
        eapply (IH s1); eauto. subst.
        eapply agree_on_update_filter'; eauto.
        exploit H6; eauto.
        unfold ParamRel. intuition.
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
