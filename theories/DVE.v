Require Import CSet Util Fresh Filter MoreExp Take MoreList OUnion AllInRel.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness.

Set Implicit Arguments.
Unset Printing Records.

Hint Extern 5 =>
match goal with
| [ H : ?A = ⎣ true ⎦, H' : ?A = ⎣ false ⎦ |- _ ] => congruence
| [ H : ?A = None , H' : ?A = Some _ |- _ ] => congruence
| [ H : ?A <> ⎣ true ⎦ , H' : ?A <> ⎣ false ⎦ |- ?A = None ] =>
  case_eq (A); [intros [] ?| intros ?]; congruence
end.

Definition filter (Z:params) (lv:set var) := List.filter (fun x => B[x ∈ lv]) Z.

Fixpoint compile (LV:list ((set var) * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      if [x ∈ getAnn an]
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
      let lvZ := nth (counted f) LV (∅, nil) in
      stmtApp f (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile LV s an)
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (zip (fun Zs a => (filter (fst Zs) (getAnn a), compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.

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
                               setTopAnn a' (getAnn a' ∪ of_list (filter (fst Zs) (getAnn a)))) F ans
      in annF (G ∪ lv) ans' (compile_live t ant ∅)
    | _, a => a
  end.


Lemma compile_live_incl G i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> getAnn (compile_live s lv G) ⊆ G ∪ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity.
    + etransitivity; eauto. rewrite H4; eauto.
    + etransitivity; eauto. rewrite <- H5; eauto.
Qed.

Lemma compile_live_incl_empty i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> getAnn (compile_live s lv ∅) ⊆ getAnn lv.
Proof.
  intros.
  eapply compile_live_incl in H.
  rewrite H. cset_tac; intuition.
Qed.

Lemma incl_compile_live G i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> G ⊆ getAnn (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; eauto with cset.
  - repeat cases; simpl; eauto.
Qed.

Lemma dve_live i ZL LV s lv G
  : true_live_sound i ZL LV s lv
    -> live_sound i (filter ⊜ ZL LV) LV (compile (zip pair LV ZL) s lv) (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - cases; eauto. econstructor; eauto.
    + eapply live_exp_sound_incl; eauto.
    + rewrite compile_live_incl; eauto.
      rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - repeat cases; eauto.
    + econstructor; eauto.
      eapply live_exp_sound_incl; eauto.
      rewrite compile_live_incl_empty; eauto with cset.
      rewrite compile_live_incl_empty; eauto with cset.
  - econstructor; eauto using zip_get.
    + simpl. cases; eauto.
      rewrite <- H1. rewrite minus_inter_empty. eapply incl_right.
      unfold filter.
      cset_tac; intuition. eapply filter_incl2; eauto.
      eapply filter_in; eauto. intuition. hnf. cases; eauto.
    + erewrite get_nth; eauto using zip_get. simpl.
      unfold filter.
      erewrite filter_filter_by_length; eauto with len.
    + intros ? ? Get. erewrite get_nth in Get; eauto using zip_get. simpl in *.
      edestruct filter_by_get as [? [? []]]; eauto; dcr. simpl in *.
      eapply live_exp_sound_incl.
      eapply argsLive_live_exp_sound; eauto. simpl in *.
      decide (x ∈ blv); intuition. eauto with cset.
  - econstructor; eauto.
    eapply live_exp_sound_incl; eauto using incl_right.
  - econstructor; eauto.
    + intros; eapply live_exp_sound_incl; eauto using incl_right.
    + rewrite compile_live_incl; eauto. rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - econstructor; simpl in *; eauto with len.
    + eapply live_sound_monotone.
      rewrite map_zip. simpl.
      do 2 rewrite zip_app in IHtrue_live_sound; eauto with len.
      rewrite zip_map_l, zip_map_r in IHtrue_live_sound.
      eapply IHtrue_live_sound.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. unfold filter.
      rewrite of_list_filter. cset_tac.
    + intros; inv_get. simpl.
      eapply live_sound_monotone.
      eapply live_sound_monotone2; eauto.
      rewrite map_zip. simpl.
      do 2 rewrite zip_app in H2; eauto with len.
      rewrite zip_map_l, zip_map_r in H2.
      eapply H2; eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto.
      unfold filter. rewrite of_list_filter. cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      unfold filter. rewrite of_list_filter. clear_all; cset_tac.
    + rewrite compile_live_incl; eauto with cset.
Qed.

Lemma DVE_callChain Lv ZL F als n l'
  : ❬F❭ = ❬als❭
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
         get F n Zs ->
         get als n a ->
         forall n0 : nat,
           trueIsCalled (snd Zs) (LabI n0) ->
           trueIsCalled (compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd Zs) a) (LabI n0))
     -> callChain trueIsCalled F (LabI l') (LabI n)
     -> callChain trueIsCalled
                 ((fun (Zs : params * stmt) (a : ann ⦃var⦄) =>
                     (filter (fst Zs) (getAnn a),
                      compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd Zs) a)) ⊜ F als)
                 (LabI l') (LabI n).
Proof.
  intros LEN IH CC.
  general induction CC.
  + econstructor.
  + inv_get. econstructor 2.
    eapply zip_get; eauto.
    eapply IH; eauto.
    eauto.
Qed.

Lemma DVE_isCalled i ZL LV s lv n
  : true_live_sound i ZL LV s lv
    -> trueIsCalled s (LabI n)
    -> trueIsCalled (compile (zip pair LV ZL) s lv) (LabI n).
Proof.
  intros LS IC.
  general induction LS; invt trueIsCalled; simpl; repeat cases; eauto using trueIsCalled;
    try congruence.
  - destruct l' as [l'].
    econstructor; rewrite <- zip_app; eauto with len.
    rewrite zip_length2; eauto. eapply DVE_callChain; eauto.
Qed.

Lemma DVE_noUnreachableCode i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> noUnreachableCode trueIsCalled s
    -> noUnreachableCode trueIsCalled (compile (zip pair LV ZL) s lv).
Proof.
  intros LS UC.
  general induction LS; inv UC; simpl; repeat cases; eauto using noUnreachableCode.
  - econstructor; intros; inv_get; rewrite <- zip_app; simpl; eauto with len.
    + edestruct H8 as [[l] [IC CC]]. rewrite zip_length2 in H4; eauto.
      eexists (LabI l); split; eauto.
      eapply DVE_isCalled; eauto.
      eapply DVE_callChain; eauto using DVE_isCalled.
Qed.

Require Import BisimSim.

Module I.

  Require Import SimI.

Instance SR : ProofRelationI ((set var) * params) := {
   ParamRelI G Z Z' := Z' = (List.filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRelI V V' G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL /\
     agree_on eq (fst G \ of_list (snd G)) V V';
   Image AL := length AL;
   IndexRelI AL n n' := n = n'
}.
- intros. hnf in H, H0; dcr; subst.
  erewrite filter_filter_by_length; eauto.
- intros AL' AL n n' H H'; subst; reflexivity.
Defined.


Lemma inv_extend s L L' ZL LV als lv f
(LEN: ❬s❭ = ❬als❭)
(H: forall (f : nat) (lv : ⦃var⦄),
       get LV f lv ->
       exists b b' : I.block, get L f b /\ get L' f b')
(Get : get (getAnn ⊝ als ++ LV) f lv)
    :  exists b b' : I.block,
      get (mapi I.mkBlock s ++ L) f b /\
      get (mapi I.mkBlock (zip (fun Zs a =>
                                  (filter (fst Zs) (getAnn a),
                                   compile (pair ⊜ (getAnn ⊝ als ++ LV) (fst ⊝ s ++ ZL)) (snd Zs) a)) s als) ++ L')
          f b'.
Proof.
  get_cases Get; inv_get.
  - edestruct (get_length_eq _ H0 (eq_sym LEN)).
    do 2 eexists; split; eauto using get_app, mapi_get_1, zip_get.
  - edestruct H as [b [b' [? ?]]]; eauto.
    exists b, b'; split.
    + eapply get_app_right; eauto.
      rewrite mapi_length.
      rewrite map_length in *. omega.
    + eapply get_app_right; eauto.
      rewrite mapi_length.
      rewrite zip_length2; eauto with len.
      rewrite map_length in *. omega.
Qed.

Lemma sim_I ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative ZL LV s lv
-> simILabenv Sim r SR (zip pair LV ZL) L L'
-> (forall (f:nat) lv,
      get LV f lv
      -> exists (b b' : I.block),
        get L f b /\
        get L' f b')
-> sim'r r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + cases.
      * pone_step. instantiate (1:=v).
        erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
        left. eapply (IH s); eauto. eapply agree_on_update_same. reflexivity.
        eapply agree_on_incl; eauto.
      * eapply sim'_expansion_closed;
          [ | eapply star2_silent;
              [ econstructor; eauto | eapply star2_refl ]
            | eapply star2_refl].
        eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
        eapply agree_on_incl; eauto.
        rewrite <- H11. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
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
      destruct o. case_eq (val2bool v); intros.
      pone_step.
      left; eapply (IH s1); eauto using agree_on_incl.
      pone_step.
      left; eapply (IH s2); eauto using agree_on_incl.
      pno_step.
  - edestruct H2 as [? [? [GetL GetL']]]; eauto.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    erewrite (get_nth); eauto using zip_get; simpl.
    destruct o.
    + destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      hnf in H1; dcr.
      exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z Heqo); eauto.
      exploit omap_exp_eval_live_agree; eauto.
      intros. eapply argsLive_liveSound; eauto.
      edestruct H4 as [[? ?] SIM]; eauto using zip_get. hnf; eauto.
      hnf in H13; dcr; subst.
      eapply SIM; eauto.
      hnf; simpl. split; eauto.
      exploit (omap_length _ _ _ _ _ Heqo); eauto. split. congruence.
      eauto using agree_on_incl.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
  - pno_step.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    + pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
    + pno_step.
  - pone_step. left. rewrite <- zip_app; eauto with len. eapply IH; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + rewrite zip_app; eauto with len.
      eapply simILabenv_extension_len; simpl; eauto 20 with len.
      * intros. hnf; intros.
        hnf in H4. subst n'. inv_get.
        simpl in *; dcr; subst.
        rewrite <- zip_app; eauto with len.
        eapply IH; eauto.
        eapply agree_on_update_filter'; eauto.
        exploit H7; eauto using zip_get.
        rewrite zip_app; eauto with len.
        intros. rewrite <- zip_app; eauto with len.
        eapply inv_extend; eauto.
      * hnf; intros.
        hnf in H3; subst. inv_get; simpl; eauto.
    + intros; eapply inv_extend; eauto.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative nil nil s lv
-> @sim I.state _ I.state _ Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_I nil nil); eauto.
  hnf; simpl; split; eauto using @sawtooth; isabsurd.
  isabsurd.
Qed.

End I.

Module F.

  Require Import SimF.

Instance SR : ProofRelation ((set var) * params) := {
   ParamRel G Z Z' := Z' = (List.filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRel G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL;
   BlockRel := fun lvZ b b' => True;
   Image AL := length AL;
   IndexRel AL n n' := n = n'
}.
- intros. hnf in H, H0; dcr; subst.
  erewrite filter_filter_by_length; eauto.
- intros AL' AL n n' H H'; subst; reflexivity.
Defined.


Lemma inv_extend s E E' L L' ZL LV als lv f
(LEN: ❬s❭ = ❬als❭)
(H: forall (f : nat) (lv : ⦃var⦄),
       get LV f lv ->
       exists b b' : F.block, get L f b /\ get L' f b')
(Get : get (getAnn ⊝ als ++ LV) f lv)
    :  exists b b' : F.block,
      get (mapi (F.mkBlock E) s ++ L) f b /\
      get (mapi (F.mkBlock E') (zip (fun Zs a =>
                                  (filter (fst Zs) (getAnn a),
                                   compile (pair ⊜ (getAnn ⊝ als ++ LV) (fst ⊝ s ++ ZL)) (snd Zs) a)) s als) ++ L')
          f b'.
Proof.
  get_cases Get; inv_get.
  - edestruct (get_length_eq _ H0 (eq_sym LEN)).
    do 2 eexists; split; eauto using get_app, mapi_get_1, zip_get.
  - edestruct H as [b [b' [? ?]]]; eauto.
    exists b, b'; split.
    + eapply get_app_right; eauto.
      rewrite mapi_length.
      rewrite map_length in *. omega.
    + eapply get_app_right; eauto.
      rewrite mapi_length.
      rewrite zip_length2; eauto with len.
      rewrite map_length in *. omega.
Qed.


Lemma sim_F ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional ZL LV s lv
-> simLabenv Sim r SR (zip pair LV ZL) L L'
-> (forall (f:nat) lv,
      get LV f lv
      -> exists (b b' : F.block),
        get L f b /\
        get L' f b')
-> sim'r r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + cases.
      * pone_step. instantiate (1:=v).
        erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
        left. eapply (IH s); eauto. eapply agree_on_update_same. reflexivity.
        eapply agree_on_incl; eauto.
      * eapply sim'_expansion_closed;
          [ | eapply star2_silent;
              [ econstructor; eauto | eapply star2_refl ]
            | eapply star2_refl].
        eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
        eapply agree_on_incl; eauto.
        rewrite <- H11. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
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
      destruct o. case_eq (val2bool v); intros.
      pone_step.
      left; eapply (IH s1); eauto using agree_on_incl.
      pone_step.
      left; eapply (IH s2); eauto using agree_on_incl.
      pno_step.
  - edestruct H2 as [? [? [GetL GetL']]]; eauto.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    erewrite (get_nth); eauto using zip_get; simpl.
    destruct o.
    + destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      hnf in H1; dcr.
      exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z Heqo); eauto.
      exploit omap_exp_eval_live_agree; eauto.
      intros. eapply argsLive_liveSound; eauto.
      edestruct H4 as [[? ?] SIM]; eauto using zip_get. hnf; eauto.
      hnf in H13; dcr; subst.
      eapply SIM; [ | eapply Heqo | eapply H9 ].
      hnf; simpl. split; eauto with len.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
  - pno_step.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    + pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
    + pno_step.
  - pone_step. left. rewrite <- zip_app; eauto with len. eapply IH; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + rewrite zip_app; eauto with len.
      eapply simLabenv_extension_len; simpl; eauto 20 with len.
      * intros. hnf; intros.
        hnf in H4. subst n'. inv_get. simpl.
        hnf in H13; dcr; subst. simpl.
        rewrite <- zip_app; eauto with len.
        eapply IH; eauto. simpl in *.
        eapply agree_on_update_filter'; eauto.
        exploit H10; eauto.
        eauto using agree_on_incl.
        exploit H7; eauto.
        rewrite zip_app; eauto with len.
        intros. rewrite <- zip_app; eauto with len.
        eapply inv_extend; eauto.
      * hnf; intros.
        hnf in H3. dcr. inv_get.
        simpl; unfold ParamRel; simpl; eauto.
    + intros; eapply inv_extend; eauto.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional nil nil s lv
-> @sim F.state _ F.state _ Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_F nil nil); eauto.
  hnf; simpl; split; eauto using @sawtooth; isabsurd.
  isabsurd.
Qed.

End F.