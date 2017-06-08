Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel.
Require Import IL Annotation LabelsDefined Sawtooth Liveness.Liveness TrueLiveness.
Require SimF SimI.

Set Implicit Arguments.
Unset Printing Records.

(** * Dead Variable Elimination *)


Fixpoint flt (lv:set var) X (Z:params) (L:list X) :=
  match Z, L with
  | x::Z, a::L => if [ x ∈ lv ] then a::flt (lv \ singleton x) Z L
                 else flt (lv \ singleton x) Z L
  | _, _  => nil
  end.

Lemma flt_length X Y Z lv (L:list X) (L':list Y)
  (LEN:length L = length L')
  : ❬flt lv Z L❭ = ❬flt lv Z L'❭.
Proof.
  general induction LEN; destruct Z; simpl; eauto.
  cases; simpl; rewrite IHLEN; eauto.
Qed.

Local Hint Resolve flt_length.
Hint Resolve flt_length : len.

Lemma get_flt X lv Z (Y:list X) n y
      (Get:get (flt lv Z Y) n y)
  : exists z k, get Z k z /\ get Y k y /\ z ∈ lv.
Proof.
  general induction Z; destruct Y; simpl in *; isabsurd.
  - cases in Get; eauto 20 using get.
    + inv Get; eauto using get.
      edestruct IHZ; dcr; eauto.
      exists x0, (S x1). repeat split; eauto using get. cset_tac.
    + edestruct IHZ; dcr; eauto.
      exists x0, (S x1). repeat split; eauto using get. cset_tac.
Qed.


Lemma omap_flt A B Z (Y:list A) lv f (l:list B)
: omap f Y = Some l
  -> length Y = length Z
  -> omap f (flt lv Z Y) = Some (flt lv Z l).
Proof.
  intros.
  general induction H0; simpl in * |- *; eauto.
  monad_inv H. cases; simpl; eauto.
  rewrite EQ. erewrite IHlength_eq; simpl; eauto.
Qed.

Lemma flt_InA (A : Type) (eqA : A -> A -> Prop) lv Z Y x
  : InA eqA x (flt lv Z Y) -> InA eqA x Y.
Proof.
  intros.
  general induction Z; destruct Y; isabsurd; simpl in *.
  cases in H.
  - inv H; eauto using InA.
  - edestruct IHZ; eauto.
Qed.

Lemma nodup_flt X lv (R:X->X->Prop) Z (Y:list X)
  : NoDupA R Y
    -> NoDupA R (flt lv Z Y).
Proof.
  general induction Z; destruct Y; simpl in *; dcr; eauto.
  - cases; eauto using NoDupA.
    constructor; eauto.
    intro XX. eapply flt_InA in XX.
    inv H. eauto.
Qed.

Lemma of_list_flt lv Z
  : of_list (flt lv Z Z) [=] lv ∩ of_list Z.
Proof.
  general induction Z; simpl.
  - cset_tac.
  - cases; simpl.
    + rewrite IHZ; eauto. cset_tac.
    + rewrite IHZ; eauto. cset_tac.
Qed.

Lemma nodup_flt' lv Z
  : NoDupA _eq (flt lv Z Z).
Proof.
  general induction Z; dcr; eauto.
  - eauto using NoDupA.
  - simpl flt. cases; eauto using NoDupA.
    constructor; eauto.
    rewrite <- of_list_1.
    rewrite of_list_flt.
    cset_tac.
Qed.

Lemma argsLive_liveSound lv blv Y Z
  : argsLive lv blv Y Z
    -> forall (n : nat) (y : op) blv',
      get (flt blv' Z Y) n y ->
      blv' ⊆ blv ->
      live_op_sound y lv.
Proof.
  intros. general induction H; simpl in * |- *.
  - isabsurd.
  - cases in H1; eauto with cset.
    + inv H1; eauto with cset.
Qed.

Lemma agree_on_update_flt Y `{Equivalence (option Y)} (lv:set nat) (V V':nat -> option Y) (Z:list nat) VL

: length Z = length VL
  -> agree_on R (lv \ of_list Z) V V'
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V' [(flt lv Z Z) <-- (List.map Some (flt lv Z VL))]).
Proof.
  intros.
  eapply agree_on_trans. eapply H.
  eapply update_with_list_agree; eauto with len.
  general induction Z; destruct VL; simpl; eauto.
  - exfalso; isabsurd.
  - cases; simpl in *.
    + eapply agree_on_update_same. reflexivity.
      eapply IHZ; eauto.
      eapply agree_on_incl; eauto. clear; cset_tac.
    + eapply agree_on_update_dead; eauto.
      assert (lv [=] lv \ singleton a) by cset_tac.
      rewrite H2 at 1. eapply IHZ; eauto.
      eapply agree_on_incl; eauto. clear; cset_tac.
Qed.

Fixpoint compile (LV:list ((set var) * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      if [x ∈ getAnn an \/ isCall e]
      then stmtLet x e (compile LV s an)
      else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [op2bool e = Some true] then
        (compile LV s ans)
      else if [ op2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtApp f Y, ann0 _ =>
      let lvZ := nth (counted f) LV (∅, nil) in
      stmtApp f (flt (fst lvZ) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (zip (fun Zs a => (flt (getAnn a) (fst Zs) (fst Zs), compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.


(** ** Correctness with respect to the imperative semantics IL/I *)

Module I.

  Import SimI.


Instance SR : PointwiseProofRelationI ((set var) * params) := {
   ParamRelIP G Z Z' := Z' = flt (fst G) (snd G) Z /\ snd G = Z;
   ArgRelIP V V' G VL VL' :=
     VL' = (flt (fst G) (snd G) VL) /\
     length (snd G) = length VL /\
     agree_on eq (fst G \ of_list (snd G)) V V';
}.

Lemma sim_I ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative ZL LV s lv
-> labenv_sim Sim (sim r) SR (zip pair LV ZL) L L'
-> sim r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - destruct e.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_op il_statetype_I);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H10. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_I); intros; eauto 20 using op_eval_live, agree_on_incl.
  - eapply labenv_sim_app; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * erewrite get_nth; eauto using zip_get; simpl.
        exploit (@omap_flt _ _ Z0 _ blv _ _ H7);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros; eapply argsLive_liveSound; eauto.
        rewrite H12. eexists; split; eauto.
        repeat split; eauto using filter_filter_by_length.
        eapply agree_on_incl; eauto.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_fun_ptw; eauto.
    + intros. left. rewrite <- zip_app;[| eauto with len]. eapply IH; eauto using agree_on_incl.
    + intros. hnf; intros; simpl in *; dcr; subst.
      inv_get.
      rewrite <- zip_app;[| eauto with len].
      eapply IH; eauto. simpl.
      eapply agree_on_update_flt; eauto.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative nil nil s lv
-> @sim I.state _ I.state _ bot3 Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros.
  eapply (@sim_I nil nil); eauto.
  eapply labenv_sim_nil.
Qed.

End I.

(** ** Correctness with respect to the functional semantics IL *)
(** Functional here means that variables are lexically scoped binders instead of assignables. *)

Module F.

  Import SimF.

Instance SR : PointwiseProofRelationF ((set var) * params) := {
   ParamRelFP G Z Z' := Z' = (flt (fst G) (snd G) Z) /\ snd G = Z;
   ArgRelFP E E' G VL VL' :=
     VL' = (flt (fst G) (snd G) VL) /\
     length (snd G) = length VL
}.

Lemma sim_F ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional ZL LV s lv
-> labenv_sim Sim (sim r) SR (zip pair LV ZL) L L'
-> sim r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - destruct e.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_op il_statetype_F);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H10. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_call il_statetype_F); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_F); intros; eauto 20 using op_eval_live, agree_on_incl.
  - eapply labenv_sim_app; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * erewrite get_nth; eauto using zip_get; simpl.
        exploit (@omap_flt _ _ Z0 _ blv _ _ H7);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros; eapply argsLive_liveSound; eauto.
        rewrite H12. eexists; split; eauto.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_fun_ptw; eauto.
    + intros. left. rewrite <- zip_app;[| eauto with len].
      eapply IH; eauto using agree_on_incl.
    + intros. hnf; intros; simpl in *; dcr; subst.
      inv_get.
      rewrite <- zip_app; [| eauto with len].
      eapply IH; eauto. simpl in *.
      exploit H9; eauto.
      eapply agree_on_update_flt; eauto using agree_on_incl.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional nil nil s lv
-> @sim F.state _ F.state _ bot3 Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros.
  eapply (@sim_F nil nil); eauto. eapply labenv_sim_nil.
Qed.

End F.


(** ** Reconstruction of Liveness Information after DVE *)
(** In this section we show that liveness information can
    be transformed alongside DVE.
    This means that liveness recomputation after the transformation is not neccessary. *)


Fixpoint compile_live (s:stmt) (a:ann (set var)) (G:set var) : ann (set var) :=
  match s, a with
    | stmtLet x e s, ann1 lv an as a =>
      if [x ∈ getAnn an \/ isCall e] then ann1 (G ∪ lv) (compile_live s an {x})
                         else compile_live s an G
    | stmtIf e s t, ann2 lv ans ant =>
      if [op2bool e = Some true] then
        compile_live s ans G
      else if [op2bool e = Some false ] then
        compile_live t ant G
      else
        ann2 (G ∪ lv) (compile_live s ans ∅) (compile_live t ant ∅)
    | stmtApp f Y, ann0 lv => ann0 (G ∪ lv)
    | stmtReturn x, ann0 lv => ann0 (G ∪ lv)
    | stmtFun F t, annF lv ans ant =>
      let ans' := zip (fun Zs a => let a' := compile_live (snd Zs) a ∅ in
                               setTopAnn a' (getAnn a' ∪ of_list (flt (getAnn a) (fst Zs) (fst Zs)))) F ans
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
    + etransitivity; eauto. rewrite H2; eauto.
    + etransitivity; eauto. rewrite <- H3; eauto.
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
    -> live_sound i ((fun Z lv => flt lv Z Z) ⊜ ZL LV) LV (compile (zip pair LV ZL) s lv) (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - cases; eauto. econstructor; eauto.
    + eapply live_exp_sound_incl; eauto.
    + rewrite compile_live_incl; eauto.
      rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - repeat cases; eauto.
    + econstructor; eauto.
      eapply live_op_sound_incl; eauto.
      rewrite compile_live_incl_empty; eauto with cset.
      rewrite compile_live_incl_empty; eauto with cset.
  - econstructor; eauto using zip_get.
    + simpl. cases; eauto.
      rewrite <- H1. rewrite minus_inter_empty. eapply incl_right.
      rewrite of_list_flt. cset_tac.
    + erewrite get_nth; eauto using zip_get.
      simpl. eauto with len.
    + intros ? ? Get. erewrite get_nth in Get; eauto using zip_get. simpl in *.
      edestruct get_flt; eauto; dcr.
      eapply live_op_sound_incl.
      eapply argsLive_live_exp_sound; eauto. eauto with cset.
  - econstructor; eauto.
    eapply live_op_sound_incl; eauto using incl_right.
  - econstructor; simpl in *; eauto with len.
    + eapply live_sound_monotone.
      rewrite map_zip. simpl.
      do 2 rewrite zip_app in IHtrue_live_sound; eauto with len.
      rewrite zip_map_l, zip_map_r in IHtrue_live_sound.
      eapply IHtrue_live_sound.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto.
      rewrite of_list_flt. clear. cset_tac.
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
      rewrite of_list_flt. clear. cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      rewrite of_list_flt.
      split. eapply nodup_flt'.
      clear_all; cset_tac.
      split. eapply nodup_flt'. eauto.
    + rewrite compile_live_incl; eauto with cset.
Qed.

(** ** DVE and Unreachable Code *)
(** We show that DVE does not introduce unreachable code. *)

Lemma DVE_callChain b Lv ZL F als n l'
  : ❬F❭ = ❬als❭
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
         get F n Zs ->
         get als n a ->
         forall n0 : nat,
           isCalled b (snd Zs) (LabI n0) ->
           isCalled b (compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd Zs) a) (LabI n0))
     -> callChain (isCalled b) F (LabI l') (LabI n)
     -> callChain (isCalled b)
                 ((fun (Zs : params * stmt) (a : ann ⦃var⦄) =>
                     (flt (getAnn a) (fst Zs) (fst Zs),
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
    -> isCalled true s (LabI n)
    -> isCalled true (compile (zip pair LV ZL) s lv) (LabI n).
Proof.
  intros LS IC.
  general induction LS; invt isCalled; simpl; repeat cases; eauto using isCalled;
    try congruence.
  - destruct l' as [l'].
    econstructor; rewrite <- zip_app; eauto with len.
    rewrite zip_length2; eauto. eapply DVE_callChain; eauto.
Qed.

Lemma DVE_noUnreachableCode i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> noUnreachableCode (isCalled true) s
    -> noUnreachableCode (isCalled true) (compile (zip pair LV ZL) s lv).
Proof.
  intros LS UC.
  general induction LS; inv UC; simpl; repeat cases; eauto using noUnreachableCode.
  - econstructor; intros; inv_get; rewrite <- zip_app; simpl; eauto with len.
    + edestruct H8 as [[l] [IC CC]]. rewrite zip_length2 in H4; eauto.
      eexists (LabI l); split; eauto.
      eapply DVE_isCalled; eauto.
      eapply DVE_callChain; eauto using DVE_isCalled.
Qed.

Require Import AppExpFree.

Lemma DVE_app_expfree LVZL s lv
: app_expfree s
  -> app_expfree (compile LVZL s lv).
Proof.
  intros AEF.
  general induction AEF; destruct lv; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      repeat cases; eauto using app_expfree.
  - econstructor. intros; inv_get; eauto.
    edestruct get_flt; eauto; dcr. eauto.
  - econstructor; intros; inv_get; eauto.
    eapply H0; eauto.
Qed.

Require Import RenamedApart PE.

Fixpoint compile_renamedApart (s:stmt) (lv:ann (set var)) (a:ann (set var * set var)) (D:set var)
  : ann (set var * set var) :=
  match s, lv, a with
  | stmtLet x e s, ann1 lv alv, ann1 (_, _) an as a =>

    if [x ∈ getAnn alv \/ isCall e] then
      let an' := compile_renamedApart s alv an {x;D} in
      ann1 (D, {x;snd (getAnn an')}) an'
    else compile_renamedApart s alv an D
  | stmtIf e s t, ann2 lv ans ant, ann2 (_,_) bns bnt =>
    let bns' := compile_renamedApart s ans bns D in
    let bnt' := compile_renamedApart t ant bnt D in
      if [op2bool e = Some true] then bns'
      else if [op2bool e = Some false ] then bnt'
           else ann2 (D,
                      snd (getAnn bns') ∪ snd (getAnn bnt'))
                     bns' bnt'
    | stmtApp f Y, ann0 lv, ann0 _ => ann0 (D, ∅)
    | stmtReturn x, ann0 lv, ann0 _ => ann0 (D, ∅)
    | stmtFun F t, annF lv anF ant, annF (_, _) bnF bnt =>
      let abnF := (pair ⊜ anF bnF) in
      let bnF' := zip (fun (Zs:params * stmt) ab =>
                        compile_renamedApart (snd Zs) (fst ab) (snd ab)
                                             (of_list (flt (getAnn (fst ab)) (fst Zs) (fst Zs)) ∪ D)) F abnF in
      let abnF' := (pair ⊜ anF bnF') in
      let bnt' := compile_renamedApart t ant bnt D in
      annF (D, list_union ((fun Zs ab => of_list (flt (getAnn (fst ab)) (fst Zs) (fst Zs)) ∪ snd (getAnn (snd ab))) ⊜ F abnF')
                          ∪ snd (getAnn bnt'))
           bnF' bnt'
    | _, _, a => a
  end.

Lemma fst_getAnn_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> fst (getAnn (compile_renamedApart s lv G D)) = D.
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; eauto.
Qed.

Lemma fst_getAnn_renamedApart' i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> fst (getAnn (compile_renamedApart s lv G D)) [=] D.
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; eauto.
Qed.

Hint Resolve fst_getAnn_renamedApart fst_getAnn_renamedApart'.

Lemma snd_getAnn_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> snd (getAnn (compile_renamedApart s lv G D)) ⊆ snd (getAnn G).
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; srewrite D'; eauto.
  - rewrite IHTLS; eauto. rewrite H9; eauto.
  - rewrite IHTLS; eauto. rewrite H9; eauto with cset.
  - rewrite IHTLS1; eauto. pe_rewrite. eauto with cset.
  - rewrite IHTLS2; eauto. pe_rewrite; eauto with cset.
  - rewrite IHTLS1, IHTLS2; eauto. pe_rewrite; eauto.
  - rewrite IHTLS, H11; eauto.
    eapply incl_union_lr; eauto.
    eapply list_union_incl; intros; inv_get; simpl.
    eapply incl_list_union; eauto using zip_get.
    rewrite H1; eauto.
    unfold defVars; rewrite of_list_flt; simpl.
    clear. cset_tac. clear; cset_tac.
Qed.

Lemma nodup_filter X R p `{Proper _ (R ==> eq) p} (L:list X)
  : NoDupA R L
    -> NoDupA R (filter p L).
Proof.
  intros ND.
  general induction ND; simpl in *; dcr; eauto.
  - cases; eauto using NoDupA.
    constructor; eauto.
    rewrite filter_InA; intuition.
Qed.

Lemma DVE_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> D ⊆ fst (getAnn G)
    -> freeVars (compile (zip pair LV ZL)  s lv) ⊆ D
    -> renamedApart (compile (zip pair LV ZL)  s lv) (compile_renamedApart s lv G D).
Proof.
  intros RA TLS Dincl inclD.
  general induction TLS; invt renamedApart; simpl in * |- *; eauto using renamedApart.
  - cases; simpl in *.
    + econstructor; try reflexivity; eauto with cset.
      * rewrite <- inclD; eauto with cset.
      * eapply IHTLS; eauto.
        -- rewrite H9, Dincl; simpl; eauto with cset.
        -- rewrite <- inclD. clear; cset_tac.
      * eapply pe_eta_split; econstructor; simpl; eauto.
    + eapply IHTLS; eauto.
      * rewrite H9; simpl; cset_tac.
  - repeat cases; eauto.
    + eapply IHTLS1; eauto with cset pe.
    + eapply IHTLS2; eauto with cset pe.
    + simpl in *.
      econstructor; try reflexivity; eauto.
      * rewrite <- inclD. eauto with cset.
      * rewrite !snd_getAnn_renamedApart, H11, H12; eauto.
      * exploit IHTLS1; eauto.
        pe_rewrite; eauto with cset.
        rewrite <- inclD; eauto with cset.
      * exploit IHTLS2; eauto.
        pe_rewrite; eauto with cset.
        rewrite <- inclD; eauto with cset.
      * eapply pe_eta_split; econstructor; simpl; eauto.
      * eapply pe_eta_split; econstructor; simpl; eauto.
  - econstructor; eauto with len; (try eapply eq_union_lr); eauto.
    * intros; inv_get. simpl in *.
      rewrite <- zip_app;[| eauto with len].
      eapply H1; eauto.
      -- edestruct H8; eauto; dcr. rewrite H4. rewrite Dincl;  eauto.
         rewrite of_list_flt. clear; cset_tac.
      -- rewrite of_list_flt.
         rewrite <- inclD.
         rewrite <- incl_list_union; eauto using zip_get; [| reflexivity].
         simpl. rewrite of_list_flt.
         rewrite <- union_assoc. eapply incl_union_left.
         rewrite zip_app; eauto with len.
         clear; cset_tac.
    * hnf; intros; inv_get.
      edestruct H8; eauto; dcr.
      simpl. econstructor; simpl in *.
      erewrite fst_getAnn_renamedApart; eauto with cset.
      split. eapply nodup_flt; eauto.
      split. eapply disj_2_incl; eauto. rewrite of_list_flt.
      eapply disj_1_incl; eauto. cset_tac.
      erewrite fst_getAnn_renamedApart, !snd_getAnn_renamedApart; only 2-7: eauto.
      pe_rewrite. rewrite of_list_flt. eapply disj_1_incl; eauto.
      clear; cset_tac.
    * hnf; intros. inv_get.
      unfold defVars; simpl.
      exploit H9; try eapply H4; only 1-2: eauto using zip_get.
      unfold defVars in*.
      rewrite !snd_getAnn_renamedApart; only 2-5: eauto.
      rewrite !of_list_flt.
      eapply disj_incl; eauto.
      clear; cset_tac.
      clear; cset_tac.
    * rewrite <- zip_app; eauto with len; simpl in *.
      eapply IHTLS; eauto.
      pe_rewrite. eauto. rewrite <- inclD; eauto.
    * eapply pe_eta_split; econstructor; eauto.
      erewrite fst_getAnn_renamedApart; eauto.
    * eapply list_union_eq; intros; eauto 20 with len.
      inv_get. unfold defVars; simpl.
      simpl. reflexivity.
Qed.

Require Import RenamedApart_Liveness.

Lemma DVE_freeVars_live ZL LV s lv
      (LS:true_live_sound Functional ZL LV s lv)
  : freeVars (compile (zip pair LV ZL) s lv) ⊆ getAnn lv.
Proof.
  general induction LS; simpl; repeat cases; simpl;
    eauto using Op.freeVars_live; set_simpl.
  - exploit Exp.freeVars_live; eauto with cset.
  - cset_tac.
  - rewrite IHLS1; eauto.
  - rewrite IHLS2; eauto.
  - exploit Op.freeVars_live; eauto.
    rewrite IHLS1, IHLS2; eauto. rewrite H0, H1, H2; eauto.
    clear; cset_tac.
  - erewrite get_nth; eauto using zip_get; simpl.
    eapply list_union_incl; intros; inv_get; eauto with cset.
    edestruct get_flt; eauto; dcr.
    exploit argsLive_live_exp_sound; eauto.
    exploit Op.freeVars_live; eauto with cset.
  - rewrite <- zip_app; eauto with len.
    rewrite IHLS; eauto.
    eapply union_incl_split; eauto.
    eapply list_union_incl; intros; inv_get; [|eauto with cset]; simpl.
    rewrite of_list_flt. rewrite H1; eauto.
    exploit H2 as INCL; dcr; eauto; simpl in *.
    rewrite <- INCL. clear; cset_tac.
Qed.

Lemma DVE_freeVars ZL LV s lv
      (LS:true_live_sound Functional ZL LV s lv)
  : freeVars (compile (zip pair LV ZL) s lv) ⊆ freeVars s.
Proof.
  general induction LS; simpl; repeat cases; simpl; eauto.
  - rewrite IHLS; eauto.
  - rewrite not_or_dist in NOTCOND; dcr.
    assert (x ∉ freeVars (compile (pair ⊜ Lv ZL) b al)). {
      exploit DVE_freeVars_live; eauto.
    }
    cset_tac.
  - rewrite IHLS1; eauto with cset.
  - rewrite IHLS2; eauto with cset.
  - rewrite IHLS1, IHLS2; eauto with cset.
  - erewrite get_nth; eauto using zip_get; simpl.
    eapply list_union_incl; intros; inv_get; eauto with cset.
    eapply get_flt in H4; eauto; dcr.
    eapply incl_list_union; eauto using get.
  - rewrite <- zip_app; eauto with len.
    rewrite IHLS; eauto. eapply incl_union_lr; eauto.
    eapply list_union_incl; intros; inv_get;[|eauto with cset]; simpl.
    eapply incl_list_union; eauto using get.
    rewrite of_list_flt.
    exploit H0; eauto. simpl in *.
    exploit DVE_freeVars_live; eauto.
    exploit H1; eauto.
    set (X:=compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd x0) x1) in *.
    revert H7 H8; clear. cset_tac.
Qed.

Lemma DVE_paramsMatch i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> paramsMatch s (@length _ ⊝ ZL)
    -> paramsMatch (compile (zip pair LV ZL) s lv) (@length _ ⊝ ((fun Z lv => flt lv Z Z) ⊜ ZL LV)).
Proof.
  intros TLS PM.
  general induction PM; invt true_live_sound; simpl in * |- *; repeat cases;
    eauto 10 using paramsMatch.
  - erewrite !get_nth; eauto using zip_get.
    econstructor; eauto with get. simpl.
    eapply map_get_eq; eauto using zip_get.
    erewrite flt_length; eauto.
  - econstructor; intros; inv_get; simpl.
    + rewrite <- !zip_app; eauto with len.
      rewrite <- !List.map_app.
      exploit H0; eauto.
      * rewrite <- !List.map_app; eauto.
      * eqassumption.
        rewrite map_zip; simpl.
        rewrite zip_app. f_equal. f_equal.
        rewrite zip_map_l, zip_map_r. reflexivity.
        eauto with len.
    + rewrite <- !zip_app; eauto.
      exploit IHPM; eauto.
      * rewrite <- !List.map_app; eauto.
      * eqassumption.
        rewrite <- List.map_app.
        rewrite map_zip; simpl.
        rewrite zip_app. f_equal. f_equal.
        rewrite zip_map_l, zip_map_r. reflexivity.
        eauto with len.
      *  eauto with len.
Qed.

Lemma DVE_live_incl i (FNC:isFunctional i) ZL LV s ra (RA:renamedApart s ra) lv (G D:set var)
      (TLS:true_live_sound i ZL LV s lv)
      (AN:ann_R (fun (x : ⦃nat⦄) (y : ⦃nat⦄ * ⦃nat⦄) => x ⊆ fst y) lv ra)
      (Incl1:getAnn lv ⊆ D)
      (Incl3:D ⊆ fst (getAnn ra))
      (Incl2:G ⊆ D)
  : ann_R (fun (x : ⦃nat⦄) (y : ⦃nat⦄ * ⦃nat⦄) => x ⊆ fst y)
          (compile_live s lv G)
          (compile_renamedApart s lv ra D).
Proof.
  time (general induction AN; invt true_live_sound; invt renamedApart; simpl in *;
        set_simpl).
  - econstructor; eauto with cset len.
  - econstructor; eauto with cset len.
  - cases; simpl in *.
    + econstructor. eauto with cset.
      eapply IHAN; try eassumption.
      eauto with cset. pe_rewrite. eauto with cset.
      eauto with cset.
    + eapply IHAN; eauto. cset_tac. pe_rewrite. cset_tac.
  - repeat cases; simpl in *.
    + eapply IHAN1; eauto. rewrite H9; eauto. pe_rewrite. eauto.
    + eapply IHAN2; eauto. rewrite H10; eauto. pe_rewrite; eauto.
    + econstructor. simpl. rewrite Incl1, Incl2; clear_all; cset_tac.
      * eapply IHAN1; eauto with cset. rewrite H9; eauto with cset.
        pe_rewrite; eauto.
      * eapply IHAN2; eauto with cset. rewrite H10; eauto.
        pe_rewrite; eauto.
  - econstructor; simpl; eauto.
    + rewrite Incl1, Incl2; clear; cset_tac.
    + eauto with len.
    + intros; inv_get.
      eapply ann_R_setTopAnn_left; eauto; simpl.
      * rewrite fst_getAnn_renamedApart';eauto.
        rewrite compile_live_incl_empty; eauto. rewrite of_list_flt.
        exploit H12; eauto.
        cases in H3. rewrite Incl1 in H3.
        rewrite <- H3. clear; cset_tac.
      * exploit H1; eauto.
        eapply ann_R_get in H3.
        edestruct H15; dcr; eauto.
        rewrite H9 in H3.
        exploit H14; try eassumption.
        exploit H12; try eassumption. simpl in *.
        cases in H21.
        rewrite Incl1 in H21.
        eapply H2; eauto.
        -- rewrite of_list_flt.
           rewrite <- H21.
           clear; cset_tac.
        -- rewrite of_list_flt.
           rewrite H9. rewrite <- Incl3.
           clear; cset_tac.
        -- eauto with cset.
    + eapply IHAN; eauto. eauto with cset.
      pe_rewrite. eauto with cset. eauto with cset.
Qed.

Require Import VarP.

Lemma DVE_var_P o (P:nat -> Prop) LV ZL (s:stmt) lv
      (VP:var_P P s)
      (TLS:true_live_sound o ZL LV s lv)
  : var_P P (compile (zip pair LV ZL) s lv).
Proof.
  general induction VP; invt true_live_sound; simpl;
    repeat cases; eauto 10 using var_P.
  - econstructor; eauto.
    erewrite get_nth; eauto using zip_get. simpl.
    hnf; intros.
    eapply list_union_get in H0; destruct H0; dcr; inv_get; [|cset_tac].
    eapply get_flt in H0; dcr.
    eapply H; eauto. eapply incl_list_union; eauto using zip_get.
    reflexivity.
  - econstructor; eauto.
    + intros; inv_get; simpl.
      rewrite <- zip_app; eauto with len.
    + intros; inv_get; simpl.
      rewrite of_list_flt.
      rewrite meet_comm.
      rewrite meet_incl; eauto.
    + rewrite <- zip_app; eauto with len.
Qed.