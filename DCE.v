Require Import CSet Util Fresh Filter MoreExp Take MoreList OUnion.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness UnreachableCode.
Require Import Sim SimTactics SimI.

Set Implicit Arguments.
Unset Printing Records.


Hint Extern 5 =>
match goal with
| [ H : ?A = ⎣ true ⎦, H' : ?A = ⎣ false ⎦ |- _ ] => congruence
| [ H : ?A = None , H' : ?A = Some _ |- _ ] => congruence
| [ H : ?A <> ⎣ true ⎦ , H' : ?A <> ⎣ false ⎦ |- ?A = None ] =>
  case_eq (A); [intros [] ?| intros ?]; congruence
end.

Fixpoint countTrue (L:list bool) :=
  match L with
  | nil => 0
  | true :: xs => 1 + countTrue xs
  | false :: xs => countTrue xs
  end.

Lemma countTrue_exists (L:list bool) n
  : get L n true
    -> countTrue L <> 0.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; eauto.
Qed.

Lemma countTrue_app (L L':list bool)
  : countTrue (L ++ L') = countTrue L + countTrue L'.
Proof.
  intros. induction L; simpl; eauto.
  destruct a; eauto. omega.
Qed.

Definition compileF (compile : forall (RZL:list (bool * params)) (s:stmt) (a:ann bool), stmt)
(RZL:list (bool * params)) :=
  fix f (F:〔params * stmt〕) (ans:list (ann bool)) :=
    match F, ans with
    | (Z,s)::F, a::ans =>
      if getAnn a then (Z, compile RZL s a) :: f F ans
      else  f F ans
    | _, _ => nil
    end.

Fixpoint compile (RZL:list (bool * params)) (s:stmt) (a:ann bool) :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      stmtLet x e (compile RZL s an)
    | stmtIf e s t, ann2 _ ans ant =>
      if [exp2bool e = Some true] then
        (compile RZL s ans)
      else if [ exp2bool e = Some false ] then
             (compile RZL t ant)
           else
             stmtIf e (compile RZL s ans) (compile RZL t ant)
    | stmtApp f Y, ann0 _ =>
      let lvZ := nth (counted f) RZL (false, nil) in
      stmtApp (LabI (countTrue (fst ⊝ (take (counted f) RZL)))) Y
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile RZL s an)
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ RZL in
      match compileF compile LV' F ans with
      | nil => compile LV' t ant
      | F' => stmtFun F' (compile LV' t ant)
      end
    | s, _ => s
  end.

Lemma compileF_get RZL F n ans Zs a
  : ❬F❭ = ❬ans❭
    -> get F n Zs
    -> get ans n a
    -> getAnn a = true
    -> get (compileF compile RZL F ans) (countTrue (getAnn ⊝ (take n ans)))
          (fst Zs, compile RZL (snd Zs) a).
Proof.
  intros LEN GetF GetAns. length_equify.
  general induction LEN.
  - isabsurd.
  - destruct x as [Z s]; inv GetF; inv GetAns.
    + simpl. rewrite H.
      * eauto using get.
    + simpl. cases; simpl; eauto using get.
Qed.

Lemma compileF_get_inv RZL F ans Z' s' n'
  : ❬F❭ = ❬ans❭
    -> get (compileF compile RZL F ans) n' (Z', s')
    -> exists Zs a n, get F n Zs
      /\ get ans n a
      /\ getAnn a = true
      /\ Z' = fst Zs
      /\ s' = compile RZL (snd Zs) a
      /\ n' = countTrue (getAnn ⊝ (take n ans)).
Proof.
  intros LEN Get. length_equify.
  general induction LEN; simpl in *.
  - isabsurd.
  - destruct x as [Z s]. case_eq (getAnn y); intros EQ.
    + rewrite EQ in *. inv Get.
      * eexists (Z',s), y, 0; eauto 20 using get.
      * clear Get. edestruct IHLEN as [Zs [a [n' [lv ?]]]]; eauto; dcr; subst.
        exists Zs, a, (S n'). simpl; rewrite EQ. eauto 20 using get.
    + rewrite EQ in *. edestruct IHLEN as [Zs [a [n [lv ?]]]]; eauto; dcr; subst.
      exists Zs, a, (S n). simpl; rewrite EQ. eauto 20 using get.
Qed.

Lemma compileF_length LV F ans
  : length F = length ans
    -> length (compileF compile LV F ans) = countTrue (getAnn ⊝ ans).
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

Lemma DVE_isCalled ZL RL s lv n
  : unreachable_code ZL RL s lv
    -> trueIsCalled s (LabI n)
    -> isCalled (compile (pair ⊜ RL ZL) s lv) (LabI (countTrue (fst ⊝ take n (pair ⊜ RL ZL)))).
Proof.
  intros Live IC.
  general induction IC; invt unreachable_code; simpl; eauto using isCalled.
  - repeat cases; eauto using isCalled. congruence.
  - repeat cases; eauto using isCalled. congruence.
  - simpl in *.
    exploit unreachable_code_trueIsCalled; try eapply IC2; eauto.
    simpl in *. inv_get. cases.
    + exfalso.
      assert (length (compileF compile (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ pair ⊜ RL ZL) F als)
              <> 0). {
        rewrite compileF_length; eauto.
        eapply countTrue_exists. rewrite H5; eauto using map_get_1.
      }
      eapply H1. rewrite <- Heq; eauto.
    + rewrite Heq; clear Heq. exploit compileF_get; eauto.
      econstructor; eauto.
      * rewrite compileF_length; eauto.
        rewrite (take_eta k (getAnn ⊝ als)). rewrite countTrue_app.
        rewrite map_take. erewrite <- get_eq_drop; eauto.
        rewrite <- H5; simpl. omega.
      * exploit IHIC1 as IH; eauto; try reflexivity; simpl.
        rewrite compileF_length; eauto with len.
        rewrite zip_app in IH; eauto with len.
        rewrite take_app_ge in IH; eauto 20 with len.
        rewrite map_app in IH.
        rewrite <- getAnn_eq in IH; eauto. rewrite countTrue_app in IH; eauto.
        rewrite zip_length2 in IH; eauto with len.
        rewrite map_length in IH. orewrite (❬F❭ + n - ❬als❭ = n) in IH.
        rewrite <- zip_app; eauto with len.
      * exploit IHIC2 as IH; eauto.
        rewrite zip_app in IH; eauto with len.
        erewrite <- getAnn_take_eq in IH; eauto.
  - cases.
    + rewrite <- zip_app; eauto with len. exploit IHIC; eauto. reflexivity.
      rewrite zip_app in H; eauto with len.
      rewrite take_app_ge in H; eauto 20 with len.
      rewrite zip_length2 in H; eauto with len.
      rewrite map_length in H.
      orewrite (❬F❭ + n - ❬als❭ = n) in H. simpl.
      rewrite map_app in H. rewrite countTrue_app in H.
      rewrite <- getAnn_eq in H; eauto.
      erewrite <- compileF_length in H; eauto.
      erewrite <- Heq in H. eauto.
    + rewrite Heq. eapply IsCalledLet.
      exploit IHIC; eauto; try reflexivity.
      rewrite compileF_length; eauto.
      rewrite zip_app in H; eauto with len.
      rewrite take_app_ge in H; eauto 20 with len.
      rewrite zip_length2 in H; eauto with len.
      rewrite map_length in H.
      orewrite (❬F❭ + n - ❬als❭ = n) in H. simpl.
      rewrite map_app in H. rewrite countTrue_app in H.
      rewrite <- getAnn_eq in H; eauto.
Qed.

Lemma DVE_noUnreachableCode ZL RL s lv
  : unreachable_code ZL RL s lv
    -> noUnreachableCode (compile (pair ⊜ RL ZL) s lv).
Proof.
  intros Live. induction Live; simpl; repeat cases; eauto using noUnreachableCode.
  - rewrite <- zip_app; eauto with len.
  - rewrite Heq; clear Heq.
    econstructor; eauto using noUnreachableCode.
    + intros. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' ?]]]; eauto; dcr; subst; simpl.
      rewrite <- zip_app; eauto with len.
    + rewrite <- zip_app; eauto with len.
    + intros.
      edestruct get_in_range as [Zs ?]; eauto. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' [lv' ?]]]]; eauto; dcr; subst; simpl.
      exploit H2; eauto.
      rewrite H7; eauto.
      exploit DVE_isCalled as IH; eauto.
      rewrite zip_app in IH; eauto with len.
      erewrite <- getAnn_take_eq in IH; eauto.
Qed.

Module I.

  Definition ArgRel (V V':onv val) (G:bool * params) (VL VL': list val) : Prop :=
      VL' = VL /\
      length (snd G) = length VL /\ V = V'.


  Definition ParamRel (G:bool * params) (Z Z' : list var) : Prop :=
    Z' = Z /\ snd G = Z.

Instance SR : ProofRelationI (bool * params) := {
   ParamRelI := ParamRel;
   ArgRelI := ArgRel;
   BlockRelI := fun lvZ b b' => block_Z b = block_Z b';
   Image AL := countTrue (List.map fst AL);
   IndexRelI AL n n' :=
     n' = countTrue (fst ⊝ (take n AL)) /\ exists Z, get AL n (true, Z)
}.
- intros. hnf in H, H0; dcr; subst.
  eauto.
- intros AL' AL n n' [H H']; subst.
  split. clear H' H.
  + general induction AL'; simpl.
    * orewrite (n - 0 = n). omega.
    * destruct n; simpl; eauto. cases; simpl; eauto.
  + destruct H' as [? ?]. rewrite get_app_ge in H0; eauto.
Defined.


Lemma inv_extend s L L' RZL als  Z f
(LEN: ❬s❭ = ❬als❭)
(H: forall (f : nat) (Z : params),
       get RZL f (true, Z) ->
       exists b b' : I.block, get L f b /\ get L' (countTrue (fst ⊝ take f RZL)) b')
(Get : get (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ RZL) f (true, Z))
  :  exists b b' : I.block, get (mapi I.mkBlock s ++ L) f b /\
                       get (mapi I.mkBlock (compileF compile (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ RZL) s als) ++ L') (countTrue (fst ⊝ take f (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ RZL))) b'.
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
    rewrite countTrue_app.
    rewrite mapi_length.
    rewrite compileF_length; eauto.
    rewrite <- getAnn_eq; eauto.
Qed.


Lemma sim_I ZL RL r L L' V s a
: unreachable_code ZL RL s a
-> simILabenv Bisim r SR (pair ⊜ RL ZL) L L'
-> (forall (f:nat) Z,
      get (pair ⊜ RL ZL) f (true, Z)
      -> exists (b b' : I.block),
        get L f b /\
        get L' (countTrue (fst ⊝ (take f (pair ⊜ RL ZL)))) b')
-> sim'r r Bisim (L,V, s) (L',V, compile (pair ⊜ RL ZL) s a).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt unreachable_code; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + pone_step; eauto.
    + pno_step.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto.
      eapply star2_silent.
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s2); eauto.
      eapply star2_silent.
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      destruct o. case_eq (val2bool v); intros.
      pfold; econstructor; try eapply plus2O; eauto.
      econstructor; eauto.
      econstructor; eauto.
      left; eapply (IH s1); eauto using agree_on_incl.
      pfold; econstructor; try eapply plus2O; eauto.
      econstructor 3; eauto.
      econstructor 3; eauto.
      left; eapply (IH s2); eauto using agree_on_incl.
      pfold. econstructor 4; try eapply star2_refl; eauto.
      stuck. stuck.
  - edestruct H1 as [? [? [GetL GetL']]]; eauto using zip_get.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    destruct o.
    + destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      edestruct H0 as [[? ?] SIM]; eauto; dcr.
      edestruct SIM as [[? ?] SIM']; eauto using zip_get.
      hnf; simpl. split; eauto using zip_get.
      instantiate (1:=LabI (countTrue (fst ⊝ take (labN l) (pair ⊜ RL ZL)))).
      reflexivity. simpl. eauto.
      eapply SIM'; eauto using zip_get.
      hnf; simpl. split; eauto using zip_get with len.
    + pfold; econstructor 4; try eapply star2_refl; eauto; stuck2.
  - pno_step.
  - remember (omap (exp_eval V) Y). symmetry in Heqo.
    destruct o.
    + pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
    + pno_step.
  - cases.
    + eapply sim'_expansion_closed;
        [| eapply star2_silent; [ econstructor; eauto | eapply star2_refl ]
         | eapply star2_refl ].
      rewrite <- zip_app; eauto with len.
      eapply IH; eauto.
      * rewrite zip_app; eauto with len.
        eapply simILabenv_extension with (F':=nil); eauto. eauto with len.
        intros; isabsurd. isabsurd.
        simpl; intros; dcr; subst. exfalso.
        rewrite get_app_lt in H9; eauto with len. inv_get.
        assert (length (compileF compile (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ pair ⊜ RL ZL) s als)
                <> 0). {
          rewrite compileF_length; eauto.
          eapply countTrue_exists. rewrite <- EQ1; eauto using map_get_1.
        }
        eapply H6. rewrite <- Heq. eauto.
        simpl; intros; dcr; subst.
        rewrite get_app_ge in H9; eauto with len. inv_get.
        rewrite map_take. rewrite map_app.
        rewrite map_zip.
        rewrite zip_map_fst; eauto with len.
        rewrite take_app_ge. rewrite countTrue_app. omega.
        rewrite map_length. omega.
        rewrite zip_length2; eauto with len.
        rewrite map_length. omega.
        simpl. rewrite <- getAnn_eq; eauto. erewrite <- compileF_length; eauto.
        erewrite <- Heq. eauto.
      * intros. rewrite zip_app in H2; eauto with len.
        eapply get_app_cases in H2. destruct H2.
        exfalso. inv_get.
        assert (length (compileF compile (pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ pair ⊜ RL ZL) s als)
                <> 0). {
          rewrite compileF_length; eauto.
          eapply countTrue_exists. rewrite <- EQ1; eauto using map_get_1.
        }
        eapply H6. rewrite <- Heq. eauto.
        dcr. exploit H1; eauto. destruct H2 as [? [? ?]]; dcr.
        do 2 eexists. split.
        eapply get_app_right; eauto. rewrite mapi_length, zip_length2; eauto with len.
        rewrite map_length. rewrite zip_length2 in H6; eauto with len.
        rewrite map_length in H6. omega.
        rewrite zip_app; eauto with len.
        rewrite take_app_ge; eauto. rewrite map_app.
        rewrite <- getAnn_eq; eauto. rewrite countTrue_app.
        erewrite <- compileF_length; eauto. erewrite <- Heq. eauto.
    + rewrite Heq; clear Heq.
      pone_step. left. rewrite <- zip_app; eauto with len.
      eapply IH; eauto.
      {
        + rewrite zip_app; eauto with len.
          eapply simILabenv_extension; eauto. eauto with len.
          * intros. hnf; intros.
            hnf in H3. dcr. hnf in H11; dcr; subst.
            rewrite get_app_lt in H14; eauto using get_range.
            inv_get.
            exploit (compileF_get ((pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ pair ⊜ RL ZL) )); eauto.
            erewrite <- getAnn_take_eq in H7; eauto.
            simpl in *. get_functional.
            rewrite <- zip_app; eauto with len.
            eapply IH; eauto. exploit H8; eauto.
            rewrite zip_app; eauto with len.
            intros.
            eapply inv_extend; eauto with len.
          * hnf; intros.
            hnf in H2. dcr; subst.
            rewrite get_app_lt in H12; eauto with len.
            inv_get. simpl; unfold ParamRel; simpl.
            exploit (compileF_get ((pair ⊜ (getAnn ⊝ als) (fst ⊝ s) ++ pair ⊜ RL ZL) )); eauto.
            erewrite <- getAnn_take_eq in H6; eauto.
            get_functional. eauto.
          * intros. rewrite compileF_length; eauto.
            hnf in H2; dcr; subst.
            rewrite get_app_lt in H9;
              [| rewrite zip_length2; eauto with len; rewrite map_length; omega].
            inv_get.
            erewrite <- getAnn_take_eq; eauto.
            rewrite map_take.
            erewrite (take_eta n (getAnn ⊝ als)) at 2.
            rewrite countTrue_app.
            erewrite <- get_eq_drop; eauto using map_get_1.
            rewrite EQ1. simpl; omega.
          * intros. rewrite compileF_length; eauto.
            hnf in H2; dcr; subst.
            rewrite map_take. rewrite map_app.
            rewrite map_zip.
            rewrite zip_map_fst; eauto with len.
            rewrite take_app_ge. rewrite countTrue_app. omega.
            rewrite map_length. omega.
          * simpl. rewrite compileF_length; eauto.
            rewrite map_zip.
            rewrite zip_map_fst; eauto with len.
      }
      rewrite zip_app; eauto with len. intros; eapply inv_extend; eauto.
Qed.

Lemma sim_DVE V s a
: unreachable_code nil nil s  a
-> @sim I.state _ I.state _ Bisim (nil,V, s) (nil,V, compile nil s a).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_I nil nil); eauto; isabsurd.
  econstructor; simpl; eauto using @sawtooth; isabsurd.
Qed.

End I.

Fixpoint compile_live (s:stmt) (a:ann (set var)) : ann (set var) :=
  match s, a with
    | stmtLet x e s, ann1 lv an as a =>
      ann1 lv (compile_live s an)
    | stmtIf e s t, ann2 lv ans ant =>
      if [exp2bool e = Some true] then
        compile_live s ans
      else if [exp2bool e = Some false ] then
        compile_live t ant
      else
        ann2 lv (compile_live s ans) (compile_live t ant)
    | stmtApp f Y, ann0 lv => ann0 lv
    | stmtReturn x, ann0 lv => ann0 lv
    | stmtExtern x f Y s, ann1 lv an as a =>
      ann1 lv (compile_live s an)
    | stmtFun F t, annF lv ans ant =>
      let ans' := zip (fun Zs a => compile_live (snd Zs) a) F ans in
      annF lv ans' (compile_live t ant)
    | _, a => a
  end.
