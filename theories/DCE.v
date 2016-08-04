Require Import CSet Util LengthEq Fresh Take MoreList Filter OUnion.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness UnreachableCode.
Require Import Sim SimTactics SimI.

Set Implicit Arguments.
Unset Printing Records.

Definition compileF (compile : forall (RL:list bool) (s:stmt) (a:ann bool), stmt)
(RL:list bool) :=
  fix f (F:〔params * stmt〕) (ans:list (ann bool)) :=
    match F, ans with
    | (Z,s)::F, a::ans =>
      if getAnn a then (Z, compile RL s a) :: f F ans
      else  f F ans
    | _, _ => nil
    end.

Fixpoint compile (RL:list bool) (s:stmt) (a:ann bool) {struct s} :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      stmtLet x e (compile RL s an)
    | stmtIf e s t, ann2 _ ans ant =>
      if [op2bool e = Some true] then
        (compile RL s ans)
      else if [ op2bool e = Some false ] then
             (compile RL t ant)
           else
             stmtIf e (compile RL s ans) (compile RL t ant)
    | stmtApp f Y, ann0 _ =>
      stmtApp (LabI (countTrue (take (counted f) RL))) Y
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtFun F t, annF lv ans ant =>
      let LV' := getAnn ⊝ ans ++ RL in
      let F' := compileF compile LV' F ans in
      match F' with
      | nil => compile LV' t ant
      | _ => stmtFun F' (compile LV' t ant)
      end
    | s, _ => s
  end.

Lemma compileF_filter RL F als
  : compileF compile RL F als
    = map (fun p => (fst (fst p), compile RL (snd (fst p)) (snd p)))
          (filter (fun b => getAnn (snd b)) (zip pair F als)).
Proof.
  length_equify. general induction F; destruct als; simpl; eauto.
  - destruct a; eauto.
  - destruct a as [Z s]; cases; simpl; f_equal; eauto.
Qed.

Lemma compileF_Z_filter_by RL F als (LEN: ❬F❭ = ❬als❭)
  : fst ⊝ compileF compile RL F als
    = filter_by (fun b => b) (getAnn ⊝ als) (fst ⊝ F).
Proof.
  length_equify. general induction LEN; simpl; eauto.
  destruct x as [Z s]; cases; simpl; f_equal; eauto.
Qed.

Lemma compileF_get RL F n ans Zs a
  : get F n Zs
    -> get ans n a
    -> getAnn a = true
    -> get (compileF compile RL F ans) (countTrue (getAnn ⊝ (take n ans)))
          (fst Zs, compile RL (snd Zs) a).
Proof.
  intros GetF GetAns EQ.
  general induction ans; destruct F as [|[Z s] ?]; isabsurd.
  - inv GetF; inv GetAns.
    + simpl. rewrite EQ; eauto using get.
    + simpl. cases; simpl; eauto using get.
Qed.

Lemma compileF_get_inv RL F ans Z' s' n'
  : get (compileF compile RL F ans) n' (Z', s')
    -> exists Zs a n, get F n Zs
      /\ get ans n a
      /\ getAnn a = true
      /\ Z' = fst Zs
      /\ s' = compile RL (snd Zs) a
      /\ n' = countTrue (getAnn ⊝ (take n ans)).
Proof.
  intros Get.
  general induction ans; destruct F as [|[Z s] ?]; simpl in *; isabsurd.
  - cases in Get.
    + inv Get.
      * eauto 20 using get.
      * clear Get. edestruct IHans as [Zs [a' [n' [lv ?]]]]; eauto; dcr; subst.
        exists Zs, a', (S n'). simpl; rewrite <- Heq; eauto 20 using get.
    + edestruct IHans as [Zs [a' [n [lv ?]]]]; eauto; dcr; subst.
      exists Zs, a', (S n). simpl; rewrite <- Heq; eauto 20 using get.
Qed.

Lemma compile_occurVars RL s uc
  : occurVars (compile RL s uc) ⊆ occurVars s.
Proof.
  revert RL uc.
  sind s; destruct s; intros RL uc; destruct uc; simpl; eauto.
  - rewrite IH; eauto.
  - repeat cases; simpl; repeat rewrite IH; eauto with cset.
  - cases.
    + rewrite IH; eauto.
    + rewrite Heq; clear Heq; simpl.
      eapply incl_union_lr; eauto.
      eapply list_union_incl; eauto with cset.
      intros; inv_get. destruct x as [Z s'].
      edestruct compileF_get_inv; eauto; dcr; subst.
      eapply incl_list_union. eauto using map_get_1.
      simpl. rewrite IH; eauto.
Qed.

Lemma compile_freeVars RL s uc
  : freeVars (compile RL s uc) ⊆ freeVars s.
Proof.
  revert RL uc.
  sind s; destruct s; intros RL uc; destruct uc; simpl; eauto.
  - rewrite IH; eauto.
  - repeat cases; simpl; repeat rewrite IH; eauto with cset.
  - cases.
    + rewrite IH; eauto.
    + rewrite Heq; clear Heq; simpl.
      eapply incl_union_lr; eauto.
      eapply list_union_incl; eauto with cset.
      intros; inv_get. destruct x as [Z s'].
      edestruct compileF_get_inv; eauto; dcr; subst.
      eapply incl_list_union. eauto using map_get_1.
      simpl. rewrite IH; eauto.
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
  intros LEN. rewrite fst_zip_pair; eauto with len.
Qed.

Lemma getAnn_take_eq X Y Y' (F:list (Y * Y')) (als:list (ann X)) k a LV
  : ❬F❭ = ❬als❭
    -> get als k a
    -> getAnn ⊝ take k als = fst ⊝ take k (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ LV).
Proof.
  intros LEN Get.
  rewrite take_app_lt; eauto with len.
  repeat rewrite map_take.
  rewrite fst_zip_pair; eauto with len.
Qed.

Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> ?B = ?C |- _ ] =>
  specialize (H' H); subst
| [ H : op2bool ?e = Some true , H' : op2bool ?e <> Some false -> ?B = ?C |- _ ] =>
  let H'' := fresh "H" in
  assert (H'':op2bool e <> Some false) by congruence;
    specialize (H' H''); subst
end.

Hint Extern 5 =>
match goal with
| [ H : Is_true ?B, EQ : ?A = ?B |- Is_true ?A] => rewrite EQ; eapply H
| [ H : Is_true ?B, EQ : ?B = ?A |- Is_true ?A] => rewrite <- EQ; eapply H
end.

Lemma compileF_nil_als_false RL F als (LEN:❬F❭ = ❬als❭)
  : nil = compileF compile RL F als
    -> forall n a, get als n a -> getAnn a = false.
Proof.
  length_equify.
  general induction LEN; simpl in *.
  - isabsurd.
  - destruct x as [Z s]; simpl in *.
    cases in H.
    + inv H.
    + inv H0; eauto.
Qed.

Lemma compileF_not_nil_exists_true RL F als (LEN:❬F❭ = ❬als❭)
  : nil <> compileF compile RL F als
    -> exists n a, get als n a /\ getAnn a.
Proof.
  length_equify.
  general induction LEN; simpl in *.
  - isabsurd.
  - destruct x as [Z s]; simpl in *.
    cases in H.
    + eexists 0, y; split; eauto using get.
      rewrite <- Heq; eauto.
    + edestruct IHLEN; dcr; eauto 20 using get.
Qed.

Lemma trueIsCalled_compileF_not_nil (i : sc)
      (s : stmt) (slv : ann bool) k F als RL x
  : unreachable_code i (getAnn ⊝ als ++ RL) s slv
    -> getAnn slv
    -> trueIsCalled s (LabI k)
    -> get als k x
    -> ❬F❭ = ❬als❭
    -> nil = compileF compile (getAnn ⊝ als ++ RL) F als
    -> False.
Proof.
  intros UC Ann IC Get Len.
  assert (LenNEq:length (compileF compile (getAnn ⊝ als ++ RL) F als)
                 <> 0). {
    rewrite compileF_length; eauto.
    edestruct (unreachable_code_trueIsCalled UC IC); eauto; simpl in *; dcr.
    inv_get.
    eapply countTrue_exists. eapply map_get_eq; eauto.
    eapply Is_true_eq_true; eauto. rewrite <- H1; eauto.
  }
  intros EQ. eapply LenNEq. rewrite <- EQ. reflexivity.
Qed.

Hint Resolve Is_true_eq_true.

Lemma DCE_callChain RL F als t alt l' k ZsEnd aEnd n
      (IH : forall k Zs,
          get F k Zs ->
       forall (RL : 〔bool〕) (lv : ann bool) (n : nat),
       unreachable_code SoundAndComplete RL (snd Zs) lv ->
       trueIsCalled (snd Zs) (LabI n) ->
       getAnn lv ->
       trueIsCalled (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (UC:unreachable_code SoundAndComplete (getAnn ⊝ als ++ RL) t alt)
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       unreachable_code SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
  (Ann: getAnn alt)
  (IC: trueIsCalled t (LabI l'))
  (CC: callChain trueIsCalled F (LabI l') (LabI k))
  (GetF: get F k ZsEnd)
  (ICEnd: trueIsCalled (snd ZsEnd) (LabI (❬F❭ + n)))
  (GetAls: get als k aEnd)
: callChain trueIsCalled
            (compileF compile (getAnn ⊝ als ++ RL) F als)
            (LabI (countTrue (take l' (getAnn ⊝ als ++ RL))))
            (LabI (countTrue (getAnn ⊝ als) +
                   countTrue (take n RL))).
Proof.
  general induction CC.
  - exploit unreachable_code_trueIsCalled as IMPL; try eapply IC; eauto.
    simpl in *; dcr; inv_get. rewrite H1 in Ann.
    exploit compileF_get; eauto.
    econstructor 2; [ | | econstructor 1 ].
    rewrite take_app_lt; eauto 20 with len.
    rewrite <- map_take. eauto. simpl.
    eapply IH in ICEnd; eauto.
    rewrite take_app_ge in ICEnd; eauto 20 with len.
    rewrite map_length in ICEnd.
    orewrite (❬F❭ + n - ❬als❭ = n) in ICEnd. simpl.
    rewrite countTrue_app in ICEnd. eauto.
  - exploit unreachable_code_trueIsCalled; try eapply IC; eauto.
    simpl in *; dcr; inv_get. assert (getAnn x0).
    rewrite <- H4. eauto.
    exploit compileF_get; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_lt; eauto 20 with len.
    rewrite <- map_take. eauto.
    simpl.
    eapply IH in H0; eauto.
    eapply IHCC in H0; eauto.
Qed.

Lemma DCE_callChain' RL F als l' k
      (IH : forall k Zs,
          get F k Zs ->
       forall (RL : 〔bool〕) (lv : ann bool) (n : nat),
       unreachable_code SoundAndComplete RL (snd Zs) lv ->
       trueIsCalled (snd Zs) (LabI n) ->
       getAnn lv ->
       trueIsCalled (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       unreachable_code SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
  (Ann: get (getAnn ⊝ als ++ RL) l' true)
  (CC: callChain trueIsCalled F (LabI l') (LabI k))
: callChain trueIsCalled
            (compileF compile (getAnn ⊝ als ++ RL) F als)
            (LabI (countTrue (take l' (getAnn ⊝ als ++ RL))))
            (LabI (countTrue (take k (getAnn ⊝ als ++ RL)))).
Proof.
  general induction CC.
  - econstructor.
  - inv_get.
    exploit unreachable_code_trueIsCalled; try eapply H0; eauto.
    simpl in *; dcr; inv_get. assert (x0 = true).
    destruct (getAnn x), x0; isabsurd; eauto.
    exploit compileF_get; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_lt; eauto 20 with len.
    rewrite <- map_take. eauto.
    simpl.
    eapply IH in H0; eauto. rewrite <- H3. eauto.
    subst. eauto.
Qed.

Lemma DCE_trueIsCalled RL s lv n
  : unreachable_code SoundAndComplete RL s lv
    -> trueIsCalled s (LabI n)
    -> getAnn lv
    -> trueIsCalled (compile RL s lv) (LabI (countTrue (take n RL))).
Proof.
  intros Live IC.
  revert RL lv n Live IC.
  sind s; simpl; intros; invt unreachable_code; invt trueIsCalled;
    simpl in *; eauto using trueIsCalled.
  - repeat cases; eauto using trueIsCalled.
  - repeat cases; eauto using trueIsCalled.
  - eapply callChain_cases in H6. destruct H6; subst.
    + cases.
      * exploit (IH t) as IHt; eauto.
        rewrite take_app_ge in IHt; eauto 20 with len.
        rewrite map_length in IHt.
        orewrite (❬F❭ + n - ❬als❭ = n) in IHt. simpl.
        rewrite countTrue_app in IHt.
        erewrite <- compileF_length in IHt; eauto.
        erewrite <- Heq in IHt. eauto.
      * rewrite Heq. econstructor. econstructor 1.
        exploit (IH t) as IHt; eauto.
        rewrite compileF_length; eauto. simpl.
        rewrite take_app_ge in IHt; eauto 20 with len.
        rewrite map_length in IHt.
        orewrite (❬F❭ + n - ❬als❭ = n) in IHt. simpl.
        rewrite countTrue_app in IHt. eauto.
    + destruct H2 as [? [? [? ?]]]; dcr.
      destruct l' as [l'].
      cases.
      * exfalso. inv_get.
        eapply get_in_range in H2. destruct H2. inv_get.
        eapply trueIsCalled_compileF_not_nil.
        eapply H0. eauto. eauto. eauto. eauto. eauto.
      * rewrite Heq; clear Heq p b. inv_get.
        econstructor; eauto. simpl.
        rewrite compileF_length; eauto.
        eapply DCE_callChain; eauto.
Qed.


Lemma DCE_isCalledFrom RL F als t alt n (Len:❬F❭ = ❬als❭)
  : (forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       unreachable_code SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
    -> unreachable_code SoundAndComplete (getAnn ⊝ als ++ RL) t alt
    -> getAnn alt
    -> isCalledFrom trueIsCalled F t (LabI n)
    -> n < ❬F❭
    -> isCalledFrom trueIsCalled (compileF compile (getAnn ⊝ als ++ RL) F als)
                   (compile (getAnn ⊝ als ++ RL) t alt) (LabI (countTrue (getAnn ⊝ take n als))).
Proof.
  intros UCF UCt gAt ICF.
  destruct ICF as [[l'] [? ?]].
  exploit DCE_trueIsCalled; eauto.
  eexists; split; eauto.
  exploit DCE_callChain'; eauto using DCE_trueIsCalled.
  exploit unreachable_code_trueIsCalled; eauto.
  dcr; subst; simpl in *. rewrite H6 in gAt.
  destruct x; isabsurd; eauto.
  setoid_rewrite take_app_lt in H3 at 2.
  setoid_rewrite <- map_take in H3. eauto.
  eauto with len.
Qed.

Lemma DCE_noUnreachableCode RL s lv
  : unreachable_code SoundAndComplete RL s lv
    -> getAnn lv
    -> noUnreachableCode trueIsCalled (compile RL s lv).
Proof.
  intros Live GetAnn.
  induction Live; simpl; repeat cases; eauto using noUnreachableCode.
  - specialize (H NOTCOND0). specialize (H0 NOTCOND). subst.
    simpl in *. econstructor; eauto.
  - rewrite Heq; clear Heq.
    econstructor; eauto using noUnreachableCode.
    + intros. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' ?]]]; eauto; dcr; subst; simpl.
      simpl in *.
      eapply H2; eauto. rewrite H7; eauto.
    + intros. simpl in *.
      edestruct get_in_range as [Zs ?]; eauto. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' [lv' ?]]]]; eauto.
      dcr; subst; simpl.
      exploit H3 as ICF; eauto. rewrite H8; eauto.
      eapply DCE_isCalledFrom; eauto with len.
Qed.


Lemma DCE_paramsMatch i PL RL s lv
  : unreachable_code i RL s lv
    -> getAnn lv
    -> paramsMatch s PL
    -> paramsMatch (compile RL s lv) (filter_by (fun b => b) RL PL).
Proof.
  intros UC Ann PM.
  general induction UC; inv PM; simpl; repeat cases; eauto using paramsMatch.
  - specialize (H NOTCOND0). specialize (H0 NOTCOND). subst. simpl in *.
    econstructor; eauto.
  - simpl in *.
    exploit (get_filter_by (fun b => b) H H3). destruct a,b; isabsurd; eauto.
    rewrite map_id in H1.
    econstructor; eauto.
  - exploit IHUC; eauto.
    rewrite filter_by_app in H0; eauto with len.
    rewrite filter_by_nil in H0; eauto.
    intros; inv_get; eauto using compileF_nil_als_false.
  - rewrite Heq; clear Heq p b.
    econstructor.
    + intros ? [Z s] Get.
      eapply compileF_get_inv in Get; destruct Get; dcr; subst; simpl; eauto.
      exploit H2; eauto. rewrite H8; eauto.
      rewrite compileF_Z_filter_by, map_filter_by, <- filter_by_app; eauto with len.
    + rewrite compileF_Z_filter_by, map_filter_by, <- filter_by_app; eauto with len.
Qed.

Module I.

Instance SR : ProofRelationI (bool * params) := {
   ParamRelI G Z Z' := Z' = Z /\ snd G = Z;
   ArgRelI V V' G VL VL' := VL' = VL /\ length (snd G) = length VL /\ V = V';
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


Lemma inv_extend s L L' RL als f
(LEN: ❬s❭ = ❬als❭)
(H: forall (f : nat),
       get RL f true ->
       exists b b' : I.block, get L f b /\ get L' (countTrue (take f RL)) b')
(Get : get (getAnn ⊝ als ++ RL) f true)
  :  exists b b' : I.block, get (mapi I.mkBlock s ++ L) f b /\
                       get (mapi I.mkBlock (compileF compile (getAnn ⊝ als ++ RL) s als) ++ L') (countTrue (take f (getAnn ⊝ als ++ RL))) b'.
Proof.
  get_cases Get; inv_get.
  - exploit compileF_get; eauto.
    do 2 eexists; split; eauto using get_app, mapi_get_1.
    eapply get_app. eapply mapi_get_1.
    rewrite take_app_lt; eauto with len.
    rewrite <- map_take; eauto.
  - edestruct H as [b [b' [? ?]]]; eauto.
    exists b, b'; split.
    + eapply get_app_right; eauto.
      rewrite mapi_length.
      rewrite map_length.
      rewrite map_length in H1. omega.
    + eapply get_app_right; eauto.
      rewrite take_app_ge; eauto.
      rewrite countTrue_app.
      rewrite mapi_length.
      rewrite compileF_length; eauto.
Qed.

Lemma sim_I i ZL RL r L L' V s (a:ann bool) (Ann:getAnn a)
 (UC: unreachable_code i RL s a)
 (LSIM:labenv_sim Bisim (sim'r r) SR (pair ⊜ RL ZL) L L')
 (LenEq:❬ZL❭=❬RL❭)
  : (forall (f:nat),
          get RL f true
          -> exists (b b' : I.block),
            get L f b /\
            get L' (countTrue (take f RL)) b')
    -> sim'r r Bisim (L,V, s) (L',V, compile RL s a).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt unreachable_code; simpl in * |- *.
  - destruct e.
    + case_eq (op_eval V e); intros.
      * pone_step; eauto.
      * pno_step.
    + remember (omap (op_eval V) Y). symmetry in Heqo.
      destruct o.
      * pextern_step; eauto using agree_on_update_same, agree_on_incl; try congruence.
      * pno_step.
  - repeat cases.
    + edestruct (op2bool_val2bool V); eauto; dcr.
      pone_step_left. eauto.
    + edestruct (op2bool_val2bool V); eauto; dcr.
      pone_step_left; eauto.
    + remember (op_eval V e). symmetry in Heqo.
      destruct o.
      * case_eq (val2bool v); intros; pone_step; eauto.
      * pno_step.
  - assert (b=true). destruct a0, b; isabsurd; eauto. subst.
    edestruct H as [? [? [GetL GetL']]]; eauto using zip_get.
    remember (omap (op_eval V) Y). symmetry in Heqo.
    destruct o.
    + destruct x as [Z1 s1 n1], x0 as [Z2 s2 n2].
      edestruct LSIM as [? [? [? [ ? SIM]]]]; eauto; dcr.
      inv_get.
      assert (IndexRelI (pair ⊜ RL ZL) l (LabI (countTrue (take l RL)))).
      hnf; simpl. split; eauto using zip_get.
      rewrite map_take. rewrite fst_zip_pair. eauto. eauto.
      exploit (H4 l (LabI (countTrue (take l RL)))); eauto using zip_get.
      decide (❬Y❭=❬Z1❭).
      * eapply (SIM l (LabI (countTrue (take l RL)))); eauto using zip_get.
        simpl in *; dcr; subst.
        simpl; eauto with len.
      * pno_step. simpl in *; dcr; subst. congruence.
    + pno_step.
  - pno_step.
  - cases.
    + pone_step_left.
      eapply (IH s ltac:(eauto) i (fst ⊝ F ++ ZL)); eauto with len.
      * rewrite zip_app; eauto with len.
        eapply labenv_sim_extension with (F':=nil); eauto.
        -- intros; hnf; intros; isabsurd.
        -- intros; hnf; intros; isabsurd.
        -- hnf; split; eauto with len. split; [| split].
           ++ simpl. erewrite <- getAnn_eq; eauto.
             erewrite <- compileF_length; eauto. rewrite <- Heq. eauto.
           ++ simpl; intros; dcr; subst.
             rewrite <- zip_app in H7; eauto with len. inv_get.
             exploit compileF_nil_als_false; eauto. congruence.
           ++ simpl; intros; dcr; subst. omega.
      * intros.
        eapply get_app_cases in H0. destruct H0.
        exfalso. inv_get.
        assert (NEQ:length (compileF compile (getAnn ⊝ als ++ RL) F als)
                <> 0). {
          rewrite compileF_length; eauto.
          eapply countTrue_exists. rewrite <- EQ; eauto using map_get_1.
        }
        eapply NEQ. rewrite <- Heq. eauto.
        dcr. edestruct H as [? [? ?]]; eauto; dcr.
        do 2 eexists. split.
        eapply get_app_right; eauto. rewrite mapi_length; eauto with len.
        rewrite map_length.
        rewrite map_length in H4. omega.
        rewrite take_app_ge; eauto.
        rewrite countTrue_app.
        erewrite <- compileF_length; eauto. erewrite <- Heq. eauto.
    + rewrite Heq; clear Heq.
      pone_step. left.
      eapply (IH s ltac:(eauto) i (fst ⊝ F ++ ZL)); eauto with len.
      {
        + rewrite zip_app; eauto with len.
          eapply labenv_sim_extension; eauto.
          * intros. hnf; intros.
            hnf in H1. dcr. hnf in H9; dcr; subst.
            rewrite get_app_lt in H12; eauto using get_range.
            inv_get.
            exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H4; eauto.
            erewrite <- getAnn_take_eq in H5; eauto.
            simpl in *. get_functional.
            exploit H6; eauto.
            eapply (IH s0 ltac:(eauto) i (fst ⊝ F ++ ZL)); eauto with len.
            rewrite EQ; eauto.
            eauto 20 using inv_extend with len.
          * hnf; intros.
            hnf in H0. dcr; subst.
            rewrite get_app_lt in H10; eauto with len.
            inv_get; simpl.
            exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H1; eauto.
            erewrite <- getAnn_take_eq in H4; eauto.
            get_functional. eauto.
          * hnf. split; eauto with len.
            split.
            rewrite compileF_length; eauto. simpl.
            erewrite <- getAnn_eq; eauto with len.
            split. intros.
            hnf in H0; dcr; subst.
            rewrite compileF_length; eauto.
            rewrite <- zip_app in H7; eauto with len.
            inv_get.
            erewrite <- getAnn_take_eq; eauto with len.
            erewrite (take_eta n (getAnn ⊝ als)).
            rewrite countTrue_app.
            erewrite <- get_eq_drop; eauto using map_get_1.
            rewrite <- H0. simpl. rewrite map_take. omega.
            intros. rewrite compileF_length; eauto.
            hnf in H0; dcr; subst.
            rewrite map_take. rewrite map_app.
            rewrite map_zip.
            rewrite zip_map_fst; eauto with len.
            rewrite take_app_ge. rewrite countTrue_app. omega.
            rewrite map_length. omega.
      }
      intros; eapply inv_extend; eauto.
Qed.

Lemma sim_DCE i V s a
  : unreachable_code i nil s a
    -> getAnn a
    -> @sim I.state _ I.state _ Bisim (nil,V, s) (nil,V, compile nil s a).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_I i nil nil); eauto; isabsurd.
  hnf; repeat split; simpl; eauto 20 using @sawtooth; isabsurd.
Qed.

End I.

Fixpoint compile_live (s:stmt) (a:ann (set var)) (b:ann bool) : ann (set var) :=
  match s, a, b with
    | stmtLet x e s, ann1 lv an, ann1 _ bn =>
      ann1 lv (compile_live s an bn)
    | stmtIf e s t, ann2 lv ans ant, ann2 _ bns bnt =>
      if [op2bool e = Some true] then
        compile_live s ans bns
      else if [op2bool e = Some false ] then
        compile_live t ant bnt
      else
        ann2 lv (compile_live s ans bns) (compile_live t ant bnt)
    | stmtApp f Y, ann0 lv, _ => ann0 lv
    | stmtReturn x, ann0 lv, _ => ann0 lv
    | stmtFun F t, annF lv anF ant, annF _ bnF bnt =>
      let anF'' := zip (fun (Zs:params * stmt) ab =>
                         compile_live (snd Zs) (fst ab) (snd ab)) F (pair ⊜ anF bnF) in
      let anF' := filter_by (fun b => b) (getAnn ⊝ bnF) anF'' in
      match anF' with
      | nil => (compile_live t ant bnt)
      | _ => annF lv anF' (compile_live t ant bnt)
      end
    | _, a, _ => a
  end.


Lemma compile_live_incl i uci ZL LV RL s lv uc
  : true_live_sound i ZL LV s lv
    -> unreachable_code uci RL s uc
    -> getAnn (compile_live s lv uc) ⊆ getAnn lv.
Proof.
  intros LS UC.
  general induction LS; inv UC; simpl; eauto.
  - repeat cases; simpl; eauto.
    + rewrite H0; eauto.
    + rewrite H2; eauto.
  - cases.
    + rewrite IHLS; eauto.
    + rewrite Heq. simpl; eauto.
Qed.

Lemma DCE_live uci i ZL LV RL s uc lv
  : unreachable_code uci RL s uc
    -> getAnn uc
    -> true_live_sound i ZL LV s lv
    -> true_live_sound i (filter_by (fun b => b) RL ZL)
                      (filter_by (fun b => b) RL LV)
                      (compile RL s uc)
                      (compile_live s lv uc).
Proof.
  intros UC Ann LS.
  general induction LS; inv UC; simpl; eauto using true_live_sound.
  - econstructor; eauto using compile_live_incl with cset.
    intros. eapply H. destruct H1; eauto.
    left. eapply compile_live_incl; eauto.
  - repeat cases; eauto. econstructor; eauto; intros.
    + rewrite compile_live_incl; eauto.
    + rewrite compile_live_incl; eauto.
  - repeat get_functional. simpl in *.
    assert (❬take (labN l) RL❭ = ❬take (labN l) ZL❭).
    eapply get_range in H. eapply get_range in H7.
    repeat rewrite take_length_le; eauto. omega. omega.
    econstructor; eauto.
    exploit (get_filter_by (fun b => b) H7 H); eauto.
    destruct a, b; isabsurd; eauto.
    simpl. rewrite map_id in H5. eauto.
    exploit (get_filter_by (fun b => b) H7 H0); eauto.
    destruct a, b; isabsurd; eauto.
    simpl. rewrite map_id in H5. eauto.
  - cases.
    + exploit IHLS; eauto.
      assert (forall (n : nat) (b : bool), get (getAnn ⊝ als0) n b -> b = false).
      intros; inv_get; eauto using compileF_nil_als_false.
      rewrite !filter_by_app in H4; eauto with len.
      rewrite filter_by_nil in H4; eauto.
      setoid_rewrite filter_by_nil in H4 at 3; eauto.
      setoid_rewrite filter_by_nil at 3; eauto.
    + rewrite Heq. exploit compileF_not_nil_exists_true; eauto.
      rewrite <- Heq; congruence. clear Heq; dcr.
      cases. exfalso. refine (filter_by_not_nil _ _ _ _ _ (eq_sym Heq));
                        eauto 20 using Is_true_eq_true with len.
      rewrite Heq; clear Heq.
      econstructor; eauto.
      rewrite compileF_Z_filter_by; eauto with len.
      rewrite map_filter_by. rewrite <- !filter_by_app; eauto 20 with len.
      eapply true_live_sound_monotone.
      eapply IHLS; eauto 20 with len.
      rewrite !filter_by_app; eauto 20 with len. eapply PIR2_app; [ | reflexivity ].
      eapply PIR2_get; intros; inv_get.

      simpl.
      eapply compile_live_incl; eauto.
      repeat rewrite filter_by_length; eauto 20 with len.
      rewrite compileF_length; eauto. rewrite filter_by_length, map_id; eauto 20 with len.
      intros; inv_get.
      destruct Zs as [Z s].
      edestruct compileF_get_inv; eauto; dcr; subst. simpl.
      rewrite compileF_Z_filter_by; eauto with len.
      inv_get. rewrite <- filter_by_app; eauto with len.
      eapply true_live_sound_monotone.
      eapply H1; eauto 20 with len.
      rewrite !filter_by_app; eauto 20 with len. eapply PIR2_app; [ | reflexivity ].
      eapply PIR2_get; intros; inv_get. simpl.
      eapply compile_live_incl; eauto.
      rewrite map_length.
      repeat rewrite filter_by_length; eauto 20 with len.
      intros. inv_get.
      destruct Zs as [Z s].
      edestruct compileF_get_inv; eauto; dcr; subst. simpl.
      inv_get. cases; eauto.
      rewrite compile_live_incl; eauto.
      rewrite compile_live_incl; eauto.
Qed.