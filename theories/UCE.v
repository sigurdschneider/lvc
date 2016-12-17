Require Import CSet Util LengthEq Fresh Take MoreList Filter OUnion AllInRel.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness Reachability.
Require Import Sim SimTactics.
Require SimI SimF.

Set Implicit Arguments.
Unset Printing Records.

(** * Unreachable Code Elimination *)

(** ** The transformer *)

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

(** *** Properties of the transformer *)

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

Smpl Add
     match goal with
     | [ H: ❬?B❭ = ❬?C❭ |- context [ ❬compileF compile ?A ?B ?C❭ ] ] =>
       rewrite (@compileF_length A B C H)
     end : len.

Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> _ |- _ ] =>
  specialize (H' H); subst
| [ H : op2bool ?e = Some true , H' : op2bool ?e <> Some false -> _ |- _ ] =>
  let H'' := fresh "H" in
  assert (H'':op2bool e <> Some false) by congruence;
    specialize (H' H''); subst
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
    + edestruct IHLEN; dcr; eauto 20 using get.
Qed.


Lemma impb_elim (a b:bool)
  : impb a b -> a -> b.
Proof.
  intros. rewrite <- H. eauto.
Qed.

Hint Resolve impb_elim.

(** ** Correctness with respect to the imperative semantics IL/I *)

Module I.

  Import SimI.

Instance SR : ProofRelationI bool := {
   ParamRelI G Z Z' := Z' = Z;
   ArgRelI V V' G VL VL' := VL' = VL /\ V = V';
   Image AL := countTrue AL;
   IndexRelI AL n n' :=
     n' = countTrue (take n AL) /\ get AL n true
}.
- intros AL' AL n n' [H H']; subst.
  split.
  + clear H' H.
    general induction AL'; simpl.
    * orewrite (n - 0 = n). omega.
    * destruct n; simpl; eauto. cases; simpl; eauto.
  + rewrite get_app_ge in H'; eauto.
Defined.

Lemma compileF_separates RL F als (Len:❬F❭ = ❬als❭)
  : separates SR (getAnn ⊝ als) RL F (compileF compile (getAnn ⊝ als ++ RL) F als).
Proof.
  hnf; intros; split; [| split; [| split]].
  - eauto with len.
  - simpl. eauto with len.
  - rewrite Len; intros; hnf in H; dcr; subst; inv_get.
    len_simpl.
    rewrite take_app_le; eauto with len.
    erewrite (take_eta n (getAnn ⊝ als)) at 2.
    rewrite countTrue_app.
    erewrite <- get_eq_drop; eauto using map_get_1.
    rewrite EQ. simpl. omega.
  - rewrite Len; intros; simpl in *; dcr; subst.
    rewrite compileF_length; eauto.
    rewrite take_app_ge; eauto with len.
    rewrite countTrue_app. omega.
Qed.


Lemma compileF_indexwise_paramrel RL F als (Len:❬F❭ = ❬als❭)
  : indexwise_paramrel SR F (compileF compile (getAnn ⊝ als ++ RL) F als) (getAnn ⊝ als) RL.
Proof.
  hnf; intros.
  simpl in *; dcr; subst.
  rewrite get_app_lt in H4; eauto with len.
  inv_get; simpl.
  exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H2; eauto.
  simpl in *.
  erewrite take_app_le, <- map_take in H1; eauto with len.
  get_functional. eauto.
Qed.

Lemma sim_compile_fun_cases r RL L V s L' F als alt
  : sim r Bisim (mapi I.mkBlock F ++ L, V, s)
   (mapi I.mkBlock (compileF compile (getAnn ⊝ als ++ RL) F als) ++ L', V,
    compile (getAnn ⊝ als ++ RL) s alt)
-> sim r Bisim (L, V, stmtFun F s)
        (L', V,
         match compileF compile (getAnn ⊝ als ++ RL) F als with
         | nil => compile (getAnn ⊝ als ++ RL) s alt
         | _ :: _ =>
           stmtFun (compileF compile (getAnn ⊝ als ++ RL) F als) (compile (getAnn ⊝ als ++ RL) s alt)
         end).
Proof.
  intros. cases.
  - simpl in *. pone_step_left. eauto.
  - rewrite Heq in *; clear Heq.
    pone_step. left. eauto.
Qed.

Lemma sim_I RL r L L' V s (a:ann bool) (Ann:getAnn a)
 (RCH: reachability Sound RL s a)
 (LSIM:labenv_sim Bisim (sim r) SR RL L L')
  : sim r Bisim (L,V, s) (L',V, compile RL s a).
Proof.
  unfold sim. revert_except s.
  sind s; destruct s; simpl in *; intros; invt reachability; simpl in * |- *.
  - destruct e.
    + eapply (sim_let_op il_statetype_I); eauto.
    + eapply (sim_let_call il_statetype_I); eauto.
  - eapply (sim_if_elim il_statetype_I); intros; eauto.
  - assert (b=true). destruct a0, b; isabsurd; eauto. subst.
    eapply labenv_sim_app; eauto.
    + hnf; simpl. split; eauto using zip_get.
    + intros; simpl in *; subst. eauto 20.
  - pno_step.
  - eapply sim_compile_fun_cases.
    eapply (IH s); eauto with len.
    eapply labenv_sim_extension; eauto.
    + intros. hnf; intros; simpl in *; dcr; subst; inv_get.
      exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H5; eauto.
      erewrite take_app_le, <- map_take in H7; eauto with len.
      simpl in *. get_functional.
      exploit H4; eauto.
    + eapply compileF_indexwise_paramrel; eauto.
    + eapply compileF_separates; eauto.
Qed.

Lemma sim_UCE V s a
  : reachability Sound nil s a
    -> getAnn a
    -> @sim I.state _ I.state _ bot3 Bisim (nil,V, s) (nil,V, compile nil s a).
Proof.
  intros.
  eapply (@sim_I nil); eauto; isabsurd.
Qed.

End I.


(** ** Correctness with respect to the functional semantics IL *)
(** Functional here means that variables are lexically scoped binders instead of assignables. *)



Module F.

  Import SimF.

  Instance SR : ProofRelationF bool := {
   ParamRelF G Z Z' := Z' = Z;
   ArgRelF G VL VL' := VL' = VL;
   IndexRelF AL n n' :=
     n' = countTrue (take n AL) /\ get AL n true;
   Image AL := countTrue AL
}.
- intros AL' AL n n' [H H']; subst.
  split.
  + clear H' H.
    general induction AL'; simpl.
    * orewrite (n - 0 = n). omega.
    * destruct n; simpl; eauto. cases; simpl; eauto.
  + rewrite get_app_ge in H'; eauto.
Defined.


Lemma compileF_separates RL F als (Len:❬F❭ = ❬als❭)
  : separates SR (getAnn ⊝ als) RL F (compileF compile (getAnn ⊝ als ++ RL) F als).
Proof.
  hnf; intros; split; [| split; [| split]].
  - eauto with len.
  - simpl. rewrite compileF_length; eauto.
  - rewrite Len; intros; hnf in H; dcr; subst; inv_get.
    rewrite compileF_length; eauto.
    rewrite take_app_le; eauto with len.
    erewrite (take_eta n (getAnn ⊝ als)) at 2.
    rewrite countTrue_app.
    erewrite <- get_eq_drop; eauto using map_get_1.
    rewrite EQ. simpl. omega.
  - rewrite Len; intros; simpl in *; dcr; subst.
    rewrite compileF_length; eauto.
    rewrite take_app_ge; eauto with len.
    rewrite countTrue_app. omega.
Qed.

Lemma compileF_indexwise_paramrel RL F als (Len:❬F❭ = ❬als❭)
  : indexwise_paramrel SR F (compileF compile (getAnn ⊝ als ++ RL) F als) (getAnn ⊝ als) RL.
Proof.
  hnf; intros.
  simpl in *; dcr; subst.
  rewrite get_app_lt in H4; eauto with len.
  inv_get; simpl.
  exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H2; eauto.
  simpl in *.
  erewrite take_app_le, <- map_take in H1; eauto with len.
  get_functional. eauto.
Qed.

Lemma sim_compile_fun_cases r RL L V s L' F als alt
  : sim r Bisim (mapi (F.mkBlock V) F ++ L, V, s)
   (mapi (F.mkBlock V) (compileF compile (getAnn ⊝ als ++ RL) F als) ++ L', V,
    compile (getAnn ⊝ als ++ RL) s alt)
-> sim r Bisim (L, V, stmtFun F s)
        (L', V,
         match compileF compile (getAnn ⊝ als ++ RL) F als with
         | nil => compile (getAnn ⊝ als ++ RL) s alt
         | _ :: _ =>
           stmtFun (compileF compile (getAnn ⊝ als ++ RL) F als) (compile (getAnn ⊝ als ++ RL) s alt)
         end).
Proof.
  intros. cases.
  - simpl in *. pone_step_left. eauto.
  - rewrite Heq in *; clear Heq.
    pone_step. left. eauto.
Qed.

Lemma sim_F RL r L L' V s (a:ann bool) (Ann:getAnn a)
 (UC: reachability Sound RL s a)
 (LSIM:labenv_sim Bisim (sim r) SR RL L L')
  : sim r Bisim (L,V, s) (L',V, compile RL s a).
Proof.
  unfold sim. revert_except s.
  sind s; destruct s; simpl in *; intros; invt reachability; simpl in * |- *.
  - destruct e.
    + eapply (sim_let_op il_statetype_F); eauto.
    + eapply (sim_let_call il_statetype_F); eauto.
  - eapply (sim_if_elim il_statetype_F); intros; eauto.
  - assert (b=true). destruct a0, b; isabsurd; eauto. subst.
    eapply labenv_sim_app; eauto.
    + hnf; simpl. split; eauto using zip_get.
    + intros; simpl in *; subst. eauto 20.
  - pno_step.
  - eapply sim_compile_fun_cases.
    eapply (IH s); eauto with len.
    eapply labenv_sim_extension; eauto.
    + intros. hnf; intros; simpl in *; dcr; subst; inv_get.
      exploit (compileF_get (getAnn ⊝ als ++ RL)); try eapply H5; eauto.
      erewrite take_app_le, <- map_take in H7; eauto with len.
      simpl in *. get_functional.
      exploit H4; eauto.
    + eapply compileF_indexwise_paramrel; eauto.
    + eapply compileF_separates; eauto.
Qed.

Lemma sim_UCE V s a
  : reachability Sound nil s a
    -> getAnn a
    -> @sim F.state _ F.state _ bot3 Bisim (nil,V, s) (nil,V, compile nil s a).
Proof.
  intros.
  eapply (@sim_F nil); eauto; isabsurd.
Qed.


End F.

(** ** UCE respects parameter/argument matching *)

Lemma UCE_paramsMatch PL RL s lv
  : reachability Sound RL s lv
    -> getAnn lv
    -> paramsMatch s PL
    -> paramsMatch (compile RL s lv) (filter_by (fun b => b) RL PL).
Proof.
  intros UC Ann PM.
  general induction UC; inv PM; simpl in * |- *; repeat cases; eauto using paramsMatch.
  - specialize (H NOTCOND0). specialize (H0 NOTCOND). subst. simpl in *.
    econstructor; eauto.
  - simpl in *.
    exploit (get_filter_by (fun b => b) H H3). destruct a,b; isabsurd; eauto.
    rewrite map_id in H1.
    econstructor; eauto.
  - exploit IHUC as IH; eauto.
    rewrite filter_by_app in IH; eauto with len.
    rewrite filter_by_nil in IH; eauto.
    intros; inv_get; eauto using compileF_nil_als_false.
  - rewrite Heq; clear Heq p b0.
    econstructor.
    + intros ? [Z s] Get.
      eapply compileF_get_inv in Get; destruct Get; dcr; subst; simpl; eauto.
      exploit H2; eauto.
      rewrite compileF_Z_filter_by, map_filter_by, <- filter_by_app; eauto with len.
    + rewrite compileF_Z_filter_by, map_filter_by, <- filter_by_app; eauto with len.
Qed.


(** ** Reconstruction of Liveness Information after UCE *)
(** In this section we show that liveness information can
    be transformed alongside UCE.
    This means that liveness recomputation after the transformation is not neccessary. *)

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
    -> reachability uci RL s uc
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

Lemma UCE_live i ZL LV RL s uc lv
  : reachability Sound RL s uc
    -> getAnn uc
    -> true_live_sound i ZL LV s lv
    -> true_live_sound i (filter_by (fun b => b) RL ZL)
                      (filter_by (fun b => b) RL LV)
                      (compile RL s uc)
                      (compile_live s lv uc).
Proof.
  intros UC Ann LS.
  general induction LS; inv UC; simpl in *; eauto using true_live_sound.
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
      assert (forall (n : nat) (b : bool), get (getAnn ⊝ als0) n b -> b = false). {
        intros; inv_get; eauto using compileF_nil_als_false.
      }
      rewrite !filter_by_app in H4; eauto with len.
      rewrite filter_by_nil in H4; eauto.
      setoid_rewrite filter_by_nil in H4 at 3; eauto.
      setoid_rewrite filter_by_nil at 3; eauto.
    + rewrite Heq. exploit compileF_not_nil_exists_true; eauto.
      rewrite <- Heq; congruence. clear Heq; dcr.
      cases.
      * exfalso. refine (filter_by_not_nil _ _ _ _ _ (eq_sym Heq));
                        eauto 20 using Is_true_eq_true with len.
      * rewrite Heq; clear Heq.
        econstructor; eauto.
        -- rewrite compileF_Z_filter_by; eauto with len.
           rewrite map_filter_by. rewrite <- !filter_by_app; eauto 20 with len.
           eapply true_live_sound_monotone.
           eapply IHLS; eauto 20 with len.
           rewrite !filter_by_app; eauto 20 with len.
           eapply PIR2_app; [ | reflexivity ].
           eapply PIR2_get; intros; inv_get.
           ++ simpl. eapply compile_live_incl; eauto.
           ++ eauto with len.
        -- eauto with len.
        -- intros; inv_get.
           destruct Zs as [Z s].
           edestruct compileF_get_inv; eauto; dcr; subst. simpl.
           rewrite compileF_Z_filter_by; eauto with len.
           inv_get. rewrite <- filter_by_app; eauto with len.
           eapply true_live_sound_monotone.
           ++ eapply H1; eauto 20 with len.
           ++ rewrite !filter_by_app; eauto 20 with len. eapply PIR2_app; [ | reflexivity ].
             eapply PIR2_get; intros; inv_get; simpl.
             ** eapply compile_live_incl; eauto.
             ** eauto with len.
        -- intros. inv_get.
           destruct Zs as [Z s].
           edestruct compileF_get_inv; eauto; dcr; subst. simpl.
           inv_get. cases; eauto.
           rewrite compile_live_incl; eauto.
        -- rewrite compile_live_incl; eauto.
Qed.

(** ** Completeness of Reachability *)
(** We show that if the analysis was complete, no unreachable code is left in the program *)

Lemma trueIsCalled_compileF_not_nil
      (s : stmt) (slv : ann bool) k F als RL x
  : reachability Sound (getAnn ⊝ als ++ RL) s slv
    -> getAnn slv
    -> isCalled true s (LabI k)
    -> get als k x
    -> ❬F❭ = ❬als❭
    -> nil = compileF compile (getAnn ⊝ als ++ RL) F als
    -> False.
Proof.
  intros UC Ann IC Get Len.
  assert (LenNEq:length (compileF compile (getAnn ⊝ als ++ RL) F als)
                 <> 0). {
    rewrite compileF_length; eauto.
    edestruct (reachability_trueIsCalled UC IC); eauto; simpl in *; dcr.
    inv_get.
    eapply countTrue_exists. eapply map_get_eq; eauto.
  }
  intros EQ. eapply LenNEq. rewrite <- EQ. reflexivity.
Qed.

Hint Resolve Is_true_eq_true.

Lemma UCE_callChain RL F als t alt l' k ZsEnd aEnd n
      (IH : forall k Zs,
          get F k Zs ->
       forall (RL : 〔bool〕) (lv : ann bool) (n : nat),
       reachability SoundAndComplete RL (snd Zs) lv ->
       (isCalled true) (snd Zs) (LabI n) ->
       getAnn lv ->
       (isCalled true) (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (UC:reachability SoundAndComplete (getAnn ⊝ als ++ RL) t alt)
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       reachability SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
  (Ann: getAnn alt)
  (IC: isCalled true t (LabI l'))
  (CC: callChain (isCalled true) F (LabI l') (LabI k))
  (GetF: get F k ZsEnd)
  (ICEnd: (isCalled true) (snd ZsEnd) (LabI (❬F❭ + n)))
  (GetAls: get als k aEnd)
: callChain (isCalled true)
            (compileF compile (getAnn ⊝ als ++ RL) F als)
            (LabI (countTrue (take l' (getAnn ⊝ als ++ RL))))
            (LabI (countTrue (getAnn ⊝ als) +
                   countTrue (take n RL))).
Proof.
  general induction CC.
  - exploit reachability_trueIsCalled as IMPL; try eapply IC; eauto.
    simpl in *; dcr; inv_get. rewrite H1 in Ann.
    exploit compileF_get; eauto.
    econstructor 2; [ | | econstructor 1 ].
    + rewrite take_app_le; eauto 20 with len.
    + simpl.
      eapply IH in ICEnd; eauto.
      rewrite take_app_ge in ICEnd; eauto 20 with len.
      rewrite map_length in ICEnd.
      orewrite (❬F❭ + n - ❬als❭ = n) in ICEnd. simpl.
      rewrite countTrue_app in ICEnd. eauto.
  - exploit reachability_trueIsCalled; try eapply IC; eauto.
    simpl in *; dcr; inv_get.
    assert (getAnn x0). {
      rewrite <- H4. eauto.
    }
    exploit compileF_get; try eapply H1; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_le; eauto 20 with len.
    simpl.
    eapply IH in H0; eauto.
    eapply IHCC in H0; eauto.
Qed.

Lemma UCE_callChain' RL F als l' k
      (IH : forall k Zs,
          get F k Zs ->
       forall (RL : 〔bool〕) (lv : ann bool) (n : nat),
       reachability SoundAndComplete RL (snd Zs) lv ->
       (isCalled true) (snd Zs) (LabI n) ->
       getAnn lv ->
       (isCalled true) (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       reachability SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
  (Ann: get (getAnn ⊝ als ++ RL) l' true)
  (CC: callChain (isCalled true) F (LabI l') (LabI k))
: callChain (isCalled true)
            (compileF compile (getAnn ⊝ als ++ RL) F als)
            (LabI (countTrue (take l' (getAnn ⊝ als ++ RL))))
            (LabI (countTrue (take k (getAnn ⊝ als ++ RL)))).
Proof.
  general induction CC.
  - econstructor.
  - inv_get.
    exploit reachability_trueIsCalled; try eapply H0; eauto.
    simpl in *; dcr; inv_get. assert (x0 = true).
    destruct (getAnn x), x0; isabsurd; eauto.
    exploit compileF_get; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_le; eauto 20 with len.
    eapply IH in H0; eauto.
    subst. eauto.
Qed.

Lemma UCE_trueIsCalled RL s lv n
  : reachability SoundAndComplete RL s lv
    -> isCalled true s (LabI n)
    -> getAnn lv
    -> isCalled true (compile RL s lv) (LabI (countTrue (take n RL))).
Proof.
  intros Live IC.
  revert RL lv n Live IC.
  sind s; simpl; intros; invt reachability; invt isCalled;
    simpl in *; eauto using isCalled.
  - repeat cases; eauto using isCalled.
  - repeat cases; eauto using isCalled.
  - eapply callChain_cases in H8. destruct H8; subst.
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
    + destruct H6 as [? [? [? ?]]]; dcr.
      destruct l' as [l'].
      cases.
      * exfalso. inv_get.
        eapply get_in_range in H2. destruct H2. inv_get.
        eapply (@trueIsCalled_compileF_not_nil t); eauto.
      * rewrite Heq; clear Heq p b. inv_get.
        econstructor; eauto. simpl.
        rewrite compileF_length; eauto.
        eapply UCE_callChain; eauto.
Qed.


Lemma UCE_isCalledFrom RL F als t alt n (Len:❬F❭ = ❬als❭)
  : (forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       reachability SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
    -> reachability SoundAndComplete (getAnn ⊝ als ++ RL) t alt
    -> getAnn alt
    -> isCalledFrom (isCalled true) F t (LabI n)
    -> n < ❬F❭
    -> isCalledFrom (isCalled true) (compileF compile (getAnn ⊝ als ++ RL) F als)
                   (compile (getAnn ⊝ als ++ RL) t alt) (LabI (countTrue (getAnn ⊝ take n als))).
Proof.
  intros UCF UCt gAt ICF.
  destruct ICF as [[l'] [? ?]].
  exploit UCE_trueIsCalled; eauto.
  eexists; split; eauto.
  exploit UCE_callChain'; eauto using UCE_trueIsCalled.
  exploit reachability_trueIsCalled; eauto.
  dcr; subst; simpl in *. rewrite H6 in gAt.
  destruct x; isabsurd; eauto.
  setoid_rewrite take_app_le in H3 at 2.
  setoid_rewrite <- map_take in H3. eauto.
  rewrite map_length. omega.
Qed.

Lemma UCE_noUnreachableCode RL s lv
  : reachability SoundAndComplete RL s lv
    -> getAnn lv
    -> noUnreachableCode (isCalled true) (compile RL s lv).
Proof.
  intros Live GetAnn.
  induction Live; simpl in *; repeat cases; eauto using noUnreachableCode.
  - specialize (H NOTCOND0). specialize (H0 NOTCOND). subst.
    simpl in *. econstructor; eauto.
  - rewrite Heq; clear Heq.
    econstructor; eauto using noUnreachableCode.
    + intros. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' ?]]]; eauto; dcr; subst; simpl.
      simpl in *.
      eapply H2; eauto.
    + intros. simpl in *.
      edestruct get_in_range as [Zs ?]; eauto. destruct Zs as [Z' s'].
      edestruct compileF_get_inv as [Zs' [a [n' [lv' ?]]]]; eauto.
      dcr; subst; simpl.
      exploit H3 as ICF; eauto.
      eapply UCE_isCalledFrom; eauto with len.
Qed.

Require Import AppExpFree.

Lemma UCE_app_expfree LVZL s lv
: app_expfree s
  -> app_expfree (compile LVZL s lv).
Proof.
  intros AEF.
  general induction AEF; destruct lv; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      repeat cases; eauto using app_expfree.
  - rewrite Heq. econstructor; intros; inv_get; eauto.
    destruct Zs; edestruct compileF_get_inv; eauto; dcr; subst.
    eapply H0; eauto.
Qed.

Require Import RenamedApart PE.

Fixpoint compile_renamedApart (s:stmt) (a:ann (set var * set var)) (b:ann bool)
  : ann (set var * set var) :=
  match s, a, b with
  | stmtLet x e s, ann1 (D, _) an, ann1 _ bn =>
    let an' := compile_renamedApart s an bn in
    ann1 (D, {x; snd (getAnn an')}) an'
  | stmtIf e s t, ann2 (D, _) ans ant, ann2 _ bns bnt =>
    let ans' := compile_renamedApart s ans bns in
    let ant' := compile_renamedApart t ant bnt in
    if [op2bool e = Some true] then ans'
    else if [op2bool e = Some false ] then ant'
         else ann2 (D, snd (getAnn ans') ∪ snd (getAnn ant')) ans' ant'
  | stmtApp f Y, ann0 lv, _ => ann0 lv
  | stmtReturn x, ann0 lv, _ => ann0 lv
  | stmtFun F t, annF (D, _) anF ant, annF _ bnF bnt =>
    let anF'' := zip (fun (Zs:params * stmt) ab =>
                       compile_renamedApart (snd Zs) (fst ab) (snd ab)) F (pair ⊜ anF bnF) in
    let anF' := filter_by (fun b => b) (getAnn ⊝ bnF) anF'' in
    let bnt' := compile_renamedApart t ant bnt in
    match anF' with
    | nil => bnt'
    | _ => annF (D, list_union (defVars ⊜ (filter_by (fun b => b) (getAnn ⊝ bnF) F) anF') ∪ snd (getAnn bnt')) anF' bnt'
    end
  | _, a, _ => a
  end.

Lemma compile_renamedApart_pes RL s an al
  : renamedApart s an
    -> reachability Sound RL s al
    -> prod_eq Equal Subset (getAnn (compile_renamedApart s an al)) (getAnn an).
Proof.
  intros RA RCH.
  time (general induction RA; inv RCH; simpl in *; repeat cases; simpl; eauto).
  - econstructor; eauto.
    rewrite IHRA; eauto. rewrite H1, H2; eauto.
  - rewrite IHRA1, H2; eauto.
    econstructor; eauto. rewrite <- H1; eauto.
  - rewrite IHRA2, H3; eauto. econstructor; eauto.
    rewrite <- H1. eauto.
  - econstructor; eauto.
    rewrite IHRA1, IHRA2; eauto. rewrite <- H1, H2, H3; eauto.
  - rewrite IHRA; eauto. rewrite H4. econstructor; eauto.
    rewrite <- H5; eauto.
  - econstructor; eauto.
    rewrite Heq. clear Heq. rewrite IHRA, H4, <- H5; eauto. simpl.
    eapply incl_union_lr; eauto.
    eapply list_union_incl; intros; eauto with cset.
    inv_get.
    eapply incl_list_union.
    instantiate (2:=posOfTrue n (getAnn ⊝ als)).
    eauto using zip_get.
    unfold defVars; simpl.
    rewrite H1; eauto; eauto.
Qed.

Lemma UCE_renamedApart RL s lv G
  : renamedApart s G
    -> reachability Sound RL s lv
    -> renamedApart (compile RL s lv) (compile_renamedApart s G lv).
Proof.
  intros RA RCH.
  general induction RCH; inv RA; simpl; eauto using renamedApart.
  - econstructor; eauto. reflexivity.
    eapply pe_eta_split. econstructor; eauto.
    rewrite compile_renamedApart_pes; eauto.
    eapply (prod_eq_proj1 H8); eauto.
  - repeat cases; eauto using renamedApart.
    simpl in *.
    econstructor; try reflexivity; eauto.
    eapply disj_incl; eauto.
    rewrite compile_renamedApart_pes, H12; eauto.
    rewrite compile_renamedApart_pes, H13; eauto.
    eapply pe_eta_split; econstructor; eauto.
    rewrite compile_renamedApart_pes, H12; eauto.
    eapply pe_eta_split; econstructor; eauto.
    rewrite compile_renamedApart_pes, H13; eauto.
  - cases.
    rewrite filter_by_nil; eauto.
    intros; inv_get; eauto using compileF_nil_als_false.
    rewrite Heq.
    cases.
    + exfalso. symmetry in Heq0.
      edestruct compileF_not_nil_exists_true; eauto; dcr.
      rewrite <- Heq. congruence.
      eapply filter_by_not_nil in Heq0; eauto 20 with len.
    + rewrite Heq0.
      eapply renamedApartLet with (Dt:=snd (getAnn (compile_renamedApart t ant alt)));
        eauto 20 with len.
      * intros; inv_get; eauto. destruct Zs.
        edestruct (compileF_get_inv _ _ _ H5); eauto; dcr; subst.
        rewrite map_take in *.
        rewrite posOfTrue_countTrue in *; eauto using map_get_eq. repeat get_functional.
        eapply H2; eauto.
      * hnf; intros; inv_get. destruct a0.
        edestruct (compileF_get_inv _ _ _ H5); eauto; dcr; subst.
        rewrite map_take in *.
        rewrite posOfTrue_countTrue in *; eauto using map_get_eq. repeat get_functional.
        edestruct H9; dcr; eauto.
        hnf; simpl in *.
        split. rewrite compile_renamedApart_pes; eauto.
        split; eauto. split; eauto.
        rewrite !compile_renamedApart_pes, H12; eauto.
      * hnf; intros; inv_get. destruct x, x1.
        edestruct (compileF_get_inv _ _ _ H15); eauto; dcr; subst.
        edestruct (compileF_get_inv _ _ _ H16); eauto; dcr; subst.
        rewrite map_take in *.
        rewrite posOfTrue_countTrue in *; eauto using map_get_eq.
        repeat get_functional. simpl.
        exploit (H10 x10 x3); eauto using zip_get.
        intro; subst. rewrite map_take in *. congruence.
        unfold defVars in *; simpl.
        rewrite !compile_renamedApart_pes; eauto.
      * eapply pe_eta_split; econstructor.
        rewrite compile_renamedApart_pes, H12; eauto.
        reflexivity.
      * eapply eq_union_lr; eauto.
        eapply list_union_eq; eauto with len.
        intros; inv_get. unfold defVars; simpl. destruct x1.
        edestruct (compileF_get_inv _ _ _ H15); eauto; dcr; subst.
        rewrite map_take in *.
        rewrite posOfTrue_countTrue in *; eauto using map_get_eq.
        repeat get_functional. simpl. eauto.
Qed.