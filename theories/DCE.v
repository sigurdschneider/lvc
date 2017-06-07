Require Import CSet Util LengthEq Fresh Take MoreList Filter OUnion.
Require Import IL Annotation LabelsDefined Sawtooth Liveness.Liveness TrueLiveness Reachability.
Require Import Sim SimTactics SimI.

Set Implicit Arguments.
Unset Printing Records.

(** * Dead Code Elimination *)

(** ** The transformer *)

Definition filter_set (Z:params) (lv:set var) := List.filter (fun x => B[x ∈ lv]) Z.

Definition compileF (compile : forall (s:stmt) (a:ann bool) (b:ann (set var)), stmt)  :=
  fix f (F:〔params * stmt〕) (anF:list (ann bool)) (bnF:list (ann (set var))) :=
    match F, anF, bnF with
    | Zs::F, a::anF, b::bnF =>
      if getAnn a then (filter_set (fst Zs) (getAnn b), compile (snd Zs) a b) :: f F anF bnF
      else f F anF bnF
    | _, _, _ => nil
    end.

Fixpoint compile (RL:list bool) (LV:list ((set var) * params)) (s:stmt) (a:ann bool) (b:ann (set var))
         {struct s} :=
  match s, a, b with
  | stmtLet x e s, ann1 _ an, ann1 _ bn =>
    if [x ∈ getAnn bn \/ isCall e]
    then stmtLet x e (compile RL LV s an bn)
    else compile RL LV s an bn
  | stmtIf e s t, ann2 _ ans ant, ann2 _ bns bnt =>
    if [op2bool e = Some true] then
      (compile RL LV s ans bns)
    else if [ op2bool e = Some false ] then
           (compile RL LV t ant bnt)
         else
           stmtIf e (compile RL LV s ans bns) (compile RL LV t ant bnt)
  | stmtApp f Y, ann0 _, ann0 _ =>
    let lvZ := nth (counted f) LV (∅, nil) in
    stmtApp (LabI (countTrue (take (counted f) RL))) (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
  | stmtReturn x, ann0 _, ann0 _ => stmtReturn x
  | stmtFun F t, annF _ anF ant, annF _ bnF bnt =>
    let RL' := getAnn ⊝ anF ++ RL in
    let LV' := pair ⊜ (getAnn ⊝ bnF) (fst ⊝ F) ++ LV in
    let F' := compileF (compile RL' LV') F anF bnF in
    match F' with
    | nil => compile RL' LV' t ant bnt
    | _ => stmtFun F' (compile RL' LV' t ant bnt)
    end
  | s, _, _ => s
  end.

(** *** Properties of the transformer *)


Notation "a ⨝ b" := (zip pair a b) (at level 59, left associativity).

Lemma compileF_filter RL LV F anF bnF
  : compileF (compile RL LV) F anF bnF
    = map (fun p => (filter_set (fst (fst p)) (getAnn (snd (snd p))), compile RL LV (snd (fst p)) (fst (snd p)) (snd (snd p))))
          (filter (fun b => getAnn (fst (snd b))) (F ⨝ (anF ⨝ bnF))).
Proof.
  length_equify. general induction F; destruct anF; destruct bnF; simpl; eauto.
  - cases; simpl; f_equal; eauto.
Qed.

(*
Lemma compileF_Z_filter_by RL LV F anF bnF (LEN: ❬F❭ = ❬anF❭)
  : fst ⊝ compileF (compile RL LV) F anF bnF
    = filter_by (fun b => b) (getAnn ⊝ anF) (fst ⊝ F).
Proof.
  length_equify. general induction LEN; simpl; eauto.
  destruct x as [Z s]; cases; simpl; f_equal; eauto.
Qed.
 *)

Lemma compileF_get RL LV F n anF bnF Zs a b
  : get F n Zs
    -> get anF n a
    -> get bnF n b
    -> getAnn a = true
    -> get (compileF (compile RL LV) F anF bnF) (countTrue (getAnn ⊝ (take n anF)))
          (filter_set (fst Zs) (getAnn b), compile RL LV (snd Zs) a b).
Proof.
  intros GetF GetAnF GetBnF EQ.
  general induction anF; destruct F, bnF; isabsurd.
  - inv GetF; inv GetAnF; inv GetBnF.
    + simpl. rewrite EQ; eauto using get.
    + simpl. cases; simpl; eauto using get.
Qed.

(*
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
 *)

Lemma compileF_length RL LV F anF bnF
  : length F = length anF
    -> length F = length bnF
    -> length (compileF (compile RL LV) F anF bnF) = countTrue (getAnn ⊝ anF).
Proof.
  intros. length_equify.
  general induction H; inv H0; simpl; eauto.
  cases; simpl; eauto.
Qed.

Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> _ |- _ ] =>
  specialize (H' H); subst
| [ H : op2bool ?e = Some true , H' : op2bool ?e <> Some false -> _ |- _ ] =>
  let H'' := fresh "H" in
  assert (H'':op2bool e <> Some false) by congruence;
    specialize (H' H''); subst
end.

Lemma compileF_nil_als_false RL LV F anF bnF (LENa:❬F❭ = ❬anF❭) (LENb:❬F❭ = ❬bnF❭)
  : nil = compileF (compile RL LV) F anF bnF
    -> forall n a, get anF n a -> getAnn a = false.
Proof.
  length_equify.
  general induction LENa; inv LENb; simpl in *.
  - isabsurd.
  - cases in H.
    + inv H.
    + inv H0; eauto.
Qed.

Lemma compileF_not_nil_exists_true RL LV F anF bnF (LENa:❬F❭ = ❬anF❭) (LENb:❬F❭ = ❬bnF❭)
  : nil <> compileF (compile RL LV) F anF bnF
    -> exists n a, get anF n a /\ getAnn a.
Proof.
  length_equify.
  general induction LENa; inv LENb; simpl in *.
  - isabsurd.
  - simpl in *.
    cases in H.
    + eexists 0, y; split; eauto using get.
    + edestruct IHLENa; dcr; eauto 20 using get.
Qed.


Lemma impb_elim (a b:bool)
  : impb a b -> a -> b.
Proof.
  intros. rewrite <- H. eauto.
Qed.

Hint Resolve impb_elim.

(** ** Correctness with respect to the imperative semantics IL/I *)

Module I.

Instance SR : ProofRelationI (bool * ((set var) * params)) := {
   ParamRelI G Z Z' := Z' = (filter (fun x => B[x ∈ fst (snd G)]) Z) /\ snd (snd G) = Z;
   ArgRelI V V' G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst (snd G)]) (snd (snd G)) VL) /\
     length (snd (snd G)) = length VL /\
     agree_on eq ((fst (snd G)) \ of_list (snd (snd G))) V V';
   Image AL := countTrue (fst ⊝ AL);
   IndexRelI AL n n' :=
     n' = countTrue (take n (fst ⊝ AL))
     /\ exists x, get AL n x /\ fst x = true
}.
- intros AL' AL n n' [H H']; subst.
  split.
  + clear H' H.
    general induction AL'; simpl.
    * orewrite (n - 0 = n). omega.
    * destruct n; simpl; eauto. cases; simpl; eauto.
  + destruct H'; dcr.
    rewrite get_app_ge in H1; eauto.
Defined.

Lemma compileF_separates RL LV (F:list (params*stmt)) (anF:list (ann bool)) bnF (LENa:❬F❭ = ❬anF❭) (LENb:❬F❭ = ❬bnF❭)
  : separates SR ((getAnn ⊝ anF) ⨝ ((getAnn ⊝ bnF) ⨝ (fst ⊝ F))) (RL ⨝ LV) F
              (compileF (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV)) F anF bnF).
Proof.
  hnf; intros; split; [| split; [| split]].
  - eauto 20 with len.
  - simpl. rewrite compileF_length, fst_zip_pair; eauto with len.
  - rewrite LENa; intros; hnf in H; destruct H as [? [? ?]]; dcr; subst; inv_get.
    rewrite compileF_length; eauto with len.
    rewrite map_app.
    rewrite take_app_le; eauto with len.
    erewrite (take_eta n (getAnn ⊝ anF)) at 2.
    rewrite countTrue_app.
    rewrite fst_zip_pair; eauto with len.
    rewrite get_app_lt in H2; eauto 20 with len. inv_get; simpl in *.
    erewrite <- get_eq_drop; eauto using map_get_1.
    rewrite H3. simpl. omega.
  - rewrite LENa; intros; simpl in *; dcr; subst.
    destruct H as [? [? ?]]; subst; dcr.
    rewrite compileF_length; eauto.
    rewrite map_app.
    rewrite take_app_ge; eauto 20 with len.
    rewrite countTrue_app.
    rewrite fst_zip_pair; eauto with len. omega.
Qed.


Lemma compileF_indexwise_paramrel RL LV F anF bnF (LENa:❬F❭ = ❬anF❭) (LENb:❬F❭ = ❬bnF❭) (LEN:❬RL❭=❬LV❭)
  : indexwise_paramrel SR F (compileF (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV)) F anF bnF) ((getAnn ⊝ anF) ⨝ ((getAnn ⊝ bnF) ⨝ (fst ⊝ F))) (RL ⨝ LV).
Proof.
  hnf; intros. destruct H as [? [? ?]]; subst.
  simpl in *; dcr; subst; inv_get.
  rewrite get_app_lt in H; [| rewrite zip_length2; eauto 20 with len].
  inv_get; simpl in *.
  exploit (compileF_get (getAnn ⊝ anF ++ RL) (pair ⊜ (getAnn ⊝ bnF) (fst ⊝ F) ++ LV));
    try eapply H0; eauto.
  simpl in *.
  rewrite <- !zip_app in H1; eauto with len.
  rewrite fst_zip_pair in H1.
  erewrite take_app_le, <- map_take in H1; eauto with len.
  get_functional. eauto. eauto 20 with len.
Qed.


Lemma sim_compile_fun_cases t r RL LV L V V' s L' F anF bnF alt blt
  : sim r t (mapi I.mkBlock F ++ L, V, s)
   (mapi I.mkBlock (compileF (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV)) F anF bnF) ++ L', V',
    compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV) s alt blt)
-> sim r t (L, V, stmtFun F s)
        (L', V',
         match compileF (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV)) F anF bnF with
         | nil => compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV) s alt blt
         | _ :: _ =>
           stmtFun (compileF (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV)) F anF bnF) (compile (getAnn ⊝ anF ++ RL) ((getAnn ⊝ bnF) ⨝ (fst ⊝ F) ++ LV) s alt blt)
         end).
Proof.
  intros. cases.
  - simpl in *. pone_step_left. eauto.
  - rewrite Heq in *; clear Heq.
    pone_step. left. eauto.
Qed.

Lemma sim_I RL LV ZL r L L' V V' s (a:ann bool) (lv:ann ⦃var⦄) (Ann:getAnn a) (Len1:❬RL❭ = ❬LV❭)
      (Len2:❬RL❭ = ❬ZL❭)
  (RCH: reachability Sound RL s a)
  (AGR:agree_on eq (getAnn lv) V V')
  (TLS:true_live_sound Imperative ZL LV s lv)
  (LSIM:labenv_sim Sim (sim r) SR (RL ⨝ (LV ⨝ ZL)) L L')
  : sim r Sim (L,V, s) (L',V', compile RL (LV ⨝ ZL) s a lv).
Proof.
  unfold sim. revert_except s.
  sind s; destruct s; simpl in *; intros; invt reachability; invt true_live_sound; simpl in * |- *.
  - destruct e.
    + cases. exploit H8; eauto. inv H.
      * eapply (sim_let_op il_statetype_I);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H9. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H8; eauto. inv H.
      * eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_I); intros; eauto 20 using op_eval_live, agree_on_incl.
  - assert (b=true). destruct a0, b; isabsurd; eauto. subst.
    eapply labenv_sim_app; eauto using zip_get.
    + hnf; simpl. rewrite fst_zip_pair; eauto with len.
      split; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z0 H6);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros. eapply argsLive_liveSound; eauto.
        erewrite get_nth; eauto using zip_get; simpl.
        rewrite H11. eexists; split; eauto.
        repeat split; eauto using filter_filter_by_length.
        eapply agree_on_incl; eauto.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_compile_fun_cases.
    rewrite <- zip_app; [|eauto with len].
    eapply (IH s); eauto using agree_on_incl with len.
    rewrite !zip_app; eauto with len.
    eapply labenv_sim_extension; eauto with len.
    + intros. hnf; intros; simpl in *; dcr; subst; inv_get.
      destruct H0 as [? [? ?]]; dcr; subst; simpl in *.
      rewrite get_app_lt in H13; [| rewrite zip_length2; eauto with len].
      inv_get. simpl in *; eauto.
      exploit (compileF_get (getAnn ⊝ als ++ RL) (getAnn ⊝ als0 ⨝ fst ⊝ F ++ LV ⨝ ZL));
        try eapply H10; eauto.
      rewrite <- !zip_app in H11; eauto with len.
      rewrite <- !zip_app in H0; eauto with len.
      rewrite fst_zip_pair in H11; eauto 20 with len.
      erewrite take_app_le, <- map_take in H11; eauto with len.
      simpl in *. get_functional.
      exploit H4; eauto. exploit H9; eauto.
      eapply IH; eauto with len.
      eapply agree_on_update_filter'; eauto.
    + eapply compileF_indexwise_paramrel; eauto with len.
    + eapply compileF_separates; eauto with len.
Qed.

Lemma correct V s a b
  : reachability Sound nil s a
    -> true_live_sound Imperative nil nil s b
    -> getAnn a
    -> @sim I.state _ I.state _ bot3 Sim (nil,V, s) (nil,V, compile nil nil s a b).
Proof.
  intros.
  eapply (@sim_I nil nil nil); simpl; eauto; isabsurd.
Qed.

End I.


(** ** Correctness with respect to the functional semantics IL *)
(** Functional here means that variables are lexically scoped binders instead of assignables. *)

Module F.

  Require Import SimF.

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
  : separates SR (getAnn ⊝ als) RL F (compileF (compile (getAnn ⊝ als ++ RL)) F als).
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
  - exploit IHUC; eauto.
    rewrite filter_by_app in H4; eauto with len.
    rewrite filter_by_nil in H4; eauto.
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
           ++ repeat rewrite filter_by_length; eauto 20 with len.
        -- rewrite compileF_length; eauto. rewrite filter_by_length, map_id; eauto 20 with len.
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
             ** rewrite map_length.
                repeat rewrite filter_by_length; eauto 20 with len.
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
       trueIsCalled (snd Zs) (LabI n) ->
       getAnn lv ->
       trueIsCalled (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (UC:reachability SoundAndComplete (getAnn ⊝ als ++ RL) t alt)
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       reachability SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
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
  - exploit reachability_trueIsCalled as IMPL; try eapply IC; eauto.
    simpl in *; dcr; inv_get. rewrite H1 in Ann.
    exploit compileF_get; eauto.
    econstructor 2; [ | | econstructor 1 ].
    rewrite take_app_le; eauto 20 with len.
    rewrite <- map_take. eauto. simpl.
    eapply IH in ICEnd; eauto.
    rewrite take_app_ge in ICEnd; eauto 20 with len.
    rewrite map_length in ICEnd.
    orewrite (❬F❭ + n - ❬als❭ = n) in ICEnd. simpl.
    rewrite countTrue_app in ICEnd. eauto.
  - exploit reachability_trueIsCalled; try eapply IC; eauto.
    simpl in *; dcr; inv_get. assert (getAnn x0).
    rewrite <- H4. eauto.
    exploit compileF_get; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_le; eauto 20 with len.
    rewrite <- map_take. eauto.
    simpl.
    eapply IH in H0; eauto.
    eapply IHCC in H0; eauto.
Qed.

Lemma UCE_callChain' RL F als l' k
      (IH : forall k Zs,
          get F k Zs ->
       forall (RL : 〔bool〕) (lv : ann bool) (n : nat),
       reachability SoundAndComplete RL (snd Zs) lv ->
       trueIsCalled (snd Zs) (LabI n) ->
       getAnn lv ->
       trueIsCalled (compile RL (snd Zs) lv)
                (LabI (countTrue (take n RL))))
  (LEN: ❬F❭ = ❬als❭)
  (UCF:forall (n : nat) (Zs : params * stmt) (a : ann bool),
       get F n Zs ->
       get als n a ->
       reachability SoundAndComplete (getAnn ⊝ als ++ RL) (snd Zs) a)
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
    exploit reachability_trueIsCalled; try eapply H0; eauto.
    simpl in *; dcr; inv_get. assert (x0 = true).
    destruct (getAnn x), x0; isabsurd; eauto.
    exploit compileF_get; eauto.
    econstructor 2; [ | | ].
    rewrite take_app_le; eauto 20 with len.
    rewrite <- map_take. eauto.
    simpl.
    eapply IH in H0; eauto.
    subst. eauto.
Qed.

Lemma UCE_trueIsCalled RL s lv n
  : reachability SoundAndComplete RL s lv
    -> trueIsCalled s (LabI n)
    -> getAnn lv
    -> trueIsCalled (compile RL s lv) (LabI (countTrue (take n RL))).
Proof.
  intros Live IC.
  revert RL lv n Live IC.
  sind s; simpl; intros; invt reachability; invt trueIsCalled;
    simpl in *; eauto using trueIsCalled.
  - repeat cases; eauto using trueIsCalled.
  - repeat cases; eauto using trueIsCalled.
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
    -> isCalledFrom trueIsCalled F t (LabI n)
    -> n < ❬F❭
    -> isCalledFrom trueIsCalled (compileF compile (getAnn ⊝ als ++ RL) F als)
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
  eauto with len.
Qed.

Lemma UCE_noUnreachableCode RL s lv
  : reachability SoundAndComplete RL s lv
    -> getAnn lv
    -> noUnreachableCode trueIsCalled (compile RL s lv).
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
