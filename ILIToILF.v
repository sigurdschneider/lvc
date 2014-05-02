Require Import AllInRel Util Map Env EnvTy Exp IL Annotation ParamsMatch Coherence Sim DecSolve Liveness Restrict.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.

(** Correctness predicate for  *)

Inductive trs 
  : list (option (set var)) (** globals *)
    -> list (params)        (** additional parameters for functions in scope *)
    -> stmt                 (** the program *)
    -> ann (set var)        (** liveness information *)    
    -> ann (list var)       (** annotation providing additional parameters for function definitions
                                inside the program *)
    -> Prop :=
 | trsExp DL ZL x e s an an_lv lv
    : trs (restrict DL (lv\{{x}})) ZL  s an_lv an
    -> trs DL ZL (stmtExp x e s) (ann1 lv an_lv) (ann1 nil an)
  | trsIf DL ZL x s t ans ant ans_lv ant_lv lv
    :  trs DL ZL s ans_lv ans
    -> trs DL ZL t ant_lv ant
    -> trs DL ZL (stmtIf x s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
  | trsRet x DL ZL lv
    :  trs DL ZL (stmtReturn x) (ann0 lv) (ann0 nil)
  | trsGoto DL ZL G' f Za Y lv
    :  get DL (counted f) (Some G')
    -> get ZL (counted f) (Za)
    -> G' ⊆ lv
(*    -> of_list Za ⊆ lv *)
    -> trs DL ZL (stmtGoto f Y) (ann0 lv) (ann0 nil)
  | trsLet DL ZL s t Z Za ans ant lv ans_lv ant_lv
    : (* of_list Za ⊆ getAnn ans_lv *)
      (* for now, require all additionals Za to be live in the function;
         this makes the proof that liveness information is valid even after
         the insertion of the arguments easier (otherwise, liveness needs to
         be recomputed) *) 
      trs (restrict (Some (getAnn ans_lv \ of_list (Z++Za))::DL) (getAnn ans_lv \ of_list (Z++Za))) (Za::ZL) s ans_lv ans
    -> trs (Some (getAnn ans_lv \ of_list (Z++Za))::DL) (Za::ZL) t ant_lv ant
    -> trs DL ZL (stmtLet Z s t) (ann2 lv ans_lv ant_lv) (ann2 Za ans ant).

Lemma trs_dec DL ZL s ans_lv ans (* (an_lv:annotation s ans_lv) (an:annotation s ans) *)
  : {trs DL ZL s ans_lv ans} + 
    {~ trs DL ZL s ans_lv ans}. 
Proof.
  general induction s; destruct ans; destruct ans_lv; isabsurd; try dec_solve.
  + destruct a; edestruct (IHs (restrict DL (a0\{{x}})) ZL ans_lv ans); try dec_solve.
  + destruct a; subst; try dec_solve;
    destruct (IHs1 DL ZL ans_lv1 ans1); try dec_solve;
    destruct (IHs2 DL ZL ans_lv2 ans2); try dec_solve.
  + destruct (get_dec DL (counted l)) as [[[G'|]]|];
    destruct (get_dec ZL (counted l)) as [[Za ?]|];
    try destruct a;
    try decide (G' ⊆ a0);
    try decide (of_list (Za) ⊆ a0);
    subst; try dec_solve; try inv an; try inv an_lv; eauto. 
  + decide (a = nil);
    subst; try dec_solve; try inv an; try inv an_lv; eauto. 
  + edestruct (IHs1 (restrict (Some (getAnn ans_lv1 \ of_list (Z++a))::DL) (getAnn ans_lv1 \ of_list (Z++a))) (a::ZL) ans_lv1 ans1); eauto;
    edestruct (IHs2 (Some (getAnn ans_lv1 \ of_list (Z++a)) :: DL) (a :: ZL) ans_lv2 ans2); decide (of_list a ⊆ getAnn ans_lv1);
    eauto; try dec_solve.
Defined.

Lemma trs_annotation DL ZL s lv Y
      : trs DL ZL s lv Y -> annotation s lv /\ annotation s Y.
Proof.
  intros. general induction H; split; dcr; econstructor; eauto.
Qed.

Instance trs_dec_inst DL ZL s lv Y
: Computable (trs DL ZL s lv Y).
Proof.
  try (now right; intro A; eapply trs_annotation in A; dcr; eauto).
  hnf; eauto using trs_dec.
Defined.

Fixpoint compile (ZL:list (list var)) (s:stmt) (an:ann (list var)) : stmt :=
  match s, an with
    | stmtExp x e s, ann1 _ an => stmtExp x e (compile ZL s an)
    | stmtIf x s t, ann2 _ ans ant => stmtIf x (compile ZL s ans) (compile ZL t ant)
    | stmtGoto f Y, ann0 _ => stmtGoto f (Y++nth (counted f) ZL nil)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtLet Z s t, ann2 Za ans ant => 
      stmtLet (Z++Za) (compile (Za::ZL) s ans) (compile (Za::ZL) t ant)
    | s, _ => s  
  end.

Inductive approx 
  : list (option (set var)) -> list (params) -> I.block -> I.block -> Prop :=
  blk_approxI o (Za Z':list var) DL ZL s ans ans_lv
  (RD:forall G, o = Some G -> 
                trs (restrict (Some G::DL) G) (Za::ZL) s ans_lv ans)
  : approx (o::DL) (Za::ZL)(I.blockI Z' s) (I.blockI (Z'++Za) (compile (Za::ZL) s ans)).

Lemma approx_restrict DL ZL L L' G
: AIR4 approx DL ZL L L'
  -> AIR4 approx (restrict DL G) ZL L L'.
Proof.
  intros. general induction H. 
  + econstructor.
  + simpl. econstructor; eauto.
    - inv pf. econstructor; intros. eapply restr_iff in H0; dcr. inv H2.
      rewrite <- restrict_incl; eauto. rewrite restrict_idem; eauto.
Qed.

Inductive trsR : I.state -> I.state -> Prop :=
  trsRI (E E':env val) L L' s ans ans_lv DL ZL 
  (RD: trs DL ZL s ans_lv ans)
  (EA: AIR4 approx DL ZL L L') 
  (EQ: E ≡ E')
  : trsR (L, E, s) (L', E', compile ZL s ans).

Lemma trsR_sim σ1 σ2
  : trsR σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros. destruct H; inv RD; simpl; try provide_invariants_4.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto using I.step, plus.
    rewrite EQ in H0; econstructor; eauto using I.step, plus.
    eapply trsR_sim. econstructor; eauto using approx_restrict. 
    rewrite EQ; reflexivity.
    eapply simE; try eapply star_refl; eauto; stuck. rewrite EQ in H0; congruence.

  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor. rewrite <- EQ; eauto.
    eapply trsR_sim; econstructor; eauto.
    eapply simS; try eapply plusO. 
    eapply I.stepIfF; eauto. 
    eapply I.stepIfF; eauto. rewrite <- EQ; eauto.
    eapply trsR_sim; econstructor; eauto.

  + eapply simE; try eapply star_refl; simpl; eauto; try stuck. rewrite EQ; eauto.

  + simpl counted in *.
    decide (length Z' = length Y).
    one_step. simpl in *; eauto.
    repeat rewrite app_length.
    eapply get_drop_eq in H6; eauto. inv H6; subst. simpl.
    rewrite app_length. erewrite get_nth_default; eauto.
    rewrite <- H5, <- H6 in EA1. 
    eapply trsR_sim; econstructor; eauto using approx_restrict.
    unfold updE. simpl.
    eapply get_drop_eq in H6; eauto. inv H6. subst.
    rewrite lookup_list_app. rewrite update_with_list_app.
    erewrite get_nth_default; eauto.
    rewrite update_with_list_lookup_list. rewrite EQ. reflexivity.
    intuition.
    edestruct (AIR4_length); eauto; dcr.
    rewrite lookup_list_length; eauto.
    no_step. get_functional; subst. simpl in *. congruence.
    get_functional; subst. simpl in *. 
    eapply n. repeat rewrite app_length in len.
    eapply get_drop_eq in H6; eauto. subst Za0.
    erewrite get_nth_default in len; eauto. omega.
  + eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    eapply trsR_sim; econstructor; eauto.
    econstructor; eauto. econstructor. 
    intros. inv H1. eauto.
Qed.

Inductive fstNoneOrR' {X Y:Type} (R:X->Y->Prop)
  : option X -> Y -> Prop :=
| fstNone' (y:Y) : fstNoneOrR' R None y
| bothR' (x:X) (y:Y) : R x y -> fstNoneOrR' R (Some x) y
.
(*
Lemma restrict_subset2 DL DL' G G'
: list_eq (fstNoneOrR (flip Subset)) DL DL' 
  -> G' ⊆ G
  -> list_eq (fstNoneOrR (flip Subset)) (restrict DL G) (restrict DL' G').
Proof.
  intros. induction H; simpl; econstructor; eauto.
  inv H. simpl. econstructor.
  unfold restr. repeat destruct if; try econstructor; eauto.
  exfalso. eapply n. transitivity G; eauto. rewrite <- H2; eauto.
Qed.
*)

Definition lessReq := (fstNoneOrR' (fun (s : set var) (t : set var * params) => s ⊆ fst t)).

Lemma restrict_lessReq DL DL' G
: PIR2 lessReq DL DL' 
  -> PIR2 lessReq (restrict DL G) DL'.
Proof.
  intros. induction H; simpl; econstructor; eauto.
  unfold restr. destruct pf. constructor.
  destruct if; eauto. subst. constructor; eauto. constructor.
Qed.

Lemma compile_typed DL AL ZL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  (LV:live_sound DL s ans_lv)
  (EQ:PIR2 lessReq AL DL)
  : srd (restrict AL (getAnn ans_lv)) (compile ZL s ans) ans_lv.
Proof. 
  general induction RD; inv LV; simpl; eauto using srd.
  + econstructor; eauto.
    eapply srd_monotone. eapply IHRD; eauto.
    eapply restrict_lessReq; eauto.
    repeat rewrite restrict_comp_meet.
    eapply restrict_subset. reflexivity.
    cset_tac; intuition.
  + econstructor; eauto.
    eapply srd_monotone. eapply IHRD1; eauto.
    eapply restrict_subset; eauto. reflexivity.
    eapply srd_monotone. eapply IHRD2; eauto.
    eapply restrict_subset; eauto. reflexivity.
  + edestruct PIR2_nth_2; eauto; dcr.
    inv H4; get_functional; subst. simpl in *.
    econstructor; eauto. unfold restrict. 
    pose proof (map_get_1 (restr lv) H3). unfold fst in H.
    assert (restr lv (Some x0) = Some x0). eapply restr_iff; split; eauto.
    cset_tac; eauto.
    rewrite <- H6; eauto.
  + econstructor; eauto. 
    - eapply srd_monotone2. eapply IHRD1; eauto.
      eapply restrict_lessReq. econstructor; eauto.
      constructor. simpl. cset_tac; intuition. 
      rewrite restrict_incl; [|reflexivity].
      rewrite restrict_incl; [|eapply minus_incl].
      rewrite restrict_incl; [|reflexivity].
      econstructor. constructor; unfold flip.
      rewrite of_list_app. cset_tac; intuition.
      repeat rewrite restrict_comp_meet.
      eapply restrict_subset2. reflexivity. 
      rewrite of_list_app.
      hnf; intros. cset_tac; intuition. 
    - eapply srd_monotone2. eapply IHRD2; eauto.
      constructor. constructor. simpl. cset_tac; intuition. eauto.
      decide (getAnn ans_lv \ of_list (Z ++ Za) ⊆ getAnn ant_lv).
      rewrite restrict_incl; eauto.
      econstructor. reflexivity. 
      eapply restrict_subset2. reflexivity. eauto.
      rewrite restrict_not_incl; eauto.
      econstructor. constructor.
      eapply restrict_subset2. reflexivity. eauto.
Qed.

Lemma live_sound_compile DL ZL AL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  (LV:live_sound DL s ans_lv)
(*  (EQ:PIR2 (fstNoneOrR' (fun s t => s = fst t)) AL DL) *)
  : live_sound (zip (fun s t => (fst s, snd s ++ t)) DL ZL) (compile ZL s ans) ans_lv.
Proof.
  general induction LV; inv RD; eauto using live_sound.
  + pose proof (zip_get  (fun (s : set var * list var) (t : list var) => (fst s, snd s ++ t)) H H9).
    econstructor. eapply H3. simpl. rewrite of_list_app. cset_tac; intuition.
    simpl. erewrite get_nth; eauto. repeat rewrite app_length. congruence.
    erewrite get_nth; eauto. rewrite of_list_app. cset_tac; intuition. admit.
  + simpl. econstructor; eauto.
    specialize (IHLV1 (Za::ZL)). eapply IHLV1; eauto.
    specialize (IHLV2 (Za::ZL)). eapply IHLV2; eauto.
    rewrite of_list_app. cset_tac; intuition. admit.
    rewrite of_list_app. cset_tac; intuition.
Qed.

Lemma compile_params_match DL ZL L s ans_lv ans
  : trs DL ZL s ans_lv ans 
    -> ParamsMatch.parameters_match L s
    -> ParamsMatch.parameters_match (List.map (fun p => snd p + length (fst p)) 
                                             (zip (fun s t => (s,t)) ZL L))  (compile ZL s ans).
Proof.
  intros. general induction H; simpl.
  + inv H0. econstructor; eauto.
  + inv H1. econstructor; eauto.
  + constructor.
  + inv H2.
    econstructor; eauto. 
    rewrite app_length.  
    simpl in *. 
    pose proof (zip_get (fun s t => (s,t)) H0 H6).
    erewrite get_nth_default; eauto.
    eapply (map_get_1 (fun p => snd p + length (fst p)) H3).
  + inv H1.
    constructor; simpl in *; rewrite app_length.
    eapply (IHtrs1 _ H5); eauto. 
    eapply (IHtrs2 _ H7); eauto. 
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
