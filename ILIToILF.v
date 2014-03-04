Require Import AllInRel Util Map Env EnvTy Exp IL ParamsMatch Coherence Sim DecSolve Liveness Restrict.

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
    -> trs DL ZL (stmtExp x e s) (annExp lv an_lv) (annExp nil an)
  | trsIf DL ZL x s t ans ant ans_lv ant_lv lv
    :  trs DL ZL s ans_lv ans
    -> trs DL ZL t ant_lv ant
    -> trs DL ZL (stmtIf x s t) (annIf lv ans_lv ant_lv) (annIf nil ans ant)
  | trsRet x DL ZL lv
    :  trs DL ZL (stmtReturn x) (annReturn lv) (annReturn nil)
  | trsGoto DL ZL G' f Za Y lv
    :  get DL (counted f) (Some G')
    -> get ZL (counted f) (Za)
    -> G' ⊆ lv
    -> of_list Za ⊆ lv
    -> trs DL ZL (stmtGoto f Y) (annGoto lv) (annGoto nil)
  | trsLet DL ZL s t Z Za ans ant lv ans_lv ant_lv
    : trs (restrict (Some (getAnn ans_lv \ of_list Z)::DL) (getAnn ans_lv \ of_list Z)) (Za::ZL) s ans_lv ans
    -> trs (Some (getAnn ans_lv \ of_list Z)::DL) (Za::ZL) t ant_lv ant
    -> trs DL ZL (stmtLet Z s t) (annLet lv ans_lv ant_lv) (annLet Za ans ant).

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
    try destruct_prop (G' ⊆ a0);
    try destruct_prop (of_list (Za) ⊆ a0);
    subst; try dec_solve; try inv an; try inv an_lv; eauto. 
  + destruct_prop (a = nil);
    subst; try dec_solve; try inv an; try inv an_lv; eauto.
  + edestruct (IHs1 (restrict (Some (getAnn ans_lv1 \ of_list Z)::DL) (getAnn ans_lv1 \ of_list Z)) (a::ZL) ans_lv1 ans1); eauto;
    edestruct (IHs2 (Some (getAnn ans_lv1 \ of_list Z) :: DL) (a :: ZL) ans_lv2 ans2); 
    eauto; try dec_solve.
Defined.

Lemma trs_annotation DL ZL s lv args
      : trs DL ZL s lv args -> annotation s lv /\ annotation s args.
Proof.
  intros. general induction H; split; dcr; econstructor; eauto.
Qed.

Instance trs_dec_inst DL ZL s lv args
: Computable (trs DL ZL s lv args).
Proof.
  try (now constructor; right; intro A; eapply trs_annotation in A; dcr; eauto).
  constructor. eauto using trs_dec.
Defined.

Fixpoint compile (ZL:list (list var)) (s:stmt) (an:ann (list var)) : stmt :=
  match s, an with
    | stmtExp x e s, annExp _ an => stmtExp x e (compile ZL s an)
    | stmtIf x s t, annIf _ ans ant => stmtIf x (compile ZL s ans) (compile ZL t ant)
    | stmtGoto f Y, annGoto _ => stmtGoto f (Y++nth (counted f) ZL nil)
    | stmtReturn x, annReturn _ => stmtReturn x
    | stmtLet Z s t, annLet Za ans ant => 
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
  (PM: params_match L s)
  (EQ: E ≡ E')
  : trsR (L, E, s) (L', E', compile ZL s ans).

Lemma trsR_sim σ1 σ2
  : trsR σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros. destruct H; inv RD; simpl; try provide_invariants_4; try params_match_tac.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto using I.step, plus.
    rewrite EQ in H1; econstructor; eauto using I.step, plus.
    eapply trsR_sim. econstructor; eauto using approx_restrict. 
    rewrite EQ; reflexivity.
    eapply simE; try eapply star_refl; eauto; stuck. rewrite EQ in H1; congruence.

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
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. simpl.
    repeat rewrite app_length.
    eapply get_drop_eq in H7; eauto. inv H7; subst. f_equal; eauto.
    erewrite get_nth_default; eauto.
    rewrite <- H6, <- H7 in EA1. 
    eapply trsR_sim; econstructor; eauto using approx_restrict.
    unfold updE. simpl.
    eapply get_drop_eq in H7; eauto. inv H7. subst.
    rewrite lookup_list_app. rewrite update_with_list_app.
    erewrite get_nth_default; eauto.
    rewrite update_with_list_lookup_list. rewrite EQ. reflexivity.
    intuition.
    edestruct (AIR4_length); eauto; dcr.
    rewrite lookup_list_length; eauto.
        
  + eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    eapply trsR_sim; econstructor; eauto.
    econstructor; eauto. econstructor. 
    intros. inv H2. eauto. 
Qed.


Lemma compile_typed DL AL ZL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  (LV:live_sound DL s ans_lv)
  : srd (restrict AL (getAnn ans_lv)) (compile ZL s ans) ans_lv.
Proof. 
  general induction RD; inv LV; simpl; eauto using srd.
  + econstructor; eauto.
    eapply srd_monotone. eapply IHRD; eauto.
    repeat rewrite restrict_comp_meet.
    eapply restrict_subset. reflexivity.
    cset_tac; intuition.
  + econstructor; eauto.
    eapply srd_monotone. eapply IHRD1; eauto.
    eapply restrict_subset; eauto. reflexivity.
    eapply srd_monotone. eapply IHRD2; eauto.
    eapply restrict_subset; eauto. reflexivity.
  + (*econstructor. unfold restrict. 
    pose proof (map_get_1 (restr lv) H).
    assert (restr G (Some G') = Some G'). eapply restr_iff; intuition.
-    rewrite <- H4; eauto.
   *)
    admit.
  + econstructor; eauto. 
    - eapply srd_monotone2. eapply IHRD1; eauto.
      rewrite restrict_incl; [|reflexivity].
      rewrite restrict_incl; [|eapply minus_incl].
      rewrite restrict_incl; [|reflexivity].
      econstructor. constructor; unfold flip.
      admit.
      repeat rewrite restrict_comp_meet.
      eapply restrict_subset2. reflexivity. admit.
    - eapply srd_monotone2. eapply IHRD2; eauto.
      admit.
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
  + inv H3.
    econstructor; eauto. 
    rewrite app_length.  
    simpl in *. 
    pose proof (zip_get (fun s t => (s,t)) H0 H7).
    erewrite get_nth_default; eauto.
    eapply (map_get_1 (fun p => snd p + length (fst p)) H4).
  + inv H1.
    constructor; simpl in *; rewrite app_length.
    eapply (IHtrs1 _ H5); eauto. 
    eapply (IHtrs2 _ H7); eauto. 
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)
