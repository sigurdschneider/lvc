Require Import AllInRel Util Map Env EnvTy Exp IL Annotation Coherence Bisim DecSolve Liveness Restrict MoreExp.

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
  | trsIf DL ZL e s t ans ant ans_lv ant_lv lv
    :  trs DL ZL s ans_lv ans
    -> trs DL ZL t ant_lv ant
    -> trs DL ZL (stmtIf e s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
  | trsRet e DL ZL lv
    :  trs DL ZL (stmtReturn e) (ann0 lv) (ann0 nil)
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


Lemma trs_annotation DL ZL s lv Y
      : trs DL ZL s lv Y -> annotation s lv /\ annotation s Y.
Proof.
  intros. general induction H; split; dcr; econstructor; eauto.
Qed.

Fixpoint compile (ZL:list (list var)) (s:stmt) (an:ann (list var)) : stmt :=
  match s, an with
    | stmtExp x e s, ann1 _ an => stmtExp x e (compile ZL s an)
    | stmtIf e s t, ann2 _ ans ant => stmtIf e (compile ZL s ans) (compile ZL t ant)
    | stmtGoto f Y, ann0 _ => stmtGoto f (Y++List.map Var (nth (counted f) ZL nil))
    | stmtReturn e, ann0 _ => stmtReturn e
    | stmtLet Z s t, ann2 Za ans ant =>
      stmtLet (Z++Za) (compile (Za::ZL) s ans) (compile (Za::ZL) t ant)
    | s, _ => s
  end.

Inductive approx
  : list (set var * list var)
    -> list (option (set var))
    -> list (params) -> I.block -> I.block -> Prop :=
  blk_approxI o (Za Z':list var) DL ZL Lv s ans ans_lv ans_lv'
              (RD:forall G, o = Some G ->
                       live_sound ((getAnn ans_lv',Z'++Za)::Lv) (compile (Za :: ZL) s ans) ans_lv'
                       /\ trs (restrict (Some G::DL) G) (Za::ZL) s ans_lv ans)
  : approx ((getAnn ans_lv',Z'++Za)::Lv) (o::DL) (Za::ZL) (I.blockI Z' s) (I.blockI (Z'++Za) (compile (Za::ZL) s ans)).

Lemma approx_restrict Lv DL ZL L L' G
: AIR53 approx Lv DL ZL L L'
  -> AIR53 approx Lv (restrict DL G) ZL L L'.
Proof.
  intros. general induction H.
  + econstructor.
  + simpl. econstructor; eauto.
    - inv pf. econstructor; intros. eapply restr_iff in H0; dcr. inv H2.
      rewrite <- restrict_incl; eauto. rewrite restrict_idem; eauto.
Qed.

Definition appsnd {X} {Y} (s:X * list Y) (t: list Y) := (fst s, snd s ++ t).

Definition defined_on {X} `{OrderedType X} {Y} (G:set X) (E:X -> option Y)
  := forall x, x ∈ G -> exists y, E x = Some y.

Lemma defined_on_update_some X `{OrderedType X} Y (G:set X) (E:X -> option Y) x v
  : defined_on (G \ {{x}}) E
    -> defined_on G (E [x <- Some v]).
Proof.
  unfold defined_on; intros. lud.
  - eauto.
  - eapply H0; eauto. cset_tac; intuition.
Qed.

Lemma defined_on_incl X `{OrderedType X} Y (G G':set X) (E:X -> option Y)
  : defined_on G E
    -> G' ⊆ G
    -> defined_on G' E.
Proof.
  unfold defined_on; intros; eauto.
Qed.

Inductive trsR : I.state -> I.state -> Prop :=
  trsRI (E E':onv val) L L' s ans Lv' ans_lv ans_lv' DL ZL
  (RD: trs DL ZL s ans_lv ans)
  (EA: AIR53 approx Lv' DL ZL L L')
  (EQ: (@feq _ _ eq) E E')
  (LV': live_sound Lv' (compile ZL s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E')
  : trsR (L, E, s) (L', E', compile ZL s ans).

Lemma omap_var_defined_on Za lv E
: of_list Za ⊆ lv
  -> defined_on lv E
  -> exists l, omap (exp_eval E) (List.map Var Za) = Some l.
Proof.
  intros. general induction Za; simpl.
  - eauto.
  - simpl in *.
    edestruct H0.
    + instantiate (1:=a). cset_tac; intuition.
    + rewrite H1; simpl. edestruct IHZa; eauto.
      cset_tac; intuition.
      rewrite H2; simpl. eauto.
Qed.

Lemma defined_on_update_list lv (E:onv val) Z vl
: length vl = length Z
  -> defined_on (lv \ of_list Z) E
  -> defined_on lv (E [Z <-- List.map Some vl]).
Proof.
  unfold defined_on; intros.
  decide (x ∈ of_list Z).
  - eapply length_length_eq in H. clear H0.
    general induction H; simpl in * |- *.
    + exfalso. cset_tac; intuition.
    + lud; eauto. edestruct IHlength_eq; eauto. cset_tac; intuition.
  - edestruct H0; eauto. instantiate (1:=x). cset_tac; intuition.
    exists x0. rewrite <- H2.
    eapply update_with_list_no_update; eauto.
Qed.



Lemma trsR_sim σ1 σ2
  : trsR σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros. destruct H; inv RD; invt live_sound; simpl; try provide_invariants_53.
  - remember (exp_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H0.
    destruct o.
    + one_step. simpl in *.
      eapply trsR_sim.
      econstructor; eauto using approx_restrict.
      rewrite EQ; reflexivity.
      eapply defined_on_update_some. eapply defined_on_incl; eauto.
    + no_step.
  - remember (exp_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H1.
    destruct o.
    case_eq (val2bool v); intros.
    + one_step. eapply trsR_sim; econstructor; eauto using defined_on_incl.
    + one_step. eapply trsR_sim; econstructor; eauto using defined_on_incl.
    + no_step.
  - no_step. simpl. rewrite EQ; eauto.
  - simpl counted in *.
    decide (length Z' = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    simpl in *.
    erewrite get_nth_default in H9; eauto.
    edestruct (omap_var_defined_on x); eauto.
    eapply get_in_incl; intros.
    exploit H9. eapply get_app_right. Focus 2.
    eapply map_get_1; eauto. reflexivity. inv X. eauto.
    + exploit get_drop_eq; try eapply H11; eauto. subst o.
      exploit get_drop_eq; try eapply H12; eauto. subst x.
      erewrite get_nth_default; eauto.
      one_step.
      * simpl; eauto.
        repeat rewrite app_length.
        rewrite map_length; eauto.
      * instantiate (1:=l ++ x0).
        rewrite omap_app.
        erewrite omap_agree. Focus 2.
        intros. rewrite <- EQ. reflexivity.
        rewrite H0; simpl. rewrite H8; simpl. reflexivity.
      * exploit RD0; eauto; dcr. simpl.
        eapply trsR_sim; econstructor; eauto.
        rewrite <- H11, <- H10, <- H12 in EA1.
        eapply (approx_restrict G' EA1).
        simpl. rewrite map_app.
        rewrite update_with_list_app.
        rewrite (omap_self_update E' Za0). rewrite EQ. reflexivity. eauto.
        rewrite map_length.
        exploit omap_length; try eapply H0; eauto. congruence.
        eapply defined_on_update_list; eauto using defined_on_incl.
        exploit omap_length; try eapply H0; eauto.
        exploit omap_length; try eapply H8; eauto.
        rewrite map_length in X0.
        repeat rewrite app_length. omega.
    + no_step. get_functional; subst. simpl in *.
      rewrite omap_app in def.
      erewrite omap_agree in H0. Focus 2.
      intros. rewrite EQ. reflexivity. rewrite H0 in def. simpl in *. congruence.
    + no_step.
      get_functional; subst. simpl in *. congruence.
      get_functional; subst. simpl in *.
      apply n. repeat rewrite app_length in len.
      eapply get_drop_eq in H12; eauto. subst Za0.
      erewrite get_nth_default in len; eauto. rewrite map_length in len. omega.
  - one_step.
    eapply trsR_sim; econstructor; eauto.
    econstructor; eauto. econstructor.
    intros. split; eauto. inv H1. eauto.
    eauto using defined_on_incl.
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

Lemma trs_srd DL AL ZL s ans_lv ans
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

Inductive additionalParameters_live : list (set var)   (* additional params *)
                                      -> stmt           (* the program *)
                                      -> ann (set var)  (* liveness *)
                                      -> ann (list var) (* additional params *)
                                      -> Prop :=
 | additionalParameters_liveExp ZL x e s an an_lv lv
    : additionalParameters_live ZL s an_lv an
    -> additionalParameters_live ZL (stmtExp x e s) (ann1 lv an_lv) (ann1 nil an)
  | additionalParameters_liveIf ZL e s t ans ant ans_lv ant_lv lv
    : additionalParameters_live ZL s ans_lv ans
    -> additionalParameters_live ZL t ant_lv ant
    -> additionalParameters_live ZL (stmtIf e s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
  | additionalParameters_liveRet ZL e lv
    :  additionalParameters_live ZL (stmtReturn e) (ann0 lv) (ann0 nil)
  | additionalParameters_liveGoto ZL Za f Y lv
    : get ZL (counted f) Za
      -> Za ⊆ lv
      -> additionalParameters_live ZL (stmtGoto f Y) (ann0 lv) (ann0 nil)
  | additionalParameters_liveLet ZL s t Z Za ans ant lv ans_lv ant_lv
    : of_list Za ⊆ getAnn ans_lv \ of_list Z
    -> additionalParameters_live (of_list Za::ZL) s ans_lv ans
    -> additionalParameters_live (of_list Za::ZL) t ant_lv ant
    -> additionalParameters_live ZL (stmtLet Z s t) (ann2 lv ans_lv ant_lv) (ann2 Za ans ant).

Lemma live_sound_compile DL ZL AL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  (LV:live_sound DL s ans_lv)
  (APL: additionalParameters_live (List.map of_list ZL) s ans_lv ans)
  : live_sound (zip (fun s t => (fst s, snd s ++ t)) DL ZL) (compile ZL s ans) ans_lv.
Proof.
  general induction LV; inv RD; inv APL; eauto using live_sound.
  + pose proof (zip_get  (fun (s : set var * list var) (t : list var) => (fst s, snd s ++ t)) H H9).
    edestruct (map_get_4); eauto; dcr; subst.
    get_functional; subst x.
    econstructor. eapply H3. simpl. rewrite of_list_app. cset_tac; intuition.
    simpl. erewrite get_nth; eauto. repeat rewrite app_length, map_length, app_length. congruence.
    erewrite get_nth; eauto.
    intros. eapply get_app_cases in H5. destruct H5; dcr; eauto.
    edestruct map_get_4; eauto; dcr; subst. econstructor.
    rewrite <- H10. eauto using get_in_of_list.
  + simpl. econstructor; eauto.
    specialize (IHLV1 (Za::ZL)). eapply IHLV1; eauto.
    specialize (IHLV2 (Za::ZL)). eapply IHLV2; eauto.
    rewrite of_list_app. rewrite H7.
    cset_tac; intuition.
    rewrite of_list_app.
    rewrite <- H0. cset_tac; intuition.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
