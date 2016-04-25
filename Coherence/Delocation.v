Require Import AllInRel Util Map Env EnvTy Exp IL Annotation Coherence Bisim DecSolve Liveness.
Require Import Restrict MoreExp InRel.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.
Unset Printing Abstraction Types.
Local Arguments lminus {X} {H} s L.


(** Correctness predicate for  *)

Notation "'mkGlobals' F Za ans_lv" := (Some ⊝ (zip lminus (zip lminus (getAnn ⊝ ans_lv) (fst ⊝ F)) Za))
                                       (at level 50, F, Za, ans_lv at level 0).

Inductive trs
  : 〔؟⦃var⦄〕 (** globals *)
    -> list (params)        (** additional parameters for functions in scope *)
    -> stmt                 (** the program *)
    -> ann (set var)        (** liveness information *)
    -> ann (list (list var)) (** annotation providing additional parameters for function definitions
                                inside the program *)
    -> Prop :=
 | trsExp DL ZL x e s an an_lv lv
    : trs (restrict DL (lv\ singleton x)) ZL  s an_lv an
    -> trs DL ZL (stmtLet x e s) (ann1 lv an_lv) (ann1 nil an)
  | trsIf DL ZL e s t ans ant ans_lv ant_lv lv
    :  trs DL ZL s ans_lv ans
    -> trs DL ZL t ant_lv ant
    -> trs DL ZL (stmtIf e s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
  | trsRet e DL ZL lv
    :  trs DL ZL (stmtReturn e) (ann0 lv) (ann0 nil)
  | trsGoto DL ZL G' f Za Y lv
    :  get DL (counted f) (Some G')
    -> get ZL (counted f) (Za)
(*    -> G' ⊆ lv *)
(*    -> of_list Za ⊆ lv *)
    -> trs DL ZL (stmtApp f Y) (ann0 lv) (ann0 nil)
  | trsExtern DL ZL x f Y s lv an_lv an
    : trs (restrict DL (lv\ singleton x)) ZL s an_lv an
    -> trs DL ZL (stmtExtern x f Y s) (ann1 lv an_lv) (ann1 nil an)
  | trsLet (DL:list (option (set var))) ZL (F:list (params*stmt)) t Za ans ant lv ans_lv ant_lv
    : length F = length ans_lv
      -> length F = length ans
      -> length F = length Za
      -> (forall n lvs Zs Za' ans', get ans_lv n lvs -> get F n Zs -> get Za n Za' -> get ans n ans' ->
                              trs (restrict (Some ⊝ (zip lminus
                                                         (zip lminus (getAnn ⊝ ans_lv) (fst ⊝ F)) Za)
                                            ++ DL)
                                            (getAnn lvs \ of_list (fst Zs++Za')))
                                  (Za++ZL) (snd Zs) lvs ans')
    -> trs (mkGlobals F Za ans_lv ++ DL) (Za++ZL) t ant_lv ant
    -> trs DL ZL (stmtFun F t) (annF lv ans_lv ant_lv) (annF Za ans ant).

Lemma trs_annotation DL ZL s lv Y
      : trs DL ZL s lv Y -> annotation s lv /\ annotation s Y.
Proof.
  intros. general induction H; split; dcr; econstructor; intros; eauto 20.
  - edestruct get_length_eq; try eapply H1; eauto.
    edestruct get_length_eq; try eapply H0; eauto.
    exploit H3; eauto.
  - edestruct get_length_eq; try eapply H1; eauto.
    edestruct get_length_eq; try eapply H; eauto.
    exploit H3; eauto.
Qed.

Definition compileF (compile : list (list var) -> stmt -> ann (list (list var)) -> stmt)
           (ZL:list (list var))
           (F:list (params*stmt))
           (Za Za':list (list var))
           (ans:list (ann (list (list var))))
  : list (params*stmt) :=
  zip (fun Zs Zaans => (fst Zs ++ fst Zaans, compile (Za'++ZL) (snd Zs) (snd Zaans)))
      F
      (zip pair Za ans).

Fixpoint compile (ZL:list (list var)) (s:stmt) (an:ann (list (list var))) : stmt :=
  match s, an with
    | stmtLet x e s, ann1 _ an => stmtLet x e (compile ZL s an)
    | stmtIf e s t, ann2 _ ans ant => stmtIf e (compile ZL s ans) (compile ZL t ant)
    | stmtApp f Y, ann0 _ => stmtApp f (Y++List.map Var (nth (counted f) ZL nil))
    | stmtReturn e, ann0 _ => stmtReturn e
    | stmtExtern x f Y s, ann1 _ an =>
      stmtExtern x f Y (compile ZL s an)
    | stmtFun F t, annF Za ans ant =>
      stmtFun (compileF compile ZL F Za Za ans)
              (compile (Za++ZL) t ant)
    | s, _ => s
  end.

Inductive approx
  : list ((set var * list var) * (option (set var)) * (params))
    -> list I.block
    -> list I.block
    -> ((set var * list var) * (option (set var)) * (params))
    -> I.block
    -> I.block -> Prop :=
  blk_approxI o (Za Z':list var) Lv DL ZL s ans ans_lv ans_lv' n L1 L2
              (RD:forall G, o = Some G ->
                       live_sound Imperative Lv (compile ZL s ans) ans_lv'
                       /\ trs (restrict DL G) ZL s ans_lv ans)
  : length DL = length ZL
  -> length ZL = length Lv
  -> approx (zip pair (zip pair Lv DL) ZL) L1 L2 ((getAnn ans_lv',Z'++Za), o, Za) (I.blockI Z' s n) (I.blockI (Z'++Za) (compile ZL s ans) n).

Lemma approx_restrict_block Lv1 Lv2 DL1 DL2 ZL1 ZL2 Lv1' DL1' ZL1' L1' L2' G n L1X L2X
: length Lv1 = length DL1
  -> length Lv2 = length DL2
  -> length DL1 = length ZL1
  -> length DL2 = length ZL2
  -> mutual_block
        (approx
           (zip pair (zip pair Lv1 DL1) ZL1 ++
            zip pair (zip pair Lv2 DL2) ZL2) L1X L2X) n
        (zip pair (zip pair Lv1' DL1') ZL1') L1' L2'
  -> mutual_block
     (approx
        (zip pair (zip pair Lv1 (restrict DL1 G)) ZL1 ++
         zip pair (zip pair Lv2 (restrict DL2 G)) ZL2) L1X L2X) n
     (zip pair (zip pair Lv1' (restrict DL1' G)) ZL1') L1' L2'.
Proof.
  intros. general induction H3.
  - destruct Lv1', DL1', ZL1'; isabsurd; constructor.
  - eapply zip_eq_cons_inv in Heql.
    destruct Heql as [? [? ?]]; eauto; dcr; subst.
    eapply zip_eq_cons_inv in H7.
    destruct H7 as [? [? ?]]; eauto; dcr; subst.
    simpl. econstructor; eauto.
    * inv H1.
      pose proof (@zip_length2 _ _ _ pair Lv2 DL2 H4).
      pose proof (@zip_length2 _ _ _ pair Lv1 DL1 H2).
      repeat rewrite <- zip_app; try rewrite restrict_length; eauto with len.
      rewrite <- zip_app in H; eauto with len.
      eapply zip_pair_app_inv in H; dcr; subst; eauto with len.
      rewrite <- zip_app in H9; eauto with len.
      eapply zip_pair_app_inv in H9; dcr; subst; eauto with len.
      econstructor; eauto with len.
      intros. eapply restr_iff in H; dcr; subst. exploit RD; eauto; dcr.
      rewrite <- restrict_app, restrict_idem.
      eauto. eauto.
Qed.

Lemma approx_restrict Lv DL ZL L L' G
  : length DL = length ZL
    -> length ZL = length Lv
    -> inRel approx (zip pair (zip pair Lv DL) ZL) L L'
    -> inRel approx (zip pair (zip pair Lv (restrict DL G)) ZL) L L'.
Proof.
  intros.
  general induction H1; simpl in *.
  - destruct DL, ZL, Lv; isabsurd; simpl; eauto using @inRel.
  - eapply zip_eq_app_inv in Heql; eauto with len.
    destruct Heql as [LVDL1 [LVDL2 [ZL1 [ZL2 ?]]]]; dcr; subst.
    symmetry in H4.
    eapply zip_eq_app_inv in H4; eauto with len.
    destruct H4 as [Lv1 [Lv2 [DL1 [DL2 ?]]]]; dcr; subst.
    pose proof (@zip_length2 _ _ _ pair Lv2 DL2 H12).
    pose proof (@zip_length2 _ _ _ pair Lv1 DL1 H9).
    rewrite restrict_app.
    repeat rewrite zip_app; try rewrite restrict_length; eauto with len.
    econstructor. eapply IHinRel; eauto; try congruence.
    eapply approx_restrict_block; try congruence.
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
  (EA: inRel approx (zip pair (zip pair Lv' DL) ZL) L L')
  (EQ: (@feq _ _ eq) E E')
  (LV': live_sound Imperative Lv' (compile ZL s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E')
  (LEN1: length DL = length ZL)
  (LEN2: length ZL = length Lv')
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

Lemma approx_mutual_block n ZL DL F F' Za Za' ans ans' ans_lv ans_lv' als als' Lv L1X L2X
      (LEN1:length F = length Za)
      (LEN2:length F = length ans_lv)
      (LEN3:length F = length ans)
      (LEN4:length F = length als)
      (LEN5:length DL = length ZL)
      (LEN6:length ZL = length Lv)
      (DROP1:F' = drop n F)
      (DROP2:Za' = drop n Za)
      (DROP3:ans' = drop n ans)
      (DROP4:ans_lv' = drop n ans_lv)
      (DROP5:als' = drop n als)
      (TRS: forall (n : nat) (ans' : ann (list params))
              (lvs : ann (set var)) (Zs : params * stmt)
              (Zx : params),
          get ans_lv n lvs ->
          get F n Zs ->
          get Za n Zx ->
          get ans n ans' ->
          trs
            (restrict (mkGlobals F Za ans_lv ++ DL)
                      (getAnn lvs \ of_list (fst Zs ++ Zx)))
            (Za ++ ZL) (snd Zs) lvs ans')
      (LIVE : forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
          get (compileF compile ZL F Za Za ans) n Zs ->
          get als n a ->
          live_sound Imperative
                     ( zip pair (getAnn ⊝ als) (fst ⊝ (compileF compile ZL F Za Za ans)) ++ Lv) (snd Zs) a)
  : mutual_block
      (approx
         (zip pair
              (zip pair
                   (zip pair (getAnn ⊝ als) (fst ⊝ (compileF compile ZL F Za Za ans)))
                   (mkGlobals F Za ans_lv)) Za ++ zip pair (zip pair Lv DL) ZL) L1X L2X)
      n
      (zip pair
           (zip pair
                (zip pair (getAnn ⊝ als') (fst ⊝ (compileF compile ZL F' Za' Za ans')))
                (mkGlobals F' Za' ans_lv')) Za')
      (mapi_impl I.mkBlock n F')
      (mapi_impl I.mkBlock n (compileF compile ZL F' Za' Za ans')).
Proof with eapply length_length_eq; subst; eauto using drop_length_stable.
  unfold compileF.
  assert (LEN1':length_eq F' Za'). eauto...
  assert (LEN2':length_eq F' ans_lv'). eauto...
  assert (LEN3':length_eq F' ans'). eauto...
  assert (LEN4':length_eq F' als'). eauto...
  general induction LEN1'; inv LEN2'; inv LEN3'; inv LEN4'.
  - econstructor.
  - simpl. econstructor; eauto.
    + eapply IHLEN1'; eauto using drop_shift_1.
    + unfold I.mkBlock. simpl fst. simpl snd.
      rewrite <- zip_app.
      rewrite <- zip_app; eauto 20 with len.
      econstructor; eauto 20 with len.
      intros. invc H0. split.
      exploit LIVE; eauto 30 using zip_get, drop_eq; eauto with len.
      exploit TRS; eauto 30 using zip_get, drop_eq; eauto with len.
      rewrite of_list_app in H0. rewrite <- minus_union in H0. eauto.
      repeat rewrite zip_length2; eauto 20 with len.
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
      * rewrite EQ; reflexivity.
      * eapply defined_on_update_some. eapply defined_on_incl; eauto.
      * rewrite restrict_length; congruence.
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
    erewrite get_nth_default; eauto.
    erewrite get_nth_default in H8; eauto.
    case_eq (omap (exp_eval E) Y); intros.
    exploit (@zip_get _ _ _ pair Lv' DL); eauto.
    exploit (@zip_get _ _ _ pair (zip pair Lv' DL) ZL); eauto.
    simpl in *.
    inRel_invs.
    erewrite get_nth_default in H6; eauto.
    edestruct (omap_var_defined_on Za); eauto.
    eapply get_in_incl; intros.
    exploit H8. eapply get_app_right. Focus 2.
    eapply map_get_1; eauto. reflexivity. inv H11; eauto.
    + (*exploit get_drop_eq; try eapply LEN1; eauto. subst o.
      exploit get_drop_eq; try eapply H11; eauto. subst x.*)
      one_step.
      * simpl; eauto.
        repeat rewrite app_length in H6. rewrite map_length in H6.
        omega.
      * instantiate (1:=l ++ x).
        rewrite omap_app.
        erewrite omap_agree. Focus 2.
        intros. rewrite <- EQ. reflexivity.
        rewrite H10; simpl. rewrite H1; simpl. reflexivity.
      * exploit RD0; eauto; dcr. simpl.
        eapply trsR_sim. econstructor. eauto.
        eapply approx_restrict.
        Focus 3.
        instantiate (1:=Lv).
        erewrite H9.
        eapply (inRel_drop EA H7).
        congruence. congruence.
        simpl. rewrite map_app.
        rewrite update_with_list_app.
        rewrite (omap_self_update E' Za). rewrite EQ. reflexivity. eauto.
        rewrite map_length.
        exploit omap_length; try eapply H0; eauto.
        exploit omap_length; try eapply H1; eauto.
        repeat rewrite app_length in H6. rewrite map_length in H6. omega.
        eauto.
        eapply defined_on_update_list; eauto using defined_on_incl.
        exploit omap_length; try eapply H0; eauto.
        exploit omap_length; try eapply H1; eauto.
        rewrite map_length in H11.
        repeat rewrite app_length in H6. rewrite map_length in H6.
        repeat rewrite app_length. omega.
        rewrite restrict_length. simpl in H7.
        congruence. congruence.
    + no_step.
      rewrite omap_app in def. monad_inv def.
      erewrite omap_agree in H1. erewrite H1 in EQ0. congruence.
      intros. rewrite EQ. reflexivity.
  - remember (omap (exp_eval E) Y); intros. symmetry in Heqo.
    pose proof Heqo. erewrite omap_agree in H0. Focus 2.
    intros. rewrite EQ. reflexivity.
    destruct o.
    extern_step.
    + eexists; split. econstructor; eauto. congruence.
      eapply trsR_sim; econstructor; eauto using approx_restrict.
      hnf; intros. lud; eauto.
      eauto using defined_on_update_some, defined_on_incl.
      rewrite restrict_length; congruence.
    + eexists; split. econstructor; eauto. congruence.
      eapply trsR_sim; econstructor; eauto using approx_restrict.
      hnf; intros. lud; eauto.
      eauto using defined_on_update_some, defined_on_incl.
      rewrite restrict_length; congruence.
    + no_step.
  - one_step.
    assert (length F = length als).
    unfold compileF in H7.
    rewrite zip_length2 in H7; eauto.
    rewrite zip_length2; eauto. congruence.
    eapply trsR_sim; econstructor; eauto 20 with len.
    + repeat rewrite zip_app; eauto 30 with len.
      econstructor; eauto.
      eapply approx_mutual_block; eauto.
    + simpl in *. eapply defined_on_incl; eauto.
Qed.

Lemma oglobals_compileF_mkGlobals_PIR2 ZL F Za Za' ans ans_lv
      (LEN1 : length F = length ans_lv)
      (LEN2 : length F = length ans)
      (LEN3 : length F = length Za)
  : PIR2 (fstNoneOrR Equal)
         (mkGlobals F Za ans_lv)
         (oglobals (compileF compile ZL F Za Za' ans) ans_lv).
Proof.
  length_equify.
  unfold compileF. simpl.
  general induction LEN1; inv LEN2; inv LEN3; simpl; eauto using PIR2.
  - econstructor.
    + unfold lminus; simpl.
      econstructor. rewrite of_list_app, minus_union. reflexivity.
    + eapply IHLEN1; eauto.
Qed.


Lemma trs_srd AL ZL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  : srd AL (compile ZL s ans) ans_lv.
Proof.
  general induction RD; simpl; eauto using srd.
  - econstructor; eauto.
    * unfold compileF; repeat rewrite zip_length2; congruence.
    * intros. unfold compileF in H4. inv_zip H4.
      inv_zip H7.
      exploit H3; eauto. simpl.
      eapply srd_monotone; eauto.
      eapply restrict_subset; eauto.
      eapply PIR2_app; eauto.
      eapply oglobals_compileF_mkGlobals_PIR2; eauto.
    * eapply srd_monotone; eauto.
      eapply PIR2_app; eauto.
      eapply oglobals_compileF_mkGlobals_PIR2; eauto.
Qed.

Inductive additionalParameters_live : list (set var)   (* additional params *)
                                      -> stmt           (* the program *)
                                      -> ann (set var)  (* liveness *)
                                      -> ann (list (list var)) (* additional params *)
                                      -> Prop :=
| additionalParameters_liveExp ZL x e s an an_lv lv
  : additionalParameters_live ZL s an_lv an
    -> additionalParameters_live ZL (stmtLet x e s) (ann1 lv an_lv) (ann1 nil an)
| additionalParameters_liveIf ZL e s t ans ant ans_lv ant_lv lv
  : additionalParameters_live ZL s ans_lv ans
    -> additionalParameters_live ZL t ant_lv ant
    -> additionalParameters_live ZL (stmtIf e s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
| additionalParameters_liveRet ZL e lv
    :  additionalParameters_live ZL (stmtReturn e) (ann0 lv) (ann0 nil)
| additionalParameters_liveGoto ZL Za f Y lv
  : get ZL (counted f) Za
    -> Za ⊆ lv
    -> additionalParameters_live ZL (stmtApp f Y) (ann0 lv) (ann0 nil)
| additionalParameters_liveExtern ZL x f Y s an an_lv lv
  : additionalParameters_live ZL s an_lv an
    -> additionalParameters_live ZL
                                (stmtExtern x f Y s)
                                (ann1 lv an_lv)
                                (ann1 nil an)
| additionalParameters_liveLet ZL F t (Za:〔〔var〕〕) ans ant lv ans_lv ant_lv
  : (forall Za' lv Zs n, get F n Zs -> get ans_lv n lv -> get Za n Za' ->
       of_list Za' ⊆ getAnn lv \ of_list (fst Zs))
    -> (forall Zs lv a n, get F n Zs -> get ans_lv n lv -> get ans n a ->
                    additionalParameters_live (of_list ⊝ Za ++ ZL) (snd Zs) lv a)
    -> additionalParameters_live ((of_list ⊝ Za) ++ ZL) t ant_lv ant
    -> length Za = length F
    -> additionalParameters_live ZL (stmtFun F t) (annF lv ans_lv ant_lv) (annF Za ans ant).


Lemma live_globals_compileF_PIR2 F als Lv Za Za' ans ZL
      (LEN1 : length F = length als)
      (LEN2 : length F = length ans)
      (LEN3 : length F = length Za)
  : PIR2 live_ann_subset
         (zip (fun (s : set var * params) (t : params) => (fst s, snd s ++ t))
              ( zip pair (getAnn ⊝ als) (fst ⊝ F) ++ Lv) (Za ++ ZL))
         (zip pair (getAnn ⊝ als) (fst ⊝ (compileF compile ZL F Za Za' ans)) ++
                                zip (fun (s : set var * params) (t : params) => (fst s, snd s ++ t)) Lv ZL).
Proof.
  length_equify. unfold compileF.
  general induction LEN1; inv LEN2; inv LEN3; eauto using PIR2.
  econstructor; simpl; eauto.
Qed.

Lemma live_sound_compile DL ZL AL s ans_lv ans o
  (RD:trs AL ZL s ans_lv ans)
  (LV:live_sound o DL s ans_lv)
  (APL: additionalParameters_live (of_list ⊝ ZL) s ans_lv ans)
  : live_sound o (zip (fun s t => (fst s, snd s ++ t)) DL ZL) (compile ZL s ans) ans_lv.
Proof.
  general induction LV; inv RD; inv APL; eauto using live_sound.
  -
    pose proof (zip_get  (fun (s : set var * list var) (t : list var) => (fst s, snd s ++ t)) H H10).
    inv_zip H3; simpl in *.
    repeat get_functional.
    econstructor. eapply H3; eauto.
    cases. simpl in * |- *.
    rewrite of_list_app. cset_tac. intuition. eauto.
    erewrite get_nth; eauto. eauto with len.
    erewrite get_nth; eauto.
    intros ? ? GET. inv_get; simpl in *; clear_trivial_eqs.
    eapply get_app_cases in GET. destruct GET; dcr; eauto. inv_get.
    econstructor. rewrite <- H9. eauto using get_in_of_list.
  - rewrite <- map_app in H20. rewrite <- map_app in H19.
    simpl. econstructor; eauto.
    + exploit IHLV; eauto.
      eapply live_sound_monotone; eauto.
      eapply live_globals_compileF_PIR2; eauto.
    + unfold compileF. eauto with len.
    + intros.
      unfold compileF in H4. inv_get. simpl.
      exploit H1; eauto.
      eapply live_sound_monotone; eauto.
      eapply live_globals_compileF_PIR2; eauto.
    + intros.
      unfold compileF in H4. inv_get; simpl.
      exploit H2; eauto. exploit H13; eauto. dcr.
      split.
      * rewrite of_list_app.
        rewrite H10, H9. eauto with cset.
      * cases; eauto. rewrite of_list_app.
        rewrite <- minus_union. rewrite <- H11. eauto with cset.
Qed.
