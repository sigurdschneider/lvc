Require Import Util CSet CMap MoreExp SetOperations OUnion.
Require Import IL InRel RenamedApart LabelsDefined Restrict.
Require Import Annotation Liveness Coherence Delocation.
Require Import Bisim BisimTactics.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.
Unset Printing Abstraction Types.
Local Arguments lminus {X} {H} s L.

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

Global Instance update_with_list_inst X `{OrderedType X} Y `{OrderedType Y} :
  Proper (eq ==> (list_eq (option_eq eq)) ==> (@feq X (option Y) eq ) ==> (@feq _ _ eq))
         (@update_with_list X _ (option Y)).
Proof.
  unfold respectful, Proper; intros. subst.
  general induction H2; simpl; eauto.
  - destruct y; simpl; eauto.
  - destruct y; simpl; eauto.
    hnf; intros. lud.
    inv H; eauto.
    eapply IHlist_eq; eauto.
Qed.

Lemma trsR_sim σ1 σ2
  : trsR σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros. destruct H; inv RD; invt live_sound; simpl.
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
        simpl. rewrite List.map_app.
        rewrite update_with_list_app.
        rewrite (omap_self_update E' Za H10). rewrite EQ. reflexivity.
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
    + extern_step; try congruence.
      eapply trsR_sim; econstructor; eauto using approx_restrict.
      hnf; intros. lud; eauto.
      eauto using defined_on_update_some, defined_on_incl.
      rewrite restrict_length; congruence.
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
