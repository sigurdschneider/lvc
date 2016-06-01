Require Import Util CSet CMap MoreExp SetOperations OUnion.
Require Import IL InRel RenamedApart LabelsDefined Restrict.
Require Import Annotation Liveness Coherence Delocation.
Require Import Bisim BisimTactics.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.
Unset Printing Abstraction Types.


Inductive mutual_block {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
: nat -> list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C -> Prop :=
  | CS_nil n : mutual_block R n nil nil nil nil nil nil
  | CS_cons a1 a2 a3 a4 b c n AL1 AL2 AL3 AL4 L L' :
      mutual_block R (S n) AL1 AL2 AL3 AL4 L L'
      -> n = block_n b
      -> n = block_n c
      -> R a1 a2 a3 a4 b c
      -> mutual_block R n (a1::AL1) (a2::AL2) (a3::AL3) (a4::AL4) (b::L) (c::L').


Lemma mutual_block_zero {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b i
: mutual_block R i AL1 AL2 AL3 AL4 L L' -> get L n b -> block_n b = (n+i).
Proof.
  intros. general induction H2. inv H1; eauto.
  inv H1; eauto. erewrite IHget; eauto. omega.
Qed.

Lemma mutual_block_length {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C} (R:A1->A2->A3->A4->B->C->Prop)
      AL1 AL2 AL3 AL4 (L1:list B) (L2:list C) i
: mutual_block R i AL1 AL2 AL3 AL4 L1 L2 -> ❬AL1❭ = ❬L1❭ /\ ❬AL2❭ = ❬L1❭ /\ ❬AL3❭ = ❬L1❭  /\ ❬AL4❭ = ❬L1❭ /\ ❬L2❭ = ❬L1❭.
Proof.
  intros. general induction H1; dcr; simpl; eauto.
  repeat split; omega.
Qed.


Lemma mutual_approx {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 AL1' AL2' AL3' AL4' F1 F2 L1 L2
  : length AL1' = length F1
    -> length AL1' = length AL2'
    -> length AL2' = length AL3'
    -> length AL3' = length AL4'
    -> length F1 = length F2
    -> (forall n a1 a2 a3 a4 b b', get AL1' n a1 -> get AL2' n a2 -> get AL3' n a3 -> get AL4' n a4
                             -> get F1 n b -> get F2 n b' -> R AL1 AL2 AL3 AL4 L1 L2 a1 a2 a3 a4 b b')
    -> (forall i b, get F1 i b -> i = block_n b)
    -> (forall i b, get F2 i b -> i = block_n b)
    -> mutual_block (R AL1 AL2 AL3 AL4 L1 L2) 0 AL1' AL2' AL3' AL4' F1 F2.
Proof.
Admitted.

Inductive inRel {A1 A2 A3 A4} {B} `{BlockType B} {C} `{BlockType C}
          (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
             A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
: list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C -> Prop :=
  | LPM_nil : inRel R nil nil nil nil nil nil
  | LPM_app AL1 AL2 AL3 AL4 AL1' AL2' AL3' AL4' L1 L2 L1' L2' :
      inRel R AL1 AL2 AL3 AL4 L1 L2
      -> mutual_block (R (AL1'++AL1) (AL2'++AL2) (AL3'++AL3) (AL4'++AL4) (L1'++L1) (L2'++L2))
                     0 AL1' AL2' AL3' AL4' L1' L2'
      -> inRel R (AL1'++AL1) (AL2'++AL2) (AL3'++AL3) (AL4'++AL4) (L1'++L1) (L2'++L2).

Inductive approx
  : list params
    -> list (set var)
    -> list (option (set var))
    -> list params
    -> list I.block
    -> list I.block
    -> params
    -> set var
    -> option (set var)
    -> params
    -> I.block
    -> I.block -> Prop :=
  blk_approxI o (Za Z':list var) ZL Lv DL ZAL s ans ans_lv ans_lv' n L1 L2
              (RD:forall G, o = Some G ->
                       live_sound Imperative (@List.app _ ⊜ ZL ZAL) Lv (compile ZAL s ans) ans_lv'
                       /\ trs (restr G ⊝ DL) ZAL s ans_lv ans)
  : length DL = length ZL
  -> length ZL = length Lv
  -> approx ZL Lv DL ZAL L1 L2 Z' (getAnn ans_lv') o Za (I.blockI Z' s n) (I.blockI (Z'++Za) (compile ZAL s ans) n).

Lemma mutual_block_restrict AL1' AL1 AL2' AL2 AL3' AL3 AL4' AL4 L1' L1 L2' L2 G n
  : mutual_block
      (approx AL1 AL2 AL3 AL4 L1 L2) n AL1' AL2' AL3' AL4' L1' L2'
    -> mutual_block (approx AL1 AL2 (restr G ⊝ AL3) AL4 L1 L2)
                   n AL1' AL2' (restr G ⊝ AL3') AL4' L1' L2'.
Proof.
  intros. general induction H; eauto using @mutual_block.
  simpl.
  econstructor; eauto.
  inv H2. econstructor; eauto with len.
  intros.
  destruct a3; isabsurd; simpl in *; cases in H4; isabsurd.
  edestruct RD; eauto.
  split; eauto. rewrite restrict_idem; eauto.
Qed.

Lemma approx_restrict ZL Lv DL ZAL L L' G
  : inRel approx ZL Lv DL ZAL L L'
    -> inRel approx ZL Lv (restr G ⊝ DL) ZAL L L'.
Proof.
  intros IR.
  general induction IR; simpl in *; eauto using @inRel.
  - rewrite List.map_app. econstructor; eauto.
    rewrite <- List.map_app.
    eapply mutual_block_restrict. eauto.
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

(*
Lemma mutual_approx_impl {A} {B} `{BlockType B} {C} `{BlockType C}
      (R: list A -> list B -> list C -> A -> B -> C -> Prop)
      (AL:list A) DL F1 F2 AL' F1' F2' i L1 L2
  : length AL = length F1
    -> length F1 = length F2
    -> F1' = drop i F1
    -> F2' = drop i F2
    -> AL' = drop i AL
    -> (forall n a b b', get AL n a -> get F1 n b -> get F2 n b' -> R DL L1 L2 a b b')
    -> (forall i b, get F1 i b -> i = block_n b)
    -> (forall i b, get F2 i b -> i = block_n b)
    -> mutual_block (R DL L1 L2) i AL' F1' F2'.
Proof.
  intros LenEq1 LenEq2 LenF1' LenF2' LenAL' GET I1 I2.
  assert (LenAL1:length_eq AL' F1'). subst; eauto using drop_length_stable with len.
  assert (LenAL2:length_eq AL' F2'). subst; eauto using drop_length_stable with len.
  general induction LenAL1; inv LenAL2; eauto using @mutual_block.
  - econstructor; eauto using drop_eq.
    eapply IHLenAL1; eauto using drop_shift_1.
Qed.
 *)

(*

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
 *)

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

Lemma inRel_less {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b
: inRel R AL1 AL2 AL3 AL4 L L' -> get L n b -> block_n b <= n.
Proof.
  intros. general induction H1. inv H2; eauto.
  eapply get_app_cases in H3; destruct H3; dcr.
  erewrite mutual_block_zero; eauto. omega.
  rewrite IHinRel; try eapply H4. omega.
Qed.

Lemma inRel_drop {A1 A2 A3 A4:Type} {B} `{BlockType B} {C} `{BlockType C}
      (R:list A1 -> list A2 -> list A3 -> list A4 -> list B -> list C ->
         A1 -> A2 -> A3 -> A4 -> B -> C -> Prop)
      AL1 AL2 AL3 AL4 (L:list B) (L':list C) n b
: inRel R AL1 AL2 AL3 AL4 L L'
  -> get L n b
  -> inRel R
          (drop (n - block_n b) AL1)
          (drop (n - block_n b) AL2)
          (drop (n - block_n b) AL3)
          (drop (n - block_n b) AL4)
          (drop (n - block_n b) L)
          (drop (n - block_n b) L').
Proof.
  intros. general induction H1; simpl; eauto; isabsurd.
  - eapply get_app_cases in H3; destruct H3; dcr.
    + exploit (mutual_block_zero H2 H3); eauto.
      rewrite H4. orewrite (n - (n + 0)= 0). simpl; econstructor; eauto.
    + exploit (inRel_less H1 H4); eauto.
      specialize (IHinRel _ _ H4).
      assert (length L1' + (n - length L1') = n) by omega.
      rewrite <- H6.
      orewrite (length L1' + (n - length L1') - block_n b
                = length L1' + (n - length L1' - block_n b)).
      exploit (mutual_block_length H2); dcr.
Admitted.

Lemma inRel_nth {A} {B} `{BlockType B} {C} `{BlockType C} R
      (AL:list A) (L:list B) (L':list C) n b
: inRel R AL L L' -> get L n b ->
  exists a:A, exists c:C,
    get AL n a /\ get L' n c /\ R (drop (n - block_n b) AL) (drop (n - block_n b) L) (drop (n - block_n b) L') a b c.
Proof.
  intros. general induction H1; isabsurd.
  eapply get_app_cases in H3; destruct H3; dcr.
  - exploit (mutual_block_zero H2 H3); eauto. rewrite H4.
    orewrite (n - (n + 0) = 0). simpl.
    edestruct (mutual_block_get H2 H3) as [? [? [? []]]].
    do 2 eexists. repeat split; eauto using get_app.
  - edestruct IHinRel; eauto; dcr. do 2 eexists.
    pose proof (mutual_block_length H2); dcr.
    repeat split; try (eapply get_app_right; eauto; omega).
    orewrite (n = length L1' + (n - length L1')).
    exploit (inRel_less H1 H4).
    orewrite (length L1' + (n - length L1') - block_n b
              = length L1' + (n - length L1' - block_n b)).
    Typeclasses eauto :=10.
    rewrite <- H8 at 1. repeat rewrite drop_app. rewrite H10. rewrite drop_app.
    rewrite <- H10. eauto.
Qed.

Tactic Notation "inRel_invs" :=
match goal with
  | [ H : inRel ?R ?A ?B ?C, H' : get ?B ?n ?b |- _ ] =>
    let InR := fresh "InR" in let G := fresh "G" in
    edestruct (inRel_nth H H') as [? [? [? [G InR]]]]; (try eassumption); dcr; inversion InR; try subst;
    let X'' := fresh "H" in pose proof (inRel_drop H H') as X'';
    repeat get_functional; (try subst)
end.

Lemma trsR_sim (E E':onv val) L L' s ans Lv' ans_lv ans_lv' DL ZL ZAL
  (RD: trs DL ZAL s ans_lv ans)
  (EA: inRel approx ZL Lv' DL ZAL L L')
  (EQ: (@feq _ _ eq) E E')
  (LV': live_sound Imperative (app (A:=var) ⊜ ZL ZAL) Lv' (compile ZAL s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E')
  (LEN1: length DL = length ZL)
  (LEN2: length ZL = length Lv')
  : bisim (L, E, s) (L', E', compile ZAL s ans).
Proof.
  revert_all. cofix; intros.
  inv RD; invt live_sound; simpl.
  - remember (exp_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H0.
    destruct o.
    + one_step. simpl in *.
      eapply trsR_sim; eauto using approx_restrict with len.
      * rewrite EQ; reflexivity.
      * eapply defined_on_update_some. eapply defined_on_incl; eauto.
    + no_step.
  - remember (exp_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H1.
    destruct o.
    case_eq (val2bool v); intros.
    + one_step. eapply trsR_sim; eauto using defined_on_incl.
    + one_step. eapply trsR_sim; eauto using defined_on_incl.
    + no_step.
  - no_step. simpl. rewrite EQ; eauto.
  - simpl counted in *.
    erewrite get_nth_default; eauto.
    erewrite get_nth_default in H8; eauto.
    case_eq (omap (exp_eval E) Y); intros.
    +
(*    exploit (@zip_get _ _ _ pair Lv' DL); eauto.
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
        congruence. congruence.*)
      admit.
    + no_step.
      rewrite omap_app in def. monad_inv def.
      erewrite omap_agree in H1. erewrite H1 in EQ0. congruence.
      intros. rewrite EQ. reflexivity.
  - remember (omap (exp_eval E) Y); intros. symmetry in Heqo.
    pose proof Heqo. erewrite omap_agree in H0. Focus 2.
    intros. rewrite EQ. reflexivity.
    destruct o.
    + extern_step; try congruence.
      * eapply trsR_sim; eauto using approx_restrict with len.
        hnf; intros. lud; eauto.
        eauto using defined_on_update_some, defined_on_incl.
      * eapply trsR_sim; eauto using approx_restrict with len.
        hnf; intros. lud; eauto.
        eauto using defined_on_update_some, defined_on_incl.
    + no_step.
  - one_step.
    assert (length F = length als).
    rewrite <- H7. eauto with len.
    rewrite fst_compileF_eq in H6; eauto with len.
    rewrite <- zip_app in H6; eauto with len.
    eapply trsR_sim; eauto 20 with len.
    + repeat rewrite zip_app; eauto 30 with len.
      econstructor; eauto.
      eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
      * intros; inv_get.
        exploit H8; eauto.
        unfold I.mkBlock. unfold compileF in H15. inv_get. simpl in *.
        eapply blk_approxI; eauto 20 with len.
        intros. invc H15. split; eauto.
        rewrite fst_compileF_eq in H10; eauto with len.
        rewrite <- zip_app in H10; eauto with len.
    + simpl in *. eapply defined_on_incl; eauto.
Qed.
