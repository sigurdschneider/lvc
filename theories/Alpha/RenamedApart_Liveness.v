Require Import Util LengthEq AllInRel Map CSet SetOperations MoreList Indexwise.
Require Import Val Var Env IL LabelsDefined Annotation Subset1 CSetDisjoint PairwiseDisjoint.
Require Import Liveness Restrict RenamedApart.

Set Implicit Arguments.


Lemma params_length (F:list (params * stmt)) (ans:list (ann (set var * set var)))
: length F = length ans
  -> List.map (fst ∘ length (A:=var)) F
    = List.map (snd ∘ length (A:=var)) (zip pair (getAnn ⊝ (List.map (mapAnn fst) ans)) (fst ⊝ F)).
Proof.
  intros. length_equify. general induction H; simpl; eauto; f_equal; eauto.
Qed.

Lemma renamedApart_live_functional s ang ZL Lv
: renamedApart s ang
  -> paramsMatch s (@length _ ⊝ ZL)
  -> length ZL = length Lv
  -> live_sound Functional ZL Lv s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - eauto 9 using @live_sound, live_exp_sound_incl, live_freeVars
            with ann pe cset.
  - eauto 9 using @live_sound, live_op_sound_incl, Op.live_freeVars
    with ann pe cset.
  - eauto using live_sound, live_op_sound_incl, Op.live_freeVars.
  - inv_get.
    econstructor; simpl;
      eauto using live_op_sound_incl, Op.live_freeVars, get_list_union_map with cset.
  - econstructor; eauto with len.
    + intros; inv_get. eapply H1; eauto with len.
    + intros; inv_get. edestruct H2; eauto; dcr.
      cases; split; pe_rewrite; eauto with cset pe ann.
    + eauto with cset pe ann.
Qed.

Lemma indexwise_R_bounded D Dt F ans
:  indexwise_R (funConstr D Dt) F ans
   -> bounded
       (Some ⊝ (fst ⊝ getAnn ⊝ ans) \\ (fst ⊝ F)) D.
Proof.
  intros.
  eapply get_bounded.
  intros; inv_get.
  edestruct H; eauto; dcr.
  eauto with cset pe ann.
Qed.

Lemma zip_lminus_get X `{OrderedType X} ZL n Z Lv lv
  : get ZL n Z
    -> get Lv n lv
    -> get (Lv \\ ZL) n (lv \ of_list Z).
Proof.
  intros GetZL GetLv. eapply (zip_get (@lminus _ _) GetLv GetZL).
Qed.

Hint Resolve zip_lminus_get.

Lemma renamedApart_live s ang ZL Lv i
: renamedApart s ang
  -> paramsMatch s (@length _ ⊝ ZL)
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> length ZL = length Lv
  -> live_sound i ZL Lv s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl in * |- *; pe_rewrite.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars with cset pe ann.
  - econstructor; eauto using live_op_sound_incl, Op.live_freeVars with cset pe ann.
  - econstructor; eauto using live_op_sound_incl, Op.live_freeVars with cset.
  - inv_get.
    econstructor; simpl;
    eauto using live_op_sound_incl, Op.live_freeVars, get_list_union_map with cset.
    + cases; eauto.
      eapply bounded_get; eauto using map_get_1.
  - assert (bounded (Some ⊝ (getAnn ⊝ mapAnn fst ⊝ ans ++ Lv) \\ (fst ⊝ F ++ ZL)) D). {
      rewrite zip_app; eauto with len.
      rewrite List.map_app.
      rewrite getAnn_mapAnn_map.
      rewrite bounded_app; split; eauto using indexwise_R_bounded.
    }
    econstructor; eauto with len.
    + intros. inv_get.
      eapply H1; eauto.
      * edestruct H2; eauto; dcr. rewrite H15.
        rewrite zip_app; eauto with len.
        rewrite List.map_app. rewrite <- incl_right.
        rewrite getAnn_mapAnn_map.
        rewrite bounded_app; split; eauto using indexwise_R_bounded.
      * eauto with len.
    + intros. inv_get. edestruct H2; eauto; dcr.
      cases; eauto with cset pe ann.
    + eauto with cset pe ann.
Qed.

Lemma disjoint_let X `{OrderedType X} (D D' D'':set X) x ZL (Lv:list (set X)) an
: D''[=]{x; D'}
  -> disjoint (Some ⊝ Lv \\ ZL) (D'')
  -> pe (getAnn an) ({x; D}, D')
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros EQ Disj PE. rewrite PE. rewrite EQ in *. eauto using disjoint_incl with cset.
Qed.

Lemma disjoint_if1 X `{OrderedType X} (D D':⦃X⦄) Ds Dt  ZL Lv an
:  Ds ∪ Dt [=] D'
  -> disjoint (Some ⊝ Lv \\ ZL) D'
  -> pe (getAnn an) (D, Ds)
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros EQ Disj PE. rewrite PE. rewrite <- EQ in *. simpl.
  eauto using disjoint_incl with cset.
Qed.

Lemma disjoint_if2 X `{OrderedType X} (D D':⦃X⦄) Ds Dt ZL Lv an
:  Ds ∪ Dt [=] D'
  -> disjoint (Some ⊝ Lv \\ ZL) D'
  -> pe (getAnn an) (D, Dt)
  -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn an)).
Proof.
  intros EQ Disj PE. rewrite PE. rewrite <- EQ in *. simpl.
  eauto using disjoint_incl with cset.
Qed.

Lemma disjoint_funF1 ZL Lv D D' F ans Dt lv als
: disjoint (Some ⊝ Lv \\ ZL) D'
  -> list_union (zip defVars F ans) ∪ Dt[=]D'
  -> indexwise_R (funConstr D Dt) F ans
  -> (forall n a b, get als n a -> get ans n b -> ann_R Subset1 a b)
  -> lv ⊆ D'
  -> length F = length ans
  -> length F = length als
  -> disj D D'
  -> disjoint (Some ⊝ ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))) lv.
Proof.
  intros.
  rewrite zip_app; eauto with len.
  rewrite List.map_app.
  rewrite disjoint_app; split.
  - hnf; intros n s A.
    inv_get; subst; simpl in *.
    edestruct (get_length_eq _ A H4).
    edestruct H1; eauto; dcr. exploit H2; eauto.
    eapply ann_R_get in H11.
    destruct (getAnn x2); simpl in *.
    repeat get_functional.
    rewrite H3. rewrite H11. rewrite H10.
    eauto with cset.
  - rewrite H3; eauto.
Qed.

Lemma lv_incl F ans Dt D' k a Zs
: list_union (zip defVars F ans) ∪ Dt[=]D'
  -> get ans k a
  -> get F k Zs
  -> snd (getAnn a) ⊆ D'.
Proof.
  intros.
  rewrite <- H. eapply incl_union_left.
  eapply incl_list_union. eapply zip_get; try eapply H3; eauto.
  unfold defVars; eapply incl_right.
Qed.

Hint Resolve disjoint_funF1 lv_incl : cset.

(* Coq ist so doof *)
Lemma renamedApart_disj_F s D D' ans ant
  :  renamedApart s (annF (D, D') ans ant)
     -> disj D D'.
Proof.
  intros H. eapply (renamedApart_disj H).
Qed.

Lemma incl_minus_disj X `{OrderedType X} s t D Ds x
  : s ⊆ t
    -> disj s D
    -> D [=] {x; Ds}
    -> s ⊆ t \ singleton x.
Proof.
  intros. eauto with cset.
Qed.

Hint Immediate incl_minus_disj renamedApart_disj_F : cset.

Lemma funConstr_disjoint_fun_defs F ans alvs D Dt k a
  : length F = length ans
    -> length F = length alvs
    -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
          get alvs n a -> get ans n b -> ann_R Subset1 a b)
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans)
    -> disj D (list_union (defVars ⊜ F ans) ∪ Dt)
    -> get ans k a
    -> disj (fst (getAnn a)) (snd (getAnn a))
    -> disjoint (Some ⊝ (getAnn ⊝ alvs) \\ (fst ⊝ F)) (snd (getAnn a)).
Proof.
  intros. hnf; intros; inv_get.
  edestruct H2; eauto; dcr.
  exploit H1 as A; eauto. eapply ann_R_get in A.
  decide (k = n); subst.
  - repeat get_functional. eauto with cset.
  - exploit H3 as B; [ eauto | eauto using zip_get | eauto using zip_get|].
    unfold defVars in B.
    exploit H1 as C; try eapply H10; eauto. eapply ann_R_get in C.
    edestruct H2; try eapply H10; eauto; dcr.
    rewrite C. rewrite H13.
    eapply disj_1_incl. eapply disj_2_incl. eapply H4.
    + eapply incl_union_left.
      eapply incl_list_union; eauto using zip_get.
      unfold defVars. eapply incl_right.
    + clear_all; cset_tac.
Qed.

Lemma renamedApart_globals_live_F ZL Lv F ans als D Dt D' f lv' Z' l'
      (LEN1 : ❬F❭ = ❬als❭)
      (LEN2 : ❬F❭ = ❬ans❭)
      (IH : forall k Zs, get F k Zs ->
                    forall (ZL : 〔params〕) (Lv : 〔⦃var⦄〕) (alv : ann ⦃var⦄)
                      (f : lab) (ang : ann (⦃var⦄ * ⦃var⦄)),
                      live_sound Imperative ZL Lv (snd Zs) alv ->
                      renamedApart (snd Zs) ang ->
                      isCalled (snd Zs) f ->
                      ann_R Subset1 alv ang ->
                      disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn ang)) ->
                      exists (lv : ⦃var⦄) (Z : params),
                        get ZL (labN f) Z /\ get Lv (labN f) lv
                        /\ lv \ of_list Z ⊆ getAnn alv)
      (LS: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (RA:forall (n : nat) (Zs : params * stmt) (a : ann (⦃var⦄ * ⦃var⦄)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (IW:indexwise_R (funConstr D Dt) F ans)
      (PWD:PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans))
      (DEQ:list_union (defVars ⊜ F ans) ∪ Dt [=] D')
      (Disj : disj D D')
      (DisjZL : disjoint (Some ⊝ Lv \\ ZL) D')
      (Sub: forall (n : nat) (a : ann ⦃var⦄) (b : ann (⦃var⦄ * ⦃var⦄)),
          get als n a -> get ans n b -> ann_R Subset1 a b)
      (CC:callChain isCalled F l' f)
      (GetZL : get (fst ⊝ F ++ ZL) (labN l') Z')
      (GetLv : get (getAnn ⊝ als ++ Lv) (labN l') lv')
  : exists (lv : ⦃var⦄) (Z : params),
    get (fst ⊝ F ++ ZL) (labN f) Z /\ get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ lv \ of_list Z ⊆ lv' \ of_list Z'.
Proof.
  general induction CC.
  - destruct l; simpl in *.
    do 2 eexists; split; [| split]; eauto with cset.
  - inv_get. exploit (IH k Zs); eauto.
    + rewrite zip_app, List.map_app; [| eauto with len].
      eapply disjoint_app. split.
      eapply funConstr_disjoint_fun_defs; eauto.
      rewrite DEQ. eauto.
      eapply renamedApart_disj. eauto.
      assert (D'Incl:snd (getAnn x) ⊆ D'). {
        rewrite <- DEQ. eapply incl_union_left.
        eapply incl_list_union; eauto using zip_get.
        unfold defVars. eapply incl_right.
      }
      rewrite D'Incl. eauto.
    + dcr.
      exploit IHCC; eauto. dcr.
      do 2 eexists; split; [| split ]; eauto.
      rewrite <- H7, <- H10.
      simpl in *.
      assert ((of_list (fst Zs)) ⊆ D'). {
        rewrite <- DEQ. eapply incl_union_left.
        eapply incl_list_union. eapply zip_get; eauto.
        unfold defVars. eauto with cset.
      }
      eapply get_app_cases in H8. destruct H8; dcr; inv_get.
      * eapply not_incl_minus; [ reflexivity | ].
        exploit Sub; eauto. eapply ann_R_get in H6.
        edestruct IW; eauto; dcr.
        rewrite H6. rewrite H12.
        eapply disj_1_incl. eapply disj_2_incl. eapply Disj.
        eauto. eauto with cset.
      * assert (LEQ:❬getAnn ⊝ als❭ = ❬fst ⊝ F❭) by eauto with len.
        rewrite LEQ in *. rewrite get_app_ge in H6; eauto.
        assert (disj (x3 \ of_list x4) D'). {
          eapply disj_1_incl; [ eapply DisjZL | ].
          eapply map_get_eq.
          eapply zip_get; eauto.
          reflexivity. reflexivity.
        }
        eauto with cset.
Qed.

Lemma renamedApart_globals_live s ZL Lv alv f ang
  : live_sound Imperative ZL Lv s alv
    -> renamedApart s ang
    -> isCalled s f
    -> ann_R Subset1 alv ang
    -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn ang))
    -> exists lv Z, get ZL (counted f) Z
              /\ get Lv (counted f) lv
              /\ (lv \ of_list Z) ⊆ getAnn alv.
Proof.
  revert ZL Lv alv f ang.
  sind s; destruct s; simpl; intros; invt live_sound;
    invt renamedApart; invt (@ann_R); invt isCalled; simpl in * |- *.
  - edestruct (IH s); dcr; eauto using disjoint_let.
    + do 2 eexists; split; [| split]; eauto with cset.
      exploit H3; eauto.
      rewrite <- H12.
      eauto with cset.
  - edestruct (IH s1); dcr; eauto using disjoint_if1.
    do 2 eexists; split; [| split]; eauto. rewrite <- H13; eauto.
  - edestruct (IH s2); dcr; eauto using disjoint_if2 with cset.
  - eauto.
  - clear H H1. eapply renamedApart_disj in H0. simpl in *.
    exploit (IH s); eauto. pe_rewrite. eauto with cset.
    dcr. simpl in *; inv_get.
    setoid_rewrite <- H13; setoid_rewrite <- H19.
    exploit renamedApart_globals_live_F; eauto.
    intros. eapply (IH (snd Zs)); eauto.
    dcr. destruct f; simpl in *. inv_get.
    eauto.
Qed.

Lemma renamedApart_globals_live_From s F als ans D Dt D' ZL Lv alv f ang
      (ICF:isCalledFrom isCalled F s f)
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) s alv)
      (RA:renamedApart s ang)
      (AnnR:ann_R Subset1 alv ang)
      (Incl: snd (getAnn ang) ⊆ D')
      (LEN1 : ❬F❭ = ❬als❭)
      (LEN2 : ❬F❭ = ❬ans❭)
      (LSF: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (RAF:forall (n : nat) (Zs : params * stmt) (a : ann (⦃var⦄ * ⦃var⦄)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (IW:indexwise_R (funConstr D Dt) F ans)
      (PWD:PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans))
      (DEQ:list_union (defVars ⊜ F ans) ∪ Dt [=] D')
      (Disj : disj D D')
      (DisjZL : disjoint (Some ⊝ Lv \\ ZL) D')
      (Sub: forall (n : nat) (a : ann ⦃var⦄) (b : ann (⦃var⦄ * ⦃var⦄)),
          get als n a -> get ans n b -> ann_R Subset1 a b)
  : exists (lv : ⦃var⦄) (Z : params),
    get (fst ⊝ F ++ ZL) (labN f) Z /\
    get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ (lv \ of_list Z) ⊆ getAnn alv.
Proof.
  destruct ICF as [? [IC CC]]; dcr.
  exploit renamedApart_globals_live; eauto using disjoint_funF1.
  dcr.
  setoid_rewrite <- H3.
  simpl in *.
  exploit renamedApart_globals_live_F; eauto using get_app_right.
  intros. eapply renamedApart_globals_live; eauto.
Qed.

Lemma renamedApart_live_imperative_is_functional s ang ZL Lv alv
  : renamedApart s ang
    -> noUnreachableCode isCalled s
    -> live_sound Imperative ZL Lv s alv
    -> ann_R Subset1 alv ang
    -> disjoint (Some ⊝ Lv \\ ZL) (snd (getAnn ang))
    -> live_sound FunctionalAndImperative ZL Lv s alv.
Proof.
  intros RA NUC LS AR DISJ.
  general induction LS; invt noUnreachableCode; invt renamedApart; invt (@ann_R);
    eauto 50 using live_sound, disjoint_let, disjoint_if1, disjoint_if2.
  - econstructor; simpl; eauto.
    + eapply IHLS; eauto using disjoint_funF1.
      eapply disjoint_funF1; eauto.
      * simpl. pe_rewrite. rewrite <- H16. eapply incl_right.
      * simpl. eapply renamedApart_disj in RA. eauto.
    + intros. inv_get.
      eapply H1; eauto.
      eapply disjoint_funF1; eauto. simpl.
      eapply lv_incl; eauto. simpl.
      eapply renamedApart_disj in RA. eauto.
    + intros. inv_get.
      edestruct H8; eauto using get_range; dcr.
      simpl in *.
      edestruct (@renamedApart_globals_live);
          eauto using get_range; simpl in *; dcr.
      * eapply disjoint_funF1; eauto. pe_rewrite.
        rewrite <- H16; eapply incl_right.
        eapply renamedApart_disj in RA; eauto.
      * edestruct (@renamedApart_globals_live_F);
          eauto using get_range, renamedApart_globals_live; simpl in *; dcr.
        eapply renamedApart_disj in RA; eauto.
        rewrite <- H3, <- H27. split; eauto.
        exploit H2; eauto.
        eapply get_in_range_app in H28; eauto using get_range.
        inv_get. eauto.
Qed.

Fixpoint mapAnn2 X X' Y (f:X -> X' -> Y) (a:ann X) (b:ann X') : ann Y :=
  match a, b with
    | ann1 a an, ann1 b bn => ann1 (f a b) (mapAnn2 f an bn)
    | ann2 a an1 an2, ann2 b bn1 bn2 => ann2 (f a b) (mapAnn2 f an1 bn1) (mapAnn2 f an2 bn2)
    | ann0 a, ann0 b => ann0 (f a b)
    | annF a anF an2, annF b bnF bn2 =>
      annF (f a b) (zip (mapAnn2 f) anF bnF) (mapAnn2 f an2 bn2)
    | a, b => ann0 (f (getAnn a) (getAnn b))
  end.

Lemma getAnn_mapAnn2 A A' A'' (a:ann A) (b:ann A') (f:A->A'->A'') s
: annotation s a
  -> annotation s b
  -> getAnn (mapAnn2 f a b) = f (getAnn a) (getAnn b).
Proof.
  intros ANa ANb. general induction ANa; inv ANb; simpl; eauto.
Qed.

Lemma renamedApart_annotation s ang
: renamedApart s ang
  -> annotation s ang.
Proof.
  intros. general induction H; eauto 20 using @annotation.
Qed.

Lemma live_op_sound_meet e D lv
  : Op.freeVars e ⊆ D
   -> live_op_sound e lv
   -> live_op_sound e (lv ∩ D).
Proof.
  intros.
  eapply Op.freeVars_live in H0.
  eapply live_op_sound_incl; eauto using Op.live_freeVars.
  rewrite <- H, <- H0. cset_tac; intuition.
Qed.

Lemma live_exp_sound_meet e D lv
  : Exp.freeVars e ⊆ D
   -> live_exp_sound e lv
   -> live_exp_sound e (lv ∩ D).
Proof.
  intros.
  eapply Exp.freeVars_live in H0.
  eapply live_exp_sound_incl; eauto using Exp.live_freeVars.
  rewrite <- H, <- H0. cset_tac; intuition.
Qed.

Local Hint Extern 0 => pe_rewrite_step : cset.

Notation "'meet1'" := (fun (x:set var) (y:set var * set var) => x ∩ fst y).

Lemma meet1_incl a b
: meet1 a b ⊆ a.
Proof.
  destruct b; simpl. cset_tac; intuition.
Qed.

Lemma meet1_Subset s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset (mapAnn2 meet1 alv ang) alv.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl.
  - econstructor; eauto using meet1_incl. (* todo make HintDb len solve this *)
    rewrite zip_length2; congruence.
    intros. destruct (get_length_eq _ H3 (eq_sym H)).
    inv_zip H2. get_functional; subst.
    eapply H1; eauto.
Qed.

Instance meet1_morphism
: Proper (Subset ==> @pe _ _ ==> Subset) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Instance meet1_morphism'
: Proper (Equal ==> @pe _ _ ==> Equal) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Hint Resolve meet1_incl : cset.

Lemma meet1_incl2 a b
: Subset1 (meet1 a b) b.
Proof.
  destruct b; simpl. hnf. cset_tac; intuition.
Qed.

Hint Resolve meet1_incl2 : cset.

Lemma meet1_Subset1 s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset1 (mapAnn2 meet1 alv ang) ang.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl2.
  - econstructor; eauto with cset len.
    + intros; inv_get.
      symmetry in H. edestruct get_length_eq; try eapply H; eauto.
Qed.

Lemma live_sound_renamedApart_minus s ang ZL Lv alv i
: renamedApart s ang
  -> live_sound i ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> live_sound i ZL Lv s (mapAnn2 meet1 alv ang).
Proof.
  intros RA LS.
  general induction RA; invt live_sound; simpl in * |- *; pe_rewrite.

  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let, bounded_incl with cset ann.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite.
      rewrite minus_dist_intersection. rewrite H12.
      eauto with cset.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation.
      pe_rewrite. simpl; cset_tac; eauto.
  - econstructor; eauto using live_op_sound_meet.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation with cset.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                               renamedApart_annotation with cset.
  - eauto using live_sound, live_op_sound_meet.
  - econstructor; eauto.
    + cases; simpl in *; eauto.
      exploit bounded_get; eauto.
      eauto with cset.
    + intros. eapply live_op_sound_meet; eauto.
      rewrite incl_list_union; eauto.

  - constructor; eauto with len.
    + eapply IHRA; eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; eauto 20 with len.
        inv_get.
        simpl.
        erewrite getAnn_mapAnn2; eauto using live_sound_annotation,
                                 renamedApart_annotation.
        edestruct H2; eauto; dcr.
        eauto with cset.
      * rewrite zip_app; eauto with len.
        rewrite List.map_app.
        eapply bounded_app; split; eauto.
        eapply get_bounded; intros; inv_get.
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x3); simpl in *.
        unfold lminus.
        rewrite H8.
        clear_all; cset_tac; intuition.
    + intros. inv_get.
      eapply H1; eauto.
      * eapply live_sound_monotone; eauto.
        eapply PIR2_app; eauto.
        eapply PIR2_get; [intros; inv_get; simpl | eauto 20 with len].
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        eauto with cset.
      * rewrite zip_app; eauto with len.
        rewrite List.map_app.
        eapply bounded_app; split; eauto.
        eapply get_bounded.
        intros; inv_get; simpl.
        erewrite getAnn_mapAnn2;
          eauto using live_sound_annotation, renamedApart_annotation.
        edestruct H2; eauto; dcr.
        destruct (getAnn x5); unfold lminus; simpl in *.
        rewrite H15.
        edestruct (H2 _ _ _ H7 H8); eauto; dcr. rewrite H19.
        clear_all; cset_tac; intuition.
        edestruct H2; eauto; dcr. rewrite H13.
        rewrite <- incl_right; eauto.
    + intros. inv_get.
      erewrite getAnn_mapAnn2;
        eauto using live_sound_annotation, renamedApart_annotation.
      edestruct H2; eauto; dcr. destruct (getAnn x0); simpl in *.
      exploit H14; eauto; dcr.
      split. eauto with cset.
      cases; eauto. rewrite H13. rewrite <- H21.
      clear_all; cset_tac; intuition.
    + erewrite getAnn_mapAnn2;
        eauto using live_sound_annotation, renamedApart_annotation with cset.
Qed.
