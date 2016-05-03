Require Import CSet Le.

Require Import Plus Util AllInRel Map Take MoreList.
Require Import Val Var Env EnvTy IL Annotation Liveness Coherence Restrict Delocation LabelsDefined.
Require Import Keep OUnion.

Set Implicit Arguments.
Unset Printing Abstraction Types.
Local Arguments lminus {X} {H} s L.

Definition addParam x (DL:list (set var)) (AP:list (set var)) :=
  zip (fun (DL:set var) AP => if [x ∈ DL]
                   then {x; AP} else AP) DL AP.

Definition addAdd s := (fun (DL:set var) AP => mdo t <- AP; Some ((s ∩ DL) ∪ t)).

Lemma addParam_length x DL AP
 : length DL = length AP
   -> length (addParam x DL AP) = length DL.
Proof.
  intros. unfold addParam. eauto with len.
Qed.

Lemma addParam_zip_lminus_length DL ZL AP x
: length AP = length DL
  -> length DL = length ZL
  -> length (addParam x (zip lminus DL ZL) AP) = length DL.
Proof.
  eauto with len.
Qed.

Notation "'olist_union' A B" := (fold_left (zip ounion) A B) (at level 50, A at level 0, B at level 0).

(*Notation "［ A | x , y 'in' X , Y ］" := (zip (fun x y => A) X Y).*)

Fixpoint computeParameters (DL: list (set var)) (ZL:list (list var)) (AP:list (set var))
         (s:stmt) (an:ann (set var)) {struct s}
: ann (list params) * list (option (set var)) :=
  match s, an with
    | stmtLet x e s, ann1 _ an =>
      let (ar, r) := computeParameters DL ZL (addParam x DL AP) s an in
      (ann1 nil ar, r)
    | stmtIf x s t, ann2 _ ans ant =>
      let (ars, rs) := computeParameters DL ZL AP s ans in
      let (art, rt) := computeParameters DL ZL AP t ant in
      (ann2 nil ars art, zip ounion rs rt)
    | stmtApp f Y, ann0 lv => (ann0 nil, keep (counted f) AP)
    | stmtReturn x, ann0 _ => (ann0 nil, (List.map (fun _ => None) AP))
    | stmtExtern x f e s, ann1 _ an =>
      let (ar, r) := computeParameters DL ZL (addParam x DL AP) s an in
      (ann1 nil ar, r)
    | stmtFun F t, annF lv ans ant =>
      let DL' := zip lminus (getAnn ⊝ ans) (fst ⊝ F) in
      let Z : list params := List.map fst F in
      let Zset := list_union (fst ∘ of_list ⊝ F) in
      let AP' := ((fun _ => ∅) ⊝ F ++ AP) in
      let ars_rF :=
          zip (fun Zs a => computeParameters (DL' ++ DL) (Z ++ ZL) AP' (snd Zs) a)
              F ans in
      let (art, rt) := computeParameters (DL' ++ DL) (Z ++ ZL) AP' t ant in
      let rFt := fold_left (zip ounion) (List.map snd ars_rF) rt in
      let ZaF := list_union (oget ⊝ (take ❬F❭ rFt)) in
      let ur : list (option (set var)) :=
          zip (addAdd (ZaF ∪ Zset)) (DL' ++ DL) rFt in
      (annF (List.map oto_list (take (length F) ur))
            (List.map fst ars_rF) art, drop (length F) ur)
    | s, a => (ann0 nil, nil)
  end.

Notation "'computeParametersF' DL ZL AP F als" :=
  ((fun Zs a0 => computeParameters ((getAnn ⊝ als) \\ (fst ⊝ F) ++ DL \\ ZL)
                                    (fst ⊝ F ++ ZL)
                                    (List.map (fun _ => ∅) F ++ AP)
                                    (snd Zs) a0)
     ⊜ F als)
    (at level 50, DL, ZL, AP, F, als at level 0).

Lemma PIR2_addParam DL AP x
  : length AP = length DL
    -> PIR2 Subset AP (addParam x DL AP).
Proof.
  intros A.
  eapply length_length_eq in A.
  general induction A.
  - constructor.
  - econstructor.
    + cases; cset_tac; intuition.
    + exploit (IHA x0); eauto.
Qed.

Lemma live_globals_zip (F:〔params*stmt〕) (als:〔ann ⦃var⦄〕) DL ZL (LEN1:length F = length als)
  : zip pair (getAnn ⊝ als) (fst ⊝ F) ++ zip pair DL ZL =
    zip pair (List.map getAnn als ++ DL) (List.map fst F ++ ZL).
Proof with eauto with len.
  rewrite zip_app...
Qed.

Local Ltac lnorm :=
  repeat (match goal with
          | [ H : context [ zip _ _ _ ++ zip _ _ _ ] |- _ ] => rewrite <- zip_app in H; [| eauto with len]
          | [ |- context [ zip _ _ _ ++ zip _ _ _ ] ] => rewrite <- zip_app; [| eauto with len]
          end).

Lemma computeParameters_length s lv DL ZL AP an' LV
 : computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
   -> live_sound Imperative (zip pair DL ZL) s lv
   -> length AP = length DL
   -> length DL = length ZL
   -> length LV = length DL.
Proof.
  intros CPEQ LS LEQ LEQ2 .
  general induction LS; simpl in *; repeat let_case_eq; inv CPEQ.
  - rewrite LEQ. eapply IHLS; eauto. rewrite addParam_zip_lminus_length; eauto.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    repeat rewrite zip_length2; eauto with len.
  - eauto with len.
  - eauto with len.
  - rewrite LEQ. eapply IHLS; eauto with len.
  - lnorm.
    exploit IHLS; eauto using live_globals_zip.
    + eauto with len.
    + eauto with len.
    + rewrite length_drop_minus.
      rewrite zip_length2.
      repeat rewrite zip_length2; eauto with len.
      rewrite app_length.
      rewrite map_length. omega.
      rewrite fold_zip_ounion_length.
      * rewrite H4. eauto with len.
      * intros. rewrite H4. rewrite app_length, map_length.
        rewrite <- LEQ, <- H.
        intros. inv_map H5.
        destruct x as [an LV]. inv_zip H6. simpl.
        eapply H1 in H9; eauto 20 using pair_eta, live_globals_zip with len.
        rewrite H9. eauto with len.
Qed.

Local Create HintDb rew.
Local Hint Extern 20 => rewrite <- zip_app : rew.
Local Hint Extern 20 => rewrite <- live_globals_zip; eauto with len : rew.

Lemma computeParametersF_length DL ZL AP F als k
  : (forall n Zs a, get F n Zs -> get als n a ->
               live_sound Imperative (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ pair ⊜ DL ZL) (snd Zs) a)
    -> k = ❬getAnn ⊝ als ++ DL❭
    -> length F = length als
    -> length AP = length DL
    -> length DL = length ZL
    -> forall n a, get (snd ⊝ computeParametersF DL ZL AP F als) n a -> k = ❬a❭.
Proof.
  intros LIVE LEN1 LEN2 LEN3 n a GET. subst.
  rewrite live_globals_zip in LIVE; eauto.
  intros. inv_get.
  symmetry. rewrite <- zip_app; eauto with len.
  eapply computeParameters_length; eauto using pair_eta with len.
Qed.

Lemma ifSndR_zip_addAdd s DL A B
 : length DL = length A
   -> PIR2 (ifSndR Subset) A B
   -> PIR2 (ifSndR Subset) A (zip (addAdd s) DL B).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; inv H0; simpl.
  - constructor.
  - econstructor; eauto.
    + inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma drop_fold_zip_ounion X `{OrderedType X} A B k
  : (forall n a, get A n a -> length a = length B)
    -> (drop k (fold_left (zip ounion) A B)) =
      fold_left (zip ounion) (List.map (drop k) A) (drop k B).
Proof with eauto 20 using get with len.
  general induction A; simpl; eauto.
  - rewrite IHA...
    + rewrite drop_zip...
Qed.

Lemma zip_AP_mon X Y `{OrderedType Y}
      (AP:list (set Y)) (DL:list X) (f:X -> set Y  -> set Y)
      (LEN:length DL = length AP)
  : (forall x y, y ⊆ f x y)
    -> PIR2 Subset AP (zip f DL AP).
Proof.
  length_equify.
  general induction LEN; simpl; eauto using PIR2.
Qed.

Lemma PIR2_ifSndR_keep n (AP:〔⦃var⦄〕)
  :  PIR2 (ifSndR Subset) AP (keep n AP).
Proof.
  unfold keep, mapi. generalize 0.
  general induction AP; simpl.
  - econstructor.
  - cases; eauto using PIR2, @ifSndR.
Qed.

Lemma computeParameters_AP_LV DL ZL AP s lv an' LV
:live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> PIR2 (ifSndR Subset) AP LV.
Proof.
  intros LS CPEQ LEQ.
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eauto using PIR2_ifSndR_Subset_left, PIR2_addParam with len.
  - eauto using ifSndR_zip_ounion.
  - eauto using PIR2_ifSndR_keep.
  - clear_all. unfold mapi. generalize 0.
    general induction AP; simpl; eauto using PIR2, @ifSndR.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eauto using PIR2_ifSndR_Subset_left, PIR2_addParam with len.
  - lnorm.
    assert (APEQ: AP = drop ❬F❭ (tab {} ‖F‖ ++ AP))
      by (rewrite drop_length_ass; eauto with len).
    rewrite APEQ at 1. eapply PIR2_drop.
    exploit computeParameters_length as B0LEN; eauto.
    eauto with len. eauto with len.
    eapply ifSndR_zip_addAdd. eauto 20 with len.
    eapply ifSndR_fold_zip_ounion; eauto.
    + clear IHLS. intros.
      inv_get.
      eapply H1;
      eauto using PIR2_drop, live_globals_zip, pair_eta with len rew.
    + exploit IHLS; [ eauto
                    | eauto with len
                    | eapply eq
                    | | | ]; eauto 20 with len.
Qed.

Lemma ifFstR_addAdds s A B
: PIR2 (ifFstR Subset) B  A
  -> PIR2 (ifFstR Subset) (zip (addAdd s) A B) A.
Proof.
  intros.
  general induction H; simpl.
  + constructor.
  + econstructor; eauto.
    - inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma addParam_Subset x DL AP
: PIR2 Subset AP DL
  -> PIR2 Subset (addParam x DL AP) DL.
Proof.
  intros. general induction H; simpl.
  - constructor.
  - econstructor. cases; eauto.
    + cset_tac.
    + eauto.
Qed.

Lemma PIR2_Subset_tab_extend AP DL ZL (F:list (params*stmt)) als
  : PIR2 Subset AP (DL \\ ZL)
    -> ❬F❭ = ❬als❭
    -> PIR2 Subset (tab {} ‖F‖ ++ AP) ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL)).
Proof.
  intros P LEN.
  rewrite zip_app; eauto using PIR2_length with len.
  eapply PIR2_app; eauto.
  eapply PIR2_get; try (intros ? ? ? GET; inv_map GET); eauto with cset len.
Qed.

Lemma computeParameters_LV_DL DL ZL AP s lv an' LV
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> PIR2 (ifFstR Subset) LV (zip lminus DL ZL).
Proof.
  intros LS CPEQ LEQ.
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eapply addParam_Subset; eauto.
  - eauto using ifFstR_zip_ounion.
  - eauto using PIR2_ifFstR_Subset_right, PIR2_ifFstR_keep.
  - eapply PIR2_get; eauto with len.
    intros. inv_get; econstructor.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eapply addParam_Subset; eauto.
  - assert (EQ: DL \\ ZL = drop ❬F❭ ((getAnn ⊝ als) \\ (fst ⊝ F) ++ DL \\ ZL))
      by (rewrite drop_length_ass; eauto with len).
    rewrite EQ at 2.
    lnorm.
    eapply PIR2_drop.
    eapply ifFstR_addAdds; eauto.
    eapply ifFstR_fold_zip_ounion; eauto.
    + intros ? ? GET. inv_get.
      eapply H1; eauto using pair_eta, live_globals_zip, PIR2_Subset_tab_extend with len.
    + eapply IHLS; eauto 20 using pair_eta, live_globals_zip, PIR2_Subset_tab_extend with len.
Qed.

Lemma PIR2_olist_union_bound X `{OrderedType X} A b c
  : ( forall n a, get A n a -> PIR2 (ifFstR Subset) a c)
    -> PIR2 (ifFstR Subset) b c
    -> PIR2 (ifFstR Subset) (olist_union A b) c.
Proof.
  intros. general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifFstR_zip_ounion.
Qed.

Lemma computeParametersF_LV_DL DL ZL AP F als A
: (forall n Zs a, get F n Zs -> get als n a ->
            live_sound Imperative (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ pair ⊜ DL ZL) (snd Zs) a)
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> PIR2 (ifFstR Subset) A ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL))
  -> length AP = length DL
  -> length DL = length ZL
  -> length F = length als
  -> PIR2 (ifFstR Subset) (olist_union (snd ⊝ computeParametersF DL ZL AP F als) A)
         ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL)).
Proof.
  intros. eapply PIR2_olist_union_bound; eauto.
  intros. inv_get. rewrite <- zip_app in H; eauto with len.
  rewrite <- zip_app; eauto with len.
  eapply computeParameters_LV_DL; eauto using pair_eta, PIR2_Subset_tab_extend with len.
Qed.

Lemma get_olist_union_b X `{OrderedType X} A b n x
  : get b n (Some x)
    -> (forall n a, get A n a -> ❬b❭ = ❬a❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETb LEN. general induction A; simpl in *.
  - eexists x. eauto with cset.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb H0) as [y GETa]; eauto.
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *.
    exploit IHA; try eapply GET; eauto.
    rewrite zip_length2; eauto using get with len.
    edestruct H2; dcr; subst. eexists; split; eauto.
    rewrite <- H7; eauto.
    exploit IHA; try eapply GET; eauto.
    rewrite zip_length2; eauto using get with len.
Qed.

Lemma get_olist_union_A X `{OrderedType X} A a b n k x
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬b❭ = ❬a❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETA GETa LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa (eq_sym H0)) as [y GETb].
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *.
    exploit (@get_olist_union_b _ _ A); eauto.
    rewrite zip_length2; eauto using get with len.
    destruct H2; dcr; subst. eexists; split; eauto.
    rewrite <- H4; eauto.
    eapply get_olist_union_b; try eapply GETunion; eauto.
    rewrite zip_length2; eauto using get with len.
  - eapply IHA; eauto.
    rewrite zip_length2; eauto using get with len.
Qed.

Tactic Notation "Rexploit" uconstr(H) :=
  eapply modus_ponens; [refine H | intros].

Tactic Notation "Rexploit" uconstr(X) "as" ident(H)  :=
  eapply modus_ponens; [refine X | intros H].

Lemma computeParameters_isCalled_Some DL ZL AP s lv an' LV n D Z p
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> isCalled s (LabI n)
  -> get DL n D
  -> get ZL n Z
  -> get LV n p
  -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  intros LS CPEQ LEN1 LEN2 IC GetDL GetZL GetLV.
  general induction IC; simpl in * |- *; inv LS; repeat let_case_eq; invc CPEQ.
  - edestruct IHIC as [Za [A B]]; eauto with len. subst; simpl.
    eexists; split; eauto.
    exploit computeParameters_AP_LV; try eapply eq; eauto with len.
    edestruct (get_length_eq _ GetDL (eq_sym LEN1)).
    edestruct PIR2_nth as [? [? SUB]]; try eapply H; eauto using zip_get.
    get_functional. rewrite <- H6, <- B. cases in SUB.
    + inv SUB.
      (* TODO improve cset_tac *)
      revert H5. clear_all; hnf; intros; cset_tac. eapply H1, H5. cset_tac.
    + unfold lminus in NOTCOND.
      revert NOTCOND; clear_all; cset_tac.
  - edestruct get_zip as [bv [bv' [GET1 [GET2 ?]]]]; eauto; subst.
    edestruct IHIC as [? [? SUB]]; eauto; subst.
    destruct bv'; eexists; split; simpl; eauto.
    + rewrite <- H7, <- SUB. clear_all; cset_tac.
    + rewrite <- H7, <- SUB. reflexivity.
  - edestruct get_zip as [bv [bv' [GET1 [GET2 ?]]]]; eauto; subst.
    edestruct IHIC as [? [? SUB]]; eauto; subst.
    destruct bv; eexists; split; simpl; eauto.
    + rewrite <- H8, <- SUB. clear_all; cset_tac.
    + rewrite <- H8, <- SUB. reflexivity.
  - simpl in *.
    intros.
    edestruct (mapi_get _ _ GetLV) as [x [ H]]; eauto; subst.
    cases; eauto. inv_get. (*TODO this repeat should not be necc *)
    eexists; split; eauto.
    rewrite <- H2. eauto with cset.
  - edestruct IHIC as [? [A B]]; eauto with len.
    subst; simpl. eexists; split; eauto.
    exploit computeParameters_AP_LV; try eapply eq; eauto with len.
    edestruct (get_length_eq _ GetDL (eq_sym LEN1)).
    edestruct PIR2_nth as [? [? SUB]]; try eapply H; eauto using zip_get.
    get_functional. rewrite <- H7, <- B. cases in SUB.
    + inv SUB.
      (* TODO improve cset_tac *)
      revert H3. clear_all; hnf; intros; cset_tac. eapply H1, H3. cset_tac.
    + unfold lminus in NOTCOND.
      revert NOTCOND; clear_all; cset_tac.
  - lnorm.
    simpl in *. inv_get.
    edestruct (get_length_eq _ H0 H4) as [alv GETalv].
    exploit (@computeParameters_length (snd Zs) alv); try eapply pair_eta.
    eapply H5; eauto. instantiate (1:=tab {} ‖F‖ ++ AP); eauto with len.
    eauto with len.
    destruct (@get_in_range _ (snd
          (computeParameters ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL))
                             (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) (snd Zs) alv)) (❬F❭ + n))
      as [pF GETpF].
    rewrite H1. eapply get_range in GetDL. rewrite app_length, map_length. omega.
    edestruct IHIC1; try eapply GETpF; eauto using pair_eta.
    eauto with len. eauto with len. eapply get_app_right; eauto.
    orewrite (n + 0 = n). eauto. eapply get_app_right; eauto.
    rewrite map_length; eauto with len. destruct H2. subst.
    rewrite zip_app; eauto with len.
    rewrite zip_app in GetLV; eauto with len.
    exploit computeParameters_length as LENb; try eapply eq; eauto with len.
    exploit (get_olist_union_A (A:=snd ⊝ computeParametersF DL ZL AP F als));
      try eapply GETpF.
    eapply map_get_1. eapply zip_get_eq; eauto.
    rewrite zip_app; eauto with len.
    eapply computeParametersF_length; eauto. rewrite live_globals_zip; eauto.
    destruct H2 as [? [? ?]]; subst. get_functional. simpl. eexists; split; eauto.
    edestruct (@get_in_range _ b k); try eapply GETalv.
    rewrite LENb. rewrite app_length, map_length. omega.
    edestruct IHIC2 as [? [ ? ?]];
      try eapply eq; eauto using map_get_1, get_app with len.
    dcr; subst. rewrite <- H9. rewrite <- H10. rewrite <- H6, <- H8.
    repeat rewrite minus_union.
    unfold lminus at 3.
    assert (of_list (fst Zs) ⊆ list_union (fst ∘ of_list ⊝ F)). {
      eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    }
    rewrite <- H2.
    assert (x2 ⊆ list_union (oget ⊝ take ❬F❭
           (olist_union (snd ⊝ computeParametersF DL ZL AP F als) b))). {
      exploit (get_olist_union_b (A:=snd ⊝ computeParametersF DL ZL AP F als));
      try eapply g.
      eapply computeParametersF_length; eauto. rewrite live_globals_zip; eauto.
      destruct H11; dcr.
      eapply incl_list_union. eapply map_get_1.
      eapply get_take; eauto.
      eassumption.
    }
    rewrite <- H11.
    clear_all; cset_tac.
  - lnorm. simpl in *. inv_get.
    rewrite zip_app in GetLV; eauto with len.
    rewrite zip_app; eauto with len.
    exploit computeParameters_length; eauto. eauto with len. eauto with len.
    destruct (@get_in_range _ b (❬F❭ + n)) as [pF GETpF].
    rewrite H, app_length, map_length. exploit (get_range GetDL). omega.
    edestruct IHIC; eauto. eauto with len. eauto with len.
    eapply get_app_right; eauto using map_get_1.
    orewrite (n+0 = n); eauto.
    eapply get_app_right; eauto using map_get_1.
    rewrite map_length; eauto. dcr; subst.
    exploit (get_olist_union_b (A:=snd ⊝ computeParametersF DL ZL AP F als));
      try eapply GETpF.
    eapply computeParametersF_length; eauto.
    rewrite live_globals_zip; eauto.
    destruct H0; dcr; subst; simpl. get_functional.
    eexists; split; try reflexivity. rewrite <- H7, <- H8, <- H6.
    repeat rewrite minus_union.
    unfold lminus at 3. clear_all; cset_tac.
Qed.

Lemma computeParameters_isCalled_get_Some DL ZL AP s lv an' LV n p A D Z
  : computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
    -> live_sound Imperative (zip pair DL ZL) s lv
    -> length AP = length DL
    -> length DL = length ZL
    -> isCalled s (LabI n)
    -> n < ❬LV❭
    -> get DL n D
    -> get ZL n Z
    -> get (olist_union A LV) n p
    -> (forall (n0 : nat) (a : 〔؟⦃var⦄〕), get A n0 a -> ❬LV❭ = ❬a❭)
    -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  intros CPEQ LS LEN1 LEN2 IC LE GETDL GETZL GET LEN3.
  destruct (@get_in_range _ LV n); eauto.
  edestruct computeParameters_isCalled_Some; eauto; dcr; subst.
  edestruct get_olist_union_b; eauto; dcr.
  get_functional.
  eexists; split; try reflexivity. rewrite <- H1, <- H2; eauto.
Qed.

Definition ominus' (s : set var) (t : option (set var)) := mdo t' <- t; ⎣s \ t' ⎦.
Definition minuso (s : set var) (t : option (set var)) := ⎣s \ oget t ⎦.

Lemma zip_ominus_contra DL b b'
  : length DL = length b
    -> length b = length b'
    -> PIR2 (fstNoneOrR Subset) b b'
    -> zip ominus' DL b ≿ zip ominus' DL b'.
Proof.
  intros. eapply length_length_eq in H. eapply length_length_eq in H0.
  general induction H; inv H0; simpl.
  - reflexivity.
  - econstructor; eauto.
    + destruct y, y0; simpl; try now econstructor.
      * inv H1. inv pf. econstructor. unfold flip; cset_tac; intuition.
      * inv H1. inv pf.
    + inv H1. eauto.
Qed.

Lemma restrict_zip_ominus' DL LV lv x al
:  length DL = length LV
-> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
-> al \ singleton x ⊆ lv
->  restrict (zip ominus' DL LV) al
 ≿ restrict (zip ominus' DL LV) (lv \ singleton x).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in *.
  - econstructor.
  - econstructor; eauto using get.
    destruct y; intros; simpl; try now econstructor.
    repeat cases; try now econstructor.
    exfalso. eapply NOTCOND. rewrite <- H1, <- COND.
    decide (x0 ∈ s).
    + cset_tac.
    + exploit H0; eauto using get.
      cset_tac.
Qed.

Lemma addParam_x DL AP x n ap' dl
  : get (addParam x DL AP) n ap'
    -> get DL n dl
    -> x ∉ ap' -> x ∉ dl.
Proof.
  unfold addParam; intros.
  edestruct get_zip as [? []]; eauto; dcr. clear H.
  repeat get_functional; subst.
  cases in H1; simpl in *.
  + cset_tac; intuition.
  + cset_tac; intuition.
Qed.

Lemma PIR2_not_in LV x DL AP
  : PIR2 (ifSndR Subset) (addParam x DL AP) LV
    -> length DL = length AP
    ->  forall (n : nat) (lv0 dl : set var),
        get LV n ⎣lv0 ⎦ -> get DL n dl -> x ∉ lv0 -> x ∉ dl.
Proof.
  intros LEQ LEN. intros. eapply length_length_eq in LEN.
  general induction n; simpl in *.
  - inv H; inv H0. invc LEN. simpl in LEQ. invc LEQ.
    cases in pf; inv pf.
    + exfalso; cset_tac; intuition.
    + eauto.
  - invc H; invc H0. invc LEN. simpl in LEQ. invc LEQ.
    eauto.
Qed.

Lemma zip_bounded DL LV lv x
: length DL = length LV
  -> bounded (List.map Some DL) lv
  -> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
  -> bounded (zip (fun (s : set var) (t : option (set var)) => mdo t' <- t; ⎣s \ t' ⎦) DL LV) (lv \ {{ x }} ).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  destruct y; simpl in * |- *.
  + split.
    - decide (x0 ∈ s).
      * cset_tac; intuition.
      * exploit H1; eauto using get. cset_tac; intuition.
    - destruct H0; eapply IHlength_eq; eauto.
      intros. eauto using get.
  + eapply IHlength_eq; eauto using get.
Qed.

Lemma PIR2_addAdds s DL b
: length DL = length b
  -> PIR2 ≼ b (zip (addAdd s) DL b).
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - econstructor.
  - simpl. econstructor.
    + destruct y.
      * econstructor. cset_tac; intuition.
      * constructor.
    + eauto.
Qed.

Lemma PIR2_addAdds' s DL b c
  : length DL = length b
    -> PIR2 ≼ b c
    -> PIR2 ≼ b (zip (addAdd s) DL c).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; invt PIR2.
  - econstructor.
  - simpl. econstructor.
    + destruct y,y0; simpl; try now econstructor.
      * econstructor. inv pf. cset_tac; intuition.
      * inv pf.
    + eauto.
Qed.

Lemma PIR2_combineParams (A:list (ann (list params) * list (option (set var))))
      (B C:list (option (set var)))
  : (forall n a, get A n a -> length (snd a) = length B)
    -> PIR2 ≼ B C
    -> PIR2 ≼ B (olist_union (List.map snd A) C).
Proof.
  general induction B; invt PIR2.
  - clear H. general induction A; eauto.
  - general induction A.
    + econstructor; eauto.
    + exploit H; eauto using get.
      destruct a. destruct l; isabsurd. simpl in *.
      assert (length YL = length l). {
        eapply PIR2_length in H0. simpl in *. omega.
      }
      eapply IHA; eauto 10 using fstNoneOrR_ounion_left, PIR2_ounion_left, get, @PIR2 with len.
Qed.

Lemma PIR2_combineParams_get (A:list (ann (list params) * list (option (set var))))
      (B C:list (option (set var))) n a
  : (forall n a, get A n a -> length (snd a) = length B)
    -> length B = length C
    -> get A n a
    -> PIR2 ≼ B (snd a)
    -> PIR2 ≼ B (olist_union (List.map snd A) C).
Proof.
  intros LEN1 LEN2 GET P. length_equify.
  general induction LEN2; simpl.
  - clear LEN1 GET P. general induction A; eauto.
  - clear IHLEN2.
    general induction GET; simpl.
    + exploit (LEN1); eauto using get.
      destruct x. destruct l; isabsurd. simpl in *.
      eapply PIR2_combineParams; eauto using get.
      inv P.
      econstructor; eauto using fstNoneOrR_ounion_right, PIR2_ounion_right with len.
    + exploit (LEN1); eauto using get.
      destruct x'. destruct l; isabsurd. simpl in *.
      eapply IHGET; eauto using get with len.
      eapply length_length_eq. rewrite zip_length2; try omega. eauto with len.
      eapply length_eq_length in LEN2. omega.
Qed.

Lemma mkGlobals_zip_ominus' (F:list (params*stmt)) als LV
  : ❬F❭ = ❬als❭ -> ❬F❭ = ❬LV❭
    -> PIR2 (option_eq Equal)
           (mkGlobals F (oto_list ⊝ LV) als)
           (minuso ⊜ ((getAnn ⊝ als) \\ (fst ⊝ F)) LV).
Proof.
  intros. rewrite map_zip.
  eapply zip_ext_PIR2; eauto with len.
  intros. inv_get.
  unfold minuso, lminus, oto_list.
  destruct y'.
  - econstructor. rewrite of_list_3; eauto.
  - econstructor; eauto.
Qed.

Lemma PIR2_ominus_minuso A B B'
  : length A = length B
    -> PIR2 (fstNoneOrR Subset) B B'
    -> ominus' ⊜ A B ≿ minuso ⊜ A B'.
Proof.
  intros LEN EQ. length_equify.
  general induction LEN; inv EQ; simpl; eauto.
  econstructor; eauto.
  inv pf; simpl; econstructor.
  simpl. unfold flip. rewrite H. reflexivity.
Qed.

Hint Extern 10 (forall _ _, get (snd ⊝ computeParametersF ?DL ?ZL ?AP ?F ?als) _ _ -> ❬?LVb❭ = ❬_❭)
=> eapply computeParametersF_length : len.

Lemma computeParameters_trs DL ZL AP s an' LV lv
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> noUnreachableCode s
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> length DL = length ZL
  -> length ZL = length AP
  -> trs (restrict (zip ominus' (zip lminus DL ZL) LV) (getAnn lv))
        (List.map oto_list LV)  s lv an'.
Proof.
  intros LIVE CPEQ NOUR P LEN1 LEN2.
  remember (zip pair DL ZL) as DLZL. revert_except LIVE.
  induction LIVE; simpl in *; intros; (repeat let_case_eq); inv NOUR.
  - invc CPEQ. eapply trsExp, trs_monotone_DL.
    + eapply IHLIVE; try eapply eq; eauto 10 using addParam_Subset with len.
    + exploit computeParameters_AP_LV; eauto with len.
      exploit computeParameters_length; eauto with len.
      rewrite restrict_comp_meet.
      assert (SEQ:lv ∩ (lv \ singleton x) [=] lv \ singleton x) by cset_tac.
      rewrite SEQ. eapply restrict_zip_ominus'; eauto with len.
      eapply PIR2_not_in; eauto with len.
  - invc CPEQ. exploit (computeParameters_length _ _ _ eq); eauto with len.
    exploit (computeParameters_length _ _ _ eq0); eauto with len.
    econstructor.
    + exploit (PIR2_zip_ounion b b0); eauto with len.
      eapply trs_monotone_DL_AP; eauto.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra; eauto with len.
    + exploit (PIR2_zip_ounion' b0 b); eauto with len.
      eapply trs_monotone_DL_AP; eauto.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra; eauto with len.
  - invc CPEQ. edestruct get_zip as [D [L [GETZL [GETDL EQ]]]]; dcr; eauto. invc EQ.
    edestruct (get_length_eq _ GETDL LEN2) as [ap GETAP].
    exploit (@keep_Some _ AP (labN l)) as GETKEEP; eauto.
    exploit (zip_get lminus GETZL GETDL) as GETLMINUS.
    exploit (zip_get ominus' GETLMINUS GETKEEP) as GETOMINUS.
    econstructor.
    eapply restrict_get_Some. eapply GETOMINUS. unfold lminus.
    rewrite <- H0. clear_all; cset_tac.
    eapply map_get_1; eauto.
  - invc CPEQ. econstructor.

  - invc CPEQ. eapply trsExtern, trs_monotone_DL.
    eapply IHLIVE; try eapply eq; eauto 10 using addParam_Subset with len.
    exploit computeParameters_AP_LV; eauto with len.
    exploit computeParameters_length; eauto with len.
    rewrite restrict_comp_meet.
    assert (SEQ:lv ∩ (lv \ singleton x) [=] lv \ singleton x) by cset_tac.
    rewrite SEQ. eapply restrict_zip_ominus'; eauto with len.
    eapply PIR2_not_in; eauto with len.

  - rewrite <- zip_app in eq; eauto with len.
    rewrite live_globals_zip in LIVE; eauto with len.
    rename b0 into LVb.
    exploit (computeParameters_length _ _ _ eq) as LENLVb; eauto with len.
    exploit (computeParameters_LV_DL _ _ LIVE eq) as PIRLVb;
      eauto using PIR2_Subset_tab_extend with len.
    invc CPEQ.
    set (NP:=list_union (oget
                           ⊝ take ❬F❭
                           (olist_union (snd
                                           ⊝
                                           computeParametersF DL ZL
                                           AP F als) LVb))
                        ∪ list_union (fst ∘ of_list ⊝ F)).
    set (NPL:=(addAdd NP
                      ⊜ ((getAnn ⊝ als) \\ (fst ⊝ F) ++ DL \\ ZL)
                      (olist_union (snd ⊝ computeParametersF DL ZL AP F als) LVb))).
    assert (LENcPF:forall n aa, get (computeParametersF DL ZL AP F als) n aa -> ❬snd aa❭ = ❬LVb❭).
    {
      intros n aa GET. destruct aa as [an LV]. inv_get.
      rewrite <- zip_app in EQ; eauto with len.
      eapply computeParameters_length in EQ; eauto with len.
      rewrite <- live_globals_zip; eauto.
    }
    assert (LENLVbNPL:❬LVb❭ = ❬NPL❭). {
      rewrite LENLVb. subst NPL.
      rewrite zip_length2; eauto 30 with len.
      rewrite fold_zip_ounion_length. rewrite LENLVb.
      eauto with len.
      intros. inv_map H4. eauto.
    }
    assert (LENLEQ1:❬F❭ <= ❬LVb❭). {
      rewrite LENLVb. rewrite app_length.
      rewrite map_length. rewrite <- H. omega.
    }
    assert (LENLEQ2:❬F❭ <= ❬NPL❭). {
      rewrite <- LENLVbNPL. eauto.
    }
    assert (LENFNPL:❬F❭ = ❬take ❬F❭ NPL❭). {
      rewrite take_less_length; eauto.
    }
    assert (LENFLVb:length F = length (take ❬F❭ LVb)). {
      rewrite take_less_length; eauto.
    }
    assert (NPLEQ: oto_list ⊝ take ❬F❭ NPL ++ oto_list ⊝ drop ❬F❭ NPL
                   = oto_list ⊝ NPL). {
      rewrite <- map_app. rewrite <- take_eta. reflexivity.
    }
    assert (LVb_LE:PIR2 ≼ LVb NPL). {
      eapply PIR2_addAdds'; eauto 20 with len.
      rewrite LENLVb. eauto 30 with len.
      eapply PIR2_combineParams; eauto 20 with len.
    }
    econstructor; eauto with len.
    + intros.
      rewrite NPLEQ. inv_map H10; clear H10. destruct x as [an LV].
      inv_get. simpl in *. rename EQ into EQcP.
      exploit computeParameters_length; eauto using live_globals_zip with len.
      assert (LENLV:❬LV❭ = length F + length DL). {
        rewrite <- zip_app in EQcP; eauto with len.
        eapply computeParameters_length in EQcP;
          eauto using live_globals_zip with len rew.
        rewrite EQcP. rewrite app_length, map_length. omega.
      }
      assert (LENLVb0:length LVb = length LV). {
        rewrite LENLVb, LENLV. eauto with len.
      }
      assert (LVNPL:PIR2 ≼ LV NPL). {
        eapply PIR2_addAdds'; eauto with len.
        rewrite LENLV. eauto 20 with len.
        eapply PIR2_combineParams_get;
          eauto using zip_get with len.
        intros.
        rewrite LENLV. destruct a0 as [an' LV'].
        inv_get; simpl in *. rename EQ into EQcP'.
        rewrite <- zip_app in EQcP'; eauto with len.
        eapply computeParameters_length in EQcP';
          eauto using live_globals_zip with len rew.
        rewrite EQcP'. eauto with len.
        simpl_pair_eqs; subst. reflexivity.
      }
      assert (LENFtake:length F = length (take (length F) LV)). {
        rewrite take_less_length; eauto. omega.
      }
      eapply trs_monotone_DL_AP.
      * rewrite <- zip_app in EQcP; eauto with len.
        eapply H1; eauto 20 using pair_eta,live_globals_zip, PIR2_Subset_tab_extend with len rew.
      * rewrite zip_app; eauto with len .
        rewrite (take_eta ❬F❭ LV).
        rewrite zip_app; eauto with len.
        repeat rewrite restrict_app.
        eapply PIR2_app.
        {
        rewrite restrict_disj.
        eapply restrict_subset2; eauto.
        eapply PIR2_flip_Subset_ext_right;
          [ | symmetry; eapply mkGlobals_zip_ominus'; eauto with len].
        eapply PIR2_ominus_minuso; eauto.
        rewrite <- LENFtake. eauto with len.
        eapply PIR2_take; eauto.

        intros. inv_get.
        unfold lminus, oto_list.
        subst NPL. inv_get.
        eapply get_in_range_app in H11; eauto with len.
        eapply get_in_range_app in H13; eauto with len.
        inv_get.


        edestruct computeParameters_isCalled_get_Some; try eapply eq;
        eauto using get_app, map_get_1 with len. dcr; subst.
        edestruct computeParameters_isCalled_get_Some; try eapply H9;
          eauto using get_app, map_get_1 with len. dcr; subst.
        Opaque to_list.
        simpl in *. rewrite of_list_app.
        repeat rewrite of_list_3. unfold lminus.
        rewrite minus_union.
        eapply disj_minus.
        rewrite (meet_comm _ (getAnn lvs)) at 1.
        rewrite union_meet_distr_r. rewrite union_meet_distr_r.
        eapply union_incl_split.

        eapply incl_union_incl_minus. eapply incl_union_left.
        eapply incl_meet_split. eapply incl_union_right.
        eapply incl_list_union; [ eapply map_get_1; try eapply H5 | ].
        clear_all; cset_tac.
        clear_all; cset_tac.
        eapply incl_union_incl_minus. eapply incl_union_left.
        revert H9 H10. clear_all. cset_tac. eapply incl_left.
        eapply incl_list_union.
        eapply map_get_1. eapply get_take; try eapply H9. eauto. reflexivity. eauto.
        }

        rewrite restrict_comp_meet.
        assert (lvsEQ:getAnn lvs \ of_list (fst Zs ++ oto_list x)
                             [=] lv ∩ (getAnn lvs \ of_list (fst Zs ++ oto_list x))).         {
          edestruct (@get_in_range _ LVb n). omega.
          subst NPL. inv_get.
          eapply get_in_range_app in H12; eauto with len.
          inv_get.
          edestruct computeParameters_isCalled_get_Some; try eapply eq;
            eauto using get_app, map_get_1 with len. dcr; subst.
          simpl. unfold lminus. rewrite H3 in H13.
          rewrite of_list_app. repeat rewrite of_list_3.
          revert H13; clear_all; cset_tac.
          eapply H13. cset_tac.
        }
        rewrite <- lvsEQ.
        rewrite restrict_disj.
        eapply restrict_subset2; eauto.
        eapply zip_ominus_contra; eauto with len.
        rewrite length_drop_minus.
        rewrite zip_length2; eauto with len. omega.

        eapply PIR2_drop; eauto.

        intros. inv_get.
        unfold ominus', lminus in EQ. destruct x1; inv EQ. simpl in *.
        clear EQ. subst NPL.
        inv_get.
        rewrite <- zip_app in H11; eauto with len.
        rewrite <- zip_app in H16; eauto with len.
        inv_get. destruct x1; simpl in *. invc EQ.

        repeat get_functional.

        edestruct computeParameters_isCalled_get_Some; try eapply H9;
        eauto using get_app, map_get_1 with len. dcr; subst. simpl.
        rewrite of_list_app.
        repeat rewrite of_list_3. simpl. unfold lminus.
        hnf; intros. cset_tac. eapply H20; eauto.
        eapply incl_right.
        eapply incl_list_union; [ eapply map_get_1 | reflexivity | eapply H18]; eauto.
        eapply H18; eauto. eapply incl_left.
        eapply incl_list_union.
        eapply map_get_1. eapply get_take; try eapply H10. eauto. reflexivity. eauto.
        congruence.
      * eauto.
    + rewrite NPLEQ.
      eapply trs_monotone_DL_AP.
      eapply IHLIVE; eauto using live_globals_zip, PIR2_Subset_tab_extend with len.
      * rewrite (take_eta (length F) LVb) at 1.
        rewrite zip_app; eauto with len.
        rewrite zip_app. rewrite restrict_app.
        eapply PIR2_app.
        eapply PIR2_flip_Subset_ext_right;
          [ | symmetry; eapply mkGlobals_zip_ominus'; eauto with len].
        eapply PIR2_restrict.
        eapply PIR2_ominus_minuso; eauto.
        rewrite <- LENFLVb. eauto with len.
        eapply PIR2_take; eauto.
        eapply restrict_subset2; eauto.
        eapply zip_ominus_contra; eauto with len.
        rewrite length_drop_minus. rewrite LENLVb.
        rewrite zip_length2; eauto with len.
        rewrite app_length; eauto. rewrite map_length. omega.
        eapply PIR2_drop; eauto.
        rewrite <- LENFLVb. eauto with len.
      * pose proof eq as H12.
        eapply computeParameters_length in H12;
          eauto using live_globals_zip with len rew.
Qed.

Print Assumptions computeParameters_trs.


Lemma additionalParameters_live_monotone LV' DL ZL s an' LV lv
: live_sound Imperative (zip pair DL ZL) s lv
  -> additionalParameters_live LV s lv an'
  -> PIR2 Subset LV' (DL \\ ZL)
  -> additionalParameters_live LV' s lv an'.
Proof.
  intros LS APLS LE.
  general induction APLS; invt live_sound;
    eauto using additionalParameters_live.
  - inv_get. simpl in *.
    edestruct PIR2_nth_2 as [? [A B]]; eauto using zip_get.
    econstructor; eauto using map_get_1; simpl; eauto with cset.
  - lnorm.
    econstructor; eauto.
    + intros. exploit H1; eauto.
      rewrite zip_app; eauto with len. eapply PIR2_app; eauto.
      eapply PIR2_get. intros. inv_get.
      exploit H; eauto using @ifFstR.
      eauto 30 with len.
    + exploit IHAPLS; eauto.
      rewrite zip_app; eauto with len. eapply PIR2_app; eauto.
      eapply PIR2_get. intros. inv_get.
      exploit H; eauto using @ifFstR.
      eauto 30 with len.
Qed.

Lemma ifFstR_addAdds2 s A B C
  : PIR2 Subset A C
  -> PIR2 (ifFstR Subset) B C
  -> PIR2 (ifFstR Subset) (zip (addAdd s) A B) C.
Proof.
  intros R1 R2.
  general induction R1; inv R2; simpl; eauto using @PIR2.
  + econstructor; eauto.
    - inv pf0; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma computeParameters_live DL ZL AP s an' LV lv
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> length DL = length ZL
  -> length ZL = length AP
  -> noUnreachableCode s
  -> additionalParameters_live (oget ⊝ LV) s lv an'.
Proof.
  intros LS CPEQ SUB LEN1 LEN2 REACH.
  general induction LS; inv REACH; simpl in *; repeat let_case_eq; invc CPEQ.
  - econstructor; eauto.
    eapply IHLS; try eapply eq; eauto 20 using addParam_Subset with len.
  - lnorm.
    exploit computeParameters_LV_DL; try eapply eq0; eauto with len.
    exploit computeParameters_LV_DL; try eapply eq; eauto with len.
    econstructor; eauto.
    eapply additionalParameters_live_monotone; eauto.
    eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion; eauto.
    eapply additionalParameters_live_monotone; eauto.
    eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion; eauto.
  - inv_get.
    edestruct PIR2_nth_2; eauto using zip_get; dcr.
    econstructor. eapply map_get_1; eauto. eapply keep_Some; eauto.
    simpl. etransitivity; eauto.
  - econstructor.
  - econstructor; eauto.
    eapply IHLS; try eapply eq; eauto 20 using addParam_Subset with len.
  - lnorm.
    rewrite zip_app; eauto with len.
    exploit (computeParameters_LV_DL); try eapply eq; eauto using PIR2_Subset_tab_extend with len.
    exploit PIR2_length as LENb0; eauto.
    econstructor; eauto.
    + intros. inv_get. rewrite zip_length2 in LENb0; eauto with len.
      edestruct computeParameters_isCalled_get_Some; try eapply eq;
        eauto using map_get_1, get_app with len.
      eapply computeParametersF_length; eauto with len. rewrite live_globals_zip; eauto.
      dcr. subst. simpl. rewrite of_list_3. rewrite <- zip_app in H12; eauto with len.
      inv_get.
      exploit computeParametersF_LV_DL; try rewrite <- zip_app; eauto with len.
      eapply PIR2_nth in H12; eauto. dcr; inv_get. inv H16.
      rewrite H13. unfold lminus. clear_all; cset_tac.
    + intros. inv_get. repeat get_functional.
      exploit H1; eauto using pair_eta, PIR2_Subset_tab_extend with len.
      rewrite zip_app in H10; eauto with len.
      eapply additionalParameters_live_monotone; try eapply H10; eauto.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len. rewrite live_globals_zip; eauto.
    + eapply additionalParameters_live_monotone; try eapply IHLS;
        eauto using PIR2_Subset_tab_extend with len.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len. rewrite live_globals_zip; eauto.
    + rewrite map_length. rewrite take_less_length; eauto.
      rewrite zip_length2. rewrite app_length. rewrite zip_length2; eauto with len.
      rewrite fold_zip_ounion_length; eauto. rewrite LENb0.
      rewrite zip_app; eauto with len.
      symmetry.
      eapply computeParametersF_length; try eapply H5; eauto with len.
      rewrite <- zip_app; eauto with len.
      rewrite LENb0; eauto with len.
Qed.
