Require Import Util LengthEq IL InRel RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness Coherence Delocation.
Require Import AddParam AddAdd MoreListSet.

Set Implicit Arguments.
Unset Printing Abstraction Types.

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
    | stmtFun F t, annF lv ans ant =>
      let DL' := (getAnn ⊝ ans) \\ (fst ⊝ F) in
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

Notation "'computeParametersF' F als DL ZL AP" :=
  ((fun Zs a0 => computeParameters
                ((getAnn ⊝ als ++ DL) \\ ((fst ⊝ F) ++ ZL))
                ((fst ⊝ F) ++ ZL)
                (List.map (fun _ => ∅) F ++ AP)
                (snd Zs) a0)
     ⊜ F als)
    (at level 50, DL, ZL, AP, F, als at level 0).

Notation "'olu' F als Lv ZL AP s alb" :=
  (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
               (snd (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                       (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb)))
(at level 50, als, Lv, ZL, AP, F, s, alb at level 0).

Ltac lnorm :=
  repeat (match goal with
          | [ H : context [ zip _ _ _ ++ zip _ _ _ ] |- _ ] => rewrite <- zip_app in H; [| eauto with len]
          | [ |- context [ zip _ _ _ ++ zip _ _ _ ] ] => rewrite <- zip_app; [| eauto with len]
          end).

Create HintDb rew.
Hint Extern 20 => rewrite <- zip_app : rew.
Hint Extern 20 => rewrite <- live_globals_zip; eauto with len : rew.


Lemma computeParameters_AP_LV Lv ZL AP s lv
:live_sound Imperative ZL Lv s lv
  -> length AP = length Lv
  -> length Lv = length ZL
  -> PIR2 (ifSndR Subset) AP (snd (computeParameters (Lv \\ ZL) ZL AP s lv)).
Proof.
  intros LS. revert AP.
  induction LS; simpl in * |- *; intros; repeat let_pair_case_eq; subst; simpl.
  - eapply PIR2_ifSndR_Subset_left; eauto.
    eapply IHLS; eauto with len.
    eapply PIR2_addParam; eauto with len.
  - eauto using ifSndR_zip_ounion.
  - eauto using PIR2_ifSndR_keep.
  - eapply PIR2_get; eauto with len.
    intros; inv_get; eauto using @ifSndR.
  - rewrite <- zip_app; eauto. len_simpl.
    eapply PIR2_ifSndR_Subset_left.
    eapply PIR2_drop.
    eapply ifSndR_zip_addAdd.
    Focus 2.
    eapply ifSndR_fold_zip_ounion; eauto.
    Focus 2.
    eapply IHLS; eauto with len.
    + clear IHLS. intros.
      inv_get.
      eapply H1;
        eauto using PIR2_drop, live_globals_zip, pair_eta with len rew.
    + eauto 20 with len.
    + rewrite drop_length_ass; eauto with len.
    + eauto with len.
Qed.

Corollary computeParameters_length AP s lv DL ZL
  : live_sound Imperative ZL DL s lv
    -> length AP = length DL
    -> length DL = length ZL
    -> length (snd (computeParameters (DL \\ ZL) ZL AP s lv)) = length DL.
Proof.
  intros. exploit computeParameters_AP_LV; eauto.
  eapply PIR2_length in H2. eauto with len.
Qed.

Lemma computeParametersF_length AP (ZL:list params) (Lv: list (set var)) F als k
  : (forall n Zs a, get F n Zs -> get als n a ->
               live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> k = ❬getAnn ⊝ als ++ Lv❭
    -> length F = length als
    -> length AP = length Lv
    -> length Lv = length ZL
    -> forall n a, get (snd ⊝ computeParametersF F als Lv ZL AP) n a -> ❬a❭ = k.
Proof.
  intros LIVE EQ LEN1 LEN2 LEN3 n a GET. subst.
  inv_get. rewrite computeParameters_length; eauto with len.
Qed.

Lemma computeParameters_length' (F:list (params * stmt)) als Lv ZL AP t alb
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t alb)
      (LEN1 : ❬Lv❭ = ❬ZL❭)
      (LEN2 : ❬ZL❭ = ❬AP❭)
      (LEN3 : ❬F❭ = ❬als❭)
  : ❬(getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)❭ =
    ❬snd
       (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)) (fst ⊝ F ++ ZL)
                          (tab {} ‖F‖ ++ AP) t alb)❭.
Proof.
  len_simpl.
  rewrite computeParameters_length; eauto with len.
Qed.

Lemma computeParameters_length_help_1 (F : 〔params * stmt〕)
      (als : 〔ann ⦃nat⦄〕)  (Lv : 〔⦃nat⦄〕) (ZL : 〔params〕)
 (LEN1 : ❬Lv❭ = ❬ZL❭) (LEN2 : ❬F❭ = ❬als❭)
  : ❬getAnn ⊝ als ++ Lv❭ = ❬fst ⊝ F ++ ZL❭.
Proof.
  eauto with len.
Qed.

Lemma computeParameters_length_help_2 (F : 〔params * stmt〕)
      (als : 〔ann ⦃nat⦄〕)  (Lv AP : 〔⦃nat⦄〕) (ZL : 〔params〕)
 (LEN1 : ❬Lv❭ = ❬ZL❭) (LEN2:❬ZL❭ = ❬AP❭) (LEN3 : ❬F❭ = ❬als❭)
  : ❬tab {} ‖F‖ ++ AP❭ = ❬getAnn ⊝ als ++ Lv❭.
Proof.
  eauto with len.
Qed.

Hint Resolve computeParameters_length' | 0 : len.
Hint Resolve computeParameters_length_help_1 computeParameters_length_help_2 | 0 : len.

Lemma computeParametersF_length_pair AP (ZL:list params) (Lv: list (set var)) F als k
  : (forall n Zs a, get F n Zs -> get als n a ->
               live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> k = ❬getAnn ⊝ als ++ Lv❭
    -> length F = length als
    -> length AP = length Lv
    -> length Lv = length ZL
    -> forall n a, get (computeParametersF F als Lv ZL AP) n a -> ❬snd a❭ = k.
Proof.
  intros LIVE EQ LEN1 LEN2 LEN3 n a GET. subst.
  inv_get. rewrite computeParameters_length; eauto with len.
Qed.

Lemma computeParameters_LV_DL ZL Lv AP s lv
: live_sound Imperative ZL Lv s lv
  -> length AP = length Lv
  -> length Lv = length ZL
  -> PIR2 Subset AP (Lv \\ ZL)
  -> PIR2 (ifFstR Subset) (snd (computeParameters (Lv \\ ZL) ZL AP s lv)) (Lv \\ ZL).
Proof.
  intros LS Len1 Len2 LEQ.
  general induction LS; simpl in * |- *; repeat let_pair_case_eq; subst; simpl.
  - eapply IHLS; eauto using addParam_Subset with len.
  - eauto using ifFstR_zip_ounion.
  - eauto using PIR2_ifFstR_Subset_right, PIR2_ifFstR_keep.
  - eapply PIR2_get; eauto with len.
    intros. inv_get; econstructor.
  - assert (EQ: Lv \\ ZL = drop ❬F❭ ((getAnn ⊝ als) \\ (fst ⊝ F) ++ Lv \\ ZL))
      by (rewrite drop_length_ass; eauto with len).
    rewrite EQ at 4.
    lnorm.
    eapply PIR2_drop.
    eapply ifFstR_addAdds; eauto.
    eapply ifFstR_fold_zip_ounion; eauto.
    + intros ? ? GET. inv_get.
      eapply H1; eauto using PIR2_Subset_tab_extend with len.
    + eapply IHLS; eauto 20 using PIR2_Subset_tab_extend with len.
Qed.

Lemma computeParametersF_LV_DL ZL Lv AP F als A
: (forall n Zs a, get F n Zs -> get als n a ->
            live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
  -> PIR2 Subset AP (Lv \\ ZL)
  -> PIR2 (ifFstR Subset) A ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
  -> length AP = length Lv
  -> length Lv = length ZL
  -> length F = length als
  -> PIR2 (ifFstR Subset) (olist_union (snd ⊝ computeParametersF F als Lv ZL AP) A)
         ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)).
Proof.
  intros. eapply PIR2_olist_union_bound; eauto.
  intros; inv_get.
  eapply computeParameters_LV_DL; eauto using PIR2_Subset_tab_extend with len.
Qed.
