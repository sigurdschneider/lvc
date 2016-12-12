Require Import Util LengthEq IL InRel RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness Coherence Delocation.

Set Implicit Arguments.
Unset Printing Abstraction Types.

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
  -> length (addParam x (DL \\ ZL) AP) = length DL.
Proof.
  eauto with len.
Qed.

Notation "'olist_union' A B" := (fold_left (zip ounion) A B) (at level 50, A at level 0, B at level 0).

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

Local Create HintDb rew.
Local Hint Extern 20 => rewrite <- zip_app : rew.
Local Hint Extern 20 => rewrite <- live_globals_zip; eauto with len : rew.

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

Lemma PIR2_olist_union_bound X `{OrderedType X} A b c
  : ( forall n a, get A n a -> PIR2 (ifFstR Subset) a c)
    -> PIR2 (ifFstR Subset) b c
    -> PIR2 (ifFstR Subset) (olist_union A b) c.
Proof.
  intros. general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifFstR_zip_ounion.
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

Lemma get_olist_union_b X `{OrderedType X} A b n x
  : get b n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETb LEN. general induction A; simpl in *.
  - eexists x. eauto with cset.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb (eq_sym H0)) as [y GETa]; eauto.
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *.
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
      edestruct H2; dcr; subst. eexists; split; eauto.
      rewrite <- H7; eauto.
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
Qed.

Lemma get_olist_union_A X `{OrderedType X} A a b n k x
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETA GETa LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa H0) as [y GETb].
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

Lemma get_olist_union_A' X `{OrderedType X} A a b n k x p
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> get (olist_union A b) n p
    -> exists s, p = (Some s) /\ x ⊆ s.
Proof.
  intros. edestruct get_olist_union_A; eauto; dcr.
  get_functional; eauto.
Qed.

Tactic Notation "Rexploit" uconstr(H) :=
  eapply modus_ponens; [refine H | intros].

Tactic Notation "Rexploit" uconstr(X) "as" ident(H)  :=
  eapply modus_ponens; [refine X | intros H].

Lemma get_fold_zip_join X (f: X-> X-> X) (A:list (list X)) (b:list X) n
  : n < ❬b❭
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip f) A b) n y.
Proof.
  intros LE LEN. general induction A; simpl in *.
  - edestruct get_in_range; eauto.
  - exploit LEN; eauto using get.
    eapply IHA; eauto using get with len.
Qed.

Lemma callChain_range F f f'
  : callChain isCalled F f f'
    -> ❬F❭ <= counted f'
    -> counted f <= counted f'.
Proof.
  intros.
  inv H; eauto; simpl in *.
  - rewrite <- H0. eapply get_range in H1. omega.
Qed.

Lemma callChain_range' F f f'
  : callChain isCalled F f f'
    -> counted f' < ❬F❭
    -> counted f < ❬F❭.
Proof.
  intros.
  inv H; eauto.
Qed.

Lemma computeParameters_isCalled_Some_F' Lv ZL AP als D Z F s alb l
      k k' x0 x1 Zs
      (IH : forall k Zs,
          get F k Zs ->
          forall (ZL : 〔params〕) (Lv AP : 〔⦃var⦄〕) (lv : ann ⦃var⦄)
            (n : nat) (D : ⦃var⦄) (Z : params) (p : ؟ ⦃var⦄),
            live_sound Imperative ZL Lv (snd Zs) lv ->
            ❬AP❭ = ❬Lv❭ ->
            ❬Lv❭ = ❬ZL❭ ->
            isCalled (snd Zs) (LabI n) ->
            get Lv n D ->
            get ZL n Z ->
            get (snd (computeParameters (Lv \\ ZL) ZL AP (snd Zs) lv)) n p ->
            exists Za : ⦃var⦄, p = ⎣ Za ⎦ /\ D \ of_list Z \ Za ⊆ getAnn lv)
      (LEN1 : ❬AP❭ = ❬Lv❭) (LEN2 : ❬Lv❭ = ❬ZL❭) (LEN3 : ❬F❭ = ❬als❭)
      (GetDL : get (getAnn ⊝ als ++ Lv) l D) (GetZL : get (fst ⊝ F ++ ZL) l Z)
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) s alb)
      (LSF : forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (INCL: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get als n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
      (GetLV : get (olu F als Lv ZL AP s alb) l x0)
      (GetF : get F k Zs) (GetAls : get als k x1)
      (IC : isCalled (snd Zs) (LabI k'))
      (CC: callChain isCalled F (LabI k') (LabI l))
  :  exists Za : ⦃var⦄,
     addAdd
       (list_union (oget ⊝ take ❬F❭ (olu F als Lv ZL AP s alb))
        ∪ list_union (fst ∘ of_list ⊝ F)) (D \ of_list Z) x0 =
     ⎣ Za ⎦ /\
     D \ of_list Z \ Za
     ⊆ getAnn x1 \ of_list (fst Zs) \
       (list_union (oget ⊝ take ❬F❭ (olu F als Lv ZL AP s alb))
                   ∪ list_union (fst ∘ of_list ⊝ F)).
Proof.
  general induction CC.
  - destruct (@get_in_range _ (snd
                                 (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                    (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) (snd Zs) x1)) l0)
      as [pF GETpF].
    rewrite computeParameters_length; [ |eauto | eauto with len | eauto with len].
    eapply get_range in GetDL. eauto.
    edestruct (IH k Zs); try eapply GETpF;
      eauto using get_app_right, map_get_1 with len;
      dcr; subst.
    edestruct get_olist_union_A' as [? [? ?]]; try eapply GetLV;
      eauto using map_get_1, zip_get.
    eapply computeParametersF_length; eauto with len.
    rewrite computeParameters_length; eauto with len.
    subst; simpl. eexists; split; eauto.
    rewrite <- H0, <- H1.
    repeat rewrite minus_union.
    assert (of_list (fst Zs) ⊆ list_union (fst ∘ of_list ⊝ F)). {
      eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    }
    revert H; clear_all; cset_tac.
  - inv_get.
    exploit IHCC; try eapply H0; eauto.
    dcr. eexists; split; eauto.
    rewrite H5.
    destruct (@get_in_range _ (snd
                                 (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                    (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) (snd Zs0) x1)) k'0)
      as [pF' GETpF'].
    rewrite computeParameters_length; [ |eauto | eauto with len | eauto with len].
    rewrite app_length, map_length. eapply get_range in H1. omega.
    exploit (IH k0 Zs0); try eapply GETpF'; eauto using get_app, map_get_1 with len.
    dcr; subst. rewrite <- H7.
    assert (x3 ⊆ list_union (oget ⊝ take ❬F❭
                                  (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                               (snd
                                                  (computeParameters
                                                     ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                     (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb))))).
    {
      exploit (@get_olist_union_A _ _ (snd ⊝ computeParametersF F als Lv ZL AP));
        [| eapply GETpF' | | ]. instantiate (1:=k0).
      eapply map_get_1. eapply zip_get_eq; [| | reflexivity]. eauto. eauto.
      instantiate (1:=(snd
                         (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                            (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb))).
      eapply computeParametersF_length; eauto with len.
      rewrite computeParameters_length; eauto with len.
      dcr.
      eapply incl_list_union. eapply map_get_1.
      eapply get_take; try eapply H6; eauto using get_range. eauto.
    }
    rewrite H2.
    assert (of_list (fst Zs0) ⊆ list_union (fst ∘ of_list ⊝ F)). {
      eapply incl_list_union. eapply map_get_1.
      instantiate (1:=Zs0). eauto. eauto.
    }
    revert H3; clear_all; cset_tac.
Qed.

Lemma computeParameters_isCalled_Some ZL Lv AP s lv n D Z p
  : live_sound Imperative ZL Lv s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> isCalled s (LabI n)
    -> get Lv n D
    -> get ZL n Z
    -> get (snd (computeParameters (Lv \\ ZL) ZL AP s lv)) n p
    -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  revert ZL Lv AP lv n D Z p.
  sind s; destruct s;
    intros ZL Lv AP lv n D Z p LS LEN1 LEN2 IC GetDL GetZL GetLV;
    simpl in * |- *; inv LS; invt isCalled;
      repeat let_case_eq; repeat let_pair_case_eq; subst; simpl in *.
  - edestruct (IH s) as [Za [A B]]; try eapply GetLV; eauto with len;
      subst; simpl.
    eexists; split; eauto.
    inv_get.
    exploit (@computeParameters_AP_LV Lv ZL (addParam x (Lv \\ ZL) AP));
      try eapply H2; eauto with len.
    PIR2_inv. unfold addParam in H3. inv_get.
    rewrite <- H7.
    revert H10 B. clear_all; cases; intros; cset_tac.
  - inv_get.
    edestruct (IH s1) as [? [? SUB]]; eauto; subst.
    setoid_rewrite <- H8. setoid_rewrite <- SUB.
    destruct x0;
      eexists; simpl; split; eauto; clear_all; cset_tac.
  - inv_get.
    edestruct (IH s2) as [? [? SUB]]; eauto; subst.
    setoid_rewrite <- H9. setoid_rewrite <- SUB.
    destruct x;
      eexists; simpl; split; eauto; clear_all; cset_tac.
  - simpl in *. unfold keep in GetLV.
    inv_get.
    cases; eauto.
    eexists; split; eauto.
    rewrite <- H3. eauto with cset.
  - lnorm. inv_get.
    invc H4.
    + exploit (computeParameters_length (tab {} ‖F‖ ++ AP) H1) as Len;
        [ eauto with len | eauto with len | ].
      assert (LE:❬F❭ + n < ❬snd
                           (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                              (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb)❭).
      rewrite Len, app_length, map_length. exploit (get_range GetDL). omega.
      destruct (get_in_range _ LE) as [pF GETpF].
      edestruct (IH s) with (AP:=tab {} ‖F‖ ++ AP); eauto.
      eauto with len. eauto with len.
      eapply get_app_right; eauto using map_get_1.
      orewrite (n+0 = n); eauto.
      eapply get_app_right; eauto using map_get_1.
      rewrite map_length; eauto. dcr; subst.
      edestruct (get_olist_union_b (A:=snd ⊝ computeParametersF F als Lv ZL AP))
        as [? [? ?]]; try eapply GETpF.
      eapply computeParametersF_length; eauto.
      get_functional.
      eexists; split; try reflexivity.
      rewrite <- H0, <- H8, <- H4.
      clear_all; cset_tac.
    + inv_get.
      destruct (@get_in_range _ (snd
                                   (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                      (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb)) k)
        as [ps GETps]; eauto.
      rewrite computeParameters_length; eauto with len.
      exploit (IH s); try eapply GETps; eauto using get_app, map_get_1 with len.
      dcr; subst.
      setoid_rewrite <- H8. setoid_rewrite <- H13.
      assert (x2 ⊆ list_union (oget ⊝ take ❬F❭
                                    (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                                 (snd
                                                    (computeParameters
                                                       ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                                       (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) s alb))))
                 ∪ list_union (fst ∘ of_list ⊝ F)). {
        exploit (get_olist_union_b (A:=snd ⊝ computeParametersF F als Lv ZL AP));
          try eapply GETps.
        eapply computeParametersF_length; eauto with len.
        rewrite computeParameters_length; eauto with len.
        dcr. eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1.
        eapply get_take; eauto using get_range.
        eauto.
      }
      clear H8 H13 LS GETps. setoid_rewrite H10. clear H7 H10.
      eapply computeParameters_isCalled_Some_F'; eauto.
      intros. eapply (IH (snd Zs0)); eauto.
      eapply get_app_right; eauto. orewrite (n + 0 = n); eauto.
      eapply get_app_right; eauto. eauto with len.
      intros; edestruct H6; eauto.
Qed.

Lemma computeParameters_isCalled_get_Some Lv ZL AP s lv n p A D Z
  : live_sound Imperative ZL Lv s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> isCalled s (LabI n)
    -> n < ❬snd (computeParameters (Lv \\ ZL) ZL AP s lv)❭
    -> get Lv n D
    -> get ZL n Z
    -> get (olist_union A (snd (computeParameters (Lv \\ ZL) ZL AP s lv))) n p
    -> (forall (n0 : nat) (a : 〔؟⦃var⦄〕),
          get A n0 a -> ❬a❭ = ❬snd (computeParameters (Lv \\ ZL) ZL AP s lv)❭)
    -> exists Za, p = Some Za /\ D \ of_list Z \ Za ⊆ (getAnn lv).
Proof.
  intros LS LEN1 LEN2 IC LE GETDL GETZL GET LEN3.
  destruct (get_in_range _ LE); eauto.
  edestruct computeParameters_isCalled_Some; eauto; dcr; subst.
  edestruct get_olist_union_b; eauto; dcr.
  get_functional.
  eexists; split; try reflexivity. rewrite <- H1, <- H2; eauto.
Qed.

Lemma computeParameters_isCalledFrom_get_Some Lv ZL AP F alv s lv p Da Zs l
      (LSF : forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get alv n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ alv ++ Lv) (snd Zs) a)
       (INCL: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get alv n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
  : live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ alv ++ Lv) s lv
    -> length AP = length Lv
    -> length Lv = length ZL
    -> length F = length alv
    -> isCalledFrom isCalled F s (LabI l)
    -> get alv l Da
    -> get F l Zs
    -> get (olist_union (snd ⊝ computeParametersF F alv Lv ZL AP)
                       (snd (computeParameters ((getAnn ⊝ alv ++ Lv) \\ (fst ⊝ F ++ ZL))
                                               (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP)
                                               s lv))) l p
    -> exists Za, p = Some Za /\ getAnn Da \ of_list (fst Zs) \ Za \
                                 list_union (oget ⊝ take ❬F❭ (olu F alv Lv ZL AP s lv))
                                 \ list_union (fst ∘ of_list ⊝ F) ⊆ (getAnn lv).
Proof.
  intros LS LEN1 LEN2 LEN3 [[n] [IC CC]] GETDL GETZL GET.
  exploit callChain_range' as LE; eauto using get_range. simpl in *.
  assert (NLE:n < ❬snd (computeParameters ((getAnn ⊝ alv ++ Lv)
                                     \\ (fst ⊝ F ++ ZL))
                                  (fst ⊝ F ++ ZL)
                                  (tab {} ‖F‖ ++ AP) s lv)❭).
  rewrite computeParameters_length; eauto with len.
  destruct (get_in_range _ NLE); eauto.
  assert (LE':n < ❬getAnn ⊝ alv ++ Lv❭).
  rewrite app_length, map_length. omega.
  destruct (get_in_range _ LE'); eauto.
  assert (LE'':n < ❬fst ⊝ F ++ ZL❭).
  rewrite app_length, map_length. omega.
  destruct (get_in_range _ LE''); eauto.
  edestruct computeParameters_isCalled_Some; try eapply g; eauto; dcr; subst.
  eauto with len. eauto with len.
  edestruct get_olist_union_b; eauto; dcr.
  intros.
  eapply computeParametersF_length; eauto.
  eapply computeParameters_length; eauto with len.
  setoid_rewrite <- H1.
  inv CC.
  - inv_get. eexists; split; eauto.
    rewrite H2. clear_all; cset_tac.
  - inv_get.
    exploit computeParameters_isCalled_Some_F'; try eapply H4; try eapply H5;
      eauto using get_app, map_get_1.
    intros. eapply computeParameters_isCalled_Some; eauto.
    dcr. destruct p; simpl in *; invc H8.
    eexists; split; [ reflexivity | ].
    rewrite H2.
    assert (Incl:x ⊆  (list_union (oget ⊝ take ❬F❭ (olu F alv Lv ZL AP s lv))
                             ∪ list_union (fst ∘ of_list ⊝ F))). {
      eapply incl_union_left.
      eapply incl_list_union.
      eapply map_get_1. eapply get_take; eauto using get_range. reflexivity.
    }
    rewrite Incl. rewrite <- H9.
    rewrite union_comm.
    rewrite <- minus_union.
    clear_all; cset_tac.
Qed.

Definition ominus' (s : set var) (t : option (set var)) := mdo t' <- t; ⎣s \ t' ⎦.
Definition minuso (s : set var) (t : option (set var)) := ⎣s \ oget t ⎦.

Lemma zip_ominus_contra DL b b'
  : PIR2 (fstNoneOrR Subset) b b'
    -> zip ominus' DL b ≿ zip ominus' DL b'.
Proof.
  intros.
  general induction H; destruct DL; simpl; eauto using PIR2.
  - econstructor; eauto.
    + inv pf; simpl; econstructor.
      unfold flip. rewrite H0. eauto.
Qed.

Lemma restrict_zip_ominus' DL LV lv x al
:  length DL = length LV
-> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
-> al \ singleton x ⊆ lv
->  restr al ⊝ (zip ominus' DL LV)
 ≿ restr (lv \ singleton x) ⊝ (zip ominus' DL LV).
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

Lemma PIR2_ominus_minuso A B B'
  : PIR2 (fstNoneOrR Subset) B B'
    -> ominus' ⊜ A B ≿ minuso ⊜ A B'.
Proof.
  intros EQ.
  general induction EQ; destruct A; simpl; eauto.
  econstructor; eauto.
  inv pf; simpl; econstructor.
  simpl. unfold flip. rewrite H. reflexivity.
Qed.

Hint Extern 10 (forall _ _, get (snd ⊝ computeParametersF ?DL ?ZL ?AP ?F ?als) _ _ -> ❬?LVb❭ = ❬_❭)
=> eapply computeParametersF_length : len.

Hint Extern 1 =>
match goal with
  [ |- context [ ❬snd (computeParameters _ _ _ _ _)❭ ] ] =>
  rewrite computeParameters_length; eauto with len
end : len.

Lemma ominus'_Some_oto_list A B C1 C2
  : PIR2 ≼ C1 C2
    -> ominus' ⊜ (A \\ B) C1 ≿ Some ⊝ A \\ app (A:=var) ⊜ B (oto_list ⊝ C2).
Proof.
  intros. general induction H; simpl; destruct A, B; try reflexivity.
  - simpl; econstructor; eauto.
    + inv pf; simpl ominus'. econstructor.
      econstructor. unfold flip, oto_list.
      rewrite of_list_app. rewrite of_list_3.
      unfold flip in H0. rewrite <- minus_union.
      rewrite H0. reflexivity.
Qed.

Lemma computeParameters_trs ZL Lv AP s lv
: live_sound Imperative ZL Lv s lv
  -> noUnreachableCode isCalled s
  -> PIR2 Subset AP (Lv \\ ZL)
  -> length Lv = length ZL
  -> length ZL = length AP
  -> trs (restr (getAnn lv) ⊝ (zip ominus' (Lv \\ ZL)
                                  (snd (computeParameters (Lv \\ ZL) ZL AP s lv))))
        (List.map oto_list (snd (computeParameters (Lv \\ ZL) ZL AP s lv)))
        s lv
        (fst (computeParameters (Lv \\ ZL) ZL AP s lv)).
Proof.
  intros LIVE NOUR P LEN1 LEN2.
  revert_except LIVE.
  induction LIVE; simpl in *; intros; repeat let_case_eq;
    repeat let_pair_case_eq; inv NOUR; simpl in *.
  - eapply trsExp, trs_monotone_DL.
    + eapply IHLIVE; eauto 10 using addParam_Subset with len.
    + rewrite restrict_comp_meet.
      assert (SEQ:lv ∩ (lv \ singleton x) [=] lv \ singleton x) by cset_tac.
      rewrite SEQ. eapply restrict_zip_ominus'; eauto with len.

      eapply PIR2_not_in; [ eapply computeParameters_AP_LV; eauto with len
                          | eauto with len].
  - econstructor.
    + eapply trs_monotone_DL_AP; eauto.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra; eauto using PIR2_zip_ounion with len.
      eapply PIR2_zip_ounion; eauto with len.
    + eapply trs_monotone_DL_AP; eauto using PIR2_zip_ounion' with len.
      eapply restrict_subset2; eauto with len.
      eapply zip_ominus_contra; eauto using PIR2_zip_ounion' with len.
  - inv_get.
    econstructor.
    + eapply restrict_get_Some.
      eapply zip_get_eq. eapply zip_get; eauto.
      eapply keep_Some; eauto. simpl. reflexivity.
      rewrite <- H1. eauto with cset.
    + eapply map_get_1. eapply keep_Some; eauto.
  - econstructor.
  - lnorm. econstructor.
    + eauto with len.
    + eauto with len.
    + rewrite map_length. rewrite take_length_le; eauto.
      rewrite zip_length2; [eauto 20 with len|].
      rewrite fold_zip_ounion_length.
      * rewrite computeParameters_length; eauto with len.
      * eapply computeParametersF_length; eauto with len.
    + intros. inv_get. simpl.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply trs_monotone_DL_AP.
      * eapply H1; eauto using PIR2_Subset_tab_extend with len.
      * { rewrite (take_eta (length F) (zip ominus' _ _)).
          do 2 rewrite List.map_app.
          eapply PIR2_app.
          - rewrite restrict_disj.
            + eapply restrict_subset2; eauto.
              do 2 rewrite take_zip.
              rewrite take_app_eq; [|eauto with len].
              rewrite take_app_eq; [|eauto with len].
              eapply ominus'_Some_oto_list.
              eapply PIR2_take. eapply PIR2_addAdds'.
              eauto with len.
              eapply PIR2_combineParams_get;
                [ eapply computeParametersF_length_pair; eauto with len
                | eauto with len
                | eapply zip_get; eauto
                | reflexivity ].
            + intros.
              inv_get.
              Opaque to_list.

              pose proof (H10 _ H12).
              edestruct computeParameters_isCalledFrom_get_Some; try eapply H6;
                eauto with len; dcr; subst.
              intros; edestruct H2; eauto.
              pose proof (H10 _ H15).
              edestruct computeParameters_isCalledFrom_get_Some; try eapply H7;
                eauto with len; dcr; subst.
              intros; edestruct H2; eauto.

              simpl.
              repeat rewrite of_list_app.
              repeat rewrite of_list_3.
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
              revert H12 H6. clear_all. cset_tac'.
              exfalso; eapply n0.
              eapply incl_list_union.
              eapply map_get_1. eapply get_take; eauto.
              reflexivity. eauto.

          - rewrite restrict_comp_meet.
            pose proof (H10 _ H12).
            edestruct computeParameters_isCalledFrom_get_Some; try eapply H6;
              eauto with len; dcr; subst.
            intros; edestruct H2; eauto.
            simpl.

            repeat rewrite of_list_app. repeat rewrite of_list_3.
            set (XX:=(list_union (oget
                                ⊝ take ❬F❭
                                    (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                     (snd
                                        (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                           (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) t alb))))
                                 ∪ list_union (fst ∘ of_list ⊝ F))).

            assert (lvsEQ:
                      lv ∩ (getAnn lvs \ (of_list (fst Zs) ∪
                                                  (XX ∩ (getAnn lvs \ of_list (fst Zs)) ∪ x)))
                         [=]
                         (getAnn lvs \ (of_list (fst Zs) ∪
                                                (XX ∩ (getAnn lvs \ of_list (fst Zs)) ∪ x)))). {
              rewrite meet_comm. symmetry. eapply incl_meet.
              rewrite <- H3. subst XX.
              rewrite <- H14.
              clear_all; cset_tac.
            }
            rewrite lvsEQ.
            rewrite restrict_disj.
            + eapply restrict_subset2; eauto.
              do 2 rewrite drop_zip.
              repeat rewrite drop_length_ass; eauto with len.
              eapply zip_ominus_contra; eauto with len.
              eapply PIR2_drop; eauto.
              eapply PIR2_addAdds'; eauto with len.
              eapply PIR2_combineParams_get;
                [ | eauto with len | eauto using zip_get_eq | reflexivity].
              eapply computeParametersF_length_pair; eauto with len.
            + intros. inv_get.
              unfold ominus', lminus in H15.
              destruct x3; invc H15. simpl in *.
              subst XX.
              revert H5 H6. clear_all.
              intros; hnf; intros. cset_tac'.
              * eapply H8; eauto.
                eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
                eauto.
              * eapply H0; eauto.
                eapply incl_list_union.
                eapply map_get_1.
                eapply get_take; eauto using get_range. reflexivity.
                eauto.
        }
      * eapply PIR2_addAdds'; eauto with len.
        eapply PIR2_combineParams_get; [ | | | reflexivity].
        eapply computeParametersF_length_pair; eauto with len.
        eauto with len. eapply zip_get_eq; eauto.
    + rewrite <- List.map_app. rewrite <- take_eta.
      eapply trs_monotone_DL_AP.
      eapply IHLIVE; eauto using PIR2_Subset_tab_extend with len.
      * { rewrite (take_eta (length F) (zip ominus' _ _)).
          rewrite List.map_app.
          eapply PIR2_app.
          - eapply PIR2_restrict.
            do 2 rewrite take_zip.
            rewrite take_app_eq; [|eauto with len].
            rewrite take_app_eq; [|eauto with len].
            eapply ominus'_Some_oto_list.
            eapply PIR2_take. eapply PIR2_addAdds'.
            eauto with len.
            eapply PIR2_combineParams; [| reflexivity].
            eapply computeParametersF_length_pair; eauto with len.
          - eapply restrict_subset2; eauto.
            do 2 rewrite drop_zip.
            repeat (rewrite drop_length_ass; [| eauto with len]).
            eapply zip_ominus_contra.
            eapply PIR2_drop; eauto.
            eapply PIR2_addAdds'. eauto with len.
            eapply PIR2_combineParams; [| reflexivity].
            eapply computeParametersF_length_pair; eauto with len.
        }
      * eapply PIR2_addAdds'; eauto with len.
        eapply PIR2_combineParams; [|reflexivity].
        eapply computeParametersF_length_pair; eauto with len.
Qed.

Print Assumptions computeParameters_trs.


Lemma additionalParameters_live_monotone ZL Lv LV' s an' LV lv
: live_sound Imperative ZL Lv s lv
  -> additionalParameters_live LV s lv an'
  -> PIR2 Subset LV' (Lv \\ ZL)
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

(*TODO move these lemmas *)
Lemma nodup_to_list_var (s: set var)
  : NoDupA eq (to_list s).
Proof.
  pose proof (elements_3w s). eauto.
Qed.

Lemma InA_In_var (L:list var) (x:var)
  : InA eq x L <-> InA _eq x L.
Proof.
  split; eauto.
Qed.


Lemma computeParameters_live ZL Lv AP s lv
: live_sound Imperative ZL Lv s lv
  -> PIR2 Subset AP (Lv \\ ZL)
  -> length Lv = length ZL
  -> length ZL = length AP
  -> noUnreachableCode isCalled s
  -> additionalParameters_live (oget ⊝ (snd (computeParameters (Lv \\ ZL) ZL AP s lv)))
                              s lv (fst (computeParameters (Lv \\ ZL) ZL AP s lv)).
Proof.
  intros LS SUB LEN1 LEN2 REACH.
  general induction LS; inv REACH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq;
    subst; simpl in *.
  - econstructor; eauto 20 using addParam_Subset with len.
  - econstructor; eauto with len.
    + eapply additionalParameters_live_monotone; eauto.
      * eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion;
          eauto using computeParameters_LV_DL with len.
    + eapply additionalParameters_live_monotone; eauto.
      * eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion;
          eauto using computeParameters_LV_DL with len.
  - inv_get. PIR2_inv. inv_get.
    econstructor; eauto using map_get_eq, keep_Some; eauto with cset.
  - econstructor.
  - lnorm.
    econstructor.
    + intros. inv_get.
      pose proof (H8 _ H10).
      edestruct computeParameters_isCalledFrom_get_Some; try eapply H9;
        eauto using map_get_1, get_app with len; dcr; subst.
      intros; edestruct H2; eauto.
      simpl. rewrite of_list_3.
      exploit (@computeParameters_LV_DL (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (tab {}  ‖F‖ ++ AP));
        eauto using PIR2_Subset_tab_extend with len.
      exploit computeParametersF_LV_DL; try rewrite <- zip_app; eauto with len.
      eapply PIR2_nth in H13; eauto. dcr; inv_get. inv H17.
      split.
      rewrite H15. clear_all; cset_tac.
      edestruct H2; eauto.
      eapply NoDupA_app; eauto.
      eapply nodup_to_list_var.
      intros.
      rewrite InA_In_var in H18. rewrite InA_in in H18.
      rewrite InA_In_var in H19. rewrite InA_in in H19.
      rewrite of_list_3 in H19. revert H15 H18 H19; clear.
      cset_tac'.
    + intros. inv_get.
      exploit H1; eauto using pair_eta, PIR2_Subset_tab_extend with len.
      eapply additionalParameters_live_monotone; try eapply H9; eauto.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len.
      eapply computeParameters_LV_DL; eauto using PIR2_Subset_tab_extend with len.
    + eapply additionalParameters_live_monotone; try eapply IHLS;
        eauto using PIR2_Subset_tab_extend with len.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len.
      eapply computeParameters_LV_DL; eauto using PIR2_Subset_tab_extend with len.
    + rewrite map_length. rewrite take_length_le; eauto.
      rewrite zip_length2. eauto 20 with len.
      rewrite fold_zip_ounion_length; eauto. eauto 20 with len.
      eapply computeParametersF_length; try eapply H5; eauto with len.
Qed.

Lemma is_trs s lv
: live_sound Imperative nil nil s lv
  -> noUnreachableCode isCalled s
  -> trs nil nil s lv (fst (computeParameters nil nil nil s lv)).
Proof.
  intros.
  assert (snd (computeParameters nil nil nil s lv) = nil). {
    exploit computeParameters_AP_LV; eauto.
    inv H1; eauto.
  }
  exploit computeParameters_trs; eauto using @PIR2.
  simpl in *. rewrite H1 in H2. eauto.
Qed.

Lemma is_live s lv
: live_sound Imperative nil nil s lv
  -> noUnreachableCode isCalled s
  -> additionalParameters_live nil s lv (fst (computeParameters nil nil nil s lv)).
Proof.
  intros.
  assert (snd (computeParameters nil nil nil s lv) = nil). {
    exploit computeParameters_AP_LV; eauto.
    inv H1; eauto.
  }
  exploit computeParameters_live; eauto using @PIR2.
  simpl in *. rewrite H1 in H2. eauto.
Qed.
