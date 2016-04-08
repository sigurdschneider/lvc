Require Import CSet Le.

Require Import Plus Util AllInRel Map Take MoreList.
Require Import Val Var Env EnvTy IL Annotation Liveness Coherence Restrict Delocation LabelsDefined.

Set Implicit Arguments.
Unset Printing Abstraction Types.
Local Arguments lminus {X} {H} s L.

Definition addParam x (DL:list (set var)) (AP:list (set var)) :=
  zip (fun (DL:set var) AP => if [x ∈ DL]
                   then {{x}} ∪ AP else AP) DL AP.

Definition oget {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => s | None => ∅ end.

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

Definition ounion {X} `{OrderedType X} (s t: option (set X)) :=
  match s, t with
    | Some s, Some t => Some (s ∪ t)
    | Some s, None => Some s
    | None, Some t => Some t
    | _, _ => None
  end.

Lemma ounion_left_Some X `{OrderedType X} s t
  : ounion (Some s) t === Some (s ∪ oget t).
Proof.
  destruct t; simpl.
  - cset_tac.
  - econstructor. hnf. cset_tac.
Qed.

Lemma ounion_right_Some X `{OrderedType X} s t
  : ounion s (Some t) === Some (oget s ∪ t).
Proof.
  destruct s; simpl.
  - cset_tac.
  - econstructor. hnf. cset_tac.
Qed.

Lemma fold_zip_ounion_length X `{OrderedType X} a b
  : (forall n aa, get a n aa -> length aa = length b)
    -> length (fold_left (zip ounion) a b) = length b.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  rewrite IHa; eauto 10 using get with len.
Qed.


Definition keep m (AP:list (set var)) :=
  mapi (fun n x => if [n = m] then Some x else None) AP.

Lemma keep_Some AP n x
  : get AP n x
    -> get (keep n AP) n (Some x).
Proof.
  intros.
  eapply (get_mapi (fun n' x => if [n' = n] then ⎣x⎦ else ⎣⎦)) in H.
  cases in H; eauto.
Qed.

Lemma keep_None n m AP x
  : get (keep n AP) m x -> n <> m -> x = None.
Proof.
  intros. edestruct (mapi_get _ _ H) as [y [A B]].
  cases in B; congruence.
Qed.

Lemma keep_get AP n m x
  : get (keep n AP) m (Some x) -> get AP m x /\ n = m.
Proof.
  intros.
  edestruct (mapi_get _ _ H) as [y [A B]].
  cases in B; inv B; eauto.
Qed.


Definition oto_list {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => to_list s | None => nil end.

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

Local Notation "≽" := (fstNoneOrR (flip Subset)).
Local Notation "≼" := (fstNoneOrR (Subset)).
Local Notation "A ≿ B" := (PIR2 (fstNoneOrR (flip Subset)) A B) (at level 60).

Lemma PIR2_flip_Subset_ext_right X `{OrderedType X} A B B'
  : A ≿ B
    -> PIR2 (option_eq Equal) B B'
    -> A ≿ B'.
Proof.
  intros GE EQ. general induction GE; inv EQ; eauto.
  econstructor; eauto.
  inv pf; inv pf0; econstructor.
  rewrite <- H2. eauto.
Qed.

Lemma trs_monotone_DL (DL DL' : list (option (set var))) ZL s lv a
 : trs DL ZL s lv a
   -> DL ≿ DL'
   -> trs DL' ZL s lv a.
Proof.
  intros. general induction H; eauto 30 using trs, restrict_subset2.
  - destruct (PIR2_nth H1 H); eauto; dcr. inv H4.
    econstructor; eauto.
  - econstructor; eauto using restrict_subset2, PIR2_app.
Qed.

Instance fstNoneOrR_flip_Subset_trans {X} `{OrderedType X} : Transitive ≽.
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Instance fstNoneOrR_flip_Subset_trans2 {X} `{OrderedType X} : Transitive (fstNoneOrR Subset).
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Lemma PIR2_restrict A B s
:  A ≿ B
   -> restrict A s ≿ B.
Proof.
  intros. general induction H; simpl.
  - econstructor.
  - econstructor; eauto.
    + inv pf; simpl.
      * econstructor.
      * cases. econstructor; eauto. econstructor.
Qed.

Opaque to_list.

Definition elem_eq {X} `{OrderedType X} (x y: list X) := of_list x [=] of_list y.

Instance elem_eq_refl X `{OrderedType X} : Reflexive (@elem_eq X _).
hnf; intros. hnf. cset_tac; intuition.
Qed.

Definition elem_incl {X} `{OrderedType X} (x y: list X) := of_list x [<=] of_list y.

Instance elem_incl_refl X `{OrderedType X} : Reflexive (@elem_incl _ _).
hnf; intros. hnf. cset_tac; intuition.
Qed.

Lemma trs_AP_seteq (DL : list (option (set var))) AP AP' s lv a
 : trs DL AP s lv a
   -> PIR2 elem_eq AP AP'
   -> trs DL AP' s lv a.
Proof.
  intros. general induction H; eauto using trs.
  - destruct (PIR2_nth H1 H0); eauto; dcr.
    econstructor; eauto.
  - econstructor; eauto using PIR2_app.
Qed.

Lemma trs_AP_incl (DL : list (option (set var))) AP AP' s lv a
 : trs DL AP s lv a
   -> PIR2 elem_incl AP AP'
   -> trs DL AP' s lv a.
Proof.
  intros. general induction H; eauto using trs.
  - destruct (PIR2_nth H1 H0); eauto; dcr.
    econstructor; eauto.
  - econstructor; eauto using PIR2_app.
Qed.

Definition map_to_list {X} `{OrderedType X} (AP:list (option (set X)))
  := List.map (fun a => match a with Some a => to_list a | None => nil end) AP.

Lemma PIR2_Subset_of_list (AP AP': list (option (set var)))
: PIR2 (fstNoneOrR Subset) AP AP'
  -> PIR2 (flip elem_incl) (map_to_list AP') (map_to_list AP).
Proof.
  intros. general induction H; simpl.
  + econstructor.
  + econstructor. destruct x, y; cset_tac; intuition.
    - hnf. setoid_rewrite of_list_3. inv pf; eauto.
    - inv pf.
    - hnf; intros; simpl in *.
      exfalso; cset_tac; intuition.
    - eauto.
Qed.

Lemma trs_monotone_AP (DL : list (option (set var))) AP AP' s lv a
 : trs DL (List.map oto_list AP) s lv a
   -> PIR2 (fstNoneOrR Subset) AP AP'
   -> trs DL (List.map oto_list AP') s lv a.
Proof.
  intros. eapply trs_AP_incl; eauto. eapply PIR2_flip.
  eapply PIR2_Subset_of_list; eauto.
Qed.

Lemma trs_monotone_DL_AP (DL DL' : list (option (set var))) AP AP' s lv a
  : trs DL (List.map oto_list AP) s lv a
   -> DL ≿ DL'
   -> PIR2 (fstNoneOrR Subset) AP AP'
   -> trs DL' (List.map oto_list AP') s lv a.
Proof.
  eauto using trs_monotone_AP, trs_monotone_DL.
Qed.

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

Lemma PIR2_map_some {X} R (AP AP':list X)
: length AP = length AP'
  -> PIR2 R AP AP'
  -> PIR2 (fstNoneOrR R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0.
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.

Lemma PIR2_map_some_option {X} R (AP AP':list X)
: length AP = length AP'
  -> PIR2 R AP AP'
  -> PIR2 (option_eq R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0.
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.

Lemma PIR2_ounion {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 ≽ A C
  -> PIR2 ≽ B C
  -> PIR2 ≽ (zip ounion A B) C.
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor. unfold flip in *.
    cset_tac; intuition.
Qed.

Lemma PIR2_ounion' {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 ≼ C A
  -> PIR2 ≼ C B
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl;
    (econstructor; [econstructor; eauto with cset | eauto]).
Qed.

Lemma PIR2_ounion_AB {X} `{OrderedType X} (A A' B B':list (option (set X)))
: length A = length A'
  -> length B = length B'
  -> length A = length B
  -> PIR2 ≼ A A'
  -> PIR2 ≼ B B'
  -> PIR2 ≼ (zip ounion A B) (zip ounion A' B').
Proof.
  intros. length_equify.
  general induction H0; inv H1; inv H2; simpl; econstructor.
  - inv H3; inv H4.
    inv pf; inv pf0; simpl; try econstructor.
    destruct y; simpl; eauto. econstructor. cset_tac; intuition.
    destruct y0; simpl; eauto. econstructor. cset_tac; intuition.
    cset_tac; intuition.
  - inv H3; inv H4. eapply IHlength_eq; eauto.
Qed.

Lemma PIR2_option_eq_Subset_zip {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 (option_eq Subset) C A
  -> PIR2 (option_eq Subset) C B
  -> PIR2 (option_eq Subset) C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl;
    now (econstructor; [econstructor; eauto with cset | eauto]).
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

Lemma computeParameters_length DL ZL AP s lv an' LV
 : computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
   -> live_sound Imperative (zip pair DL ZL) s lv
   -> length AP = length DL
   -> length DL = length ZL
   -> length LV = length DL.
Proof.
  intros CPEQ LS LEQ LEQ2.
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
      rewrite zip_length2; eauto with len.
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

Inductive ifSndR {X Y} (R:X -> Y -> Prop) : X -> option Y -> Prop :=
  | ifsndR_None x : ifSndR R x None
  | ifsndR_R x y : R x y -> ifSndR R x (Some y).

Lemma PIR2_ifSndR_Subset_left X `{OrderedType X} A B C
: PIR2 (ifSndR Subset) B C
-> PIR2 Subset A B
-> PIR2 (ifSndR Subset) A C.
Proof.
  intros. general induction H1; simpl in *.
  + inv H0. econstructor.
  + inv H0. inv pf0; eauto using @PIR2, @ifSndR with cset.
Qed.


Lemma ifSndR_zip_ounion X `{OrderedType X} A B C
: PIR2 (ifSndR Subset) C A
  -> PIR2 (ifSndR Subset) C B
  -> PIR2 (ifSndR Subset) C (zip ounion A B).
Proof.
  intros.
  general induction H0.
  - inv H1; econstructor.
  - inv H1.
    inv pf; inv pf0; eauto using @PIR2, @ifSndR with cset.
Qed.

Lemma ifSndR_fold_zip_ounion X `{OrderedType X} A B C
: (forall n a, get A n a -> PIR2 (ifSndR Subset) C a)
  -> PIR2 (ifSndR Subset) C B
  -> PIR2 (ifSndR Subset) C (fold_left (zip ounion) A B).
Proof.
  intros GET LE.
  general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifSndR_zip_ounion.
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

Lemma PIR2_ifSndR_keep n AP
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

Inductive ifFstR {X Y} (R:X -> Y -> Prop) : option X -> Y -> Prop :=
  | IfFstR_None y : ifFstR R None y
  | IfFstR_R x y : R x y -> ifFstR R (Some x) y.

Lemma ifFstR_zip_ounion X `{OrderedType X} A B C
: PIR2 (ifFstR Subset) A C
  -> PIR2 (ifFstR Subset) B C
  -> PIR2 (ifFstR Subset) (zip ounion A B) C.
Proof.
  intros.
  general induction H0.
  - inv H1; econstructor.
  - inv H1.
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor.
    cset_tac; intuition.
Qed.

Lemma PIR2_ifFstR_keep n AP
  :  PIR2 (ifFstR Subset) (keep n AP) AP.
Proof.
  unfold keep, mapi. generalize 0.
  general induction AP; simpl.
  - econstructor.
  - cases; eauto using PIR2, @ifFstR.
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

Lemma PIR2_ifFstR_option_eq_left X `{OrderedType X} A B C
      : PIR2 (ifFstR Subset) B C
        -> PIR2 (option_eq Subset) A B
        -> PIR2 (ifFstR Subset) A C.
Proof.
  intros H1 H2. general induction H2; inv H1; eauto using @PIR2.
  econstructor; eauto.
  inv pf; try econstructor. inv pf0. intuition.
Qed.

Lemma PIR2_ifFstR_Subset_right X `{OrderedType X} A B C
: PIR2 (ifFstR Subset) A B
-> PIR2 Subset B C
-> PIR2 (ifFstR Subset) A C.
Proof.
  intros P S. general induction P; inv S; simpl in *; eauto using PIR2.
  - inv pf; eauto using PIR2, @ifFstR.
    econstructor; eauto.
    econstructor; cset_tac; intuition.
Qed.


Lemma ifFstR_fold_zip_ounion X `{OrderedType X} A B C
  : (forall n a, get A n a -> PIR2 (ifFstR Subset) a C)
    -> PIR2 (ifFstR Subset) B C
    -> PIR2 (ifFstR Subset) (fold_left (zip ounion) A B) C.
Proof.
  intros GET LE.
  general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifFstR_zip_ounion.
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

Lemma get_olist_union_b X `{OrderedType X} A b n x p
  : get b n (Some x)
    -> get (olist_union A b) n p
    -> (forall n a, get A n a -> ❬b❭ = ❬a❭)
    -> exists s, p = Some s.
Proof.
  intros GETb GET LEN. general induction A; simpl in *.
  - get_functional; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb H0) as [y GETa]; eauto.
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *;
    eapply IHA; try eapply GET; eauto;
    rewrite zip_length2; eauto using get with len.
Qed.

Lemma get_olist_union_A X `{OrderedType X} A a b n k x p
  : get A k a
    -> get a n (Some x)
    -> get (olist_union A b) n p
    -> (forall n a, get A n a -> ❬b❭ = ❬a❭)
    -> exists s, p = Some s.
Proof.
  intros GETA GETa GETunion LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa (eq_sym H0)) as [y GETb].
    exploit (zip_get ounion GETb GETa).
    destruct y; eapply get_olist_union_b; try eapply GETunion; eauto;
    rewrite zip_length2; eauto using get with len.
  - eapply IHA; eauto.
    rewrite zip_length2; eauto using get with len.
Qed.

Tactic Notation "Rexploit" uconstr(H) :=
  eapply modus_ponens; [refine H | intros].

Tactic Notation "Rexploit" uconstr(X) "as" ident(H)  :=
  eapply modus_ponens; [refine X | intros H].

Lemma zip_get_eq X Y Z (f:X -> Y -> Z) L L' n (x:X) (y:Y)
  : get L n x -> get L' n y -> forall fxy, fxy = f x y -> get (zip f L L') n fxy.
Proof.
  intros. general induction n; inv H; inv H0; simpl; eauto using get.
Qed.

Lemma computeParameters_isCalled_Some DL ZL AP s lv an' LV n p
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> isCalled s (LabI n)
  -> get LV n p
  -> exists s, p = Some s.
Proof.
  intros LS CPEQ LEN1 LEN2 IC GET.
  general induction IC; simpl in * |- *; inv LS; repeat let_case_eq; invc CPEQ.
  - edestruct IHIC; eauto with len.
  - edestruct get_zip as [bv [bv' [GET1 [GET2 ?]]]]; eauto; subst.
    edestruct IHIC; eauto; subst. destruct bv'; eexists; reflexivity.
  - edestruct get_zip as [bv [bv' [GET1 [GET2 ?]]]]; eauto; subst.
    edestruct IHIC; eauto; subst. destruct bv; eexists; reflexivity.
  - simpl in *.
    intros.
    edestruct (mapi_get _ _ GET) as [x [ H]]; eauto; subst.
    cases; eauto.
  - edestruct IHIC; eauto with len.
  - simpl in *. inv_get.
    rewrite <- zip_app in H1; eauto with len. inv_get.
    rewrite live_globals_zip in H5; eauto with len.
    rewrite <- zip_app in eq; eauto with len.
    edestruct (get_length_eq _ H0 H4) as [alv GETalv].
    exploit computeParameters_length; try eapply pair_eta.
    eapply H5; eauto. instantiate (1:=tab {} ‖F‖ ++ AP); eauto with len.
    eauto with len.
    destruct (@get_in_range _ (snd
          (computeParameters ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL))
                             (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) (snd Zs) alv)) (❬F❭ + n))
      as [pF GETpF].
    rewrite H6. eapply get_range in H2. rewrite app_length, map_length. omega.
    edestruct IHIC1; try eapply GETpF; eauto using pair_eta.
    eauto with len. eauto with len. subst.
    Rexploit (get_olist_union_A _ _ GETpF GET _).
    eapply map_get_1.
    rewrite zip_app; eauto with len.
    eapply zip_get_eq; eauto.
    eapply computeParameters_length in eq; eauto with len.
    rewrite eq.
    eapply computeParametersF_length; eauto. rewrite live_globals_zip; eauto.
    rewrite <- live_globals_zip; eauto.
    edestruct H8; subst. simpl. eauto.
  - simpl in *. inv_get.
    rewrite <- zip_app in H; eauto with len. inv_get.
    rewrite live_globals_zip in H1; eauto with len.
    rewrite <- zip_app in eq; [| eauto with len].
    exploit computeParameters_length; eauto. eauto with len. eauto with len.
    destruct (@get_in_range _ b (❬F❭ + n)) as [pF GETpF].
    rewrite H4, app_length, map_length. exploit (get_range H0). omega.
    edestruct IHIC; eauto. eauto with len. eauto with len. subst.
    Rexploit (get_olist_union_b GETpF GET _).
    rewrite H4.
    eapply computeParametersF_length; eauto.
    destruct H6; subst; simpl; eauto.
Qed.

Lemma computeParameters_isCalled_get_Some DL ZL AP s lv an' LV n p A
  : computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
    -> live_sound Imperative (zip pair DL ZL) s lv
    -> length AP = length DL
    -> length DL = length ZL
    -> isCalled s (LabI n)
    -> n < ❬LV❭
    -> get (olist_union A LV) n p
    -> (forall (n0 : nat) (a : 〔؟⦃var⦄〕), get A n0 a -> ❬LV❭ = ❬a❭)
    -> exists s, p = Some s.
Proof.
  intros CPEQ LS LEN1 LEN2 IC LE GET LEN3.
  destruct (@get_in_range _ LV n); eauto.
  edestruct computeParameters_isCalled_Some; eauto; subst.
  edestruct get_olist_union_b; eauto.
Qed.

Definition ominus' (s : set var) (t : option (set var)) := mdo t' <- t; ⎣s \ t' ⎦.
Definition minuso (s : set var) (t : option (set var)) := ⎣s \ oget t ⎦.

Lemma bounded_disjoint_incl_minus s t u L
  : s \ t ⊆ u
    -> bounded L s
    -> (forall n x, get L n (Some x) -> disj x t)
    -> bounded L u.
Proof.
  intros INCL BOUNDED DISJ.
  eapply get_bounded. intros.
  Rexploit (bounded_get _ BOUNDED _) as INCL2; eauto.
  exploit DISJ; eauto.
  rewrite <- INCL, <- INCL2.
  eauto with cset.
Qed.

Lemma computeParameters_bounded DL ZL AP s lv an' LV
: live_sound Imperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> bounded (zip ominus' (zip lminus DL ZL) LV) (getAnn lv).
Proof.
  intros LS CPEQ LEN1 LEN2.
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    exploit computeParameters_AP_LV; eauto. eauto with len.
    eapply bounded_disjoint_incl_minus; eauto.
    intros. inv_get. destruct x2; inv EQ.
    edestruct (get_length_eq _ H7 (eq_sym LEN1)).
    edestruct PIR2_nth; eauto using zip_get; dcr.
    cases in H10.
    + inv H10; get_functional; subst.
      rewrite <- H8. clear_all; hnf; intros; cset_tac.
    + revert NOTCOND; clear_all; intros; hnf; intros; cset_tac.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    eapply get_bounded. intros. inv_get.
    destruct x2, x3; inv EQ; simpl in *.
    + Rexploit (bounded_get _ H2 _); eauto; try eapply zip_get_eq; eauto using zip_get;
        eauto; try reflexivity.
      rewrite <- H0. rewrite <- H6. clear_all; cset_tac.
    + Rexploit (bounded_get _ H2 _); eauto; try eapply zip_get_eq; eauto using zip_get;
        eauto; try reflexivity.
      rewrite <- H0. rewrite <- H6. clear_all; cset_tac.
    + Rexploit (bounded_get _ H3 _); eauto; try eapply zip_get_eq; eauto using zip_get;
        eauto; try reflexivity.
      rewrite <- H1. rewrite <- H6. reflexivity.
  - eapply get_bounded; intros.
    inv_get; subst. destruct x1; simpl in *; try congruence.
    invc EQ. edestruct keep_get; eauto; subst.
    repeat get_functional. unfold lminus. rewrite H0. cset_tac.
  - eapply get_bounded; intros; inv_get; simpl in *; congruence.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    exploit computeParameters_AP_LV; eauto. eauto with len.
    eapply bounded_disjoint_incl_minus; eauto.
    intros. inv_get. destruct x2; inv EQ.
    edestruct (get_length_eq _ H7 (eq_sym LEN1)).
    edestruct PIR2_nth; eauto using zip_get; dcr.
    cases in H10.
    + inv H10; get_functional; subst.
      rewrite <- H8. clear_all; hnf; intros; cset_tac.
    + revert NOTCOND; clear_all; intros; hnf; intros; cset_tac.
  - lnorm.
    eapply get_bounded. intros. inv_get.
    get_functional.
    destruct x3; invc EQ.
    exploit IHLS; eauto with len.
    exploit bounded_get; eauto.
    eapply zip_get_eq. rewrite zip_app.
    eapply get_shift. eapply zip_get; eauto with len. eauto with len.
    admit. admit.

Qed.

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


(*
Lemma srd_globals_live DL ZL AP s lv an' LV f slv Z Za
  : live_sound FunctionalAndImperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> get (zip pair DL ZL) (counted f) (slv, Z)
  -> get LV (counted f) (Some Za)
  -> slv \ (of_list Z ∪ Za) ⊆ getAnn lv.
Proof.
  intros LS CPEQ.
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_length with len.
Qed.
*)


Lemma ounion_comm X `{OrderedType X} (s t:option (set X))
  : option_eq Equal (ounion s t) (ounion t s).
Proof.
  destruct s,t; simpl; try now econstructor.
  - econstructor. cset_tac; intuition.
Qed.

Lemma zip_PIR2 X Y (eqA:Y -> Y -> Prop) (f:X -> X -> Y) l l'
  : (forall x y, eqA (f x y) (f y x))
    -> PIR2 eqA (zip f l l') (zip f l' l).
Proof.
  general induction l; destruct l'; simpl; try now econstructor.
  econstructor; eauto.
Qed.

Lemma PIR2_zip_ounion X `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> PIR2 (fstNoneOrR Subset) b (zip ounion b b').
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
Qed.

Lemma PIR2_zip_ounion' X `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> PIR2 (fstNoneOrR Subset) b (zip ounion b' b).
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
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

(*
Lemma restrict_zip_ominus' DL LV lv x al
:  length DL = length LV
-> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
-> al \ singleton x ⊆ lv
->  restrict (zip ominus DL LV) al
 ≿ restrict (zip ominus DL LV) (lv \ singleton x).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in *.
  - econstructor.
  - econstructor.
    + destruct y; intros; simpl.
      repeat cases; try now econstructor.
      * econstructor. reflexivity.
      * decide (x0 ∈ s). exfalso. eapply n.
        hnf; intros. decide (a === x0). rewrite e in H2.
        exfalso; cset_tac; intuition.
        rewrite <- H1.
        cset_tac; intuition.
        exploit H0; eauto using get.
        exfalso. eapply n. rewrite <- H1. cset_tac; intuition.
      * econstructor.
    + eapply IHlength_eq; eauto using get.
Qed.
 *)


Lemma restrict_get L s t n
: get L n (Some s)
  -> s ⊆ t
  -> get (restrict L t) n (Some s).
Proof.
  intros. general induction H; simpl.
  + cases.
    - econstructor.
    + econstructor; eauto.
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


Lemma fstNoneOrR_ounion_left X `{OrderedType X} a b c
  : ≼ a b -> ≼ a (ounion b c).
Proof.
  intros A; inv A; eauto using @fstNoneOrR.
  destruct c; simpl; eauto.
  econstructor. cset_tac.
Qed.


Lemma fstNoneOrR_ounion_right X `{OrderedType X} a b c
  : ≼ a c -> ≼ a (ounion b c).
Proof.
  intros A; inv A; eauto using @fstNoneOrR.
  destruct b; simpl; eauto.
  econstructor. cset_tac.
Qed.


Lemma PIR2_ounion_left X `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> PIR2 ≼ C A
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; invt PIR2; simpl.
  - econstructor.
  - exploit IHlength_eq; eauto.
    econstructor; eauto using fstNoneOrR_ounion_left.
Qed.

Lemma PIR2_ounion_right X `{OrderedType X} (A B C:list (option (set X)))
: length A = length C
  -> PIR2 ≼ C B
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; invt PIR2; simpl.
  - econstructor.
  - exploit IHlength_eq; eauto.
    econstructor; eauto using fstNoneOrR_ounion_left, fstNoneOrR_ounion_right.
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
  unfold minuso, lminus.
  destruct y'; simpl.
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

Lemma PIR2_take X Y (R: X -> Y -> Prop) L L' n
  : PIR2 R L L'
    -> PIR2 R (take n L) (take n L').
Proof.
  intros REL.
  general induction REL; destruct n; simpl; eauto using PIR2.
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
    exploit (@keep_get (labN l)) as GETKEEP; eauto.
    exploit (zip_get lminus GETZL GETDL) as GETLMINUS.
    exploit (zip_get ominus' GETLMINUS GETKEEP) as GETOMINUS.
    econstructor.
    eapply restrict_get. eapply GETOMINUS. unfold lminus.
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

        intros. inv_get; clear_dup. subst.
        unfold lminus, oto_list.
        subst NPL. inv_get.
        eapply get_in_range_app in H11; eauto with len.
        eapply get_in_range_app in H13; eauto with len.
        inv_get.


        edestruct computeParameters_isCalled_get_Some; try eapply eq;
        eauto with len. subst.
        edestruct computeParameters_isCalled_get_Some; try eapply H9; eauto with len.
        subst.

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
                             [=] lv ∩ (getAnn lvs \ of_list (fst Zs ++ oto_list x))). {
          exploit H2; eauto; dcr.
          rewrite of_list_app.
          exploit computeParameters_bounded as BOUNDED; try eapply eq; eauto with len.
          rewrite H3 in BOUNDED.
          evar (xxx:⦃var⦄).
          exploit bounded_get; eauto.
          eapply zip_get_eq. rewrite zip_app.
          eapply get_app. eapply zip_get; eauto using map_get_1; eauto with len.
          eauto with len. instantiate (1:=Some xxx). admit.
          simpl. reflexivity. unfold lminus in H12.

          rewrite <- zip_app in BOUNDED.
          simpl in BOUNDED. rewrite eq in BOUNDED. simpl in *.
          eapply bounded_get in BOUNDED.
          Focus 2. eapply zip_get_eq. admit.
          eapply drop_get. eapply zip_get. admit.
          admit.
          (* eapply H13; eauto. cset_tac; intuition. *)
        }
        rewrite <- lvsEQ.
        rewrite restrict_disj.
        eapply restrict_subset2; eauto.
        eapply zip_ominus_contra; eauto with len.
        rewrite length_drop_minus.
        rewrite zip_length2; eauto with len. omega.

        eapply PIR2_drop; eauto.

        intros. inv_get; clear_dup.
        unfold ominus', lminus in EQ. destruct x1; inv EQ. simpl in *.
        eapply get_drop in H12. clear EQ. subst NPL.
        inv_get.
        rewrite <- zip_app in H14; eauto with len.
        rewrite <- zip_app in H17; eauto with len.
        inv_get. destruct x1; inv H16. simpl in *.
        inv_get.



        eapply get_app_right_ge in H19; eauto with len.
        rewrite map_length in H19. orewrite (❬F❭ + n0 - ❬als❭ = n0) in H19.
        eapply get_app_right_ge in H14; eauto with len.
        rewrite map_length in H14. orewrite (❬F❭ + n0 - ❬F❭ = n0) in H14.
        exploit (get_range H5).
        assert (n < ❬fst ⊝ F❭). rewrite map_length. omega.
        assert (n < ❬getAnn ⊝ als❭). rewrite map_length. omega.
        eapply get_in_range_app in H18; eauto with len.
        eapply get_in_range_app in H17; eauto with len.
        inv_get. clear lvsEQ.


        edestruct computeParameters_isCalled_get_Some; try eapply H9;
        eauto with len. subst. simpl.
        rewrite of_list_app.
        repeat rewrite of_list_3. simpl. unfold lminus.
        hnf; intros. cset_tac. eapply H23; eauto.
        eapply incl_right.
        eapply incl_list_union; [ eapply map_get_1 | reflexivity | eapply H19]; eauto.
        eapply H19; eauto. eapply incl_left.
        eapply incl_list_union.
        eapply map_get_1. eapply get_take; try eapply H10. eauto. reflexivity. eauto.
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

        simpl_pair_eqs; subst. reflexivity.


    (*rewrite NPLEQ.


        eapply ifSndR_fold_zip_ounion.
        eapply PIR2_zip_ounion; congruence.
      eapply PIR2_ounion_AB; try congruence; try reflexivity.


      * rewrite zip_app.

        rewrite restrict_app. rewrite restrict_comp_meet.
        rewrite <- zip_app; eauto with len.
        rewrite (take_eta (length F) LV).
        rewrite zip_app; eauto with len.
        rewrite zip_app.
        rewrite restrict_app.
        eapply PIR2_app.
        admit.
        assert (LVEQ: forall Za', lv ∩ (getAnn lvs \ of_list (fst Zs ++ Za')) [=]
                   getAnn lvs \ of_list (fst Zs ++ Za')). {
          edestruct H2 as [INCL1 INCL2]; eauto.
          intros.
          rewrite of_list_app.
          revert INCL2. clear_all. intros.
          cset_tac; intuition.
        }
        rewrite LVEQ.
        intros.
        rewrite restrict_disj.
        eapply restrict_subset2; eauto.
        eapply zip_ominus_contra. rewrite length_drop_minus. admit.
        admit. eapply PIR2_drop.
        eapply PIR2_addAdds'; eauto with len.
        rewrite H6; eauto with len. admit.
        intros. inv_zip H7. clear H7.
        rewrite drop_zip in H15. inv_zip H15. clear H15.
        rewrite <- zip_app in H7.
        rewrite drop_zip in H7. inv_zip H7. clear H7.
        rewrite drop_length_ass in H15; eauto with len.
        rewrite drop_length_ass in H18; eauto with len.
        inv_zip H14. repeat get_functional; subst. clear H14.
        simpl in *.
        destruct x4; simpl in *; invc H16.
        inv_map H8; clear H8.
        intros. eapply take_get in H14; dcr.
        inv_zip H8. clear H8. clear LVEQ.
        rewrite of_list_app.
        symmetry.
        eapply disj_app; split.
        hnf; intros. cset_tac.
        eapply H23; eauto.
        destruct x as [Z t]. simpl in *.
        eapply incl_list_union; try eapply H18; eauto using map_get.
        hnf; intros. cset_tac.
        eapply H8; eauto.
        destruct x4. simpl in *. rewrite of_list_3 in H18.

        simpl in *. cset_tac.


      * eauto with len. *)


    + inv X1; inv X2.
      exploit trs_monotone3'.
      eapply (IHlive_sound1 (getAnn als::DL) (Z::ZL)); simpl; eauto; try congruence.
      simpl. rewrite addParams_zip_lminus_length; congruence.
      econstructor. cset_tac; intuition.
      eapply addParams_Subset2; eauto.
      instantiate (1:= (ounion x x0 :: zip ounion (addAdds (oget (ounion x x0))
                              (zip lminus DL ZL) XL) XL0)).
      simpl.
      econstructor.  unfold lminus in *.
      inv pf; inv pf0; econstructor; simpl.
      clear_all; cset_tac; intuition.
      clear_all; cset_tac; intuition.
      simpl in *.
      transitivity (zip ounion XL XL0).
      eapply PIR2_zip_ounion; congruence.
      eapply PIR2_ounion_AB; try congruence; try reflexivity.
      rewrite addAdds_length. rewrite zip_length2; congruence.
      rewrite zip_length2; congruence.
      eapply PIR2_addAdds. repeat rewrite zip_length2; eauto; congruence.
      eapply trs_monotone. simpl.
      simpl addAdds in X3.
      destruct (ounion x x0). simpl in *.
      assert (s0 ∩ (getAnn als \ of_list Z) ∪ s0 [=] s0).
      cset_tac; intuition. eapply trs_AP_seteq. eapply X3.
      econstructor; try reflexivity.
      simpl in X3. eapply X3.
      simpl.
      econstructor. cases.
      destruct x, x0; simpl; try now econstructor.
      * repeat cases; unfold lminus in * |- *. econstructor.
      unfold flip; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      exfalso; intuition.
      * unfold lminus. cases.
        econstructor.
        unfold flip; clear_all. repeat rewrite of_list_app.
        rewrite of_list_3. cset_tac; intuition.
        econstructor.
      * exfalso. eapply n. reflexivity.
      * rewrite restrict_comp_meet.
        assert (lv ∩ (getAnn als \ of_list (Z ++ oto_list (ounion x x0)))
               [=] (getAnn als \ of_list (Z ++ oto_list (ounion x x0)))).
        repeat rewrite of_list_app. cset_tac; intuition.
        rewrite H4.
        exploit (computeParameters_AP_LV (getAnn als::DL) (Z::ZL)); try eapply eq; simpl; eauto; simpl; eauto; try congruence.
        rewrite addParams_zip_lminus_length; congruence.
        simpl in *.
        assert (length XL = length XL0) by congruence. inv X4.
        revert H2 H3 H6 pf pf0 H H7 H8 H10. clear_all.
        repeat rewrite of_list_app.
        intros.
        length_equify.
        general induction H; inv H0; inv H1; inv H5; inv H6; inv H7; simpl; try econstructor; eauto.
        inv H2; inv H3; inv pf; inv pf0; inv pf1; simpl; try now econstructor.
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat cases; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
   +  inv X1; inv X2.
      exploit trs_monotone3'.
      eapply (IHlive_sound2 (getAnn als::DL) (Z::ZL)); simpl; eauto; simpl; try congruence.
      econstructor. cset_tac; intuition. eauto.
      instantiate (1:= (ounion x x0 :: zip ounion (addAdds (oget (ounion x x0))
                              (zip lminus DL ZL) XL) XL0)).
      simpl. econstructor.
      destruct x,x0; simpl; econstructor.
      clear_all; cset_tac; intuition.
      clear_all; cset_tac; intuition.
      simpl.       simpl in *.
      transitivity (zip ounion XL XL0).
      eapply PIR2_zip_ounion'; eauto; congruence.
      eapply PIR2_ounion_AB; try congruence; try reflexivity.
      rewrite addAdds_length. rewrite zip_length2; congruence.
      rewrite zip_length2; congruence.
      eapply PIR2_addAdds. repeat rewrite zip_length2; eauto; congruence.
      eapply trs_monotone. simpl in X1.
      simpl. destruct (ounion x x0). simpl in *.
      eapply trs_AP_seteq. eapply X3.
      econstructor; try reflexivity.
      eapply X3.
      econstructor. destruct x,x0. simpl.
      cases. unfold lminus. econstructor.
      unfold flip; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      econstructor.
      simpl. econstructor.
      simpl. cases.
      constructor. unfold flip, lminus; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      econstructor.
      simpl. simpl in *. econstructor.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra.
      rewrite zip_length2; eauto. simpl in *; congruence.
      rewrite zip_length2; eauto.
      rewrite addAdds_length. rewrite zip_length2; eauto.
      repeat rewrite zip_length2; eauto.
      simpl. simpl in *. eauto; congruence.
      rewrite addAdds_length. rewrite zip_length2; eauto.
      simpl. simpl in *. eauto; congruence.
      repeat rewrite zip_length2; eauto.
      simpl. simpl in *. eauto; congruence.
      eapply PIR2_trans. eapply fstNoneOrR_flip_Subset_trans2.
      reflexivity. simpl.
      eapply PIR2_zip_ounion'.
      rewrite addAdds_length. rewrite zip_length2; eauto.
      rewrite zip_length2; eauto. symmetry; simpl in *; congruence.
Qed.

Print Assumptions computeParameters_trs.

Definition oemp X `{OrderedType X} (s : option (set X)) :=
  match s with
    | ⎣s0 ⎦ => s0
    | ⎣⎦ => ∅
  end.

Arguments oemp [X] {H} s.

Lemma additionalParameters_live_monotone (LV':list (option (set var))) DL ZL s an' LV lv
: length DL = length ZL
  -> live_sound FunctionalAndImperative (zip pair DL ZL) s lv
  -> additionalParameters_live LV s lv an'
  -> PIR2 (ifFstR Subset) LV' (zip lminus DL ZL)
  -> additionalParameters_live (List.map (@oemp var _) LV') s lv an'.
Proof.
  intros. general induction H1; invt live_sound; eauto using additionalParameters_live.
  - edestruct get_zip as [? [? []]]; dcr; subst; eauto. invc H8.
    edestruct PIR2_nth_2; eauto. eapply zip_get; eauto.
    dcr.
    econstructor.
    eapply map_get_1; eauto. simpl in *. rewrite <- H9.
    inv H12; simpl. cset_tac; intuition. eapply H5.
  - econstructor; eauto.
    exploit (IHadditionalParameters_live1 (Some (of_list Za)::LV') (getAnn ans_lv::DL) (Z::ZL0)); simpl; try congruence.
    econstructor; eauto. econstructor. unfold lminus.
    rewrite H. reflexivity.
    eapply X.
    exploit (IHadditionalParameters_live2 (Some (of_list Za)::LV') (getAnn ans_lv::DL) (Z::ZL0)); simpl; try congruence.
    econstructor; eauto. econstructor. rewrite H; reflexivity.
    eauto.
Qed.

Lemma computeParameters_live DL ZL AP s an' LV lv
: length DL = length ZL
  -> length ZL = length AP
  -> live_sound FunctionalAndImperative (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> additionalParameters_live (List.map (@oemp _ _) LV) s lv an'.
Proof.
  intros.
  general induction H1; simpl in *.
  - let_case_eq; inv H5.
    econstructor. eapply IHlive_sound; try eapply eq; eauto using addParam_Subset.
    rewrite addParam_length; rewrite zip_length2; eauto; congruence.
  - repeat let_case_eq; invc H4.
    exploit computeParameters_LV_DL; try eapply eq0; eauto. congruence.
    exploit computeParameters_LV_DL; try eapply eq; eauto. congruence.
    econstructor; eauto.
    eapply additionalParameters_live_monotone; eauto.
    eapply ifFstR_zip_ounion; eauto.
    eapply additionalParameters_live_monotone; eauto.
    eapply ifFstR_zip_ounion; eauto.
  - edestruct get_zip as [? [? []]]; dcr; subst; eauto. invc H10.
    edestruct PIR2_nth_2; eauto. eapply zip_get; eauto. dcr.
    econstructor. eapply map_get_1; eauto. eapply killExcept_get; eauto.
    simpl. rewrite <- H0. eapply H11.
  - econstructor.
  - let_case_eq; inv H5.
    econstructor. eapply IHlive_sound; try eapply eq; eauto using addParam_Subset.
    rewrite addParam_length; rewrite zip_length2; eauto; congruence.
  - repeat let_case_eq. invc H4.
    exploit (computeParameters_LV_DL (getAnn als::DL) (Z::ZL)); try eapply eq; eauto; simpl; try congruence. rewrite addParams_length, zip_length2; try congruence.
    rewrite zip_length2; congruence.
    econstructor; eauto. cset_tac; intuition. eapply addParams_Subset2. eauto.
    exploit (computeParameters_LV_DL (getAnn als::DL) (Z::ZL)); try eapply eq0; eauto; simpl; try congruence.
    econstructor; eauto. cset_tac; intuition.
    econstructor. simpl in X,X0.
    inv X; inv X0. simpl. inv pf; inv pf0; simpl.
    eapply incl_empty.
    rewrite of_list_3; eauto.
    rewrite of_list_3; eauto.
    rewrite of_list_3. rewrite H4, H6. rewrite union_idem. reflexivity.
    exploit (IHlive_sound1 (getAnn als::DL) (Z::ZL));
      simpl; eauto.
    simpl. rewrite addParams_length, zip_length2; eauto.
    rewrite zip_length2; congruence.
    constructor. cset_tac; intuition.
    eapply addParams_Subset2; eauto.
    eapply (@additionalParameters_live_monotone
              (Some (of_list (oto_list (ounion (hd ⎣⎦ b0) (hd ⎣⎦ b1))))
                             ::
                             (zip ounion
                                  (addAdds (oget (ounion (hd ⎣⎦ b0) (hd ⎣⎦ b1)))
                                           (zip lminus DL ZL) (tl b0)) (tl b1)))
               (getAnn als::DL) (Z::ZL)).
    simpl. congruence. eauto. eauto. simpl.
    econstructor. constructor. unfold lminus. unfold oto_list.
    simpl in X, X0. inv X; inv X0; simpl.
    inv pf; inv pf0; simpl.
    eapply incl_empty.
    rewrite of_list_3. eauto.
    rewrite of_list_3. eauto.
    rewrite of_list_3. rewrite H6. rewrite H4. rewrite union_idem. reflexivity.
    eapply ifFstR_zip_ounion; eauto.
    eapply ifFstR_addAdds.
    simpl in X, X0. inv X; inv X0; simpl.
    simpl. congruence.
    simpl in X, X0. inv X; inv X0; simpl.
    simpl. congruence.
    exploit (IHlive_sound2 (getAnn als::DL) (Z::ZL)); simpl; eauto.
    simpl. congruence.
    constructor. cset_tac; intuition. eauto.
    eapply (@additionalParameters_live_monotone
              (Some (of_list (oto_list (ounion (hd ⎣⎦ b0) (hd ⎣⎦ b1))))::
                    zip ounion
             (addAdds (oget (ounion (hd ⎣⎦ b0) (hd ⎣⎦ b1)))
                (zip lminus DL ZL) (tl b0)) (tl b1)) (getAnn als::DL) (Z::ZL)).
    simpl. congruence.
    eauto. eauto. simpl.
    econstructor. constructor. unfold lminus. unfold oto_list.
    simpl in X, X0. inv X; inv X0; simpl.
    inv pf; inv pf0; simpl.
    eapply incl_empty.
    rewrite of_list_3. eauto.
    rewrite of_list_3. eauto.
    rewrite of_list_3. rewrite H6. rewrite H4. rewrite union_idem. reflexivity.
    eapply ifFstR_zip_ounion; eauto.
    eapply ifFstR_addAdds.
    simpl in X, X0. inv X; inv X0; simpl. eauto.
    simpl in X, X0. inv X; inv X0; simpl. eauto.
Qed.
