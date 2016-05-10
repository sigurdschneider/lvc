Require Import Util IL InRel RenamedApart LabelsDefined.
Require Import Restrict MoreExp SetOperations OUnion.
Require Import Annotation Liveness Coherence.
Require Import Bisim BisimTactics.

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

Opaque to_list.

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
  intros. general induction H; simpl; eauto using PIR2.
  - econstructor; eauto.
    destruct x, y; unfold flip, elem_incl; repeat rewrite of_list_3; simpl; inv pf; eauto with cset.
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
  - rewrite <- List.map_app in H20. rewrite <- List.map_app in H19.
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
