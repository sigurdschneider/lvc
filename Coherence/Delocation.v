Require Import Util IL InRel RenamedApart LabelsDefined.
Require Import Restrict MoreExp SetOperations OUnion.
Require Import Annotation Liveness Coherence.
Require Import Bisim BisimTactics.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.
Unset Printing Abstraction Types.

(** Correctness predicate for  *)

Inductive trs
  : 〔؟⦃var⦄〕 (** globals *)
    -> list (params)        (** additional parameters for functions in scope *)
    -> stmt                 (** the program *)
    -> ann (set var)        (** liveness information *)
    -> ann (list (list var)) (** annotation providing additional parameters for function definitions
                                inside the program *)
    -> Prop :=
| trsExp DL ZL x e s an an_lv lv
  : trs (restr (lv\ singleton x) ⊝ DL) ZL  s an_lv an
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
  : trs (restr (lv\ singleton x) ⊝ DL) ZL s an_lv an
    -> trs DL ZL (stmtExtern x f Y s) (ann1 lv an_lv) (ann1 nil an)
| trsLet (DL:list (option (set var))) ZL (F:list (params*stmt)) t Za ans ant lv ans_lv ant_lv
  : length F = length ans_lv
    -> length F = length ans
    -> length F = length Za
    -> (forall n lvs Zs Za' ans',
          get ans_lv n lvs -> get F n Zs -> get Za n Za' -> get ans n ans'
          -> trs (restr (getAnn lvs \ of_list (fst Zs++Za')) ⊝ (Some ⊝ (getAnn ⊝ ans_lv) \\ zip (@List.app _) (fst ⊝ F) Za ++ DL))
                (Za++ZL) (snd Zs) lvs ans')
    -> trs (Some ⊝ (getAnn ⊝ ans_lv) \\ zip (@List.app _) (fst ⊝ F) Za ++ DL)
          (Za++ZL) t ant_lv ant
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


Lemma fst_compileF_eq ZL F Za Za' ans
      (LEN1 : length F = length ans)
      (LEN2 : length F = length Za)
  : fst ⊝ compileF compile ZL F Za Za' ans = app (A:=var) ⊜ (fst ⊝ F) Za.
Proof.
  length_equify.
  unfold compileF.
  general induction LEN1; inv LEN2; simpl; eauto using PIR2.
  - f_equal. eauto.
Qed.


Lemma trs_srd AL ZL s ans_lv ans
  (RD:trs AL ZL s ans_lv ans)
  : srd AL (compile ZL s ans) ans_lv.
Proof.
  general induction RD; simpl; eauto using srd.
  - econstructor; eauto.
    * unfold compileF; repeat rewrite zip_length2; congruence.
    * intros. unfold compileF in H4. inv_get. simpl.
      exploit H3; eauto. simpl.
      eapply srd_monotone; eauto.
      eapply restrict_subset; eauto.
      eapply PIR2_app; eauto.
      rewrite fst_compileF_eq; eauto.
    * eapply srd_monotone; eauto.
      eapply PIR2_app; eauto.
      rewrite fst_compileF_eq; eauto.
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

Lemma live_sound_compile ZL ZAL Lv DL s ans_lv ans o
  (RD:trs DL ZAL s ans_lv ans)
  (LV:live_sound o ZL Lv s ans_lv)
  (APL: additionalParameters_live (of_list ⊝ ZAL) s ans_lv ans)
  : live_sound o (zip (@List.app _) ZL ZAL) Lv (compile ZAL s ans) ans_lv.
Proof.
  general induction LV; inv RD; inv APL; eauto using live_sound.
  - simpl. erewrite get_nth; eauto.
    inv_get.
    econstructor; eauto using zip_get with len.
    + cases; eauto. rewrite <- H1. rewrite of_list_app. eauto with cset.
    + intros ? ? Get.
      eapply get_app_cases in Get. destruct Get; dcr; eauto.
      inv_get.
      econstructor. rewrite <- H10. eauto using get_in_of_list.
  - simpl. rewrite <- List.map_app in H20.
    rewrite <- List.map_app in H19.
    econstructor; eauto with len.
    + rewrite fst_compileF_eq; eauto.
      rewrite <- zip_app; eauto with len.
    + intros.
      unfold compileF in H4. inv_get. simpl.
      rewrite fst_compileF_eq; eauto. rewrite <- zip_app; eauto with len.
    + intros.
      unfold compileF in H4. inv_get; simpl.
      exploit H2; eauto. exploit H13; eauto. dcr.
      rewrite of_list_app at 1.
      split.
      * rewrite H10, H9. eauto with cset.
      * cases; eauto. rewrite of_list_app.
        rewrite <- minus_union. rewrite <- H11. eauto with cset.
Qed.
