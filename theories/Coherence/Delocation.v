Require Import Util LengthEq IL RenamedApart LabelsDefined AppExpFree.
Require Import Restrict SetOperations OUnion OptionR.
Require Import Annotation Liveness.Liveness Coherence.

Set Implicit Arguments.
Unset Printing Records.

(** Correctness predicate for  *)

Inductive trs
  : 〔؟⦃var⦄〕 (** globals *)
    -> stmt                 (** the program *)
    -> ann (set var)        (** liveness information *)
    -> ann (list (list var)) (** annotation providing additional parameters for function definitions
                                inside the program *)
    -> Prop :=
| trsExp DL x e s an an_lv lv
  : trs (restr (getAnn an_lv \ singleton x) ⊝ DL) s an_lv an
    -> trs DL (stmtLet x e s) (ann1 lv an_lv) (ann1 nil an)
| trsIf DL e s t ans ant ans_lv ant_lv lv
  :  trs DL s ans_lv ans
     -> trs DL t ant_lv ant
     -> trs DL (stmtIf e s t) (ann2 lv ans_lv ant_lv) (ann2 nil ans ant)
| trsRet e DL lv
  :  trs DL (stmtReturn e) (ann0 lv) (ann0 nil)
| trsGoto DL G' f Y lv
  :  get DL (counted f) (Some G')
     -> trs DL (stmtApp f Y) (ann0 lv) (ann0 nil)
| trsLet (DL:list (option (set var))) (F:list (params*stmt)) t Za ans ant lv ans_lv ant_lv
  : length F = length ans_lv
    -> length F = length ans
    -> length F = length Za
    -> (forall n lvs Zs Za' ans',
          get ans_lv n lvs -> get F n Zs -> get Za n Za' -> get ans n ans'
          -> trs (restr (getAnn lvs \ of_list (fst Zs++Za')) ⊝ (Some ⊝ (getAnn ⊝ ans_lv) \\ zip (@List.app _) (fst ⊝ F) Za ++ DL)) (snd Zs) lvs ans')
    -> trs (Some ⊝ (getAnn ⊝ ans_lv) \\ zip (@List.app _) (fst ⊝ F) Za ++ DL)
          t ant_lv ant
    -> trs DL (stmtFun F t) (annF lv ans_lv ant_lv) (annF Za ans ant).

Lemma trs_annotation DL s lv Y
      : trs DL s lv Y -> annotation s lv /\ annotation s Y.
Proof.
  intros. general induction H; split; dcr; econstructor; intros; eauto 20.
  - edestruct get_length_eq; try eapply H1; eauto.
    edestruct get_length_eq; try eapply H0; eauto.
    exploit H3; eauto.
  - edestruct get_length_eq; try eapply H1; eauto.
    edestruct get_length_eq; try eapply H; eauto.
    exploit H3; eauto.
Qed.


Lemma trs_monotone_DL (DL DL' : list (option (set var))) s lv a
 : trs DL s lv a
   -> DL ≿ DL'
   -> trs DL' s lv a.
Proof.
  intros. general induction H; eauto 30 using trs, restrict_subset2.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor; eauto using restrict_subset2, PIR2_app.
Qed.

Opaque to_list.

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
  general induction LEN1; simpl; eauto using PIR2.
  - f_equal. eauto.
Qed.


Lemma trs_srd AL ZL s ans_lv ans
  (RD:trs AL s ans_lv ans)
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
| additionalParameters_liveLet ZL F t (Za:〔〔var〕〕) ans ant lv ans_lv ant_lv
                               (ZaLen:❬F❭ = ❬ans❭)
  : (forall Za' lv Zs n, get F n Zs -> get ans_lv n lv -> get Za n Za' ->
       of_list Za' ⊆ getAnn lv \ of_list (fst Zs) /\ NoDupA eq (fst Zs ++ Za'))
    -> (forall Zs lv a n, get F n Zs -> get ans_lv n lv -> get ans n a ->
                    additionalParameters_live (of_list ⊝ Za ++ ZL) (snd Zs) lv a)
    -> additionalParameters_live ((of_list ⊝ Za) ++ ZL) t ant_lv ant
    -> length Za = length F
    -> additionalParameters_live ZL (stmtFun F t) (annF lv ans_lv ant_lv) (annF Za ans ant).

Lemma live_sound_compile ZL ZAL Lv s ans_lv ans o (Len:❬ZL❭=❬ZAL❭)
  (LV:live_sound o ZL Lv s ans_lv)
  (APL: additionalParameters_live (of_list ⊝ ZAL) s ans_lv ans)
  : live_sound o (zip (@List.app _) ZL ZAL) Lv (compile ZAL s ans) ans_lv.
Proof.
  general induction LV; inv APL; inv_get; eauto using live_sound.
  - simpl. erewrite get_nth; eauto.
    econstructor; eauto using zip_get with len.
    + cases; eauto. rewrite <- H1. rewrite of_list_app. eauto with cset.
    + intros ? ? Get.
      eapply get_app_cases in Get. destruct Get; dcr; eauto.
      inv_get.
      econstructor. rewrite <- H10. eauto using get_in_of_list.
  - simpl. rewrite <- List.map_app in *.
    econstructor; eauto.
    + rewrite fst_compileF_eq; eauto.
      rewrite <- zip_app; eauto with len.
    + eauto with len.
    + unfold compileF; intros; inv_get; simpl.
      exploit H2; eauto. exploit H12; eauto. dcr.
      exploit H1; try eapply H9; eauto with len.
      erewrite @list_get_eq at 1; eauto.
      * len_simpl.
        rewrite <- Len.
        rewrite Nat.add_min_distr_r.
        rewrite <- ZaLen; eauto with len.
      * intros. inv_get. eapply get_app_cases in H19 as [?|?]; dcr; len_simpl.
        -- inv_get. rewrite get_app_lt in H15; [|eauto with len]. inv_get.
           reflexivity.
        -- inv_get. rewrite get_app_ge in H15; [|eauto with len]. inv_get.
           len_simpl.
           rewrite <- ZaLen in *. rewrite H14 in *. len_simpl. inv_get.
           rewrite get_app_ge in H18; rewrite H14 in *; eauto with len.
           inv_get. reflexivity.
    + intros.
      unfold compileF in H4. inv_get; simpl.
      exploit H2; eauto. exploit H10; eauto. dcr.
      repeat split; eauto.
      * rewrite of_list_app. clear - H9 H11; cset_tac.
      * cases; eauto. rewrite of_list_app. clear - H18; cset_tac.
Qed.



(** ** DVE and Unreachable Code *)
(** We show that DVE does not introduce unreachable code. *)


Lemma compile_callChain (trueIsCalled : stmt -> lab -> Prop)  ZL Za F ans n l'
  : ❬F❭ = ❬ans❭ -> ❬F❭ = ❬Za❭
    -> (forall (n : nat) (Zs : params * stmt) (a : ann 〔params〕),
         get F n Zs ->
         get ans n a ->
         forall n0 : nat,
           trueIsCalled (snd Zs) (LabI n0) ->
           trueIsCalled (compile (Za ++ ZL) (snd Zs) a) (LabI n0))
     -> callChain trueIsCalled F (LabI l') (LabI n)
     -> callChain trueIsCalled (compileF compile ZL F Za Za ans)
    (LabI l') (LabI n).
Proof.
  intros Len1 Len2 IH CC.
  general induction CC.
  + econstructor.
  + inv_get. econstructor 2.
    eapply zip_get; eauto using zip_get.
    simpl.
    eapply IH; eauto.
    eauto.
Qed.

Lemma compile_isCalled b AL ZL s ans_lv ans n
      (RD:trs AL s ans_lv ans)
      (TIC: isCalled b s (LabI n))
  : isCalled b (compile ZL s ans) (LabI n).
Proof.
  general induction RD;
    invt isCalled; simpl; repeat cases; eauto using isCalled;
    try congruence.
  - destruct l' as [l'].
    econstructor; eauto.
    unfold compileF at 2; len_simpl.
    eapply compile_callChain; intros; eauto.
    inv_get. eauto.
Qed.

Lemma compile_noUnreachableCode b AL ZL s ans_lv ans
      (RD:trs AL s ans_lv ans)
      (NUC: noUnreachableCode (isCalled b) s)
  : noUnreachableCode (isCalled b) (compile ZL s ans).
Proof.
  general induction NUC; invt trs; simpl;
    eauto using noUnreachableCode.
  - econstructor; try (unfold compileF at 1); intros; inv_get; simpl in *; try len_simpl; eauto with len.
    + edestruct H1 as [[l] [IC CC]]; eauto.
      eexists (LabI l); split; eauto.
      * eapply compile_isCalled; eauto.
      * eapply compile_callChain; intros; eauto using compile_isCalled.
        inv_get. eapply compile_isCalled; eauto.
Qed.

Lemma compileF_map_length ZL F Za' Za ans (Len1:❬F❭=❬Za❭) (Len2:❬F❭=❬ans❭)
  : length (A:=var) ⊝ fst ⊝ compileF compile ZL F Za Za' ans =
    (fun Z (n0 : nat) => n0 + ❬Z❭) ⊜ Za (length (A:=var) ⊝ fst ⊝ F).
Proof.
  unfold compileF. rewrite map_map.
  general induction Len1; destruct ans; isabsurd; simpl; eauto.
  f_equal. eauto with len.
  erewrite <- IHLen1; eauto.
Qed.

Lemma compile_paramsMatch ZAL DL s L lv ans (Len:❬DL❭=❬ZAL❭)
      (PM:paramsMatch s L)
      (TRS:trs DL s lv ans)
  : paramsMatch (compile ZAL s ans) ((fun Z n => n + ❬Z❭) ⊜ ZAL L).
Proof.
  general induction TRS; invt paramsMatch; simpl in *; eauto using paramsMatch with len.
  - inv_get.
    econstructor; eauto using zip_get.
    erewrite get_nth; eauto with len.
  - econstructor; eauto.
    + unfold compileF at 1; intros; inv_get; simpl.
      exploit H3; eauto. instantiate (1:=(Za ++ ZAL)). len_simpl. omega.
      eqassumption. rewrite zip_app; eauto with len.
      f_equal.
      eapply compileF_map_length; eauto with len.
    + exploit IHTRS; eauto.
      instantiate (1:=(Za ++ ZAL)). len_simpl. omega.
      eqassumption. rewrite zip_app; eauto with len.
      f_equal.
      eapply compileF_map_length; eauto with len.
Qed.

Lemma compile_app_expfree DL s lv
      (AEF:app_expfree s)
  : app_expfree (compile DL s lv).
Proof.
  general induction AEF; destruct lv; simpl; eauto using app_expfree.
  - econstructor; intros ? ? Get.
    eapply get_app_cases in Get.
    destruct Get; dcr; eauto; inv_get;
      eauto using isVar.
  - econstructor; eauto.
    unfold compileF; intros; inv_get; simpl; eauto.
Qed.