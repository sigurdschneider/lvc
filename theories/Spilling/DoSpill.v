Require Import List Map Env AllInRel Exp AppExpFree Filter LengthEq.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import SpillSound SpillUtil.
Require Import ToBeOutsourced Slot.
Require Export SlotLiftParams SlotLiftArgs.


Fixpoint write_moves
           (Z Z' : params)
           (s : stmt)
  : stmt
  := match Z, Z' with
    | x::Z, x'::Z' =>
      stmtLet x (Operation (Var x')) (write_moves Z Z' s)
    | _, _ => s
    end.


Definition mark_elements
           (*(X : Type)
           `{OrderedType X}*)
           (L : list var)
           (s : ⦃var⦄)
  : list bool
  := (fun x => if [x ∈ s] then true else false) ⊝ L.

Lemma countTrue_mark_elements Z D
      (NoDup:NoDupA eq Z)
  : countTrue (mark_elements Z D) = cardinal (of_list Z ∩ D).
Proof.
  general induction NoDup; simpl.
  - assert ({} ∩ D [=] {}) by (clear; cset_tac).
    rewrite H. eauto.
  - cases.
    + assert ({x; of_list l} ∩ D [=] {x; of_list l ∩ D}) as EQ by (cset_tac).
      rewrite EQ. rewrite IHNoDup; eauto.
      rewrite add_cardinal_2; eauto. clear IHNoDup.
      cset_tac.
    + assert ({x; of_list l} ∩ D [=] of_list l ∩ D) as EQ by (cset_tac).
      rewrite EQ. rewrite IHNoDup; eauto.
Qed.

(*
Lemma update_with_list_lookup_in_list_first_slot (slot:var->var)
      A (E:onv A) n (R M:set var)
      Z (Y:list A) z
: length Z = length Y
  -> get Z n z
  -> z ∈ R
  -> disj (of_list Z) (map slot (of_list Z))
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> exists y, get Y n y
         /\ E [slot_lift_params slot (R, M) Z <--
                               Some ⊝ extend_args Y (mark_elements Z (R ∩ M))] z = Some y.
Proof.
  intros Len Get In Disj First. length_equify.
  general induction Len; simpl in *; isabsurd.
  inv Get.
  - exists y; repeat split; eauto using get.
    cases; simpl.
    + lud; eauto using get.
    + cases; simpl.
      * lud; eauto using get.
  - edestruct (IHLen slot E n0) as [? [? ]]; eauto using get; dcr.
    + eapply disj_incl; eauto with cset.
    + intros. eapply (First (S n')); eauto using get. omega.
    + exists x0. eexists; repeat split; eauto using get.
      exploit (First 0); eauto using get; try omega.
      cases; simpl.
      * rewrite lookup_nequiv; eauto.
        rewrite lookup_nequiv; eauto.
        intro.
        eapply (Disj z). eapply get_in_of_list in H3.
        cset_tac. rewrite <- H2.
        eapply map_iff; eauto. eexists x; split; eauto with cset.
      * cases; simpl; lud.
        -- rewrite lookup_nequiv; eauto.
        -- exfalso.
           eapply (Disj (slot x)). eapply get_in_of_list in H3.
           rewrite <- H5. cset_tac.
           eapply map_iff; eauto. eexists x; split; eauto with cset.
        -- eauto.
Qed.
 *)

Definition do_spill_rec
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (ZL : list params)
           (RML : list (set var * set var))
           (do_spill' : forall (s' : stmt)
                          (sl' : spilling)
                          (ZL : list params)
                          (RML : list (set var * set var)),
                            stmt)
  : stmt
  :=
    match s,sl with
    | stmtLet x e s, ann1 _ sl1
      => stmtLet x e (do_spill' s sl1 ZL RML)

    | stmtIf e s1 s2, ann2 _ sl1 sl2
      => stmtIf e (do_spill' s1 sl1 ZL RML) (do_spill' s2 sl2 ZL RML)

    | stmtFun F t, annF (_,_, rms) sl_F sl_t
      => let RML' := rms ++ RML in
        let ZL' := fst ⊝ F ++ ZL in
      stmtFun
          (pair ⊜
                (slot_lift_params slot ⊜ rms (fst ⊝ F))
                ((fun (Zs : params * stmt) (sl_s : spilling)
                  => do_spill' (snd Zs) sl_s ZL' RML') ⊜ F sl_F)
  (* we can't write "(do_spill' ⊜ (snd ⊝ F) sl_F)" because termination wouldn't be obvious *)
          )
          (do_spill' t sl_t ZL' RML')

    | stmtApp f Y, ann0 (_,_, (RMapp)::nil)
      => stmtApp f (slot_lift_args slot (nth f RML (∅,∅)) RMapp Y (nth f ZL nil))

    | _,_
      => s
    end
.


Fixpoint do_spill
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (ZL : list params)
           (RML : list (set var * set var))
           {struct s}
  : stmt
  := let sp := elements (getSp sl) in
    let ld := elements (getL sl) in
    write_moves (slot ⊝ sp) sp (
        write_moves ld (slot ⊝ ld) (
            do_spill_rec slot s sl ZL RML (do_spill slot)
        )
     )
.



Lemma do_spill_rec_s
      (slot : var -> var)
      (Sp' L': ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
  :
    do_spill_rec slot s sl
    = do_spill_rec slot s (setTopAnn sl (Sp',L',snd (getAnn sl)))
.
Proof.
  destruct s, sl;
    simpl;
    unfold do_spill_rec;
    try reflexivity;
  destruct a;
    destruct p;
    eauto.
Qed.

Lemma do_spill_empty
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
      (ZL : list params)
      (RML : list (set var * set var))
  :
    count sl = 0
    -> do_spill slot s sl ZL RML
      = do_spill_rec slot s sl ZL RML (do_spill slot)
.
Proof.
  intros count_zero.
  apply count_zero_Empty_Sp in count_zero as Empty_Sp.
  apply count_zero_Empty_L  in count_zero as Empty_L.
  unfold do_spill.
  rewrite elements_Empty in Empty_Sp.
  rewrite elements_Empty in Empty_L.
  induction s;
    rewrite Empty_Sp;
    rewrite Empty_L;
    simpl; reflexivity.
Qed.


Lemma do_spill_empty_Sp
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
      (ZL : list params)
      (RML : list (set var * set var))
  :
    cardinal (getSp sl) = 0
    -> do_spill slot s sl ZL RML
      = write_moves (elements (getL sl)) (slot ⊝ elements (getL sl))
                    (do_spill_rec slot s sl ZL RML (do_spill slot))
.
Proof.
  intros card_zero.
  unfold do_spill.
  apply cardinal_Empty in card_zero.
  rewrite elements_Empty in card_zero.
  induction s;
    rewrite card_zero;
    fold do_spill;
    reflexivity.
Qed.


Lemma do_spill_extract_writes
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
      (ZL : list params)
      (RML : list (set var * set var))
  :
    do_spill slot s sl ZL RML
    = write_moves (slot ⊝ elements (getSp sl)) (elements (getSp sl))
         (write_moves (elements (getL sl)) (slot ⊝ elements (getL sl))
             (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))) ZL RML))
.
Proof.
  symmetry.
  rewrite do_spill_empty.
  - rewrite do_spill_rec_s with (Sp':=∅) (L':=∅).
    rewrite setTopAnn_setTopAnn.
    destruct s,sl;
      simpl; eauto; try reflexivity;
    do 2 f_equal;
    destruct a;
    simpl;
      destruct p;
      reflexivity.
  - unfold count.
    rewrite getAnn_setTopAnn.
    simpl.
    eauto.
Qed.



Lemma do_spill_extract_spill_writes
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
      (ZL : list params)
      (RML : list (set var * set var))
  :
    do_spill slot s sl ZL RML
    = write_moves (slot ⊝ (elements (getSp sl))) (elements (getSp sl))
                   (do_spill slot s (clear_Sp sl) ZL RML)
.
Proof.
  unfold clear_Sp.
  symmetry.
  rewrite do_spill_empty_Sp.
  - rewrite do_spill_rec_s with (Sp':=∅) (L':=getL sl).
    rewrite setTopAnn_setTopAnn.
    destruct s,sl;
      simpl; eauto;
    do 2 f_equal;
    destruct a;
    simpl;
      destruct p;
      reflexivity.
  - rewrite getAnn_setTopAnn.
    simpl.
    eauto.
Qed.


Lemma do_spill_sub_empty_invariant
      (slot : var -> var)
      (Sp' L': ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
      (ZL : list params)
      (RML : list (set var * set var))
  :
    count sl = 0
    -> Sp' [=] ∅
    -> L' [=] ∅
    ->  do_spill slot s sl ZL RML
       = do_spill slot s (setTopAnn sl (Sp',L',snd (getAnn sl))) ZL RML
.
Proof.
  intros count_zero Sp_empty L_empty.
  rewrite do_spill_empty; eauto.
  rewrite do_spill_empty;
    swap 1 2.
  {
    unfold count.
    rewrite getAnn_setTopAnn.
    simpl.
    rewrite Sp_empty.
    rewrite L_empty.
    eauto.
  }
  destruct s, sl;
    simpl; eauto;
  destruct a;
    destruct p;
    simpl; eauto.
Qed.

Lemma write_moves_app_expfree xl xl' s
  : app_expfree s
    -> app_expfree (write_moves xl xl' s).
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using app_expfree.
Qed.

Lemma extend_args_app_expfree (slot:var -> var) RM RMapp Y Z f
  (IV : forall (n : nat) (y : op), get Y n y -> isVar y)
  : app_expfree (stmtApp f (slot_lift_args slot RM RMapp Y Z)).
Proof.
  econstructor.
  intros; inv_get; eauto using slot_lift_args_isVar.

Qed.

Lemma do_spill_app_expfree (slot:var -> var) s spl ZL RML
  : app_expfree s
    -> app_expfree (do_spill slot s spl ZL RML).
Proof.
  intros AEF.
  general induction AEF;
    destruct spl; try destruct a; try destruct l; simpl;
      repeat let_pair_case_eq; subst; simpl;
        eauto using app_expfree, write_moves_app_expfree.
  - destruct l;
     do 2 apply write_moves_app_expfree;
        repeat cases; clear_trivial_eqs;
          eauto using app_expfree, extend_args_app_expfree.
  - do 2 apply write_moves_app_expfree;
      repeat cases; clear_trivial_eqs;
        eauto using app_expfree, extend_args_app_expfree.
    econstructor; intros; inv_get; simpl; eauto.
  - do 2 apply write_moves_app_expfree;
        repeat cases; clear_trivial_eqs;
          eauto using app_expfree, extend_args_app_expfree.
    + econstructor; intros; inv_get; simpl; eauto.
    + econstructor; intros; inv_get; simpl; eauto.
Qed.

Lemma write_moves_labels_defined xl xl' s n
  : labelsDefined s n
    -> labelsDefined (write_moves xl xl' s) n.
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using labelsDefined.
Qed.

Lemma write_moves_paramsMatch xl xl' s L
  : paramsMatch s L
    -> paramsMatch (write_moves xl xl' s) L.
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using paramsMatch.
Qed.

Lemma do_spill_labels_defined (slot:var -> var) k RM ZL Λ spl s n
  : labelsDefined s n
    -> spill_sound k ZL Λ RM s spl
    -> labelsDefined (do_spill slot s spl ZL Λ) n.
Proof.
  intros.
  general induction H; invt spill_sound; simpl;
    repeat cases; simpl; clear_trivial_eqs;
      eauto 20 using labelsDefined, write_moves_labels_defined.
  - do 2 eapply write_moves_labels_defined.
    econstructor; intros; inv_get; simpl; len_simpl; eauto using labelsDefined.
    + exploit H16; eauto.
      rewrite <- H9. eauto with len.
    + rewrite <- H9; eauto with len.
Qed.

Lemma zip_map_fst_f X Y (L:list X) (L':list Y) Z (f:X -> Z)
  : length L = length L'
    -> zip (fun x _ => f x) L L' = f ⊝ L.
Proof.
  intros. length_equify.
  general induction H; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma ZL_NoDupA_ext ZL F ans D Dt
      (Len: ❬F❭ = ❬ans❭)
      (IFC:Indexwise.indexwise_R (RenamedApart.funConstr D Dt) F ans)
      (H:forall (n : nat) (Z : params), get ZL n Z -> NoDupA eq Z)
  : forall (n0 : nat) (Z : params), get (fst ⊝ F ++ ZL) n0 Z -> NoDupA eq Z.
Proof.
  intros. eapply get_app_cases in H0; destruct H0; dcr; inv_get; eauto.
  edestruct IFC; eauto.
Qed.

Lemma do_spill_paramsMatch (slot:var -> var) k RM ZL Λ spl s ra
  : paramsMatch s (@length _ ⊝ ZL)
    -> spill_sound k ZL Λ RM s spl
    -> RenamedApart.renamedApart  s ra
    -> (forall n Z, get ZL n Z -> NoDupA eq Z)
    -> app_expfree s
    -> paramsMatch (do_spill slot s spl ZL Λ)
                                   (@length _ ⊝ (slot_lift_params slot) ⊜ Λ ZL).
Proof.
  intros PM SPS RA NDUP AEF.
  general induction PM; invt spill_sound; invt RenamedApart.renamedApart; invtc app_expfree;
    simpl; repeat cases; simpl; clear_trivial_eqs;
      eauto 20 using paramsMatch, write_moves_paramsMatch.
  - do 2 eapply write_moves_paramsMatch. inv_get.
    erewrite !get_nth; eauto using zip_get.
    econstructor; try reflexivity.
    eapply map_get_eq; eauto using zip_get.
    eapply op_eval_var in H1 as [? ?]; subst Y.
    rewrite slot_lift_params_length; eauto.
    rewrite slot_lift_args_length; eauto.
  - do 2 eapply write_moves_paramsMatch.
    econstructor; intros; inv_get; simpl; try len_simpl; eauto using paramsMatch.
    + exploit H0; eauto.
      * rewrite List.map_app; eauto.
      * eapply ZL_NoDupA_ext; eauto.
      * eqassumption.
        -- rewrite !map_zip; eauto with len. simpl.
           rewrite !zip_app; eauto with len. f_equal.
           rewrite zip_map_fst_f; eauto with len.
           rewrite map_zip; eauto.
    + exploit IHPM; eauto.
      * rewrite List.map_app; eauto.
      * eapply ZL_NoDupA_ext; eauto.
      * eqassumption.
        -- rewrite !map_zip; eauto with len. simpl.
           rewrite !zip_app; eauto with len. f_equal.
           rewrite zip_map_fst_f; eauto with len.
           rewrite map_zip; eauto.
Qed.

Lemma write_moves_no_unreachable_code b xl xl' s
  : noUnreachableCode (isCalled b) s
    -> noUnreachableCode (isCalled b) (write_moves xl xl' s).
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using noUnreachableCode.
Qed.

Lemma write_moves_isCalled b xl xl' s f
  : isCalled b s f
    -> isCalled b (write_moves xl xl' s) f.
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using isCalled.
Qed.

Lemma do_spill_callChain b (slot: var -> var) k ZL Λ F sl_F rms f l'
  (IH : forall n Zs, get F n Zs ->
       forall (ZL : 〔params〕) (Λ : 〔⦃var⦄ * ⦃var⦄〕) (RM : ⦃var⦄ * ⦃var⦄)
         (sl_t : spilling) (f : lab),
       spill_sound k ZL Λ RM (snd Zs) sl_t ->
       isCalled b (snd Zs) f
       -> isCalled b (do_spill slot (snd Zs) sl_t ZL Λ) f)
  (Len1: ❬F❭ = ❬sl_F❭)
  (Len2: ❬F❭ = ❬rms❭)
  (SPS: forall (n : nat) (Zs : params * stmt) (rm : ⦃var⦄ * ⦃var⦄) (sl_s : spilling),
       get rms n rm ->
       get F n Zs ->
       get sl_F n sl_s -> spill_sound k (fst ⊝ F ++ ZL) (rms ++ Λ) rm (snd Zs) sl_s)
  (CC: callChain (isCalled b) F l' f)
  : callChain (isCalled b)
    (pair ⊜ (slot_lift_params slot ⊜ rms (fst ⊝ F))
     ((fun (Zs : params * stmt) (sl_s : spilling) =>
       do_spill slot (snd Zs) sl_s (fst ⊝ F ++ ZL) (rms ++ Λ)) ⊜ F
      sl_F)) l' f.
Proof.
  general induction CC.
  + econstructor.
  + inv_get.
    econstructor; eauto using zip_get_eq.
    * eapply IH; eauto.
Qed.


Lemma do_spill_isCalled b (slot: var -> var) k ZL Λ RM t sl_t f
  (SPS : spill_sound k ZL Λ RM t sl_t)
  (IC : isCalled b t f)
  : isCalled b (do_spill slot t sl_t ZL Λ) f.
Proof.
  move t before k.
  revert_until t.
  sind t; intros; invt spill_sound; invt isCalled; simpl;
    eauto using write_moves_isCalled, isCalled.
  - do 2 eapply write_moves_isCalled.
    econstructor; eauto.
    len_simpl. rewrite <- H3; eauto using do_spill_callChain.
Qed.

Lemma do_spill_no_unreachable_code b (slot:var -> var) k RM ZL Λ spl s
  : noUnreachableCode (isCalled b) s
    -> spill_sound k ZL Λ RM s spl
    -> noUnreachableCode (isCalled b) (do_spill slot s spl ZL Λ).
Proof.
  intros.
  general induction H; invt spill_sound; simpl;
    clear_trivial_eqs.
  - eauto 20 using noUnreachableCode, write_moves_no_unreachable_code.
  - eauto 20 using noUnreachableCode, write_moves_no_unreachable_code.
  - eauto 20 using noUnreachableCode, write_moves_no_unreachable_code.
  - eauto 20 using noUnreachableCode, write_moves_no_unreachable_code.
  - do 2 eapply write_moves_no_unreachable_code.
    econstructor; intros; inv_get; simpl; eauto using noUnreachableCode.
    + len_simpl. rewrite <- H10 in H4. exploit H2; eauto.
      destruct H5; dcr.
      eexists x; split; eauto using do_spill_isCalled, do_spill_callChain.
Qed.