Require Import List Map Env AllInRel Exp AppExpFree Filter LengthEq.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SpillSound SpillUtil.
Require Import ToBeOutsourced.

(* this file is too long, should be splitted in DoSpill, DoSpillParams, DoSpillArgs *)

Fixpoint slot_lift_params
           (slot : var -> var)
           (RM : ⦃var⦄ * ⦃var⦄)
           (Z : params)
  : params
  :=
    match Z with
    | nil => nil
    | z::Z => if [z ∈ fst RM ∩ snd RM]
             then z::(slot z)::(slot_lift_params slot RM Z)
             else if [z ∈ fst RM]
                  then z::(slot_lift_params slot RM Z)
                  else (slot z)::(slot_lift_params slot RM Z)
    end.

Lemma slot_lift_params_app
      L1 L2 L1' L2' slot
  :
    length L1 = length L1'
    -> slot_lift_params slot ⊜ L1 L1'
                       ++ slot_lift_params slot ⊜ L2 L2'
      = slot_lift_params slot ⊜ (L1 ++ L2) (L1' ++ L2')
.
Proof.
  intros. rewrite zip_app; eauto with len.
Qed.

Lemma slot_lift_params_length (slot:var -> var) R_f M_f Z
      (NoDup:NoDupA eq Z)
  : ❬slot_lift_params slot (R_f, M_f) Z❭ = ❬Z❭ + cardinal (of_list Z ∩ (R_f ∩ M_f)).
Proof.
  general induction NoDup; simpl.
  - assert ({} ∩ (R_f ∩ M_f) [=] {}) by (clear; cset_tac).
    rewrite H. eauto.
  - cases; simpl.
    + assert (forall D, x ∈ D -> {x; of_list l} ∩ D [=] {x; of_list l ∩ D}) as EQ by (cset_tac).
      rewrite EQ; eauto. rewrite IHNoDup; eauto.
      rewrite add_cardinal_2; eauto. cset_tac. rewrite <- InA_in in H3; eauto.
    + assert (forall D, x ∉ D -> {x; of_list l} ∩ D [=] of_list l ∩ D) as EQ by (cset_tac).
      cases; simpl; rewrite EQ; eauto.
Qed.


Definition slot_lift_args
           (slot : var -> var)
           (M : set var)
  : op -> op
  := (fun y => match y with
            | Var v => if [v ∈ M] then Var (slot v) else Var v
            | _ => y
            end) .

Lemma slot_lift_args_isVar (slot:var -> var) (M:set var) op
  : isVar op
    -> isVar (slot_lift_args slot M op).
Proof.
  intros []; simpl; cases; eauto using isVar.
Qed.

Lemma slot_lift_args_elem_eq_ext
      (slot : var -> var)
      (Sl : ⦃var⦄)
      (Y Y' : args)
  :
    elem_eq Y Y'
    -> elem_eq (slot_lift_args slot Sl ⊝ Y)
               (slot_lift_args slot Sl ⊝ Y')
.
Proof.
  apply elem_eq_sym_proof.
  intros.
  unfold elem_eq.
  general induction xl;
    simpl in *; eauto.
  - cset_tac.
  - rewrite IHxl with (xl':=xl');
      simpl; eauto.
    + assert (a ∈ of_list xl') as a_in.
      {
        rewrite <- H.
        clear; cset_tac.
      }
      enough (slot_lift_args slot Sl a ∈ of_list (slot_lift_args slot Sl ⊝ xl')) as sla_in.
      {
        apply incl_singleton in sla_in.
        rewrite add_union_singleton.
        rewrite sla_in.
        clear; cset_tac.
      }
      apply of_list_1.
      apply of_list_1 in a_in.
      clear H.
      general induction a_in;
        simpl; eauto.
      rewrite H.
      econstructor; eauto.
    + rewrite <- H.
      eauto with cset.
Qed.

Fixpoint extend_args {X}
         (Y : list X)
         (ib : list bool)
  : list X
  := match Y with
     | nil => nil
     | y :: Y => match ib with
                 | nil => y :: Y
                 | true  :: ib => y :: y :: extend_args Y ib
                 | false :: ib => y :: extend_args Y ib
                end
     end.

Lemma extend_args_get X (Y : list X) (ib : list bool) n x
  : get (extend_args Y ib) n x
    -> exists n, get Y n x.
Proof.
  intros.
  general induction H; destruct Y, ib; simpl in *;
    clear_trivial_eqs; isabsurd;
      eauto using get.
  - cases in Heql; clear_trivial_eqs; eauto using get.
  - cases in Heql; clear_trivial_eqs; eauto using get.
    + edestruct (IHget (x0::Y) (false::ib)); eauto.
    + edestruct IHget; eauto using get.
Qed.


Lemma extend_args_length X (L:list X) ib (Len:❬L❭=❬ib❭)
  : ❬extend_args L ib❭ = ❬L❭ + countTrue ib.
Proof.
  length_equify.
  general induction Len; simpl; eauto.
  cases; simpl.
  - rewrite IHLen. omega.
  - rewrite IHLen; eauto.
Qed.

Lemma extend_args_elem_eq_ext
      (Y : args)
      (ib : list bool)
  : elem_eq Y (extend_args Y ib).
Proof.
  general induction Y;
    destruct ib;
    unfold elem_eq;
    simpl; eauto.
  unfold elem_eq in IHY.
  destruct b; simpl; eauto with cset.
  rewrite <- IHY.
  rewrite !add_union_singleton.
  cset_tac.
Qed.

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

Definition compute_ib
           (Z : params)
           (RM : ⦃var⦄ * ⦃var⦄)
  : list bool
  :=
    mark_elements Z (fst RM ∩ snd RM).


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
      rewrite add_cardinal_2; eauto. cset_tac. rewrite <- InA_in in H1; eauto.
    + assert ({x; of_list l} ∩ D [=] of_list l ∩ D) as EQ by (cset_tac).
      rewrite EQ. rewrite IHNoDup; eauto.
Qed.


Lemma update_with_list_lookup_in_list_first_slot (slot:var->var)
      A (E:onv A) n (R M:set var)
      Z (Y:list A) z
: length Z = length Y
  -> get Z n z
  -> z ∈ R
  -> disj (of_list Z) (map slot (of_list Z))
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> exists y, get Y n y /\ E [slot_lift_params slot (R, M) Z <--
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

Definition do_spill_rec
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (IB : list (list bool))
           (do_spill' : forall (s' : stmt)
                          (sl' : spilling)
                          (IB' : list (list bool)),
                            stmt)
  : stmt
  :=
    match s,sl with
    | stmtLet x e s, ann1 _ sl1
      => stmtLet x e (do_spill' s sl1 IB)

    | stmtIf e s1 s2, ann2 _ sl1 sl2
      => stmtIf e (do_spill' s1 sl1 IB) (do_spill' s2 sl2 IB)

    | stmtFun F t, annF (_,_, rms) sl_F sl_t
      => let IB' := compute_ib ⊜ (fst ⊝ F) rms ++ IB in
      stmtFun
          (pair ⊜
                (slot_lift_params slot ⊜ rms (fst ⊝ F))
                ((fun (Zs : params * stmt) (sl_s : spilling)
                  => do_spill' (snd Zs) sl_s IB') ⊜ F sl_F)
  (* we can't write "(do_spill' ⊜ (snd ⊝ F) sl_F)" because termination wouldn't be obvious *)
          )
          (do_spill' t sl_t IB')

    | stmtApp f Y, ann0 (_,_, (R,M)::nil)
      => stmtApp f (slot_lift_args slot M
                                  ⊝ (extend_args Y (nth f IB nil)))

    | _,_
      => s
    end
.


Fixpoint do_spill
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (IB : list (list bool))
           {struct s}
  : stmt
  := let sp := elements (getSp sl) in
    let ld := elements (getL sl) in
    write_moves (slot ⊝ sp) sp (
        write_moves ld (slot ⊝ ld) (
            do_spill_rec slot s sl IB (do_spill slot)
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
      (IB : list (list bool))
  :
    count sl = 0
    -> do_spill slot s sl IB
      = do_spill_rec slot s sl IB (do_spill slot)
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
      (IB : list (list bool))
  :
    cardinal (getSp sl) = 0
    -> do_spill slot s sl IB
      = write_moves (elements (getL sl)) (slot ⊝ elements (getL sl))
                    (do_spill_rec slot s sl IB (do_spill slot))
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
      (IB : list (list bool))
  :
    do_spill slot s sl IB
    = write_moves (slot ⊝ elements (getSp sl)) (elements (getSp sl))
         (write_moves (elements (getL sl)) (slot ⊝ elements (getL sl))
             (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))) IB))
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
      (IB : list (list bool))
  :
    do_spill slot s sl IB
    = write_moves (slot ⊝ (elements (getSp sl))) (elements (getSp sl))
                   (do_spill slot s (clear_Sp sl) IB)
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
      (IB : list (list bool))
  :
    count sl = 0
    -> Sp' [=] ∅
    -> L' [=] ∅
    ->  do_spill slot s sl IB
       = do_spill slot s (setTopAnn sl (Sp',L',snd (getAnn sl))) IB
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

Lemma extend_args_app_expfree (slot:var -> var) Y s l f
  (IV : forall (n : nat) (y : op), get Y n y -> isVar y)
  : app_expfree (stmtApp f (slot_lift_args slot s ⊝ extend_args Y l)).
Proof.
  econstructor.
  intros; inv_get.
  edestruct extend_args_get; eauto using slot_lift_args_isVar.
Qed.

Lemma do_spill_app_expfree (slot:var -> var) s spl ib
  : app_expfree s
    -> app_expfree (do_spill slot s spl ib).
Proof.
  intros AEF.
  general induction AEF;
    destruct spl, ib; simpl;
      repeat let_pair_case_eq; subst; simpl;
          eauto using app_expfree, write_moves_app_expfree.
  - do 2 apply write_moves_app_expfree;
      repeat cases; clear_trivial_eqs;
        eauto using app_expfree, extend_args_app_expfree.
  - do 2 apply write_moves_app_expfree;
      repeat cases; clear_trivial_eqs;
        eauto using app_expfree, extend_args_app_expfree.
  - do 2 apply write_moves_app_expfree;
      repeat cases; clear_trivial_eqs;
        eauto using app_expfree, extend_args_app_expfree.
    econstructor; intros; inv_get; simpl; eauto.
  - do 2 apply write_moves_app_expfree;
      repeat cases; clear_trivial_eqs;
        eauto using app_expfree, extend_args_app_expfree.
    econstructor; intros; inv_get; simpl; eauto.
Qed.

Lemma write_moves_labels_defined xl xl' s n
  : labelsDefined s n
    -> labelsDefined (write_moves xl xl' s) n.
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using labelsDefined.
Qed.

Lemma do_spill_labels_defined (slot:var -> var) k RM ZL Λ spl s n
  : labelsDefined s n
    -> spill_sound k ZL Λ RM s spl
    -> labelsDefined (do_spill slot s spl (compute_ib ⊜ ZL Λ)) n.
Proof.
  intros.
  general induction H; invt spill_sound; simpl;
    repeat cases; simpl; clear_trivial_eqs;
      eauto 20 using labelsDefined, write_moves_labels_defined.
  - do 2 eapply write_moves_labels_defined.
    econstructor; intros; inv_get; simpl; len_simpl; eauto using labelsDefined.
    + exploit H16; eauto.
      rewrite <- H9. rewrite <- zip_app; eauto with len.
    + rewrite <- H9, <- zip_app; eauto with len.
Qed.

Lemma write_moves_no_unreachable_code xl xl' s
  : noUnreachableCode isCalled s
    -> noUnreachableCode isCalled (write_moves xl xl' s).
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using noUnreachableCode.
Qed.

Lemma write_moves_isCalled xl xl' s f
  : isCalled s f
    -> isCalled (write_moves xl xl' s) f.
Proof.
  intros AEF.
  general induction xl; destruct xl'; simpl; eauto using isCalled.
Qed.



Lemma do_spill_callChain (slot: var -> var) k ZL Λ F sl_F rms f l'
  (IH : forall n Zs, get F n Zs ->
       forall (ZL : 〔params〕) (Λ : 〔⦃var⦄ * ⦃var⦄〕) (RM : ⦃var⦄ * ⦃var⦄)
         (sl_t : spilling) (f : lab),
       spill_sound k ZL Λ RM (snd Zs) sl_t ->
       isCalled (snd Zs) f
       -> isCalled (do_spill slot (snd Zs) sl_t (compute_ib ⊜ ZL Λ)) f)
  (Len1: ❬F❭ = ❬sl_F❭)
  (Len2: ❬F❭ = ❬rms❭)
  (SPS: forall (n : nat) (Zs : params * stmt) (rm : ⦃var⦄ * ⦃var⦄) (sl_s : spilling),
       get rms n rm ->
       get F n Zs ->
       get sl_F n sl_s -> spill_sound k (fst ⊝ F ++ ZL) (rms ++ Λ) rm (snd Zs) sl_s)
  (CC: callChain isCalled F l' f)
  : callChain isCalled
    (pair ⊜ (slot_lift_params slot ⊜ rms (fst ⊝ F))
     ((fun (Zs : params * stmt) (sl_s : spilling) =>
       do_spill slot (snd Zs) sl_s (compute_ib ⊜ (fst ⊝ F ++ ZL) (rms ++ Λ))) ⊜ F
      sl_F)) l' f.
Proof.
  general induction CC.
  + econstructor.
  + inv_get.
    econstructor; eauto using zip_get_eq.
    * eapply IH; eauto.
Qed.


Lemma do_spill_isCalled (slot: var -> var) k ZL Λ RM t sl_t f
  (SPS : spill_sound k ZL Λ RM t sl_t)
  (IC : isCalled t f)
  : isCalled (do_spill slot t sl_t (compute_ib ⊜ ZL Λ)) f.
Proof.
  move t before k.
  revert_until t.
  sind t; intros; invt spill_sound; invt isCalled; simpl;
    eauto using write_moves_isCalled, isCalled.
  - do 2 eapply write_moves_isCalled.
    rewrite <- zip_app; eauto with len.
    econstructor; eauto.
    len_simpl. rewrite <- H3; eauto using do_spill_callChain.
Qed.

Lemma do_spill_no_unreachable_code (slot:var -> var) k RM ZL Λ spl s
  : noUnreachableCode isCalled s
    -> spill_sound k ZL Λ RM s spl
    -> noUnreachableCode isCalled (do_spill slot s spl (compute_ib ⊜ ZL Λ)).
Proof.
  intros.
  general induction H; invt spill_sound; simpl;
    repeat cases; simpl; clear_trivial_eqs;
      eauto 20 using noUnreachableCode, write_moves_no_unreachable_code.
  - do 2 eapply write_moves_no_unreachable_code.
    rewrite <- zip_app; eauto with len.
    econstructor; intros; inv_get; simpl; eauto using noUnreachableCode.
    + len_simpl. rewrite <- H10 in H4. exploit H2; eauto.
      destruct H5; dcr.
      eexists x; split; eauto using do_spill_isCalled, do_spill_callChain.
Qed.