Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill DoSpillRm DiscardMergeSl SpillUtil.

Set Implicit Arguments.


Fixpoint list_union'
         (X : Type) `{OrderedType X}
         (L : list (set X))
  : set X
  :=
    match L with
    | nil => ∅
    | s::xl => s ∪ list_union' xl
    end
.


Fixpoint spill_live
(Lv : list (set var))
(ZL : list (params))
(G : set var)
(s : stmt)
(rm : ann (option (list (set var))))
{struct s}
: ann (set var)
:=
match s, rm with
| stmtLet x e t, ann1 _ rm  (* checked *)
     => let lv_t := spill_live Lv ZL (singleton x) t rm in
        ann1 ((getAnn lv_t) \ singleton x ∪ Exp.freeVars e ∪ G) lv_t

| stmtReturn e, ann0 _ (* checked *)
     => ann0 (Op.freeVars e ∪ G)

| stmtIf e t v, ann2 _ rm_t rm_v (* checked *)
     => let lv_t := spill_live Lv ZL ∅ t rm_t in
        let lv_v := spill_live Lv ZL ∅ v rm_v in
        ann2 (getAnn lv_t ∪ getAnn lv_v ∪ Op.freeVars e ∪ G) lv_t lv_v

| stmtApp f Y, ann0 _ (* checked *)
     => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (list_union (Op.freeVars ⊝ Y) ∪ blv \ of_list Z ∪ G)

| stmtFun F t, annF (Some Lv') rm_F rm_t (* checked *)
     => let lv_t := spill_live (Lv' ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s
                 => spill_live (Lv' ++ Lv) (fst ⊝ F ++ ZL) ∅
                               (snd ps) rm_s) ⊜ F rm_F in
        (* maybe i will need a guarantee of ❬F❭ = ❬als❭ somewhere *)
        annF (getAnn lv_t ∪ G) lv_F lv_t

| _,_ => ann0 G

end.


Lemma spill_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (x : var)
      (s : stmt)
      (a : ann (option (list (set var))))
  :
    x ∈ getAnn (spill_live Lv ZL (singleton x) s a).
Proof.
  induction s,a ; simpl; eauto with cset.
  - destruct a; simpl; eauto.
    cset_tac.
Qed.







Lemma spill_live_sound_s
      (slot : var -> var)
      (n : nat)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (Lv : list (set var))
      (s : stmt)
      (sl sl': ann (set var * set var * option (list (set var * set var))))
  :
    sub_spill sl' sl
    -> n = count sl'
    -> let sl0 := setTopAnn sl (∅,∅,snd (getAnn sl)) in
   (forall G', live_sound Imperative ZL Lv
              (do_spill slot s sl0)
              (spill_live (slot_merge slot Λ) ZL G'
                          (do_spill slot s sl0)
                          (discard_merge_sl slot (do_spill_rm' slot 0 sl))))
-> live_sound Imperative ZL Lv
              (do_spill slot s sl')
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl')
                          (discard_merge_sl slot (do_spill_rm' slot n sl))).
Proof.

set (Sp' := fst (fst (getAnn sl'))).
set (L'  := snd (fst (getAnn sl'))).
set (rm' := snd (getAnn sl')).
intros sub_sl n_count sl0 strong_sls.

remember (cardinal Sp') as n_Sp'.
symmetry in Heqn_Sp'.
rename Heqn_Sp' into card_Sp'.
revert dependent sl'.
revert G.
revert n.
induction n_Sp';
  intros n G sl' Sp' L' rm' sub_sl n_count card_Sp'.

- remember (cardinal L') as n_L'.
  symmetry in Heqn_L'.
  rename Heqn_L' into card_L'.
  revert dependent sl'.
  revert G.
  revert n.
  induction n_L';
    intros n G sl' Sp' L' rm' sub_sl n_count card_Sp' card_L'.

  {
    assert (count sl' = 0) as count_sl'.
    { unfold count. subst Sp'. subst L'.
      rewrite card_Sp'. rewrite card_L'. omega. }
    rewrite do_spill_empty_invariant
    with (Sp':=∅) (L':=∅) (rm:=rm') (sl':=sl0);
      simpl; eauto; try apply empty_1;
      try apply cardinal_Empty; eauto.

    + rewrite n_count.
      rewrite count_sl'.
      rewrite do_spill_rm_zero.
      destruct sl; destruct a; destruct p; apply strong_sls.
    + subst sl0.
      unfold sub_spill in sub_sl.
      destruct  sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite <- eq_rm.
      rewrite top_sl'.
      rewrite setTopAnn_setTopAnn.
      rewrite getAnn_setTopAnn.
      subst rm'.
      reflexivity.
  }


  rewrite do_spill_L.
  Focus 2. rewrite cardinal_Empty. subst Sp'. assumption.
  Focus 2. clear - card_L'. intro N.
           apply cardinal_Empty in N. subst L'. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  subst L'.
  rewrite card_L'.
  rewrite card_Sp'.
  simpl.

  rewrite do_spill_rm_s.

  rewrite discard_merge_sl_step.

  constructor; fold spill_live.

  * apply IHn_L'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.

    -- rewrite count_reduce_L with (n:=n_L') (m:=n_L'); eauto.
       unfold count. rewrite card_Sp'. rewrite card_L'. eauto.
    -- rewrite getAnn_setTopAnn.
       simpl.
       assumption.
    -- rewrite getAnn_setTopAnn.
       simpl. erewrite cardinal_set_tl. eauto.
       rewrite of_list_elements. rewrite card_L'. eauto.
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl'))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

- rewrite do_spill_Sp.
  Focus 2. subst Sp'. clear - card_Sp'. intro N.
           apply cardinal_Empty in N. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  rewrite card_Sp'.
  simpl.


  rewrite do_spill_rm_s with (n:=n_Sp' + cardinal L').

  econstructor; fold spill_live.
  * apply IHn_Sp'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.
    -- rewrite count_reduce_Sp with (n:=n_Sp' + cardinal L') (m:=n_Sp'); eauto.
       unfold count. rewrite card_Sp'. subst L'. omega.
    -- rewrite getAnn_setTopAnn.
       simpl.
       erewrite cardinal_set_tl; eauto.
       rewrite of_list_elements.
       rewrite card_Sp'.
       omega.
     * apply live_exp_sound_incl
        with (lv':= singleton (hd 0 (elements (fst (fst (getAnn sl')))))).
      -- econstructor. econstructor. eauto with cset.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.
Qed.


Lemma sub_spill_refl sl
  :
    sub_spill sl sl
.
Proof.
  unfold sub_spill.
  repeat split.
    simpl; eauto.
  - unfold setTopAnn.
    destruct sl; destruct a; destruct p;
      simpl; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Lemma get_get_eq
      (X : Type)
      (L : list X)
      (n : nat)
      (x x' : X)
  :
    get L n x -> get L n x' -> x = x'
.
Proof.
  intros get_x get_x'.
  induction get_x; inversion get_x'.
  - reflexivity.
  - apply IHget_x. assumption.
Qed.

Lemma spill_live_sound
(k : nat)
(slot : var -> var)
(n : nat)
(ZL : list params)
(G : set var)
(Λ : list (set var * set var))
(R M : set var)
(Lv : list (set var))
(s : stmt)
(sl : ann (set var * set var * option (list (set var * set var))))
(alv : ann (set var))
:  app_expfree s
-> spill_sound k ZL Λ (R,M) s sl
-> live_sound Imperative ZL (slot_merge slot Λ) s alv
-> live_sound Imperative ZL (slot_merge slot Λ)
              (do_spill slot s sl)
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl)
                          (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound lvSound.

general induction lvSound;
  inversion_clear aeFree;
  inversion_clear spillSound;
  apply spill_live_sound_s;
  try apply sub_spill_refl; eauto.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step. simpl.

  econstructor.
  + eapply IHlvSound; eauto.
  + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
    * apply Exp.live_freeVars.
    * clear. cset_tac.
  +  clear. cset_tac.
  + apply spill_live_G.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + eapply IHlvSound1; eauto.
  + eapply IHlvSound2; eauto.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
  + clear. cset_tac.
  + clear. cset_tac.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  intro G'.
  rewrite get_nth with (m:=Z0).
  assert (Z = Z0) as eq_Z.
  { apply get_get_eq with (L:=ZL) (n:=counted l); eauto. }
  assert (blv = R_f ∪ map slot M_f) as eq_blv.
  {
    clear - H0 H7.
    unfold slot_merge in H0.
    change (R_f ∪ map slot M_f)
           with ((fun rm => fst rm ∪ map slot (snd rm)) (R_f,M_f)).
    eapply map_get; eauto.
  }
  econstructor; simpl in *; eauto; rewrite <- eq_Z; eauto.
  + rewrite get_nth with (m:=blv).
    * cset_tac.
    * assumption.
  + subst Z0.
    rewrite get_nth with (m:=blv); eauto.
    intros n y get_y.
    apply live_op_sound_incl with (lv':=Op.freeVars y).
    * apply Op.live_freeVars.
    * repeat apply incl_union_left.
      eapply get_list_union_map; eauto.
  + eauto.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  assert (forall F sl_F, length F = length sl_F -> fst
      ⊝ (fun (Zs : params * stmt) (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) =>
           (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F
      = fst ⊝ F) as fst_F.
  {
    clear.
    intros F sl_F eq_len.
    assert (length F = length (
                           (fun (Zs : params * stmt)
                              (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕))
                            => (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
           ) as F_len.
    { symmetry. apply zip_length2. assumption. }
    revert dependent sl_F.
    induction F; intros sl_F eq_F eq_zip.
    - eauto.
    - simpl. destruct sl_F.
      + isabsurd.
      + simpl. f_equal.
        apply IHF; simpl in *; omega.
  }
  assert (slot_merge slot rms = getAnn ⊝ als) as maybe.
  { admit. }

  econstructor; fold spill_live; simpl in *; eauto.
  + rewrite fst_F. rewrite maybe.
    unfold spill_live at 1.
    admit. admit.
  + rewrite fst_F. admit. admit.
  + admit.
  + admit.


Admitted.