Require Import List.
Require Import Util Var Val Exp Env Map CSet AutoIndTac IL.
Require Import Sim SimTactics Infra.Status Position ILN InRel Sawtooth.

Set Implicit Arguments.
Unset Printing Records.

Instance block_type_I : BlockType (I.block) :=
  {
    block_n := I.block_f;
    block_Z := I.block_Z
  }.


Fixpoint labIndices (symb: list var) (s:nstmt) : status stmt :=
  match s with
    | nstmtLet x e s => sdo s' <- (labIndices symb s); Success (stmtLet x e s')
    | nstmtIf x s1 s2 =>
      sdo s1' <- (labIndices symb s1);
      sdo s2' <- (labIndices symb s2);
      Success (stmtIf x s1' s2')
    | nstmtApp l Y =>
      sdo f <- option2status (pos symb l 0) "labIndices: Undeclared function" ; Success (stmtApp (LabI f) Y)
    | nstmtReturn x => Success (stmtReturn x)
    | nstmtFun F s2 =>
      let fl := List.map (fst ∘ fst) F in
      sdo F' <- smap (fun (fZs:var*params*nstmt) => sdo s <- labIndices (fl ++ symb) (snd fZs);
                    Success (snd (fst fZs), s)) F;
      sdo s2' <- labIndices (fl++symb) s2;
      Success (stmtFun F' s2')
  end.

Lemma labIndices_freeVars ilin s L
: labIndices L ilin = Success s
  -> freeVars ilin = IL.freeVars s.
Proof.
  revert_except ilin.
  sind ilin; destruct ilin; simpl in *; intros; monadS_inv H; simpl.
  - erewrite IH; eauto with cset.
  - erewrite IH; eauto.
    erewrite IH; eauto.
  - reflexivity.
  - reflexivity.
  - erewrite IH; eauto.
    f_equal. f_equal.
    exploit smap_length; eauto.
    erewrite map_ext_get_eq; eauto with len.
    intros; inv_get.
    eapply smap_spec in EQ; eauto. destruct EQ; dcr.
    monadS_inv H3; get_functional; simpl in *.
    erewrite IH; eauto.
Qed.

Lemma pos_drop_eq symb (l:lab) x
: pos symb l 0 = Some x
  -> drop x symb = l::tl (drop x symb).
Proof.
  general induction symb.
  unfold pos in H; fold pos in H.
  cases in H; simpl; eauto.
  - inv COND; eauto.
  - destruct x.
    + exfalso. exploit (pos_ge _ _ _ H); eauto. omega.
    + simpl. erewrite IHsymb; eauto.
      eapply (pos_sub 1); eauto.
Qed.

Lemma pos_plus symb (f:lab) n i
: pos symb f 0 = Some (n + i)
  -> pos (drop n symb) f 0 = Some i.
Proof.
  general induction n; simpl; eauto.
  destruct symb; simpl.
  + inv H.
  + eapply IHn; eauto. simpl in H; cases in H.
    * inv H.
    * eapply (pos_sub 1); eauto.
Qed.

Require Import InRel Sawtooth.

Lemma mkBlocks_I_less
      : forall F' L F (n k : nat) (b : I.block),
          get (mapi_impl (I.mkBlock L F') k F) n b -> I.block_f b <= k + length F - 1.
Proof.
  intros. general induction F; simpl in *.
  - inv H; simpl in *; try omega.
  - inv H; simpl in *; try omega.
    eapply IHF in H4; eauto. omega.
Qed.

Inductive lab_approx : list var -> list IL.I.block -> list I.block -> Prop :=
  Lai symb L' LB
    (LEQ: forall f f' Lb F i,
            get LB i (I.blockI Lb F f')
            -> get symb i f
            -> (*lab_approx (drop (i-f') symb) (drop (i-f') L')  (drop (i-f') LB)
              /\ *) (forall f blk, Lb f = Some blk -> f ∉ of_list (List.map (fst ∘ fst) F)
                          -> exists j, pos (drop (i - f') symb) f 0 = Some j /\
                                 get (drop (i - f') LB) j blk)
              /\ (forall f i' k, pos (drop (i-f' + length F) symb) f k = Some i' -> exists blk, Lb f = Some blk)
              /\ (exists Z s, get F f' (f, Z, s))
              /\ (forall fn fb Z s, get F fn (fb,Z,s) ->
                              (forall b n, n < fn -> get F n b -> fst (fst b) <> fb) ->
                              exists s', get (drop (i-f') L') fn
                                        (IL.I.blockI Z s' fn)
                                    /\ labIndices (drop (i-f') symb) s
                                      = Success s'
                                    /\ pos (drop (i-f') symb) fb 0 = Some fn)
              /\ (exists symb', drop (i-f') symb
                          = (List.map (fst ∘ fst) F ++ symb')%list)
              /\ (exists LB', drop (i-f') LB
                          = (mapi (I.mkBlock Lb F) F ++ LB')%list)
              /\ i >= f'

    )
    (ST:sawtooth LB)
 : lab_approx symb L' LB.

Lemma lab_approx_drop symb L' LB
: forall f f' Lb F i,
    get LB i (I.blockI Lb F f')
    -> get symb i f
    -> i >= f'
    -> lab_approx symb L' LB
    -> lab_approx (drop (i -f') symb) (drop (i -f') L') (drop (i -f') LB).
Proof.
  intros.
  econstructor; intros. repeat rewrite drop_drop.
  eapply get_drop in H3.
  eapply get_drop in H4.
  inv H2; exploit LEQ; eauto; dcr; clear LEQ.
  exploit (sawtooth_resetting ST _ H H3); eauto. simpl in *.
  orewrite (i0 - f'0 + (i - f') = (i - f') + i0 - f'0).
  split; eauto. split; eauto.
  orewrite (i0 - f'0 + length F0 + (i - f') = i - f' + i0 - f'0 + length F0). eauto.
  split; eauto.
  split; eauto.
  inv H2; clear LEQ.
  eapply sawtooth_drop in H; eauto.
Qed.



Inductive labIndicesSim : I.state -> IL.I.state -> Prop :=
  | labIndicesSimI (L:env (option I.block)) L' E s s' symb LB
    (EQ:labIndices symb s = Success s')
    (LA:lab_approx symb L' LB)
    (EX:forall f i k, pos symb f k = Some i -> exists blk, L f = Some blk)
    (BL:forall f blk, L f = Some blk -> exists j, pos symb f 0 = Some j /\
                                        get LB j blk)
    : labIndicesSim (L, E, s) (L', E, s').

Lemma labIndicesSim_sim σ1 σ2
  : labIndicesSim σ1 σ2 -> sim Bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl in *; try monadS_inv EQ.
  - destruct e.
    + case_eq (op_eval E e); intros.
      * one_step. eapply labIndicesSim_sim; econstructor; eauto.
      * no_step.
    + case_eq (omap (op_eval E) Y); intros.
      * extern_step.
        -- eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
        -- eapply labIndicesSim_sim; econstructor; eauto.
        -- eapply labIndicesSim_sim; econstructor; eauto.
      * no_step.

  - case_eq (op_eval E e); intros.
    case_eq (val2bool v); intros; one_step; eapply labIndicesSim_sim; econstructor; eauto.
    no_step.
  - eapply option2status_inv in EQ0.
    edestruct EX as [[Lb F f]]; eauto. intros.
    edestruct BL as [i [A B]]; eauto.
    inv LA. edestruct (pos_get_first _ _ _ EQ0); dcr; eauto.
    symmetry in H3; invc H3.
    assert (x = i) by congruence; subst; clear_dup.
    orewrite (i - 0 = i) in H1.
    edestruct LEQ as [C2 [C3 [[Z [s C4]] [C5 [C6 [C7 C8]]]]]]; eauto.
    decide (length Z = length Y).
    case_eq (omap (op_eval E) Y); intros.
    edestruct C5 as [s' [D1 [D2 D3]]]; eauto.
    {
      edestruct C6.
      intros. eapply H5. instantiate (1:=i - f + n). omega.
      eapply get_drop. rewrite H3.
      eapply get_app. eapply (map_get_1 (fst ∘ fst) H6).
    }
    + one_step. orewrite (l + 0 = l). eauto. simpl.
      eapply get_drop in D1; eauto.
      orewrite (i - f + f = i) in D1. eauto.
      simpl. congruence.
      eapply labIndicesSim_sim.
      econstructor; eauto. simpl.
      * eapply lab_approx_drop; eauto.
      * intros.
        decide (f0 ∈ of_list (List.map (fst ∘ fst) F)).
        eapply update_with_list_lookup_in_list in i1. dcr.
        erewrite H7. simpl in *. inv_map H4. eauto. eauto with len.
        erewrite (update_with_list_no_update _ _ _ n); eauto.
        destruct C6. rewrite H4 in H3.
        rewrite pos_app_not_in in H3.
        eapply C3. rewrite Plus.plus_comm. rewrite <- drop_drop. rewrite H4.
        erewrite <- map_length. erewrite drop_length_eq. eauto. eauto.
      * intros. destruct C6; subst. rewrite H4.
        decide (f0 ∈ of_list (List.map (fst ∘ fst) F)).
        edestruct (of_list_get_first _ i0) as [n]; eauto. dcr. hnf in H7. subst x0.
        rewrite pos_app_in; eauto.
        pose proof H8.
        eapply update_with_list_lookup_in_list_first in H8; dcr.
        erewrite H12 in H3. subst x0.
        eexists; split. eapply get_first_pos; eauto.
        rewrite H6. eapply get_app.
        inv_map H11; eauto.
        eauto with len.
        eauto.
        erewrite (update_with_list_no_update _ _ _ n) in H3; eauto.
        edestruct C2; eauto; dcr.
        rewrite H4 in H7. eexists; eauto.
    +  intros. no_step.
    +  no_step.
       rewrite Ldef in H. inv H. simpl in *. repeat get_functional; subst. eauto.
       repeat get_functional; subst. eauto.
       edestruct C5; eauto; dcr. simpl in *.
       intros. eapply H5. instantiate (1:=i - f + n0). omega.
       eapply get_drop. rewrite H3.
       eapply get_app. eapply (map_get_1 (fst ∘ fst) H6).
       eapply get_drop in H3. orewrite (i - f + f = i) in H3.
       get_functional; subst. simpl in *. congruence.
  - no_step.
  - one_step. eapply labIndicesSim_sim. econstructor; eauto.
    instantiate (1:=(mapi (I.mkBlock L F) F ++ LB)).
    econstructor. intros.
    eapply get_app_cases in H. destruct H.
    * {
        inv_mapi H.
        exploit @get_length; eauto. rewrite mapi_length in H2.
        eapply get_in_range_app in H0.
        orewrite (f' - f' = 0); simpl.
        split.
        - intros. edestruct BL; eauto; dcr.
          eexists (length F0 + x2); split.
          rewrite pos_app_not_in; eauto.
          rewrite map_length. eapply pos_add; eauto.
          eapply get_app_right.
          rewrite mapi_length. reflexivity. eauto.
        - split. intros. erewrite <- map_length in H3.
          rewrite drop_length_eq in H3.
          eapply EX; eauto.
          split; eauto. destruct x1 as [[? ?] ?].
          inv_map H0; unfold comp in *; simpl in *.
          do 2 eexists; eauto.
          split; eauto.
          intros. eapply smap_spec in EQ0; eauto; dcr. destruct EQ0; dcr.
          monadS_inv H6. simpl in *. eexists. repeat split; eauto.
          eapply get_app.
          intros.
          eapply (mapi_get_1 0 (IL.I.mkBlock)) in H7. eauto.
          assert (get (List.map (fst ∘ fst) F0) fn fb).
          eapply (map_get_1 (fst ∘ fst) H3).
          rewrite pos_app_in.
          eapply get_first_pos; eauto.
          intros. inv_map H8. eapply H4; eauto.
          eapply get_in_of_list; eauto.
          split; eauto.
        - eauto with len.
      }
    * dcr.
      assert (length (List.map (fst ∘ fst) F) = length (mapi (I.mkBlock L F) F)) by eauto with len.
      assert (length F = length (mapi (I.mkBlock L F) F)) by eauto with len.
      orewrite (i =  length (List.map (fst ∘ fst) F) + (i -  length (mapi (I.mkBlock L F) F))) in H0.
      eapply shift_get in H0.
      inv LA; exploit LEQ; eauto; dcr; clear LEQ.
      orewrite (i - f' = i - length (mapi (I.mkBlock L F) F) - f' + length (mapi (I.mkBlock L F) F)).
      split.
      repeat rewrite <- drop_drop. repeat rewrite drop_length_eq.

      intros.
      setoid_rewrite <- H at 2.
      rewrite drop_length_eq. eauto.
      split; eauto.
      orewrite (i - length (mapi (I.mkBlock L F) F) - f' + length (mapi (I.mkBlock L F) F) +
         length F0 = i - length (mapi (I.mkBlock L F) F) - f' +
                     length F0 + length (mapi (I.mkBlock L F) F)).
      setoid_rewrite <- H at 2.
      rewrite <- drop_drop. rewrite drop_length_eq. eauto.
      split; eauto.
      rewrite <- drop_drop.
      eapply smap_length in EQ0.
      repeat rewrite mapi_length.
      repeat rewrite mapi_length in *.
      repeat rewrite drop_drop.
      repeat rewrite drop_app_gen. repeat rewrite mapi_length. repeat rewrite map_length.
      assert (PLUSEQ: forall x y, x + y -y = x) by (intros; omega).
      rewrite EQ0. repeat rewrite PLUSEQ. split; eauto.
      split; eauto. split; eauto. omega.
      rewrite mapi_length; omega.
      rewrite map_length. omega.
      rewrite mapi_length; omega.
    * { inv LA. revert ST. clear_all.
        intros. econstructor; eauto.
        unfold mapi. generalize 0. generalize F at 1.
        general induction F; simpl; eauto.
        econstructor.
        econstructor. eapply IHF. econstructor; simpl. reflexivity.
      }
    * {
        intros.
        decide (f ∈ of_list (List.map (fst ∘ fst) F)).
        - eapply update_with_list_lookup_in_list in i0. dcr.
          rewrite H2. simpl in *. inv_map H0. eauto.
          eauto with len.
        -  erewrite (update_with_list_no_update _ _ _ n); eauto.
           rewrite pos_app_not_in in H; eauto.
      }
    * { intros.
        decide (f ∈ of_list (List.map (fst ∘ fst) F)).
        - edestruct (of_list_get_first _ i) as [n]; eauto. dcr. hnf in H1. subst x1.
          rewrite pos_app_in; eauto.
          pose proof H2.
          eapply update_with_list_lookup_in_list_first in H0; dcr.
          erewrite H5 in H. subst x1.
          erewrite get_first_pos; eauto.
          eexists; split; eauto.
          inv_map H3. eapply get_app; eauto.
          eauto with len.
          eauto.
        - erewrite update_with_list_no_update in H; eauto.
          edestruct BL; eauto; dcr.
          eexists; split; eauto using get_shift.
          repeat rewrite pos_app_not_in; eauto.
          assert (length (List.map (fst ∘ fst) F) = length (mapi (I.mkBlock L F) F))
                 by eauto with len.
          rewrite H0. eapply pos_add; eauto.
      }
Qed.
