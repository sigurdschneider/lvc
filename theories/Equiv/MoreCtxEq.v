Require Import Util MapDefined LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp Envs IL Sawtooth.
Require Import ILProperties SimTactics SimF BisimEq Fresh.

Set Implicit Arguments.
Unset Printing Records.

Definition bexternals (b:F.block) :=
  externals (F.block_s b).

Definition trivs (f:external) (Z:params) :=
  let Z := fresh_list fresh {} ❬Z❭ in
  stmtLet default_var (Call f (Var ⊝ Z)) (stmtReturn (Con default_val)).

Definition trivL (b:F.block) (f:external) :=
  match b with
  | F.blockI E Z s n =>
    let Z' := fresh_list fresh {} ❬Z❭ in
    F.blockI E Z' (trivs f Z) n
  end.

Lemma trivL_star_inv (L:〔F.block〕) E xf σ n Z
  :  star2n step n (L, E, trivs xf Z) nil σ
     -> n = 0 /\ σ = (L, E, trivs xf Z).
Proof.
  intros. inv H; eauto.
  exfalso. inv H1. isabsurd.
Qed.

Local Hint Extern 0 (NoDupA _eq (fresh_list fresh _ ❬_❭))
=> eapply fresh_list_nodup; eauto using fresh_spec.

Class Triv A (PR:ProofRelationF A) := {
               triv1 :> F.block -> external -> F.block;
               triv2 :> F.block -> external -> F.block;
               triv1_block_n : forall b xf, F.block_n (triv1 b xf) = F.block_n b;
               triv2_block_n : forall b xf, F.block_n (triv2 b xf) = F.block_n b;
               triv1_block_Z : forall b xf, ❬F.block_Z (triv1 b xf)❭ = ❬F.block_Z b❭;
               triv_star_inv:forall (L:F.labenv) E xf σ b n,
                   star2n step n (L, E, F.block_s (triv1 b xf)) nil σ
                   -> n = 0 /\ σ = (L, E, F.block_s (triv1 b xf));
               triv_paramrel : forall AL L L' XF,
                 paramrel PR AL L L'
                 -> paramrel PR AL (triv1 ⊜ L XF) (triv2 ⊜ L' XF);
               triv_app_r : forall t AL L L' XF,
                 app_r t (sim bot3) PR AL (triv1 ⊜ L XF) (triv2 ⊜ L' XF)
             }.

Instance trivL_triv : Triv SR := {
                               triv1 := trivL;
                               triv2 := trivL
                             }.
Proof.
  - intros; destruct b; eauto.
  - intros; destruct b; eauto.
  - intros; destruct b; simpl; eauto with len.
  - intros. destruct b; eapply trivL_star_inv; eauto.
  - intros; hnf; intros.
    destruct f,f'; subst; simpl in *; clear_trivial_eqs.
    inv_get.
    destruct x,x1; simpl in *; clear_trivial_eqs.
    exploit (H (LabI n0) (LabI n0)); eauto using map_get_1.
    simpl in *; dcr.
    eauto with len.
  - intros; hnf; intros.
    destruct f, f'; simpl in *. subst.
    pone_step. inv_get. simpl.
    destruct x,x1; simpl in *; clear_trivial_eqs. unfold trivs.
    dcr; subst.
    left. pextern_step; eauto.
    hnf; intros. eexists; eauto. eexists. econstructor. rewrite omap_lookup_vars; eauto. eauto.
    hnf; intros. eexists; eauto. eexists. econstructor. rewrite omap_lookup_vars; eauto.
    rewrite omap_lookup_vars in *; eauto.
    left. pno_step.
    rewrite omap_lookup_vars in *; eauto.
    left. pno_step.
    Grab Existential Variables.
    eapply default_val.
    eapply default_val.
Defined.

(*
Class PPRConstr A {PR:PointwiseProofRelationF A} :=
  {
    RelParamsF : A -> params -> params;
    RelParamsF_correct : forall a Z, ParamRelFP a Z (RelParamsF a Z);
    RelArgTest : A -> params -> stmt*stmt;
    RelArgTest_correct :
      forall t a Z L L' E E', sim bot3 t (L,E,fst (RelArgTest a Z)) (L',E',snd (RelArgTest a Z))
                       -> ArgRelFP E E'

  }.
 *)

Lemma drop_nil X (L:list X) k
  : ❬L❭ <= k
    -> drop k L = nil.
Proof.
  general induction k; destruct L; simpl in *; eauto; try omega.
  rewrite drop_nil; eauto.
  eapply IHk; eauto. omega.
Qed.

Lemma zip_app_first (X Y Z : Type) (f : X -> Y -> Z) L1 L2 L
  :  ❬L2❭ <= ❬L1❭ -> zip f (L1 ++ L) L2 = zip f L1 L2.
Proof.
  intros. general induction L1; destruct L2; simpl in *; try omega; eauto.
  - destruct L; eauto.
  - f_equal; eauto. rewrite IHL1; eauto. omega.
Qed.


Lemma triv2_sawtooth A PR (trivL:@Triv A PR) L XF
  : sawtooth L
    -> sawtooth (triv2 ⊜ L XF).
Proof.
  intros H.
  general induction H; simpl; eauto using @sawtooth.
  erewrite (@take_eta ❬L❭ _ XF).
  decide (❬XF❭ > ❬L❭).
  - rewrite zip_app.
    econstructor; eauto.
    revert H0; clear. generalize 0; intros n T.
    general induction T; destruct XF; simpl; eauto using @tooth.
    econstructor; eauto.
    rewrite triv2_block_n; eauto.
    rewrite Take.take_length_le; eauto. omega.
  - rewrite drop_nil; try omega.
    rewrite zip_app_first.
    rewrite app_nil_r.
    rewrite <- app_nil_r.
    econstructor 2; eauto using @sawtooth.
    revert H0; clear. generalize 0; intros n T.
    general induction T; destruct XF; simpl; eauto using @tooth.
    econstructor; eauto.
    rewrite triv2_block_n; eauto.
    len_simpl. simpl. rewrite min_l; omega.
Qed.

Lemma triv1_sawtooth A PR (trivL:@Triv A PR) L XF
  : sawtooth L
    -> sawtooth (triv1 ⊜ L XF).
Proof.
    intros H.
  general induction H; simpl; eauto using @sawtooth.
  erewrite (@take_eta ❬L❭ _ XF).
  decide (❬XF❭ > ❬L❭).
  - rewrite zip_app.
    econstructor; eauto.
    revert H0; clear. generalize 0; intros n T.
    general induction T; destruct XF; simpl; eauto using @tooth.
    econstructor; eauto.
    rewrite triv1_block_n; eauto.
    rewrite Take.take_length_le; eauto. omega.
  - rewrite drop_nil; try omega.
    rewrite zip_app_first.
    rewrite app_nil_r.
    rewrite <- app_nil_r.
    econstructor 2; eauto using @sawtooth.
    revert H0; clear. generalize 0; intros n T.
    general induction T; destruct XF; simpl; eauto using @tooth.
    econstructor; eauto.
    rewrite triv1_block_n; eauto.
    len_simpl. simpl. rewrite min_l; omega.
Qed.

Lemma triv_sat A PR (trivL:@Triv A PR) AL t L L' XF r (Len:❬XF❭= ❬L❭) (Len2:❬L❭=❬L'❭)
  : labenv_sim t (sim r) PR AL L L'
    -> labenv_sim t (sim bot3) PR AL (triv1 ⊜ L XF) (triv2 ⊜ L' XF).
Proof.
  intros. hnf; intros.
  destruct H; dcr. len_simpl.
  split; eauto.
  split. {
    eapply triv2_sawtooth; eauto.
  }
  split. {
    eapply triv1_sawtooth; eauto.
  }
  split. {
    eapply triv_paramrel; eauto.
  }
  split. {
    hnf; intros; inv_get. edestruct H4; eauto. inv_get.
    eexists; eapply zip_get; eauto.
  }
  eapply triv_app_r.
Qed.

Lemma trivL_step_tau_inv' A PR (trivL:@Triv A PR)
      (L1:〔F.block〕) L XF E s σ (STL1:sawtooth L1) (STL2: smaller L)
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
  : step (L1 ++ triv1 ⊜ L XF, E, s) EvtTau σ
    -> (exists L2 E' s', σ = (L2 ++ triv1 ⊜ L XF, E', s') /\
                   step (L1 ++ L, E, s) EvtTau (L2 ++ L, E', s') /\ sawtooth L2 /\
                   disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
      \/ exists f Y vl Z n s' xf E', s = stmtApp f Y /\ f >= ❬L1❭ /\
                      omap (op_eval E) Y = Some vl /\
                      get XF (f - ❬L1❭) xf  /\
                      get L (f - ❬L1❭) (F.blockI E' Z s' n) /\
                      σ = (drop ((f - ❬L1❭)- n) (triv1 ⊜ L XF),
                           (F.block_E (triv1 (F.blockI E' Z s' n) xf))
                             [F.block_Z (triv1 (F.blockI E' Z s' n) xf) <-- Some ⊝ vl],
                           F.block_s (triv1 (F.blockI E' Z s' n) xf)) /\
                 step (L1 ++ L, E, s) EvtTau (drop ((f - ❬L1❭) - n) L, E'[Z <-- Some ⊝ vl], s') /\
                 ❬Z❭ = ❬Y❭.
Proof.
  intros.
  inv H; simpl in *;
    try now (
          left; eexists L1; do 2 eexists;
          (split; [try reflexivity
                  |split; [try single_step
                          |split; [eassumption|eapply disj_2_incl; eauto with cset]]])
        ).
  - eapply get_app_cases in Ldef as [|[? ?]].
    + left. eexists (drop (l - F.block_n blk) L1).
      rewrite <- !drop_le; eauto.
      do 2 eexists; (split; [try reflexivity|split; try single_step]).
      eapply get_app; eauto.
      split.
      eapply sawtooth_drop'; eauto using get_app.
      rewrite drop_map. rewrite list_union_drop_incl.
      eapply disj_2_incl; eauto.
      eapply union_incl_split; eauto with cset.
      rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
      cset_tac.
      eapply get_range in H0. omega.
      eapply get_range in H0. omega.
    + right.
      inv_get. destruct x as [E'' Z s' n].
      do 8 eexists; split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto. simpl.
      split; eauto. simpl.
      rewrite drop_app_gen.
      rewrite !triv1_block_n; simpl.
      orewrite (l - n - ❬L1❭ = l - ❬L1❭ - n). reflexivity.
      exploit STL2; eauto. simpl in *. rewrite triv1_block_n. simpl. omega.
      split; eauto.
      orewrite (l - ❬L1❭ - n = l - n - ❬L1❭).
      rewrite <- drop_app_gen.
      eapply get_app_right with (L':=L1) (n':=l) in H2.
      eapply (F.StepGoto _ _ _ H2); eauto with len. simpl in *.
      rewrite triv1_block_Z in len. simpl in *. eauto.
      omega.
      exploit STL2; eauto. simpl in *. omega.
      rewrite triv1_block_Z in len. simpl in *. eauto.
  - left. eexists (mapi (F.mkBlock E) F ++ L1). rewrite <- !app_assoc.
    do 2 eexists; (split; [try reflexivity|try single_step]).
    split; eauto. single_step. split; eauto.
    eapply disj_2_incl; eauto.
    apply union_incl_split; eauto with cset.
    rewrite map_app.
    rewrite list_union_app.
    apply union_incl_split; eauto with cset.
    eapply incl_union_left.
    eapply incl_union_left.
    eapply list_union_incl; eauto with cset.
    intros; inv_get.
    eapply incl_list_union; eauto using map_get.
Qed.


Lemma trivL_plus_step_tau_inv A PR (trivL : @Triv A PR)
      L1 (L:〔F.block〕) XF E s σ n
      (STEP:star2n step n (L1 ++ triv1 ⊜ L XF, E, s) nil σ) (STL1:sawtooth L1) (STL2: smaller L)
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
  : ((exists L2 E' s',
         star2n step n (L1 ++ L, E, s) nil (L2 ++ L, E', s') /\
         sawtooth L2 /\ σ = (L2 ++ triv1 ⊜ L XF, E', s') /\
         disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
     \/ ( exists E' f Y vl Z n' s' xf L2 m E'',
           star2n step m (L1 ++ L, E, s) nil (L2 ++ L, E', stmtApp (LabI (❬L2❭ + f)) Y) /\ n = S m /\
           step (L2 ++ L, E', stmtApp (LabI (❬L2❭ + f)) Y) EvtTau
                (drop (f - n') L, E''[Z <-- Some ⊝ vl], s') /\
           omap (op_eval E') Y = Some vl /\
           get XF f xf  /\
           get L f (F.blockI E'' Z s' n') /\
           σ = (drop (f - n') (triv1 ⊜ L XF),
                (F.block_E (triv1 (F.blockI E'' Z s' n') xf))
                  [F.block_Z (triv1 (F.blockI E'' Z s' n') xf) <-- Some ⊝ vl],
                F.block_s (triv1 (F.blockI E'' Z s' n') xf)) /\
           ❬Z❭ = ❬Y❭)).
Proof.
  intros. general induction STEP.
  - left.
    eexists L1; do 2 eexists; eauto 20 using star2n.
  - destruct y, yl; isabsurd.
    edestruct (@trivL_step_tau_inv' _ _ trivL0 L1 L); eauto.
    + dcr. subst. simpl in *; clear_trivial_eqs.
      exploit IHSTEP as IH; eauto.
      destruct IH as [[? ?]|[? ?]]; dcr; subst.
      * left. do 3 eexists. split.
        -- eapply S_star2n with (y:=EvtTau) (yl:=nil); eauto.
        -- eauto.
      * right.
        do 11 eexists. split.
        -- eapply S_star2n with (y:=EvtTau) (yl:=nil); eauto.
        -- eauto 20.
    + destruct H0; dcr; subst.
      edestruct (triv_star_inv _ _ STEP); eauto; subst.
      right. destruct x; simpl in *.
      assert (NEQ:n = ❬L1❭ + (n - ❬L1❭)) by omega.
      setoid_rewrite NEQ at 1.
      do 11 eexists. split.
      * econstructor.
      * split; eauto.
        split; eauto.
        rewrite <- NEQ. eauto.
Qed.

Lemma event_inversion' (L:F.labenv) (E:onv val) xf (L':F.labenv) E' s' Z vl (Len:❬Z❭= ❬vl❭) r
  : (forall evt σ1'', step (L, E[fresh_list fresh {} ❬Z❭ <-- Some ⊝ vl], trivs xf Z) evt σ1'' -> exists σ2'',
          step (L', E', s') evt σ2'' /\ r σ1'' σ2'')
    -> exists Y x s'', s' = stmtLet x (Call xf Y) s''
                 /\ omap (op_eval E') Y = Some vl.
Proof.
  intros.
  edestruct event_inversion_F; eauto.
  rewrite omap_lookup_vars; eauto with len.
  dcr; subst.
  setoid_rewrite omap_lookup_vars in H3; eauto with len.
Qed.

Lemma event_inversion2 (L:F.labenv) (E:onv val) xf (L':F.labenv) E' s' Z vl (Len:❬Z❭= ❬vl❭) r
  : (forall evt σ1'', step (L', E', s') evt σ1'' -> exists σ2'',
          step (L, E[fresh_list fresh {} ❬Z❭ <-- Some ⊝ vl], trivs xf Z) evt σ2'' /\ r σ1'' σ2'')
    -> activated (L', E', s')
    -> exists Y x s'', s' = stmtLet x (Call xf Y) s''
                 /\ omap (op_eval E') Y = Some vl.
Proof.
  intros SIM [? [? STEP]]; inv STEP.
  edestruct SIM; eauto; dcr. inv H0.
  rewrite omap_lookup_vars in *; eauto with len.
Qed.

Lemma trivs_inversion (L:F.labenv) XF E s L' E' xf n s' x L2 Y'
      (GET:get XF n xf) (Len:❬XF❭ = ❬L❭) (ND:NoDupA eq XF)
      (NOTIN1:xf ∉ externals s) (NOTIN2:xf ∉ list_union (bexternals ⊝ L2))
  (Step:step (L2 ++ trivL ⊜ L XF, E, s) EvtTau (L', E', stmtLet x (Call xf Y') s'))
  : exists Y b vl, s = stmtApp (LabI (❬L2❭ + n)) Y
         /\ get L n b
         /\ ❬Y❭ = ❬F.block_Z b❭
         /\ omap (op_eval E) Y = Some vl.
Proof.
  inv Step; simpl in *;
    try now (exfalso; cset_tac).
  eapply get_app_cases in Ldef as [?|[? ?]].
  - exfalso. eapply NOTIN2. rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
    unfold bexternals. rewrite H5. simpl. cset_tac.
  - destruct blk; simpl in *. subst.
    inv_get. destruct x0. simpl in *. unfold trivs in EQ. invc EQ.
    decide (n = l - ❬L2❭).
    + rewrite e. do 3 eexists.
      split. f_equal. destruct l. f_equal. simpl in *. omega.
      split; eauto. simpl.
      split; eauto. eauto with len.
    + exfalso.
      eapply NoDupA_get_neq in GET; eauto. congruence.
Qed.

Lemma trivL_block_Z L1 L XF
  : forall (n : nat) (b b' : F.block),
    get (L1 ++ trivL ⊜ L XF) n b -> get (L1 ++ L) n b' -> ❬block_Z b❭ = ❬block_Z b'❭.
Proof.
  intros.
  eapply get_app_cases in H as [?|[? ?]]; inv_get; eauto.
  eapply get_app_ge in H0; eauto.
  destruct x; inv_get. simpl. eauto with len.
Qed.


Lemma labenv_lift r t XF L1 L2 L L' E E' s s'
      (Len:❬XF❭=❬L❭) (Len2:❬L❭=❬L'❭)
      (DISJ:disj (of_list XF) (externals s ∪ list_union (bexternals ⊝ L1)))
      (DISJ':disj (of_list XF) (externals s' ∪ list_union (bexternals ⊝ L2)))
      (ND:NoDupA eq XF)
  (LAB:labenv_sim t (sim r) SR (@length _ ⊝ block_Z ⊝ L') L L')
  (SIMbot:sim bot3 t (L1 ++ trivL ⊜ L XF, E, s) (L2 ++ trivL ⊜ L' XF, E', s'))
  (STL1:sawtooth L1)
  (STL2: sawtooth L2)
  : sim r t (L1 ++ L, E, s) (L2 ++ L', E', s').
Proof.
  revert_all. pcofix CIH; intros.
  pinversion SIMbot; subst.
  - eapply plus2_star2n in H. eapply plus2_star2n in H0. dcr.
    edestruct (trivL_plus_step_tau_inv trivL_triv _ H2); eauto; dcr; subst;
      try eapply sawtooth_smaller,LAB.
    + edestruct (trivL_plus_step_tau_inv trivL_triv _ H0); eauto; dcr; subst;
        try eapply sawtooth_smaller,LAB.
      * uncount_star2.
        pfold.
        econstructor 1; eauto.
      * eapply sim_activated in H1 as [? [? [? ?]]]; dcr.
        destruct x15 as [[? ?] ?].
        eapply event_inversion2 in H15 as [? [? ?]]; dcr; subst. clear H13.
        eapply star2_star2n in H. dcr.
        eapply star2n_trans_silent in H12; eauto. simpl in *.
        eapply (trivL_plus_step_tau_inv trivL_triv) in H12 as [|];
          dcr; subst; clear_trivial_eqs; simpl in *; eauto.
        -- exfalso. eapply H18. eapply get_in_of_list; eauto.
           clear. cset_tac.
        -- rewrite omap_lookup_vars in H17;
             [ invc H17 | eauto with len | eauto ].
           uncount_star2.
           eapply sim_expansion_closed; try eassumption.
           eapply sim_app_shift_F; [eapply sawtooth_smaller,LAB | eapply sawtooth_smaller,LAB |].
           edestruct LAB; dcr. rename H24 into APPR.
           hnf in APPR. len_simpl.
           assert (x5 = x20). {
             decide (x5 = x20); eauto.
             exfalso.
             eapply NoDupA_get_neq in H18; eauto. congruence.
           } subst.
           eapply paco3_mon; try eapply CIH0.
           eapply (APPR (LabI x20) (LabI x20)); eauto.
           hnf. simpl in *. split; eauto. eauto with len.
           exploit (APPR (LabI x20)); eauto using map_get_1;
             hnf in H; dcr; simpl in *; eauto with len. eauto with len.
        -- eapply sawtooth_smaller,LAB.
        -- eauto with len.
        -- eauto.
        -- hnf. do 2 eexists; econstructor.
           rewrite omap_lookup_vars; eauto. eauto with len.
    + clear_trivial_eqs.
      eapply sim_activated_2 in H1 as [? [? [?|?]]]; dcr.
      * destruct x as [[? ?] ?].
        eapply event_inversion' in H10 as [? [? ?]]; dcr; subst. clear H12.
        eapply star2_star2n in H. dcr.
        eapply star2n_trans_silent in H1; eauto. simpl in *.
        eapply (trivL_plus_step_tau_inv trivL_triv) in H1 as [|];
          dcr; subst; clear_trivial_eqs; simpl in *; eauto.
        -- exfalso. eapply H14. eapply get_in_of_list; eauto.
           clear. cset_tac.
        -- rewrite omap_lookup_vars in H13;
             [ invc H13 | eauto with len | eauto ].
           uncount_star2.
           eapply sim_expansion_closed; try eassumption.
           eapply sim_app_shift_F; [eapply sawtooth_smaller,LAB | eapply sawtooth_smaller,LAB |].
           edestruct LAB; dcr. rename H21 into APPR.
           hnf in APPR. len_simpl.
           assert (x2 = x16). {
             decide (x2 = x16); eauto.
             exfalso.
             eapply NoDupA_get_neq in H14; eauto. congruence.
           } subst.
           eapply paco3_mon; try eapply CIH0.
           eapply (APPR (LabI x16) (LabI x16)); eauto.
           hnf. simpl in *. split; eauto. eauto with len.
           exploit (APPR (LabI x16)); eauto using map_get_1;
             hnf in H; dcr; simpl in *; eauto with len. eauto with len.
        -- eapply sawtooth_smaller,LAB.
        -- eauto with len.
      * subst.
        eapply star2_star2n in H. dcr.
        eapply star2n_trans_silent in H1; eauto. simpl in *.
        eapply (trivL_plus_step_tau_inv trivL_triv) in H1 as [|];
          dcr; subst; clear_trivial_eqs; simpl in *; eauto.
        -- uncount_star2.
           eapply plus2_star2 in H9.
           eapply sim_expansion_closed; try eassumption.
           pfold. eapply SimErr; eauto using star2_refl.
           simpl; eauto.
           eapply normal2_labenv_F; eauto using trivL_block_Z with len.
        -- exfalso.
           eapply H3. do 2 eexists.
           econstructor. rewrite omap_lookup_vars; eauto. eauto with len.
        -- eapply sawtooth_smaller,LAB.
      * do 2 eexists. econstructor. rewrite omap_lookup_vars. reflexivity.
        eauto with len. eapply fresh_list_nodup; eauto using fresh_spec.
  - eapply star2_star2n in H. dcr.
    eapply star2_star2n in H0. dcr.
    edestruct (trivL_plus_step_tau_inv trivL_triv _ H5); eauto; dcr; subst;
      try eapply sawtooth_smaller,LAB.
    + edestruct (trivL_plus_step_tau_inv trivL_triv _ H); eauto; dcr; subst;
        try eapply sawtooth_smaller,LAB.
      * uncount_star2.
        pfold.
        econstructor 2; eauto using activated_labenv_F.
        -- intros. subst.
           exploit activated_inv_F; try eapply H1; dcr; subst.
           exploit activated_inv_F; try eapply H2; dcr; subst.
           destruct σ1' as [[? ?] ?].
           edestruct (H3 ltac:(eauto) evt (x1 ++ trivL ⊜ L XF, o, s0)); eauto.
           inv H11. econstructor; eauto. dcr.
           destruct x6 as [[? ?] ?].
           eexists (x4 ++ L', o0, s1); split; eauto.
           inv H14. econstructor; eauto.
           right. destruct H15; [|isabsurd].
           inv H14. inv H11.
           eapply CIH; try eapply H14; eauto.
           simpl in *. eapply disj_2_incl; try eapply H10; eauto. eauto with cset.
           eapply disj_2_incl; eauto. eauto with cset.
        -- intros.
           exploit activated_inv_F; try eapply H1; dcr; subst.
           exploit activated_inv_F; try eapply H2; dcr; subst.
           destruct σ2' as [[? ?] ?].
           edestruct (H4 evt (x4 ++ trivL ⊜ L' XF, o, s0)); eauto.
           inv H0. econstructor; eauto. dcr.
           destruct x6 as [[? ?] ?].
           eexists (x1 ++ L, o0, s1); split; eauto.
           inv H12. econstructor; eauto.
           right. destruct H14; [|isabsurd].
           inv H0. inv H12.
           eapply CIH; try eapply H14; eauto.
           simpl in *. eapply disj_2_incl; try eapply H10; eauto. eauto with cset.
           eapply disj_2_incl; eauto. eauto with cset.
      * uncount_star2. eapply plus2_star2 in H.
        assert (SIMbot':paco3 (@sim_gen F.state _ F.state _) bot3 t
                      (L1 ++ trivL ⊜ L XF, E, s) (L2 ++ trivL ⊜ L' XF, E', s')).
        pfold; eauto.
        eapply sim_reduction_closed in SIMbot'; eauto.
        edestruct activated_inv_F; try eapply H1; dcr; subst.
        unfold trivs in SIMbot'.
        eapply sim_call_inv_F in SIMbot' as [|]; dcr; subst.
        -- exfalso. eapply H10.
           eapply get_in_of_list; eauto. simpl. clear. cset_tac.
        -- destruct t.
           ++ specialize (H15 eq_refl).
             rewrite H8 in H15. rewrite omap_lookup_vars in H15; eauto. congruence.
             eauto with len.
           ++ pfold. eapply SimErr; try eapply H7.
             reflexivity.
             intros [? [? ?]]. inv H0. congruence. eauto.
           ++ pfold. eapply SimErr; try eapply H7.
             reflexivity.
             intros [? [? ?]]. inv H0. congruence. eauto.
    + edestruct (trivL_plus_step_tau_inv trivL_triv _ H); eauto; dcr; subst;
        try eapply sawtooth_smaller,LAB.
      * uncount_star2. eapply plus2_star2 in H5.
        assert (SIMbot':paco3 (@sim_gen F.state _ F.state _) bot3 t
                      (L1 ++ trivL ⊜ L XF, E, s) (L2 ++ trivL ⊜ L' XF, E', s')).
        pfold; eauto.
        eapply sim_reduction_closed in SIMbot'; eauto.
        edestruct activated_inv_F; try eapply H2; dcr; subst.
        unfold trivs in SIMbot'.
        eapply sim_call_inv_F in SIMbot' as [|]; dcr; subst.
        -- simpl in *. exfalso. eapply H16.
           eapply get_in_of_list; eauto. simpl. clear. cset_tac.
        -- destruct t.
           ++ specialize (H15 eq_refl).
             rewrite H13 in H15. rewrite omap_lookup_vars in H13; eauto. congruence.
             eauto with len.
           ++ rewrite omap_lookup_vars in H13; eauto. congruence.
             eauto with len.
           ++ rewrite omap_lookup_vars in H13; eauto. congruence.
             eauto with len.
      * uncount_star2. eapply plus2_star2 in H.
        eapply plus2_star2 in H5.
        assert (SIMbot':paco3 (@sim_gen F.state _ F.state _) bot3 t
                      (L1 ++ trivL ⊜ L XF, E, s) (L2 ++ trivL ⊜ L' XF, E', s')). {
          pfold; eauto.
        }
        eapply sim_reduction_closed in SIMbot'; eauto.
        eapply sim_call_inv_F in SIMbot' as [|]; dcr; subst.
        -- rewrite !omap_lookup_vars in H6; only 2-5: eauto with len.
           clear_trivial_eqs.
          eapply sim_expansion_closed; eauto.
           eapply sim_app_shift_F; [eapply sawtooth_smaller,LAB | eapply sawtooth_smaller,LAB |].
           edestruct LAB; dcr. rename H24 into APPR.
           hnf in APPR. len_simpl.
           assert (x2 = x12). {
             decide (x2 = x12); eauto.
             exfalso.
             eapply NoDupA_get_neq in H16; eauto. congruence.
           } subst.
           eapply paco3_mon; try eapply CIH0.
           eapply (APPR (LabI x12) (LabI x12)); eauto.
           hnf. simpl in *. split; eauto. eauto with len.
           exploit (APPR (LabI x12)); eauto using map_get_1;
             hnf in H; dcr; simpl in *; eauto with len. eauto with len.
        -- destruct t.
           ++ specialize (H18 eq_refl).
             rewrite H6 in H18. rewrite omap_lookup_vars in H18; eauto. congruence.
             eauto with len.
           ++ rewrite omap_lookup_vars in H6; eauto. congruence.
             eauto with len.
           ++ rewrite omap_lookup_vars in H6; eauto. congruence.
             eauto with len.
  - eapply star2_star2n in H0. dcr.
    edestruct (trivL_plus_step_tau_inv trivL_triv _ H3); eauto; dcr; subst; only 1: eapply sawtooth_smaller,LAB.
    + eapply star2n_star2 in H5.
      pfold.
      eapply SimErr; try eapply H5; eauto.
      eapply normal2_labenv_F; eauto using trivL_block_Z with len.
    + exfalso. eapply H1.
      hnf. do 2 eexists. econstructor.
      rewrite omap_lookup_vars; eauto.
      eauto with len.
  - eapply star2_star2n in H0. eapply star2_star2n in H1. dcr.
    edestruct (trivL_plus_step_tau_inv trivL_triv _ H4); eauto; dcr; subst;
      only 1: eapply sawtooth_smaller,LAB.
    + edestruct (trivL_plus_step_tau_inv trivL_triv _ H1); eauto; dcr; subst;
        only 1: eapply sawtooth_smaller,LAB.
      * pfold.
        eapply star2n_star2 in H6. eapply star2n_star2 in H8.
        eapply SimTerm; try eapply H6; try eapply H8.
        eauto.
        eapply normal2_labenv_F; eauto using trivL_block_Z with len.
        eapply normal2_labenv_F; eauto using trivL_block_Z with len.
      * exfalso. eapply H2.
        hnf. do 2 eexists. econstructor.
        rewrite omap_lookup_vars. reflexivity.
        eauto with len.
        eapply fresh_list_nodup; eauto using fresh_spec.
    + exfalso. eapply H3.
      hnf. do 2 eexists. econstructor.
      rewrite omap_lookup_vars. reflexivity.
      eauto with len.
      eapply fresh_list_nodup; eauto using fresh_spec.
      Grab Existential Variables.
      eapply default_val.
      eapply default_val.
      eapply default_val.
      eapply default_val.
      eapply default_val.
      eapply default_val.
Qed.

Lemma trivL_Z_len L XF
  (Len:❬XF❭=❬L❭)
  : length (A:=positive) ⊝ block_Z ⊝ L = length (A:=positive) ⊝ block_Z ⊝ trivL ⊜ L XF.
Proof.
  eapply map_eq_ext_get; intros; inv_get; eauto with len.
  destruct x0; simpl; eauto with len.
Qed.

Lemma bisimeq_bot t s s'
  : bisimeq bot3 t s s' -> forall r, bisimeq r t s s'.
Proof.
  intros. hnf; intros.
  set (XF:=fresh_list fresh (externals s ∪ externals s') ❬L❭).
  exploit (H (trivL ⊜ L XF) (trivL ⊜ L' XF) E).
  - rewrite <- trivL_Z_len.
    eapply (triv_sat trivL_triv XF (ltac:(eauto with len)) H1 H0); eauto.
    subst XF; eauto with len.
    rewrite fresh_list_length; eauto.
  - eauto with len.
  - eapply labenv_lift with (L1:=nil) (L2:=nil) (XF:=XF) (E:=E); simpl; eauto.
    + subst XF; eauto with len.
    + simpl.
      eapply disj_2_incl.
      eapply fresh_list_spec; eauto using fresh_spec.
      eauto with cset.
    + simpl.
      eapply disj_2_incl.
      eapply fresh_list_spec; eauto using fresh_spec.
      eauto with cset.
    + eapply fresh_list_nodup; eauto using fresh_spec.
    + econstructor.
    + econstructor.
Qed.
