Require Import Util LengthEq AllInRel IL Computable Sim SimTactics.

Import F.

Set Implicit Arguments.
Unset Printing Records.

(** * Alpha Equivalence *)

Inductive alpha : env var -> env var -> stmt -> stmt -> Prop :=
| AlphaReturn ra ira e e'
  : alpha_op ra ira e e'  -> alpha ra ira (stmtReturn e) (stmtReturn e')
| AlphaApp ra ira l X Y
  : length X = length Y
    -> (forall n x y, get X n x -> get Y n y -> alpha_op ra ira x y)
    -> alpha ra ira (stmtApp l X) (stmtApp l Y)
| AlphaLet ra ira x y e e' s s'
  : alpha_exp ra ira e e'
  -> alpha (ra[x<-y]) (ira[y <- x]) s s' -> alpha ra ira (stmtLet x e s) (stmtLet y e' s')
| AlphaCond ra ira e e' s s' t t'
  : alpha_op ra ira e e'
  -> alpha ra ira s s'
  -> alpha ra ira t t'
  -> alpha ra ira (stmtIf e s t) (stmtIf e' s' t')
| AlphaFun ra ira F F' t t'
  : length F = length F'
    -> (forall n Zs Zs', get F n Zs -> get F' n Zs' -> length (fst Zs) = length (fst Zs'))
    -> (forall n Zs Zs', get F n Zs -> get F' n Zs'
                   -> alpha (ra [ fst Zs <-- fst Zs']) (ira [ fst Zs' <-- fst Zs ]) (snd Zs) (snd Zs'))
    -> alpha ra ira t t' -> alpha ra ira (stmtFun F t) (stmtFun F' t').

(** ** Morphisims *)
(** These properties are required because we do not assume functional extensionality. *)


Global Instance alpha_morph
 : Proper ((@feq _ _ _eq) ==> (@feq _ _ _eq) ==> eq ==> eq ==> impl) alpha.
Proof.
  unfold respectful, Proper, impl; intros; subst.
  general induction H3; econstructor; eauto using alpha_exp_morph, alpha_op_morph.
  - eapply IHalpha; eapply update_inst; eauto.
  - intros. eapply H2; eauto.
    + rewrite H4; reflexivity.
    + rewrite H5; reflexivity.
Qed.

Lemma alpha_agree_on_morph f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t
  -> agree_on _eq (lookup_set ϱ (freeVars s)) g ϱ'
  -> agree_on _eq (freeVars s) f ϱ
  -> alpha f g s t.
Proof.
  intros.
  general induction H; simpl in * |- *;
    eauto using alpha, alpha_exp_agree_on_morph, alpha_op_agree_on_morph, alpha_op_list_agree_on_morph.
  - econstructor.
    eapply alpha_exp_agree_on_morph;
      eauto using agree_on_incl, lookup_set_union_incl with cset.
    eapply IHalpha; eauto.
    + eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      hnf; intros. eapply lookup_set_spec; eauto.
      cset_tac; eqs. eapply lookup_set_spec in H4; eauto.
      destruct H4; dcr. eexists x0.
      lud; split; eqs; cset_tac. intuition.
    + eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    + eapply alpha_op_agree_on_morph;
      eauto using agree_on_incl, lookup_set_union_incl with cset.
    + eapply IHalpha1; eauto using agree_on_incl, lookup_set_union_incl with cset.
    + eapply IHalpha2; eauto using agree_on_incl, lookup_set_union_incl with cset.
  - econstructor; eauto.
    + intros.
      eapply H2; eauto.
      * eapply update_with_list_agree; eauto using length_eq_sym.
        eapply agree_on_incl; eauto.
        hnf; intros. eapply lookup_set_spec. eauto.
        lset_tac.
        exists x. cset_tac. left. eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        rewrite H12 in H10.
        eapply lookup_set_update_not_in_Z'_not_in_Z in H10.
        cset_tac. eapply H0; eauto.
        eauto.
        rewrite H12 in H10. eapply lookup_set_update_not_in_Z' in H10.
        rewrite <- H10; eauto. symmetry. eapply H0; eauto.
      * eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto. eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    + eapply IHalpha;
      eauto using agree_on_incl, lookup_set_union_incl with cset.
Qed.

(** ** Properties *)

(** *** [ϱ] and [ϱ'] are inverses of each other on the free variables of [s] *)
Lemma alpha_inverse_on  ϱ ϱ' s t
  : alpha ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros A. general induction A; simpl; eauto using alpha_op_inverse_on, alpha_exp_inverse_on.
  + hnf; intros.
    edestruct (list_union_get (List.map Op.freeVars X)) as [[? []]|]; eauto; dcr.
    edestruct map_get_4; eauto; dcr.
    edestruct get_length_eq; eauto. subst.
    eapply alpha_op_inverse_on; eauto.
    inv i.
  + eapply inverse_on_union;
    eauto 10 using inverse_on_dead_update, alpha_exp_inverse_on with cset.
  + eapply inverse_on_union; try eapply inverse_on_union; eauto using alpha_op_inverse_on.
  + eapply inverse_on_union; eauto.
    eapply inverse_on_list_union.
    intros. inv_get.
    edestruct (get_length_eq _ H3 H); eauto.
    eauto using @update_with_list_inverse_on.
Qed.

Lemma alpha_inverse_on_agree f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t
  -> inverse_on (freeVars s) f g
  -> agree_on _eq (freeVars s) f ϱ
  -> alpha f g s t.
Proof.
  intros. eapply alpha_agree_on_morph; eauto.
  symmetry in H1.
  eapply inverse_on_agree_on_2; eauto.
  - eapply inverse_on_agree_on; eauto.
    eapply agree_on_sym; eauto.
  - eapply alpha_inverse_on in H.
    eapply inverse_on_agree_on; try eassumption; eauto.
    eapply inverse_on_agree_on_2; eauto.
    eapply agree_on_sym; eauto.
Qed.


(** *** Reflexivity *)

Lemma alpha_refl s
  : alpha id id s s.
Proof.
  sind s; destruct s; eauto using alpha, alpha_op_refl.
  - econstructor. eapply alpha_exp_refl.
    rewrite update_id; eauto.
  - constructor; eauto using lookup_id.
    + intros. get_functional; subst; eauto using alpha_op_refl.
  - econstructor; try rewrite update_with_list_id; eauto using length_eq_refl.
    + intros; get_functional; subst; eauto.
    + intros; get_functional; subst.
      rewrite update_with_list_id.
      eapply IH; eauto.
Qed.

(** *** Symmetry *)

Lemma alpha_sym ϱ ϱ' s s'
  :  alpha ϱ ϱ' s s'
  ->  alpha ϱ' ϱ s' s.
Proof.
  intros. general induction H; eauto using alpha, length_eq_sym, alpha_exp_sym, alpha_op_sym.
  - econstructor; intros; eauto.
    symmetry; eauto.
Qed.

(** *** Transitivity *)

Lemma alpha_trans ϱ1 ϱ1' ϱ2 ϱ2' s s' s''
  : alpha ϱ1 ϱ1' s s' -> alpha ϱ2 ϱ2' s' s'' -> alpha (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H; invt alpha; eauto using alpha_exp_trans, alpha_op_trans, alpha.
  - econstructor; eauto. etransitivity; eauto.
    intros. edestruct (get_length_eq _ H2 H); eauto.
    eapply alpha_op_trans; eauto.
  - econstructor; eauto using alpha_exp_trans.
    specialize (IHalpha _ _ _ H9).
    eapply alpha_inverse_on in H0.
    eapply alpha_inverse_on_agree; eauto.
    eapply inverse_on_comp; eauto. eapply alpha_inverse_on; eauto.
    symmetry. eapply lookup_set_agree_on_comp. intuition.
    eapply inverse_on_update_lookup_set. intuition. eauto.
  - econstructor; eauto.
    + congruence.
    + intros. edestruct (get_length_eq _ H5 H).
      exploit H8; eauto. exploit H0; eauto. congruence.
    + intros.
      edestruct (get_length_eq _ H5 H).
      exploit H0; eauto. exploit H8; eauto.
      exploit H2; eauto.
      * eapply H11; eauto.
      * eapply alpha_inverse_on_agree. eauto.
        {
          - eapply alpha_inverse_on in H14; eauto.
            eapply inverse_on_agree_on; eauto.
            eapply inverse_on_comp_list; eauto.
            eapply inverse_on_sym in H14.
            eapply inverse_on_comp_list; eauto.
            unfold comp; intuition.
            unfold comp; intuition.
        }
        symmetry.
        eapply inverse_on_comp_list; eauto.
        eapply alpha_inverse_on; eauto.
Qed.

(** ** Soundness wrt. equivalence *)

Definition envCorr ra ira (E E':onv val) :=
  forall x y, ra x = y -> ira y = x -> E x = E' y.

Lemma envCorr_idOn_refl (E:onv val)
  : envCorr id id E E.
Proof.
  hnf; intros; firstorder.
Qed.

Inductive approx : F.block -> F.block ->  Prop :=
| EA2_cons ra ira E E' s s' Z Z' n
  : length Z = length Z'
  -> alpha (ra [ Z <-- Z']) (ira [ Z' <-- Z ]) s s'
  -> envCorr ra ira E E'
  -> approx (F.blockI E Z s n) (F.blockI E' Z' s' n).

Lemma approx_refl b
  : approx b b.
Proof.
  destruct b. econstructor; eauto.
  rewrite update_with_list_id. eapply alpha_refl.
  firstorder.
Qed.

Lemma envCorr_update ra ira x y v E E'
  (EC:envCorr ra ira E E')
  : envCorr (ra [x <- y]) (ira [y <- x]) (E [x <- v]) (E' [y <- v]).
Proof.
  hnf; intros; lud.
  + exfalso. eapply H0. reflexivity.
  + exfalso. eapply H1. reflexivity.
  + eapply EC; eauto.
Qed.

Lemma envCorr_update_lists bra bira block_E block_E' block_Z block_Z' ra ira
  E E' X Y (EC':envCorr ra ira E E')
  (LL : lookup_list ra X = Y)
  (LL' : lookup_list ira Y = X)
  (EC: envCorr bra bira block_E block_E')
  (LC: length block_Z = length block_Z')
  (LC': length block_Z = length X)
  (LC'': length block_Z' = length Y)
  : envCorr (bra [ block_Z <-- block_Z' ]) (bira [ block_Z' <-- block_Z ])
  (block_E  [ block_Z <-- lookup_list E X ])
  (block_E' [ block_Z' <-- lookup_list E' Y ]).
Proof.
  eapply length_length_eq in LC.
  eapply length_length_eq in LC'.
  eapply length_length_eq in LC''.
  general induction LC; simpl; eauto.
  - inversion LC'; subst x0 XL0. inv LC''.
    simpl in *; injection LL. injection H; intros.
    subst y0 YL0.
    erewrite EC'; eauto using envCorr_update.
Qed.

Lemma envCorr_update_list bra bira block_E block_E' block_Z block_Z' ra ira
  E E' vl (EC':envCorr ra ira E E')
  (EC: envCorr bra bira block_E block_E')
  (LC: length block_Z = length block_Z')
  (LC': length block_Z = length vl)
  : envCorr (bra [ block_Z <-- block_Z' ]) (bira [ block_Z' <-- block_Z ])
  (block_E  [ block_Z <-- vl ])
  (block_E' [ block_Z' <-- vl ]).
Proof.
  eapply length_length_eq in LC.
  eapply length_length_eq in LC'.
  general induction LC; inv LC'; simpl; eauto.
  eapply envCorr_update; eauto.
Qed.

Lemma alpha_op_eval : forall ra ira e e' E E',
  alpha_op ra ira e e' ->
  envCorr ra ira E E' ->
  op_eval E e = op_eval E' e'.
Proof.
  intros. general induction H; simpl in *; eauto.
  - erewrite IHalpha_op; eauto.
  - erewrite IHalpha_op1, IHalpha_op2; eauto.
Qed.

Inductive alphaSim : F.state -> F.state -> Prop :=
 | alphaSimI ra ira s s' L L' E E'
  (AE:alpha ra ira s s')
  (EA:PIR2 approx L L')
  (EC:envCorr ra ira E E')
   : alphaSim (L, E, s) (L', E', s').

Lemma alphaSim_sim σ1 σ2
: alphaSim σ1 σ2 -> sim bot3 Bisim σ1 σ2.
Proof.
  revert σ1 σ2; pcofix alphaSim_sim; intros.
  destruct H0; inversion AE; subst ra0 ira0; simpl in * |- *;
  try subst s s'; simpl in * |- *.
  - pno_step. simpl. eapply alpha_op_eval; eauto.
  - destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    decide (length Zb = length Y).
    case_eq (omap (op_eval E) X); intros.
    + edestruct PIR2_nth; eauto; dcr. inv H4.
      simpl in *.
      pone_step; simpl; try congruence; eauto.
      erewrite omap_agree_2; eauto. intros. symmetry.
      eapply alpha_op_eval. eapply H0; eauto; eauto. hnf; intros; eauto.
      simpl. right; eapply alphaSim_sim; econstructor; eauto using PIR2_drop.
      eapply envCorr_update_list; eauto with len.
    + pno_step. erewrite omap_agree_2 in H1; try eapply H.
      erewrite H1 in def. congruence.
      intros. eapply alpha_op_eval. eapply H0; eauto. eauto.
    + edestruct PIR2_nth; eauto; dcr. inv H3.
      pno_step.
    + pno_step; eauto. edestruct PIR2_nth_2; eauto; dcr. eauto.
  - inv H.
    + case_eq (op_eval E e0); intros.
      * pone_step. erewrite <- alpha_op_eval; eauto.
        right; eapply alphaSim_sim; econstructor; eauto using envCorr_update.
      * pno_step.
        erewrite alpha_op_eval in H2; eauto. congruence.
    + remember (omap (op_eval E) Y); intros. symmetry in Heqo.
      assert (omap (op_eval E') Y' = o).
      erewrite omap_agree_2; eauto.
      intros. symmetry.
      eapply alpha_op_eval; eauto.
      destruct o.
      * pextern_step; try congruence.
        -- right; eapply alphaSim_sim; econstructor; eauto using envCorr_update.
        -- right; eapply alphaSim_sim; econstructor; eauto using envCorr_update.
      * pno_step.
  - case_eq (op_eval E e); intros.
    case_eq (val2bool v); intros.
    pone_step. erewrite <- alpha_op_eval; eauto.
    right; eapply alphaSim_sim; econstructor; eauto.
    pone_step. erewrite <- alpha_op_eval; eauto.
    right; eapply alphaSim_sim; econstructor; eauto.
    pno_step; erewrite <- alpha_op_eval in def; eauto.
    congruence. congruence.
  - pone_step. right; eapply alphaSim_sim.
    econstructor; eauto.
    eapply PIR2_app; eauto.
    eapply PIR2_get; eauto with len.
    + intros. inv_get. econstructor; eauto.
Qed.
