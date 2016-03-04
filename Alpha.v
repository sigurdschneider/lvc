Require Import Util Map Env EnvTy Exp IL AllInRel Bisim Computable.

Import F.

Set Implicit Arguments.
Unset Printing Records.

(** * Alpha Equivalence *)

Inductive alpha : env var -> env var -> stmt -> stmt -> Prop :=
| alpha_return ra ira e e'
  : alpha_exp ra ira e e'  -> alpha ra ira (stmtReturn e) (stmtReturn e')
| alpha_goto ra ira l X Y
  : length X = length Y
    -> (forall n x y, get X n x -> get Y n y -> alpha_exp ra ira x y)
    -> alpha ra ira (stmtApp l X) (stmtApp l Y)
| alpha_assign ra ira x y e e' s s'
  : alpha_exp ra ira e e'
  -> alpha (ra[x<-y]) (ira[y <- x]) s s' -> alpha ra ira (stmtLet x e s) (stmtLet y e' s')
| alpha_if ra ira e e' s s' t t'
  : alpha_exp ra ira e e'
  -> alpha ra ira s s'
  -> alpha ra ira t t'
  -> alpha ra ira (stmtIf e s t) (stmtIf e' s' t')
| alpha_extern ra ira x y f Y Y' s s'
  : length Y = length Y'
  -> (forall n x y, get Y n x -> get Y' n y -> alpha_exp ra ira x y)
  -> alpha (ra[x<-y]) (ira[y <- x]) s s'
  -> alpha ra ira (stmtExtern x f Y s) (stmtExtern y f Y' s')
| alpha_let ra ira F F' t t'
  : length F = length F'
    -> (forall n Zs Zs', get F n Zs -> get F' n Zs' -> length (fst Zs) = length (fst Zs'))
    -> (forall n Zs Zs', get F n Zs -> get F' n Zs'
                   -> alpha (ra [ fst Zs <-- fst Zs']) (ira [ fst Zs' <-- fst Zs ]) (snd Zs) (snd Zs'))
    -> alpha ra ira t t' -> alpha ra ira (stmtFun F t) (stmtFun F' t').

(** ** Morphisims *)
(** These properties are requires because we do not assume functional extensionality. *)

Global Instance alpha_morph
 : Proper ((@feq _ _ _eq) ==> (@feq _ _ _eq) ==> eq ==> eq ==> impl) alpha.
Proof.
  unfold respectful, Proper, impl; intros; subst.
  general induction H3; econstructor; eauto using alpha_exp_morph.
  - eapply IHalpha.
    + rewrite H0; reflexivity.
    + rewrite H1; reflexivity.
  - eapply IHalpha.
    + rewrite H1; reflexivity.
    + rewrite H2; reflexivity.
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
  intros. general induction H; simpl in * |- *; eauto using alpha, alpha_exp_agree_on_morph.
  - econstructor; intros; eauto.
    eapply alpha_exp_agree_on_morph; eauto.
    eapply agree_on_incl; eauto.
    eapply lookup_set_incl; try now intuition; eauto using get_list_union_map.
    eapply agree_on_incl; eauto using get_list_union_map.
  - econstructor.
    eapply alpha_exp_agree_on_morph; eauto using agree_on_incl, lookup_set_union_incl.
    eapply IHalpha; eauto.
    + eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      hnf; intros. eapply lookup_set_spec. intuition.
      cset_tac; eqs. eapply lookup_set_spec in H4; eauto.
      destruct H4; dcr. eexists x0.
      lud; split; eqs; cset_tac; intuition.
    + eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
  - econstructor; eauto.
    + eapply alpha_exp_agree_on_morph; eauto using agree_on_incl, lookup_set_union_incl.
    + eapply IHalpha1; eauto using agree_on_incl, lookup_set_union_incl.
    + eapply IHalpha2; eauto using agree_on_incl, lookup_set_union_incl.
  - econstructor; eauto.
    + intros. eapply alpha_exp_agree_on_morph; eauto.
      eapply agree_on_incl; eauto.
      eapply lookup_set_incl; try now intuition.
      rewrite get_list_union_map; eauto. eapply incl_right.
      eapply agree_on_incl; eauto using get_list_union_map.
    + eapply IHalpha.
      * eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
        lset_tac. eexists x0.
        lud; split; eqs; cset_tac; intuition.
      * eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
  - econstructor; eauto.
    + intros.
      eapply H2; eauto.
      * eapply update_with_list_agree; eauto using length_eq_sym.
        eapply agree_on_incl; eauto.
        hnf; intros. eapply lookup_set_spec. intuition.
        cset_tac. eapply lookup_set_spec in H9. destruct H9; dcr.
        exists x. cset_tac. left. eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        rewrite H11 in H10.
        eapply lookup_set_update_not_in_Z'_not_in_Z in H10.
        cset_tac; intuition. intuition. eapply H0; eauto.
        eauto.
        rewrite H11 in H10. eapply lookup_set_update_not_in_Z' in H10.
        rewrite <- H10; eauto. intuition. symmetry. eapply H0; eauto.
      * eapply update_with_list_agree; eauto.
        eapply agree_on_incl; eauto. eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    + eapply IHalpha; eauto using agree_on_incl, lookup_set_union_incl.
Qed.

(** ** Properties *)

Lemma inverse_on_list_union {X} `{OrderedType X} {Y} (f:X->Y) (g:Y->X) L
  : (forall n D, get L n D -> inverse_on D f g)
  -> inverse_on (list_union L) f g.
Proof.
  intros. hnf; intros. exploit list_union_get. eapply H1.
  destruct X0; dcr. eapply H0; eauto. cset_tac; intuition.
Qed.

(** *** [ϱ] and [ϱ'] are inverses of each other on the free variables of [s] *)
Lemma alpha_inverse_on  ϱ ϱ' s t
  : alpha ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros A. general induction A; simpl; eauto using alpha_exp_inverse_on.
  + hnf; intros.
    edestruct (list_union_get (List.map Exp.freeVars X)) as [[? []]|]; eauto; dcr.
    edestruct map_get_4; eauto; dcr.
    edestruct get_length_eq; eauto. subst.
    eapply alpha_exp_inverse_on; eauto.
    inv i.
  + eapply inverse_on_union;
    eauto using inverse_on_dead_update, alpha_exp_inverse_on.
  + eapply inverse_on_union; try eapply inverse_on_union; eauto using alpha_exp_inverse_on.
  + eapply inverse_on_union; eauto using inverse_on_dead_update.
    hnf; intros.
    edestruct (list_union_get (List.map Exp.freeVars Y)) as [[? []]|]; eauto; dcr.
    edestruct map_get_4; eauto; dcr; subst.
    edestruct get_length_eq; try eapply H; eauto.
    eapply alpha_exp_inverse_on; eauto.
    inv i.
  + eapply inverse_on_union; eauto.
    eapply inverse_on_list_union.
    intros. inv_map H3.
    edestruct (get_length_eq _ H4 H); eauto.
    eapply update_with_list_inverse_on; try eapply (H2 _ _ _ H4 H6); eauto.
Qed.

Lemma alpha_inverse_on_agree f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t
  -> inverse_on (freeVars s) f g
  -> agree_on _eq (freeVars s) f ϱ
  -> alpha f g s t.
Proof.
  intros. eapply alpha_agree_on_morph; eauto.
  symmetry in H1.
  eapply inverse_on_agree_on_2; eauto; try now intuition.
  - eapply inverse_on_agree_on; eauto; try intuition.
  - eapply alpha_inverse_on in H.
    eapply inverse_on_agree_on; try eassumption; try intuition.
    eapply inverse_on_agree_on_2; eauto; try intuition.
Qed.


(** *** Reflexivity *)

Lemma alpha_refl s
  : alpha id id s s.
Proof.
  sind s; destruct s; eauto using alpha, alpha_exp_refl.
  - econstructor. eapply alpha_exp_refl.
    rewrite update_id; eauto.
  - constructor; eauto using lookup_id.
    + intros. get_functional; subst; eauto using alpha_exp_refl.
  - econstructor; eauto.
    + intros. get_functional; subst; eauto using alpha_exp_refl.
    + rewrite update_id; eauto.
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
  intros. general induction H; eauto using alpha, length_eq_sym, alpha_exp_sym.
  - econstructor; intros; eauto.
    symmetry; eauto.
Qed.

(** *** Transitivity *)

Lemma alpha_trans ϱ1 ϱ1' ϱ2 ϱ2' s s' s''
  : alpha ϱ1 ϱ1' s s' -> alpha ϱ2 ϱ2' s' s'' -> alpha (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H; invt alpha; eauto using alpha_exp_trans, alpha.
  - econstructor; eauto. etransitivity; eauto.
    intros. edestruct (get_length_eq _ H2 H); eauto.
    eapply alpha_exp_trans; eauto.
  - econstructor; eauto using alpha_exp_trans.
    specialize (IHalpha _ _ _ H9).
    eapply alpha_inverse_on in H0.
    eapply alpha_inverse_on_agree; eauto.
    eapply inverse_on_comp; eauto. eapply alpha_inverse_on; eauto.
    symmetry. eapply lookup_set_agree_on_comp. intuition.
    eapply inverse_on_update_lookup_set. intuition. eauto.
  - econstructor; eauto. congruence.
    + intros. edestruct (get_length_eq _ H3 H); eauto.
      eapply alpha_exp_trans; eauto.
    + specialize (IHalpha _ _ _ H12).
      eapply alpha_inverse_on in H1.
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
  general induction LC; simpl. destruct X,Y; eauto.
  inversion LC'. subst x0 XL0 X. inv LC''.
  simpl in *; injection LL; injection H2; intros.
  rewrite <- H0 in H3. rewrite <- H in H1. erewrite EC'; eauto.
  eapply envCorr_update; eauto.
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

Lemma alpha_exp_eval : forall ra ira e e' E E',
  alpha_exp ra ira e e' ->
  envCorr ra ira E E' ->
  exp_eval E e = exp_eval E' e'.
Proof.
  intros. general induction H; simpl in *; eauto.
  - erewrite IHalpha_exp; eauto.
  - erewrite IHalpha_exp1, IHalpha_exp2; eauto.
Qed.

Inductive alphaSim : F.state -> F.state -> Prop :=
 | alphaSimI ra ira s s' L L' E E'
  (AE:alpha ra ira s s')
  (EA:PIR2 approx L L')
  (EC:envCorr ra ira E E')
   : alphaSim (L, E, s) (L', E', s').

Lemma alphaSim_sim σ1 σ2
: alphaSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2; cofix; intros.
  destruct H; inversion AE; subst ra0 ira0; simpl in * |- *;
  try subst s s'; simpl in * |- *.
  - no_step. simpl. eapply alpha_exp_eval; eauto.
  - destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    decide (length Zb = length Y).
    case_eq (omap (exp_eval E) X); intros.
    + edestruct PIR2_nth; eauto; dcr. inv H4.
      simpl in *.
      one_step; simpl; try congruence; eauto.
      erewrite omap_agree_2; eauto. intros. symmetry.
      eapply alpha_exp_eval. eapply H0; eauto; eauto. hnf; intros; eauto.
      simpl. eapply alphaSim_sim; econstructor; eauto using PIR2_drop.
      eapply envCorr_update_list; eauto. exploit omap_length; eauto.
      rewrite map_length. congruence.
    + no_step. erewrite omap_agree_2 in H1; try eapply H.
      erewrite H1 in def. congruence.
      intros. eapply alpha_exp_eval. eapply H0; eauto. eauto.
    + edestruct PIR2_nth; eauto; dcr. inv H3.
      no_step. simpl in *.
      get_functional; subst. simpl in *. congruence.
      get_functional; subst. simpl in *. congruence.
    + no_step; eauto. edestruct PIR2_nth_2; eauto; dcr. eauto.
  - case_eq (exp_eval E e); intros.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    no_step.
    erewrite alpha_exp_eval in H1; eauto. congruence.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto.
    no_step; erewrite <- alpha_exp_eval in def; eauto.
    congruence. congruence.
  - remember (omap (exp_eval E) Y); intros. symmetry in Heqo.
    assert (omap (exp_eval E') Y' = o).
    erewrite omap_agree_2; eauto.
    intros. symmetry.
    eapply alpha_exp_eval. eapply H0; eauto; eauto. hnf; intros; eauto.
    destruct o.
    extern_step.
    + eexists; split. econstructor; eauto. congruence.
      eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    + eexists; split. econstructor; eauto. congruence.
      eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    + no_step.
  - one_step. eapply alphaSim_sim.
    econstructor; eauto.
    eapply PIR2_app; eauto.
    eapply PIR2_get.
    + intros. unfold mkBlocks in *. inv_mapi H3. inv_mapi H4.
      econstructor; eauto.
    + unfold mkBlocks, mapi; repeat rewrite mapi_length; eauto.
Qed.
