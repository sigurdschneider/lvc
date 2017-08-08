Require Import List Map Env AllInRel Exp AppExpFree Filter LengthEq.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import SpillSound SpillUtil.
Require Import Slot SetUtil.


(** * DoSpill *)

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

Lemma slot_lift_params_length (slot:var -> var) RM Z
      (NoDup:NoDupA eq Z)
  : ❬slot_lift_params slot RM Z❭ = ❬Z❭ + cardinal (of_list Z ∩ (fst RM ∩ snd RM)).
Proof.
  general induction NoDup; simpl.
  - assert ({} ∩ (fst RM ∩ snd RM) [=] {}) by (clear; cset_tac).
    rewrite H. eauto.
  - cases; simpl.
    + rewrite cap_special_in; eauto. rewrite IHNoDup; eauto.
      rewrite add_cardinal_2; eauto. cset_tac.
    + cases; simpl; rewrite cap_special_notin; eauto.
Qed.

Lemma of_list_slot_lift_params (slot:var -> var) R M (Z:params)
      (Incl:of_list Z ⊆ R ∪ M)
  : of_list (slot_lift_params slot (R, M) Z)
            [=] of_list Z \ (M \ R)
            ∪ map slot (of_list Z \ (R \ M)).
Proof.
  intros. general induction Z; simpl in *.
  - cset_tac.
  - assert (of_list Z [<=] R ∪ M /\ a ∈ R ∪ M) by (revert Incl; clear_all; cset_tac).
    cases; simpl.
    + rewrite IHZ; eauto; clear IHZ Incl.
      assert (a ∉ R \ M) by cset_tac.
      assert ({a; of_list Z} \ (R \ M) [=] {a; of_list Z \ (R \ M)})
        by (revert H0; clear_all; cset_tac).
      rewrite H1. clear H1. rewrite map_add; eauto.
      clear H. cset_tac.
    + cases; simpl; rewrite IHZ; eauto; clear IHZ.
      * assert ({a; of_list Z} \ (R \ M) [=] of_list Z \ (R \ M)) by cset_tac.
        rewrite H0. clear H0. clear H Incl. cset_tac.
      * assert ({a; of_list Z} \ (R \ M) [=] {a; of_list Z \ (R \ M)}) by cset_tac.
        rewrite H0. clear H0. rewrite map_add; eauto.
        clear Incl. cset_tac.
Qed.

Lemma InA_slot_lift_params VD RM Z (slot:Slot VD) x
      (In:InA eq x (slot_lift_params slot RM Z))
  : InA _eq x Z \/ exists y, InA _eq y Z /\ x = slot y.
Proof.
  general induction Z; simpl in *; isabsurd.
  cases in In.
  - inv In; eauto.
    inv H0; eauto.
    edestruct IHZ; dcr; eauto.
  - cases in In; eauto.
    * inv In; eauto.
      edestruct IHZ; dcr; eauto.
    * inv In; eauto.
      edestruct IHZ; dcr; eauto.
Qed.

Lemma Slot_absurd VD x
      (slot:Slot VD) (EQ:slot x = x)
      (In: x ∈ VD)
  : False.
Proof.
  eapply (@Slot_Disj _ slot x); eauto. cset_tac.
Qed.

Lemma NoDupA_slot_lift_params VD R M Z (slot:Slot VD)
      (ND:NoDupA eq Z) (Incl:R ∪ M ⊆ VD)
      (Incl2: of_list Z ⊆ VD)
  : NoDupA _eq (slot_lift_params slot (R,M) Z).
Proof.
  general induction ND; eauto using NoDupA.
  simpl slot_lift_params. cases.
  - econstructor.
    + intro A. inv A.
      * eapply Slot_absurd; eauto. cset_tac.
      * eapply InA_slot_lift_params in H1.
        destruct H1; dcr; eauto; subst.
        rewrite InA_in in H2. simpl in *.
        eapply (@Slot_Disj _ slot (slot x0)); eauto;
          cset_tac.
    + econstructor.
      * intro A.
        eapply InA_slot_lift_params in A.
        rewrite InA_in in A. simpl in *.
        destruct A; dcr.
        -- eapply (@Slot_Disj _ slot (slot x));
             eauto; cset_tac.
        -- eapply Slot_Inj in H3; eauto.
           cset_tac. cset_tac. cset_tac.
      * eapply IHND; eauto.
        simpl in *. cset_tac.
  - cases.
    + econstructor; eauto.
      * intro A. eapply InA_slot_lift_params in A.
        destruct A; dcr; eauto; subst.
        rewrite InA_in in H2. simpl in *.
        eapply (@Slot_Disj _ slot (slot x0)); eauto;
          cset_tac.
      * eapply IHND; eauto. simpl in *. cset_tac.
    + econstructor; eauto.
      * intro A. eapply InA_slot_lift_params in A.
        destruct A; dcr; eauto; subst.
        -- rewrite InA_in in H0. simpl in *.
           eapply (@Slot_Disj _ slot (slot x)); eauto;
             cset_tac.
        -- simpl in *.
           eapply Slot_Inj in H3; eauto.
           cset_tac. cset_tac.
           rewrite <- Incl2.
           eapply in_add_right.
           eapply InA_in. eauto.
      * eapply IHND; eauto.
        simpl in *. cset_tac.
Qed.


Lemma slp_union_incl
      (s t VD : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  :
    injective_on VD slot
    -> s ⊆ VD
    -> t ⊆ VD
    -> of_list Z ⊆ VD
    -> (s ∩ of_list Z) ∪ (map slot t ∩ map slot (of_list Z))
                      ⊆ of_list (slot_lift_params slot (s,t) Z)
.
Proof.
  intros inj_VD s_VD t_VD Z_VD.
  induction Z; simpl in *; eauto.
  - rewrite map_empty; eauto. cset_tac.
  - apply add_incl in Z_VD as [a_VD Z_VD].
    specialize (IHZ Z_VD).
    decide (a ∈ s ∩ t).
    + apply inter_iff in i as [a_s a_t].
      apply union_incl_split; simpl; eauto.
      * rewrite <- IHZ.
        clear; cset_tac.
      * rewrite lookup_set_add; eauto.
        rewrite <- IHZ. unfold lookup_set.
        clear; cset_tac.
    + decide (a ∈ s).
      * assert (a ∉ t ∩ {a; of_list Z}) as an_tZ by cset_tac.
        assert (map slot t ∩ map slot {a; of_list Z}
                    ⊆ map slot t ∩ map slot (of_list Z)) as elim_a. {
          rewrite lookup_set_add; eauto.
          unfold lookup_set.
          assert (forall (u v : ⦃var⦄) (x : var),
                     u ∩ {x; v} ⊆ (u ∩ v) ∪ (u ∩ singleton x))
            as demo by (clear; cset_tac).
          rewrite demo. apply union_incl_split.
          - reflexivity.
          - rewrite <- map_singleton; eauto.
            rewrite <- injective_on_map_inter; eauto.
            + assert (t ∩ singleton a [=] ∅) as ta_empty
                  by (revert an_tZ; clear_all; cset_tac).
              rewrite ta_empty.
              rewrite map_empty; eauto.
              clear; cset_tac.
            + clear - a_VD; cset_tac.
        }
        rewrite elim_a.
        simpl.
        rewrite <- IHZ.
        clear; cset_tac.
      * assert (a ∉ s ∩ {a; of_list Z}) as an_sZ by cset_tac.
        assert (s ∩ {a; of_list Z} ⊆ s ∩ (of_list Z)) as elim_a. {
          hnf; intros. decide (a0 = a).
          + subst a0. contradiction.
          + cset_tac'. destruct H1; eauto.
        }
        rewrite elim_a; simpl.
        rewrite <- IHZ.
        rewrite lookup_set_add; eauto. unfold lookup_set.
        clear; cset_tac.
Qed.


Lemma slp_union_minus_incl
      (s t VD : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  : injective_on VD slot
    -> s ⊆ VD
    -> t ⊆ VD
    -> of_list Z ⊆ VD
    -> (s ∪ map slot t) \ of_list (slot_lift_params slot (s,t) Z)
               ⊆ s \ of_list Z ∪ map slot t \ map slot (of_list Z)
.
Proof.
  intros.
  rewrite <- slp_union_incl with (s:=s); eauto.
  unfold lookup_set. cset_tac.
Qed.
