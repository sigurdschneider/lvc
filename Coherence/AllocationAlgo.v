Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map Status.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh Sim MoreList.
Require Import Coherence Allocation.

Set Implicit Arguments.

Section ParametricDualFold.
  Variables A X Y : Type.
  Hypothesis f : A -> X -> Y -> status A : Type.

  Fixpoint dfold (a:A) (L:list X) (L':list Y) : status A :=
    match L, L' with
      | x::L, y::L' => sdo a' <- f a x y;
                      dfold a' L L'
      | nil, nil => Success a
      | _, _ => Error "dfold: argument list size mismatch"
    end.
End ParametricDualFold.

Arguments dfold [A] [X] [Y] f a L L'.

Fixpoint linear_scan (st:stmt) (an: ann (set var)) (ϱ:var -> var)
  : status (var -> var) :=
 match st, an with
    | stmtExp x e s, ann1 lv ans =>
      let xv := least_fresh (lookup_set ϱ (getAnn ans\{{x}})) in
        linear_scan s ans (ϱ[x<- xv])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- linear_scan s ans ϱ;
        linear_scan t ant ϱ'
    | stmtGoto _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtExtern x f Y s, ann1 lv ans =>
      let xv := least_fresh (lookup_set ϱ (getAnn ans\{{x}})) in
      linear_scan s ans (ϱ[x<- xv])
    | stmtLet Z s t, ann2 _ ans ant =>
      let Z' := fresh_list least_fresh (lookup_set ϱ (getAnn ans\of_list Z)) (length Z) in
      sdo ϱ' <- linear_scan s ans (ϱ[Z <-- Z']);
        linear_scan t ant ϱ'
    | _, _ => Error "linear_scan: Annotation mismatch"
  end.


Hint Extern 10 (agree_on _ _?a ?a) => reflexivity.

Lemma linear_scan_ssa_agree' i s al ϱ ϱ' LV alv G
      (sd:ssa s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (G \ (snd (getAnn al) \ fst (getAnn al))) ϱ ϱ'.
Proof.
  general induction LS; inv sd; simpl in * |- *; try monadS_inv allocOK; eauto.
  - exploit IHLS; eauto.
    rewrite H8 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv. eapply X.
    instantiate (1:=G).
    pose proof (ssa_incl H7); eauto. rewrite H8 in H1. simpl in *.
    revert H4 H1; clear_all; cset_tac; intuition.
    invc H. specialize (H1 a). cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H11 in X. rewrite H12 in X0. simpl in *.
    etransitivity; eapply agree_on_incl; eauto.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
  - exploit IHLS; eauto.
    rewrite H9 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv. eapply X.
    instantiate (1:=G).
    pose proof (ssa_incl H8); eauto. rewrite H9 in H1. simpl in *.
    revert H5 H1; clear_all; cset_tac; intuition.
    invc H. specialize (H1 a). cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H9 in X. rewrite H12 in X0. simpl in *.
    etransitivity; try eapply X0.
    eapply agree_on_incl. eapply update_with_list_agree_inv; try eapply X; eauto.
    rewrite fresh_list_length; eauto.
    instantiate (1:=G). rewrite <- H7.
    pose proof (ssa_incl H8); eauto. rewrite H9 in H2. simpl in *.
    revert H5 H2; clear_all; cset_tac; intuition; eauto.
    specialize (H2 a). specialize (H3 a). cset_tac; intuition.
    eapply agree_on_incl; eauto. instantiate (1:=G).
    rewrite <- H7. clear_all; cset_tac; intuition; eauto.
Qed.

Lemma linear_scan_ssa_agree i s al ϱ ϱ' LV alv
      (sd:ssa s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) ϱ ϱ'.
Proof.
  general induction LS; inv sd; simpl in * |- *; try monadS_inv allocOK; eauto.
  - exploit IHLS; eauto.
    rewrite H8 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv; eauto. cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H11 in X. rewrite H12 in X0. simpl in *.
    etransitivity; eauto.
  - exploit IHLS; eauto.
    rewrite H9 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv; eauto. cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H9 in X. rewrite H12 in X0. simpl in *.
    etransitivity; try eapply X0.
    eapply agree_on_incl. eapply update_with_list_agree_inv; try eapply X; eauto.
    rewrite fresh_list_length; eauto.
    revert H5; clear_all; cset_tac; intuition; eauto.
Qed.

Hint Extern 10 (Subset ?a (_ ∪ ?a)) => eapply incl_right.

Lemma locally_inj_live_agree s ϱ ϱ' ara alv LV
      (LS:live_sound Functional LV s alv)
      (sd: ssa s ara)
      (inj: locally_inj ϱ s alv)
      (agr: agree_on eq (snd (getAnn ara)) ϱ ϱ')
      (incl:getAnn alv ⊆ fst (getAnn ara))
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction inj; invt ssa; invt live_sound; simpl in *.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H8; simpl; eauto.
      rewrite H8; simpl.
      revert H13 incl; clear_all; cset_tac; intuition.
      specialize (H13 a). decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H7; eauto.
      rewrite H8 in *.
      simpl in *. rewrite incl in H13.
      revert H13 X; clear_all; cset_tac; intuition.
      specialize (X a); specialize (H13 a); cset_tac; intuition; eauto.
      decide (x === a); eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H9; simpl; eauto.
      rewrite H9; simpl.
      revert H14 incl; clear_all; cset_tac; intuition.
      specialize (H14 a). decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H8; eauto.
      rewrite H9 in *.
      simpl in *. rewrite incl in H14.
      revert H14 X; clear_all; cset_tac; intuition.
      specialize (X a); specialize (H14 a); cset_tac; intuition; eauto.
      decide (x === a); eauto.
  - econstructor; eauto.
    eapply IHinj1; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; try eapply H7; eauto. rewrite H8 in X. simpl in *.
    rewrite H8; simpl. rewrite <- H6. cset_tac; intuition.
    rewrite H8; simpl. rewrite <- incl. rewrite <- H19.
    clear_all; cset_tac; intuition.
    eapply IHinj2; eauto.
    eapply agree_on_incl; eauto.
    rewrite H11. simpl. rewrite <- H6. cset_tac; intuition.
    rewrite H11; simpl. rewrite <- incl. rewrite <- H20. reflexivity.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H7; eauto. rewrite H8 in X. simpl in *.
      rewrite <- H6. rewrite <- X, <- incl, <- H19.
      clear_all; cset_tac; intuition.
      decide (a ∈ of_list Z); eauto.
Qed.

Lemma linear_scan_correct (ϱ:var->var) LV s alv ϱ' al
      (LS:live_sound Functional LV s alv)
      (inj:injective_on (getAnn alv) ϱ)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:ssa s al)
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction LS; simpl in *; try monadS_inv allocOK; invt ssa;
    eauto 10 using locally_inj, injective_on_incl.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_incl.
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eauto.
    + rewrite H8. simpl in *. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a); eauto. left; eapply H0; cset_tac; intuition.
    + exploit linear_scan_ssa_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H8 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv. eapply X0.
      revert H4 incl; clear_all; cset_tac; intuition. invc H0. eauto.
      exploit locally_injective; eauto.
      eapply injective_on_agree; try eapply X0.
      Focus 2.
      eapply agree_on_incl; eauto. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a). intuition.
      left. eapply H0; eauto. cset_tac; intuition.
      eapply injective_on_incl.
      eapply injective_on_fresh; eauto.
      Focus 2.
      eapply least_fresh_spec.
      eapply injective_on_incl; eauto.
      cset_tac; intuition.
  - exploit linear_scan_ssa_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_ssa_agree; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H11 in X. rewrite H12 in X0.
    simpl in *.
    exploit IHLS1; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
    eapply injective_on_incl; eauto.
    eapply injective_on_agree; eauto using agree_on_incl.
    rewrite H12; simpl. rewrite <- incl; eauto.
    econstructor; eauto.
    assert (agree_on eq D ϱ ϱ'). etransitivity; eauto.
    eapply injective_on_agree; eauto. eauto using agree_on_incl.
    eapply locally_inj_live_agree. eauto. eauto. eauto.
    rewrite H11; simpl; eauto.
    exploit linear_scan_ssa_agree'; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H12 in X3. simpl in *. instantiate (1:=Ds) in X3.
    eapply agree_on_incl. eapply X3.
    revert H6; clear_all; cset_tac; intuition. specialize (H6 a). intuition.
    rewrite H11; simpl. rewrite <- incl; eauto.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_incl.
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eauto.
    + rewrite H9. simpl in *. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a); eauto. left; eapply H0; cset_tac; intuition.
    + exploit linear_scan_ssa_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv. eapply X0.
      revert H5 incl; clear_all; cset_tac; intuition. invc H0. eauto.
      exploit locally_injective; eauto.
      eapply injective_on_agree; try eapply X0.
      Focus 2.
      eapply agree_on_incl; eauto. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a). intuition.
      left. eapply H0; eauto. cset_tac; intuition.
      eapply injective_on_incl.
      eapply injective_on_fresh; eauto.
      Focus 2.
      eapply least_fresh_spec.
      eapply injective_on_incl; eauto.
      cset_tac; intuition.
  - simpl in *.
    exploit linear_scan_ssa_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_ssa_agree; try eapply EQ0; simpl; eauto using live_sound.
    exploit IHLS1; eauto.
    + eapply injective_on_incl.
      instantiate (1:=getAnn als \ of_list Z ++ of_list Z).
      eapply injective_on_fresh_list; eauto.
      eapply injective_on_incl; eauto.
      rewrite fresh_list_length; eauto.
      eapply fresh_list_spec. eapply least_fresh_spec.
      eapply fresh_list_unique, least_fresh_spec.
      clear_all; cset_tac; intuition.
      decide (a ∈ of_list Z); intuition.
    + rewrite H9. simpl. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition.
      decide (a ∈ of_list Z); intuition.
    + assert (injective_on lv ϱ').
      eapply injective_on_incl.
      eapply injective_on_agree; try eapply inj; eauto.
      etransitivity.
      eapply agree_on_incl.
      eapply update_with_list_agree_inv; try eapply X; eauto.
      rewrite fresh_list_length; eauto.
      rewrite H9; simpl. rewrite incl.
      revert H5; clear_all; cset_tac; intuition; eauto.
      eapply agree_on_incl; eauto. rewrite H12; simpl; eauto. reflexivity.
      exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
      * eapply injective_on_incl.
        eapply injective_on_agree; try eapply inj; eauto.
        eapply agree_on_incl.
        eapply update_with_list_agree_inv; try eapply X; eauto.
        rewrite fresh_list_length; eauto.
        rewrite H9; simpl. rewrite incl.
        revert H5; clear_all; cset_tac; intuition; eauto. eauto.
      * rewrite H12. simpl. simpl in *. rewrite <- incl. eauto.
      * econstructor; eauto.
        eapply locally_inj_live_agree; eauto.
        rewrite H9. simpl.
        eapply agree_on_incl.
        eapply linear_scan_ssa_agree'; try eapply EQ0; eauto.
        rewrite H12; simpl. instantiate (1:=Ds).
        revert H6; clear_all; cset_tac; intuition eauto.
        specialize (H6 a); intuition.
        rewrite H9. simpl. rewrite <- incl.
        revert H0; clear_all; cset_tac; intuition.
        specialize (H0 a). cset_tac; intuition.
        decide (a ∈ of_list Z); intuition.
        eapply injective_on_incl. instantiate (1:=(getAnn als \ of_list Z) ∪ of_list Z).
        eapply injective_on_agree with (ϱ:=(ϱ [Z <--
         fresh_list least_fresh (lookup_set ϱ (getAnn als \ of_list Z))
           (length Z)])).
        eapply injective_on_fresh_list; eauto using injective_on_incl.
        rewrite fresh_list_length; eauto.
        eapply fresh_list_spec. eapply least_fresh_spec.
        eapply fresh_list_unique. eapply least_fresh_spec.
        etransitivity. eapply agree_on_incl; eauto.
        rewrite H9; simpl. rewrite H0, incl. cset_tac; intuition.
        eapply agree_on_incl.
        exploit linear_scan_ssa_agree'; try eapply EQ0; simpl; eauto using live_sound.
        rewrite H12; simpl. instantiate (1:=D ++ of_list Z).
        exploit ssa_incl; try eapply H8. rewrite H9 in X3; simpl in *.
        rewrite H0. rewrite incl.
        revert X3 H6; clear_all; cset_tac; intuition.
        specialize (X3 a); specialize (H6 a); cset_tac; intuition.
        clear_all; cset_tac; intuition. decide (a ∈ of_list Z); eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
