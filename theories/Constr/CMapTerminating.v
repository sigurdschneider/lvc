Require Import CMap CMapDomain CMapPartialOrder Infra.PartialOrder Terminating.

Lemma terminating_Dom_eq_add_some X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (T:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : forall (y : Y) m p,
    find x m === ⎣ y ⎦ ->
    terminates poLt (exist (fun X0 : Map [X, Y] => domain X0 [<=] {x; U}) m p).
Proof.
  intros y m pr FEQ.
  pose proof (TRM y).
  revert dependent m.
  induction H1; intros.

  assert (RD:domain (remove x m) ⊆ U). {
    rewrite domain_remove; eauto. cset_tac.
  }
  specialize (T (exist _ (remove x m) RD)).
  remember_arguments T. revert dependent m.
  induction T; intros; clear_trivial_eqs.

  econstructor; intros [m' d'] [LE1 LE2]. simpl in *.

  decide (poLt (find x m) (find x m')).
  - rewrite FEQ in p. destruct p as [p1 p2]. inv p1.
    eapply H2; eauto.
    split; eauto. rewrite <- H6 in *. clear_trivial_eqs.
    intro; eapply p2; eauto. econstructor; eauto.
    rewrite H6; eauto.
  - assert (RD':domain (remove x m') ⊆ U). {
      rewrite domain_remove; eauto. cset_tac.
    }
    eapply H4; try reflexivity. instantiate (1:=RD').
    split; simpl.
    + eapply leMap_remove; eauto.
    + intro.
      specialize (LE1 x).
      eapply not_poLt_poLe_poEq in n; eauto.
      eapply LE2.
      hnf; intros.
      decide (x1 === x).
      * rewrite e. symmetry in n; eauto.
      * specialize (H5 x1). lud.
        rewrite !MapFacts.remove_neq_o in H5; eauto.
    + specialize (LE1 x).
      rewrite FEQ in *.
      inv LE1.  econstructor.
      eapply poLe_antisymmetric; eauto.
      decide (y ⊑ x0); eauto.
      exfalso. eapply n.
      rewrite <- H6. split; try econstructor. eauto.
      intro. eapply n0. inv H5. rewrite H10. eauto.
Qed.

Lemma terminating_Dom_eq_add_none X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (TA:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : forall m p,
    find x m = None ->
    terminates poLt (exist (fun X0 : Map [X, Y] => domain X0 [<=] {x; U}) m p).
Proof.
  intros m pr FEQ.
  assert (RD:domain m ⊆ U). {
    eapply not_find_domain in FEQ. cset_tac.
  }
  pose proof (TA (exist _ m RD)) as T.
  remember_arguments T. revert dependent m.
  induction T; intros; clear_trivial_eqs.

  econstructor; intros [m' d'] [LE1 LE2]. simpl in *.

  decide (poLt (find x m) (find x m')).
  - rewrite FEQ in p. destruct p as [p1 p2].
    case_eq (find x m').
    + intros.
      eapply terminating_Dom_eq_add_some; eauto.
      rewrite H3; eauto.
    + intros.
      assert (RD':domain m' ⊆ U). {
        eapply not_find_domain in H3. cset_tac.
      }
      eapply H2; eauto. instantiate (1:=RD').
      split; eauto.
  - pose proof (LE1 x) as LE1x.
    eapply not_poLt_poLe_poEq in n; eauto.
    rewrite FEQ in n. inv n.
    symmetry in H3.
    assert (RD':domain m' ⊆ U). {
      eapply not_find_domain in H3. cset_tac.
    }
    eapply H2; eauto.
    + instantiate (1:=RD'). split; simpl; eauto.
Qed.

Instance terminating_Dom_eq_add X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (T:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : Terminating ({ X : Map [X, Y] | domain X ⊆ {x; U} }) poLt.
Proof.
  hnf; intros [m d].
  case_eq (find x m).
  - intros.
    eapply terminating_Dom_eq_add_some; eauto.
    rewrite H1; eauto.
  - intros.
    eapply terminating_Dom_eq_add_none; eauto.
Qed.

Lemma terminates_bound_inv X `{OrderedType X} Y `{PartialOrder Y} (P P':Map [X, Y] -> Prop)
      (IMPL: forall x, P' x -> P x )
      (x: Map [X, Y]) (px:P x) (py:P' x)
  : terminates (@poLt { x : Map [X, Y] | P x } _ ) (exist _ x px)
    -> terminates (@poLt { x : Map [X, Y] | P' x } _ ) (exist _ x py).
Proof.
  intros T.
  general induction T.
  econstructor; intros [] [LE1 LE2]; simpl in *.
  eapply H2; eauto. instantiate (1:=IMPL x p).
  split; eauto.
Qed.

Instance terminating_bound_inv X `{OrderedType X} Y `{PartialOrder Y} (P P':Map [X, Y] -> Prop)
      (IMPL: forall x, P' x -> P x )
  : Terminating ({ x : Map [X, Y] | P x }) poLt
    -> Terminating ({ x : Map [X, Y] | P' x }) poLt.
Proof.
  intros T. hnf; intros [x p].
  eapply terminates_bound_inv; eauto.
  Unshelve. eauto.
Qed.


Instance terminating_Dom X `{OrderedType X} Y `{PartialOrder Y} U
      (TRM:Terminating Y poLt)
  : Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt.
Proof.
  pattern U.
  eapply set_induction; intros.
  - eapply empty_is_empty_1 in H1.
    hnf; intros [m d].
    econstructor; intros [m' d'] [LE1 LE2].
    simpl in *.
    exfalso. eapply LE2. hnf; intros.
    rewrite eq_domain_find; intros. reflexivity.
    cset_tac.
  - eapply terminating_bound_inv.
    instantiate (1:=fun x0 => domain x0 ⊆ {x; s}); simpl.
    cset_tac.
    eapply terminating_Dom_eq_add; eauto.
Qed.
