Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet  Containers.SetDecide.
Require Export LengthEq MapBasics MapLookup MapUpdate.

Set Implicit Arguments.

Definition defined_on {X} `{OrderedType X} {Y} (G:set X) (E:X -> option Y)
  := forall x, x ∈ G -> exists y, E x = Some y.

Lemma defined_on_update_some X `{OrderedType X} Y (G:set X) (E:X -> option Y) x v
  : defined_on (G \ {{x}}) E
    -> defined_on G (E [x <- Some v]).
Proof.
  unfold defined_on; intros. lud.
  - eauto.
  - eapply H0; eauto. cset_tac; intuition.
Qed.

Lemma defined_on_incl X `{OrderedType X} Y (G G':set X) (E:X -> option Y)
  : defined_on G E
    -> G' ⊆ G
    -> defined_on G' E.
Proof.
  unfold defined_on; intros; eauto.
Qed.

Lemma defined_on_update_list X `{OrderedType X} Y lv (E: X -> option Y) Z vl
: length vl = length Z
  -> defined_on (lv \ of_list Z) E
  -> defined_on lv (E [Z <-- List.map Some vl]).
Proof.
  unfold defined_on; intros.
  decide (x ∈ of_list Z).
  - length_equify. clear H1.
    general induction H0; simpl in * |- *.
    + exfalso. cset_tac.
    + lud; eauto.
      eapply IHlength_eq; eauto; cset_tac; intuition.
  - edestruct H1; eauto. cset_tac.
    exists x0. rewrite <- H3.
    eapply update_with_list_no_update; eauto.
Qed.

Instance defined_on_morph_incl X `{OrderedType X} Y
  : Proper (flip Subset ==> eq ==> impl) (@defined_on X _ Y).
Proof.
  unfold Proper, respectful, impl; intros; subst.
  eapply defined_on_incl; eauto.
Qed.

Instance defined_on_morph_equal X `{OrderedType X} Y
  : Proper (Equal ==> eq ==> iff) (@defined_on X _ Y).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  eapply eq_incl in H0; dcr; split; intros; eauto using defined_on_incl.
Qed.
