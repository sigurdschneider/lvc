Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet  Containers.SetDecide MoreList.
Require Export LengthEq MapBasics MapLookup MapUpdate MapComposition.

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


Lemma defined_on_agree X `{OrderedType X} Y R D (f g:X->option Y)
  : defined_on D f
    -> agree_on (option_eq R) D f g
    -> defined_on D g.
Proof.
  intros; hnf; intros.
  edestruct H0; eauto.
  exploit H1; eauto.
  rewrite H3 in H4. inv H4. eauto.
Qed.

Lemma defined_on_agree_eq X `{OrderedType X} Y D (f g:X->option Y)
  : defined_on D f
    -> agree_on eq D f g
    -> defined_on D g.
Proof.
  intros; hnf; intros.
  edestruct H0; eauto.
  exploit H1; eauto.
  rewrite H3 in H4. inv H4. eauto.
Qed.

Lemma defined_on_union X `{OrderedType X} Y (f:X -> option Y) s t
  : defined_on s f
    -> defined_on t f
    -> defined_on (s ∪ t) f.
Proof.
  intros; hnf; intros. cset_tac.
Qed.


Inductive defined X : list (option X) -> Prop :=
| NilDefined : defined nil
| ConsDefined x xs: defined xs -> defined (Some x::xs).

Lemma defined_get X (L:list (option X)) n x
  : defined L
    -> get L n x
    -> exists y, x = Some y.
Proof.
  intros. general induction H0; invt defined; eauto.
Qed.

Lemma defined_on_update_list' X `{OrderedType X} Y (E:X -> option Y) L L' (Len:❬L❭=❬L'❭) s
  : defined_on (s \ of_list L) E
    -> defined L'
    -> defined_on s (E [L <-- L']).
Proof.
  intros.
  hnf; intros. decide (x ∈ of_list L).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr; eauto.
    rewrite H6. exploit defined_get; eauto.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply H0; cset_tac.
Qed.

Lemma get_defined X (L:list (option X))
  : (forall n x, get L n x -> exists y, x = Some y)
    -> defined L.
Proof.
  intros. general induction L; eauto using defined, get.
  edestruct H; dcr; eauto using get. subst.
  eauto using defined, get.
Qed.

Lemma defined_on_defined X `{OrderedType X} Y (V:X->option Y) L
      `{Proper _ (_eq ==> eq) V}
  : defined_on (of_list L) V
    <-> defined (V ⊝ L).
Proof.
  split; intros.
  - eapply get_defined; intros; inv_get.
    eapply get_in_of_list in H2. eauto.
  - hnf; intros.
    edestruct of_list_get_first; eauto; dcr.
    eapply defined_get; eauto.
    rewrite H4. eapply map_get_1; eauto.
Qed.

Lemma defined_on_comp X `{OrderedType X} Y (f:X->X) D (V:X -> option Y)
      `{Proper _ (_eq ==> _eq) f}  `{Proper _ (_eq ==> eq) V}
  : defined_on (map f D) V <-> defined_on D (f ∘ V).
Proof.
  split; intros; hnf; intros.
  - exploit H2; eauto with cset.
  - eapply map_iff in H3; dcr; eauto.
    setoid_rewrite H6; eauto.
Qed.
