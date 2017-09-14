Require Import List Map Envs AllInRel Exp AppExpFree Filter LengthEq.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import Slot.

Definition choose_y (slot : var -> var)
           (X : ⦃var⦄) (x:var)
           (RMapp : ⦃var⦄ * ⦃var⦄)
           (y:var) :=
  if [x ∈ X] then (* reg prefered *)
    if [y ∈ fst RMapp] then Var y
    else Var (slot y)
  else (* slot prefered *)
    if [y ∈ snd RMapp] then Var (slot y)
    else Var y.


Lemma choose_y_freeVars slot X x RM y
  : Op.freeVars (choose_y slot X x RM y) ⊆ {y; singleton (slot y)}.
Proof.
  unfold choose_y; repeat cases; simpl; cset_tac.
Qed.

Fixpoint slot_lift_args
           (slot : var -> var)
           (RM : ⦃var⦄ * ⦃var⦄)
           (RMapp : ⦃var⦄ * ⦃var⦄)
           (Y: list op) (Z : params)
  : list op
  :=
    match Y, Z with
    | e::Y, z::Z => let y := getVar e in
      if [z ∈ fst RM ∩ snd RM]
      then choose_y slot (fst RM) z RMapp y::
                    choose_y slot (snd RM) z RMapp y::
                    slot_lift_args slot RM RMapp Y Z
      else if [z ∈ fst RM]
           then choose_y slot (fst RM) z RMapp y::slot_lift_args slot RM RMapp Y Z
           else choose_y slot (snd RM) z RMapp y::slot_lift_args slot RM RMapp Y Z
    | _, _ => nil
    end.


Lemma slot_lift_args_length slot RM RMapp Y Z (Len:❬Y❭=❬Z❭)
      (NoDup:NoDupA eq Z)
  : ❬slot_lift_args slot RM RMapp Y Z❭ =
    ❬Z❭ + cardinal (of_list Z ∩ (fst RM ∩ snd RM)).
Proof.
  general induction Len; simpl; eauto.
  inv NoDup.
  repeat cases; simpl; rewrite IHLen; eauto.
  - rewrite cap_special_in; eauto.
    rewrite add_cardinal_2; eauto. cset_tac.
  - rewrite cap_special_notin; eauto.
  - rewrite cap_special_notin; eauto.
Qed.

Smpl Add match goal with
         | [ H : context [ ❬slot_lift_args ?slot ?RM ?RMapp ?Y ?Z❭ ],
             Len : ❬?Y❭ = ❬?Z❭, NoDup : NoDupA eq ?Z |- _ ]
           => rewrite (@slot_lift_args_length slot RM RMapp Y Z Len NoDup) in H
         | [ Len : ❬?Y❭ = ❬?Z❭, NoDup : NoDupA eq ?Z |-
             context [ ❬slot_lift_args ?slot ?RM ?RMapp ?Y ?Z❭ ] ]
           => rewrite (@slot_lift_args_length slot RM RMapp Y Z Len NoDup)
         end : len.

Lemma choose_y_isVar slot X y RMapp v
  :  isVar (choose_y slot X y RMapp v).
Proof.
  unfold choose_y; repeat cases; eauto using isVar.
Qed.

Lemma slot_lift_args_isVar (slot:var -> var) RM RMapp Y Z
  : (forall (n : nat) (y : op), get Y n y -> isVar y)
    -> forall (n : nat) (y : op), get (slot_lift_args slot RM RMapp Y Z) n y -> isVar y.
Proof.
  intros.
  general induction Y; destruct Z; simpl in *; isabsurd.
  exploit H; eauto using get. inv H1; simpl in *.
  repeat cases in H0; inv H0; eauto using get, choose_y_isVar.
  inv H6; eauto using get, choose_y_isVar.
Qed.

Lemma slot_lift_args_get slot RM RMapp Y Z n x
  : get (slot_lift_args slot RM RMapp Y Z) n x
    -> exists n y z X, get Y n y /\ get Z n z /\
               x = choose_y slot X z RMapp (getVar y) /\
               (X = fst RM \/ X = snd RM).
Proof.
  intros.
  general induction Y; destruct Z; isabsurd; simpl in *.
  - repeat cases in H; clear_trivial_eqs; inv H; eauto 20 using get.
    + inv H4; eauto 20 using get. eapply IHY in H5; dcr.
      eauto 20 using get.
    + eapply IHY in H4; dcr.
      eauto 20 using get.
    + eapply IHY in H4; dcr.
      eauto 20 using get.
Qed.

Lemma lifted_args_in_RL_slot_SpM
      (Y : args)
      (R M : ⦃var⦄) RM
      (slot : var -> var)
      (H5 : forall (n : nat) (y : op), get Y n y -> isVar y)
      (Sp L K M' R' : ⦃var⦄)
      (Cover : list_union (Op.freeVars ⊝ Y) ⊆ R' ∪ M')
      (M'_incl: M' ⊆ Sp ∪ M) (R'_incl : R' ⊆ (R \ K ∪ L)) Z
  : list_union (Op.freeVars ⊝ slot_lift_args slot RM (R',M') Y Z) ⊆ R ∪ L ∪ map slot (Sp ∪ M) .
Proof.
  apply list_union_incl; [|eauto with cset].
  intros; inv_get.
  eapply slot_lift_args_get in H. dcr; subst.
  exploit H5; eauto. inv H; simpl in *.
  assert (v ∈ R' ∪ M'). {
    rewrite <- Cover.
    eapply incl_list_union; eauto using get. reflexivity. simpl. cset_tac.
  }
  unfold choose_y; repeat cases; simpl in *.
  - rewrite R'_incl in COND0. revert COND0; clear. intros. cset_tac.
  - rewrite <- map_singleton; eauto.
    apply incl_union_right.
    apply lookup_set_incl; eauto.
    cset_tac.
  - rewrite <- map_singleton; eauto.
    apply incl_union_right.
    apply lookup_set_incl; eauto.
    cset_tac.
  - assert (v ∈ R') by cset_tac.
    rewrite R'_incl in H3. revert H3; clear. intros. cset_tac.
Qed.


Lemma slot_lift_args_app_expfree (slot:var -> var) RM RMapp Y Z f
  (IV : forall (n : nat) (y : op), get Y n y -> isVar y)
  : app_expfree (stmtApp f (slot_lift_args slot RM RMapp Y Z)).
Proof.
  econstructor.
  intros; inv_get; eauto using slot_lift_args_isVar.
Qed.
