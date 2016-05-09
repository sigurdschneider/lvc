Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec CSetNotation Util.
Require Export Sets SetInterface SetConstructs SetProperties Get.

Lemma In_add_empty {X} `{OrderedType X} x y
  : In x (add y empty) <-> x === y.
Proof.
  rewrite add_iff. split; firstorder.
  exfalso. eapply empty_iff; eauto.
Qed.

Lemma In_single {X} `{OrderedType X} x y
  : In x (singleton y) <-> y === x.
Proof.
  split.
  - eapply singleton_1.
  - eapply singleton_2.
Qed.

Lemma not_In_add_empty {X} `{OrderedType X} x y
  : ~In x (add y empty) <-> x =/= y.
Proof.
  rewrite add_iff. split; firstorder.
  intro; firstorder. eapply empty_iff; eauto.
Qed.

Lemma not_In_single {X} `{OrderedType X} x y
  : ~In x (singleton y) <-> y =/= x.
Proof.
  split; intros B; intro A; eapply B; clear B; eapply In_single; eauto.
Qed.

Lemma not_in_empty {X} `{OrderedType X} (x:X)
: x ∉ ∅.
Proof.
  hnf; intros. eapply empty_iff in H0; eauto.
Qed.

Lemma de_morgan_dec {A} `{Computable A} {B} `{Computable B}
: not (A /\ B) <-> (not A \/ not B).
Proof.
  decide A; decide B; intuition.
Qed.

Lemma dneg_dec {A} `{Computable A}
: not (not A) <-> A.
Proof.
  decide A; intuition.
Qed.

Lemma P_or_False P
: (P \/ False) <-> P.
Proof.
  intuition.
Qed.

Lemma not_or_dist A B
: not (A \/ B) <-> not A /\ not B.
Proof.
  intuition.
Qed.

Lemma not_False_is_True
: not False <-> True.
Proof.
  intuition.
Qed.

Lemma and_True_away_right A
: A /\ True <-> A.
Proof.
  intuition.
Qed.

Lemma and_True_away_left A
: True /\ A <-> A.
Proof.
  intuition.
Qed.

Lemma of_list_app X `{OrderedType X} (A B: list X)
  : of_list (A ++ B) [=] of_list A ∪ of_list B.
Proof.
  split; intros H0.
  - rewrite of_list_1 in H0. eapply InA_app in H0.
    eapply union_iff. repeat rewrite of_list_1. intuition.
  - rewrite of_list_1. eapply InA_app_iff.
    eapply union_iff in H0.
    repeat rewrite of_list_1 in H0. intuition.
Qed.

  Ltac cset_assumption :=
    match goal with
      | [ H : context [ In _ (union ?s ?t) ] |- _ ] =>
        setoid_rewrite (union_iff s t _) in H
      | [ H : context [ In _ (diff ?s ?t) ] |- _ ] =>
        setoid_rewrite (diff_iff s t) in H
      | [ |- context [ In _ (diff ?s ?t) ] ] =>
        setoid_rewrite (diff_iff s t)
      | [ H : context [ In _ (add ?s ?t) ] |- _ ] =>
        setoid_rewrite (add_iff t s) in H
      | [ H : context [ In _ (inter ?s ?t) ] |- _ ] =>
        setoid_rewrite (inter_iff s t _) in H
      | [ H : context [ (?P \/ False) ] |- _ ] =>
        setoid_rewrite (P_or_False P) in H
      | [ |- context [ (?P \/ False) ] ] =>
        setoid_rewrite (P_or_False P)
      | [ H : context [ not (_ \/ _) ] |- _ ] =>
        setoid_rewrite not_or_dist in H
      | [ |- context [ not (_ \/ _) ] ] =>
        setoid_rewrite not_or_dist
      | [ |- context [ In _ (add ?s ?t) ] ] =>
        setoid_rewrite (add_iff t s)
(*      | [ H : context [ member ?x (minus ?s ?t) ] |- _ ] =>
        rewrite (minus_spec _ s t x) in H
      | [ H : context [ member ?x empty ] |- _ ] =>
        rewrite (empty_spec _ x) in H *)
(*      | [ H : context [ member ?x empty ] |- _ ] =>
        rewrite (not_In_add_empty _ x) in H *)
      | [ H : In ?x ?s, H' : ~In ?x ?s |- _ ] => exfalso; eapply H'; eapply H
      | [ H : In ?x ?s, H' : ~In ?y ?s |- _ ] =>
        match goal with
          | [ H'' : x =/= y |- _ ] => fail 1
          | [ H'' : x === y |- _ ] => fail 1
          | [ H'' : ~x === y |- _ ] => fail 1
          | [ H'' : ~y === x |- _ ] => fail 1
          | [ H'' : y =/= x |- _ ] => fail 1
          | [ H'' : y === x |- _ ] => fail 1
          | [ |- _ ] => decide(x === y)
        end
      | [ H : context [ not False ] |- _ ] =>
        setoid_rewrite not_False_is_True in H
      | [ |- context [ not False ] ] =>
        setoid_rewrite not_False_is_True

      | [ H : context [ In _ empty ] |- _ ] =>
        setoid_rewrite empty_iff in H
      | [ |- context [ In _ empty ] ] =>
        setoid_rewrite empty_iff

      | [ H : context [ _ /\ True ] |- _ ] =>
        setoid_rewrite and_True_away_right in H
      | [ |- context [ _ /\ True ] ] =>
        setoid_rewrite and_True_away_right
      | [ H : context [ True /\ _ ] |- _ ] =>
        setoid_rewrite and_True_away_left in H
      | [ |- context [ True /\ _ ] ] =>
        setoid_rewrite and_True_away_left

      | [ H : context [ In _ (add _ empty) ] |- _ ] =>
        setoid_rewrite In_add_empty in H
      | [ |- context [ In _ (add _ empty) ] ] =>
        setoid_rewrite In_add_empty
      | [ H : context [ In _ (singleton _) ] |- _ ] =>
        setoid_rewrite In_single in H
      | [ |- context [ In _ (singleton _) ] ] =>
        setoid_rewrite In_single
(*      | [ H : context [ Is_true (@member _ _ ?x (@single _ ?y)) ] |- _ ] =>
        rewrite (@single_spec _ _ x y) in H *)
(*      | [ H : @eq_cset _ _ ?s ?t, H' : not (Is_true (@member _ _ ?x ?s))
        |- not (Is_true (@member _ _ ?x ?t)) ] => rewrite <- H; eauto
      | [ H : @eq_cset _ _ ?t ?s, H' : not (Is_true (@member _ _ ?x ?s))
        |- not (Is_true (@member _ _ ?x ?t)) ] => rewrite H; eauto
      | [ |- not ?Q ] => intro
      | [ |- ?P = ?Q ] => match type of P with
                            | bool => eapply bool_extensionality; intros
(*                          | cset _ => eapply set_extensionality; intros *)
                          end
*)
    (* goal *)
      | [ |- context [ In _ (union ?s ?t) ]] =>
        setoid_rewrite (union_iff s t _)
(*      | [ |- @eq_cset _ _ _ _ ] => unfold eq_cset; intro
      | [ H : @eq_cset _ _ ?s ?t, H' : Is_true (member ?x ?s)
        |- Is_true (member ?x ?t) ] => rewrite <- H; eauto
      | [ H : @eq_cset _ _ ?t ?s, H' : Is_true (member ?x ?s)
        |- Is_true (member ?x ?t) ] => rewrite H; eauto
      | [ |- context [ @member _ _ ?x (@meet _ _ ?s ?t) ]] =>
        rewrite (@intersection_spec _ _ s t x)
      | [ |- context [ @member _ _ ?x empty ]] =>
        rewrite (@empty_spec _ _ x)
      | [ |- context [ Is_true (@member _ _ ?x (@single _ ?y)) ]] =>
        rewrite (@single_spec _ _ x y) *)
      | [ H : ?x === ?y, H' : In ?x ?s, H'' : ~In ?y ?s |- _ ] =>
        now (exfalso; rewrite H in H'; eauto)
      | [ H : ?x === ?y, H' : In ?y ?s, H'' : ~In ?x ?s |- _ ] =>
        now (exfalso; rewrite <- H in H'; eauto)
      | [ H : ?x === ?y, H' : In ?y ?s |- In ?x ?s ] =>
        now (rewrite H; eauto)
      | [ H : ?y === ?x, H' : In ?y ?s |- In ?x ?s ] =>
        now (rewrite <- H; eauto)
      | [ H : ?x === ?y, H' : In ?y ?s |- (In ?x ?s) \/ _ ] =>
        now (left; rewrite H; eauto)
      | [ H : ?y === ?x, H' : In ?y ?s |- (In ?x ?s) \/ _ ] =>
        now (left; rewrite <- H; eauto)
      | [ H : ?x === ?y, H' : In ?y ?s |- _ \/ (In ?x ?s) ] =>
        now (right; rewrite H; eauto)
      | [ H : ?y === ?x, H' : In ?y ?s |- _ \/ (In ?x ?s) ] =>
        now (right; rewrite <- H; eauto)
      | [ H : ?s === ?s', H' : In ?x ?s' |- (In ?x ?s) \/ _ ] =>
        now (left; rewrite H; eauto)
      | [ H : ?s === ?s', H' : In ?x ?s |- (In ?x ?s') \/ _ ] =>
        now (left; rewrite <- H; eauto)
      | [ H : ?s === ?s', H' : In ?y ?s' |- _ \/ (In ?x ?s) ] =>
        now (right; rewrite H; eauto)
      | [ H : ?s === ?s', H' : In ?y ?s |- _ \/ (In ?x ?s') ] =>
        now (right; rewrite <- H; eauto)
      | [ H : ?s === ?s', H' : In ?y ?s' |- In ?x ?s ] =>
        now (rewrite H; eauto)
      | [ H : ?s === ?s', H' : In ?y ?s |- In ?x ?s' ] =>
        now (rewrite <- H; eauto)
      | [ H : ?x === ?y, H' : ~In ?y ?s |- ~In ?x ?s ] =>
        now (rewrite H; eauto)
      | [ H : ?y === ?x, H' : ~In ?y ?s |- ~In ?x ?s ] =>
        now (rewrite <- H; eauto)
      | [ |- context [ In _ (diff ?s ?t) ] ] =>
        setoid_rewrite (diff_iff s t)
      | [ |- context [ In _ (inter ?s ?t) ] ] =>
        setoid_rewrite (inter_iff s t)
      | [ |- ?s [=] ?t] => intro
      | [ |- complement _ _ _ ] => intro
      | [ H : ?x =/= ?y |- ~In ?x (add ?y empty) ] =>
        now (rewrite not_In_add_empty; eauto)
      | [ |- context [~In ?x (add ?y empty)] ] =>
        setoid_rewrite (not_In_add_empty x y)
      | [ |- context [~In _ (singleton _)] ] =>
        setoid_rewrite (not_In_single)
      | [ H : context [~In _ (singleton _)] |- _ ] =>
        setoid_rewrite not_In_single in H
      | [ |- context [In ?x (add ?y empty)] ] =>
        setoid_rewrite (In_add_empty x y)
      | [ |- context [In ?x empty] ] =>
        setoid_rewrite (empty_iff x)
      | [ |- context [ ~In ?x empty ] ] =>
        setoid_rewrite (empty_iff x)
      | [ |- _ ⊆ _ ] => hnf; intros
      | [ |- context [ In ?x (diff ?s ?t) ]] =>
        intros
      | [ |- context [ In ?x (singleton ?y) ]] =>
        setoid_rewrite (singleton_iff y x)
      | [ H : context [ In ?x (singleton ?y) ] |- _ ] =>
        setoid_rewrite (singleton_iff y x) in H
      | [ |- context [ In ?y (add ?x ?s) ]] =>
        setoid_rewrite (add_iff s x y )
      | [ H : context [ In ?y (add ?x ?s) ] |- _ ] =>
        setoid_rewrite (add_iff s x y ) in H
      | [ H : ?A [=] ∅ |- _ ] =>
        assert (A ⊆ ∅);
          [ let H := fresh "H" in
            edestruct (double_inclusion A ∅) as [[H ?] ?]; eauto| clear H]
      | [ H : ?A ⊆ ∅ |- _ ] =>
        assert (forall a, a ∈ A -> False);[
            let a := fresh "a" in let C := fresh "H" in
                                  intros a C;
                                    eapply (@not_in_empty _ _ a (H _ C))| clear H]
      | [ |- ?a ∈ ?s \/ ( _ /\ ?a ∉ ?s) ] =>
        lazymatch goal with
          | [ H : a ∈ s |- _ ] => fail
          | [ H : a ∉ s |- _ ] => fail
          | [ H : a ∈ s -> False |- _ ] => fail
          | _ => decide (a ∈ s)
        end
      | [ |- ?a ∈ ?s \/ ( _ /\ (?a ∈ ?s -> False) ) ] =>
        lazymatch goal with
        | [ H : a ∈ s |- _ ] => fail
        | [ H : a ∉ s |- _ ] => fail
        | [ H : a ∈ s -> False |- _ ] => fail
        | _ => decide (a ∈ s)
        end
      | [ |- ( _ /\ (?a ∈ ?s -> False) \/ ?a ∈ ?s) ] =>
        lazymatch goal with
        | [ H : a ∈ s |- _ ] => fail
        | [ H : a ∉ s |- _ ] => fail
        | [ H : a ∈ s -> False |- _ ] => fail
        | _ => decide (a ∈ s)
        end
      | [ H: (not ?A) -> False |- ?A ] => try now (eapply dneg_dec; intuition)
      | [ H : context [ InA _ ?x ?l ] |- _ ] => setoid_rewrite <- of_list_1 in H
      | [ |- context [ InA _ ?x ?l ] ] => setoid_rewrite <- of_list_1
      | [ H : (?x ∈ ?s -> False) -> False |- _ ] =>
        lazymatch goal with
        | [ H : x ∈ s |- _ ] => fail
        | [ H : x ∉ s |- _ ] => fail
        | [ H : x ∈ s -> False |- _ ] => fail
        | _ => decide (x ∈ s)
        end
      | [ INCL: ?s1 ⊆ ?s2, NINCL : ~ ?t1 ⊆ ?t2 |- _ ] =>
        match s1 with
        | t1 =>
          match s2 with
          | t2 => exfalso; eapply NINCL, INCL
          | _ => match goal with
                | [ H : s2 [=] t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H; eapply INCL
                | [ H : t2 [=] s2 |- _ ] => exfalso; eapply NINCL; rewrite H; eapply INCL
                | [ H : s2 ⊆ t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H; eapply INCL
                end
          end
        | _ => match goal with
              | [ H1 : s1 [=] t1 |- _ ] =>
                match s2 with
                | t2 => exfalso; eapply NINCL; rewrite <- H1; eapply INCL
                | _ => match goal with
                      | [ H : s2 [=] t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, <- H; eapply INCL
                      | [ H : t2 [=] s2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, H; eapply INCL
                      | [ H : s2 ⊆ t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, <- H; eapply INCL
                      end
                end
              | [ H1 : t1 [=] s1 |- _ ] =>
                match s2 with
                | t2 => exfalso; eapply NINCL; rewrite H1;  INCL
                | _ => match goal with
                      | [ H : s2 [=] t2 |- _ ] => exfalso; eapply NINCL; rewrite H1, <- H; eapply INCL
                      | [ H : t2 [=] s2 |- _ ] => exfalso; eapply NINCL; rewrite H1, H; eapply INCL
                      | [ H : s2 ⊆ t2 |- _ ] => exfalso; eapply NINCL; rewrite H1, <- H; eapply INCL
                      end
                end
              | [ H1 : s1 ⊆ t1 |- _ ] =>
                match s2 with
                | t2 => exfalso; eapply NINCL; rewrite <- H1; eapply INCL
                | _ => match goal with
                      | [ H : s2 [=] t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, <- H; eapply INCL
                      | [ H : t2 [=] s2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, H; eapply INCL
                      | [ H : s2 ⊆ t2 |- _ ] => exfalso; eapply NINCL; rewrite <- H1, <- H; eapply INCL
                      end
                end
              end
        end
      | [ H : ?s [=] ?t |- _ ] => unfold Equal in H
    end.

  Ltac mycleartrivial :=
    try (progress (clear_trivial_eqs;
              match goal with
                | [ H : @Equivalence.equiv _
                                           (@_eq _ (@SOT_as_OT _ (@eq _) nat_OrderedType))
                                           (@OT_Equivalence _ (@SOT_as_OT _ (@eq _) nat_OrderedType))
                                           ?a ?b |- _ ] =>
                  is_var a; is_var b; invc H; clear_trivial_eqs
              end)).

  Ltac cset_tac_step f :=
    intros; (try subst); decompose records; destr; mycleartrivial; (try cset_assumption);
    (try (f tt)); (try bool_to_prop); (try (bool_to_prop in *)); mycleartrivial.

  Ltac set_tac f :=
    repeat ((repeat (eauto using get; cset_tac_step f))
            || intuition (eauto using get; cset_tac_step f)).

  Ltac cset_tac := set_tac idtac.

Hint Extern 9 =>
     match goal with
       | [ H : ?x === ?y, H' : In ?x ?s, H'' : ~In ?y ?s |- _ ] =>
        now (exfalso; rewrite H in H'; eauto)
       | [ H : ?x === ?y, H' : In ?y ?s, H'' : ~In ?x ?s |- _ ] =>
         now (exfalso; rewrite <- H in H'; eauto)
     end.

Hint Extern 10 => match goal with
                   | [ H : ?x ∈ ?s, H' : ?y ∈ ?s -> False, H'' : ?y === ?x |- _ ] => exfalso; eapply H'; rewrite H''; eapply H
                   | [ H : ?x ∈ ?s, H' : ?y ∈ ?s -> False, H'' : ?x === ?y |- _ ] => exfalso; eapply H'; rewrite <- H''; eapply H
                 end.

(*Hint Extern 20 (incl ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).*)
Hint Extern 20 (Subset ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).
Hint Extern 20 (Equal ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).

Ltac srewrite s :=
  match goal with
  | [ H : s [=] _ |- _ ] => rewrite H
  | [ H : _ [=] s |- _ ] => rewrite <- H
  end.
