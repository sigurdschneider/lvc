Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec CSetNotation Util.
Require Export Sets SetInterface SetConstructs SetProperties Get.

Create HintDb cset discriminated.

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

Lemma Is_true_eq_right_eq x
  :  x = true <-> x.
Proof.
  destruct x; firstorder.
Qed.

Lemma Is_true_eq_left_eq x
  :  true = x <-> x.
Proof.
  destruct x; firstorder.
Qed.

Lemma Is_not_true_eq_right_eq x
  :  x = false <-> (x -> False).
Proof.
  destruct x; firstorder.
Qed.

Lemma Is_not_true_eq_left_eq x
  :  false = x <-> (x -> False).
Proof.
  destruct x; firstorder.
Qed.

Lemma eq_incl X `{OrderedType X} (s t:set X)
  : t [=] s -> s ⊆ t /\ t ⊆ s.
Proof.
  rewrite double_inclusion; eauto.
Qed.

  Ltac cset_assumption :=
    match goal with
    | [ H : Add ?x ?s ?t |- _ ] => rewrite (Add_Equal x s t) in H
    | [ H : context [ In _ (union ?s ?t) ] |- _ ] =>
      not_ignored H; setoid_rewrite (union_iff s t _) in H
      | [ H : context [ In _ (diff ?s ?t) ] |- _ ] =>
        not_ignored H; setoid_rewrite (diff_iff s t) in H
      | [ |- context [ In _ (diff ?s ?t) ] ] =>
        setoid_rewrite (diff_iff s t)
      | [ H : context [ In _ (add ?s ?t) ] |- _ ] =>
        not_ignored H; setoid_rewrite (add_iff t s) in H
      | [ H : context [ In _ (inter ?s ?t) ] |- _ ] =>
        not_ignored H; setoid_rewrite (inter_iff s t _) in H
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
          | [ H'' : x === y -> False |- _ ] => fail 1
          | [ H'' : y === x -> False |- _ ] => fail 1
          | [ H'' : y =/= x |- _ ] => fail 1
          | [ H'' : y === x |- _ ] => fail 1
          | [ |- _ ] => decide(x === y)
        end

      | [ H : context [ In _ empty ] |- _ ] =>
        not_ignored H; setoid_rewrite empty_iff in H
      | [ |- context [ In _ empty ] ] =>
        setoid_rewrite empty_iff

      | [ H : context [ In _ (add _ empty) ] |- _ ] =>
        not_ignored H; setoid_rewrite In_add_empty in H
      | [ |- context [ In _ (add _ empty) ] ] =>
        setoid_rewrite In_add_empty
      | [ H : context [ In _ (singleton _) ] |- _ ] =>
        not_ignored H; setoid_rewrite In_single in H
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
      | [ H: Empty ?s, H' : ?a ∈ ?s |- _ ] => destruct (H a H')
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
        not_ignored H; setoid_rewrite not_In_single in H
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
        not_ignored H; setoid_rewrite (singleton_iff y x) in H
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
      | [ H : context [ InA _ ?x ?l ] |- _ ] => setoid_rewrite <- of_list_1 in H
      | [ |- context [ InA _ ?x ?l ] ] => setoid_rewrite <- of_list_1
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
      | [ H : ?s [=] ?t |- _ ] =>
        first [ match goal with
                | [ _ : s ⊆ t |- _ ] =>
                  match goal with
                  | [ _ : t ⊆ s |- _ ] => idtac
                  | _ => let I := fresh "eq_incl" in destruct (eq_incl _ _ _ H) as [I _]
                  end
                end
              | match goal with
                | [ _ : t ⊆ s |- _ ] => let I := fresh "eq_incl" in destruct (eq_incl _ _ _ H) as [_ I]
                end
              | let I := fresh "eq_incl" in let I' := fresh "eq_incl" in destruct (eq_incl _ _ _ H) as [I I']
              ]; eapply protect in H
      | [ H : ?s ⊆ ?t |- _ ] => unfold Subset in H
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

  Smpl Create cset.
  Smpl Add cset_assumption : cset.

  Ltac cset_tac_step f :=
    intros; (try subst); dcr; destr; mycleartrivial; (try (smpl cset));
    (try (f tt)); (try bool_to_prop); (try (bool_to_prop in *)); mycleartrivial.

  Ltac cset_tac_step_A f := eauto using get; cset_tac_step f.
  Ltac cset_tac_step_B f := ((repeat (cset_tac_step_A f)) || intuition (cset_tac_step_A f)).

  Ltac set_tac f := repeat (cset_tac_step_B f; repeat clear_dup_fast).

  Ltac cset_tac' := set_tac idtac.
  Ltac cset_tac := solve [ cset_tac' ].

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


Smpl Add
     match goal with
     | [ |- @Equivalence.equiv
             _ (@_eq _ (@SOT_as_OT _ (@eq _) _))
             (@OT_Equivalence _ (@SOT_as_OT _ (@eq _) _))
             ?x ?y ] => hnf
     | [ H : @Equivalence.equiv
               _ (@_eq _ (@SOT_as_OT _ (@eq _) _))
               (@OT_Equivalence _ (@SOT_as_OT _ (@eq _) _))
               ?x ?y |- _ ] => hnf in H; clear_trivial_eqs
     | [ H1 : ?a === ?f ?y, H2 : ?f ?x === ?a -> False,
                               H3 : ?x === ?y, PR : Proper (_ ==> _) ?f |- _ ]
       => exfalso; eapply H2; rewrite H1, H3; reflexivity
     | [ H1 : ?y === ?a -> False, H2 : ?x === ?a, H3 : ?x === ?y |- _ ] =>
       exfalso; eapply H1; rewrite <- H2, H3; reflexivity
     | [ H1 : ?y === ?a -> False, H2 : ?x === ?a, H3 : ?y === ?x |- _ ] =>
       exfalso; eapply H1; rewrite <- H2, H3; reflexivity
     end : cset.

Smpl Add
     match goal with
     | [ |- ?a ∈ filter ?p ?lv ] => eapply filter_iff; [eauto|]
     | [ H : context [ ?a ∈ filter ?p ?lv ] |- _ ] => setoid_rewrite filter_iff in H; [|eauto]
     | [ H : (if [?P] then true else false) = true |- _ ] => cases in H
     | [ |- (if [?P] then true else false) = true ] => cases
     | [ |- (@Equivalence.equiv ?X (@_eq ?X ?H) (@OT_Equivalence ?X ?H) ?x ?a) \/ _ ] =>
       decide (@Equivalence.equiv X (@_eq X H) (@OT_Equivalence X H) x a);
         [ left; assumption | right ]
     | [ H : Is_true (?p ?x),
             H' : @Equivalence.equiv ?X (@_eq ?X ?H) (@OT_Equivalence ?X ?H) ?x ?a,
                  PR: Proper (@_eq ?X ?H ==> eq) ?p |- ?p ?a = true] => rewrite <- H'
     | [ H : Is_true (?p ?x),
             H' : @Equivalence.equiv ?X (@_eq ?X ?H) (@OT_Equivalence ?X ?H) ?x ?a,
                  PR: Proper (@_eq ?X ?H ==> eq) ?p |- Is_true (?p ?a)] => rewrite <- H'
     | [ H : Is_true (?p ?x),
             H' : @Equivalence.equiv ?X (@_eq ?X ?H) (@OT_Equivalence ?X ?H) ?a ?x,
                  PR: Proper (@_eq ?X ?H ==> eq) ?p |- Is_true (?p ?a)] => rewrite H'
     | [ H : Is_true (?p ?a), H'' : Is_true (?p ?x) -> False,
             H' : @Equivalence.equiv ?X (@_eq ?X ?H) (@OT_Equivalence ?X ?H) ?x ?a,
                    PR: Proper (@_eq ?X ?H ==> eq) ?p |- _ ] => exfalso; eapply H''; rewrite H'; eauto
     | [ H : _ = true |- _ ] => eapply Is_true_eq_left in H
     end : cset.

Smpl Add match goal with
         | [ H : ?x ∈ map ?f ?s |- _ ] =>
           rewrite (map_iff f) in H; destruct H as [? [? ?]]
         | [ H : context [ _ ∈ map ?f _ ] |- _ ] =>
           rewrite (map_iff f) in H
         | [ |- context [ _ ∈ map ?f _ ] ] =>
           rewrite (map_iff f)
         end : cset.

Lemma premise_and_to_impl X (P Q R: X -> Prop)
  :(forall x, P x /\ Q x -> R x)
    <-> (forall x, P x -> Q x -> R x).
Proof.
  firstorder.
Qed.

Lemma premise_or_to_two X (P Q R: X -> Prop)
  :(forall x, P x \/ Q x -> R x)
    <-> ((forall x, P x -> R x) /\ (forall x, Q x -> R x)).
Proof.
  firstorder.
Qed.

Lemma conclusion_and_to_two X (P Q R: X -> Prop)
  : (forall x, P x -> Q x /\ R x)
    <-> ((forall x, P x -> Q x) /\ (forall x, P x -> R x)).
Proof.
  split.
  - intros Incl; split; intros; exploit Incl; cset_tac.
  - cset_tac.
Qed.

Lemma conclusion_or_to_two X (P Q R: X -> Prop)
  : (forall x, P x -> Q x \/ R x)
    -> ((forall x, P x -> (R x -> False) -> Q x) /\ (forall x, P x -> (Q x -> False) -> R x)).
Proof.
  split; intros; edestruct H; eauto; exfalso; eauto.
Qed.

Lemma exists_to_forall X (P:X->Prop) (Q:Prop)
  : ((exists x, P x) -> Q) <-> (forall x, P x -> Q).
Proof.
  firstorder.
Qed.

Smpl Add 70 match goal with
         | [ H : forall _, _ -> _ /\ _ |- _ ] =>
           rewrite conclusion_and_to_two in H;
             let I := fresh H in destruct H as [H I]
         | [ H : forall _, _ \/ _ -> _ |- _ ] =>
           rewrite premise_or_to_two in H;
             let I := fresh H in destruct H as [H I]
         | [ H : (exists x, @?P x) -> ?Q |- _ ] => setoid_rewrite (@exists_to_forall _ P Q) in H
         end : cset.

Smpl Add 71 match goal with
         | [ H : forall _, _ /\ _ -> _ |- _ ] => rewrite premise_and_to_impl in H
         | [ H : forall _, _  -> _ \/ _ |- _ ] => eapply conclusion_or_to_two in H
         end : cset.

Smpl Add 120 match goal with
            | [ H : ?x ∈ ?s, H' : forall y, _ ∈ ?s -> @?P y |- _ ] =>
              let P' := eval cbv beta in (P x) in
                  lazymatch goal with
                  | [ H : P' |- _ ] => fail
                  | _ =>
                    record_instance H' x;
                    let H'' := fresh H' in pose proof (H' x H) as H''
                  end
            end : cset.


Lemma P_P_False_False (P:Prop)
  : P -> ((P -> False) <-> False).
Proof.
  firstorder.
Qed.

Lemma P_P_True (P:Prop)
  : P -> (P <-> True).
Proof.
  firstorder.
Qed.

Lemma equiv_True X (x:X)
  : x === x <-> True.
Proof.
  firstorder.
Qed.

Lemma True_or_left (P:Prop)
  : True \/ P <-> True.
Proof.
  firstorder.
Qed.

Lemma True_or_right (P:Prop)
  : True \/ P <-> True.
Proof.
  firstorder.
Qed.

Lemma True_and_left (P:Prop)
  : True /\ P <-> P.
Proof.
  firstorder.
Qed.

Lemma True_and_right (P:Prop)
  : P /\ True <-> P.
Proof.
  firstorder.
Qed.

Lemma P_or_False_right P
: (P \/ False) <-> P.
Proof.
  intuition.
Qed.

Lemma P_or_False_left P
: (False \/ P) <-> P.
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

Lemma de_morgan_dec {A} `{Computable A} {B} `{Computable B}
: not (A /\ B) <-> (not A \/ not B).
Proof.
  decide A; decide B; intuition.
Qed.

Lemma de_morgan_dec' {A} `{Computable A} {B} `{Computable B}
: (A /\ B -> False) <-> ((A -> False) \/ (B -> False)).
Proof.
  decide A; decide B; intuition.
Qed.

Lemma dneg_dec {A} `{Computable A}
: not (not A) <-> A.
Proof.
  decide A; intuition.
Qed.

Lemma dneg_dec' {A} `{Computable A}
  : ((A -> False) -> False) <-> A.
Proof.
  decide A; intuition.
Qed.


Smpl Add 50
     match goal with
     | [ H : ?x ∈ ?s |- context [?x ∈ ?s -> False ] ] => rewrite (@P_P_False_False _ H)
     | [ H : ?x ∈ ?s, H' : context [?x ∈ ?s -> False ] |- _ ] => rewrite (@P_P_False_False _ H) in H'
     | [ H : ?x ∈ ?s |- context [?x ∈ ?s] ] => rewrite (@P_P_True _ H)
     | [ H : ?x ∈ ?s, H' : context [?x ∈ ?s] |- _ ] => rewrite (@P_P_True _ H) in H'
     | [ |- context [ ?x === ?x ] ] => rewrite (@equiv_True _ x)
     | [ H : context [ ?x === ?x ] |- _ ] => rewrite (@equiv_True _ x) in H
     | [ |- context [ True \/ _ ] ] => setoid_rewrite True_or_left
     | [ H : context [ True \/ _ ] |- _ ] => setoid_rewrite True_or_left in H
     | [ |- context [ _ \/ True ] ] => setoid_rewrite True_or_right
     | [ H : context [ _ \/ True ] |- _ ] => setoid_rewrite True_or_right in H
     | [ |- context [ True /\ _ ] ] => setoid_rewrite True_and_left
     | [ H : context [ True /\ _ ] |- _ ] => setoid_rewrite True_and_left in H
     | [ |- context [ _ /\ True ] ] => setoid_rewrite True_and_right
     | [ H : context [ _ /\ True ] |- _ ] => setoid_rewrite True_and_right in H
     | [ |- context [ _ \/ False ] ] => setoid_rewrite P_or_False_right
     | [ H : context [ _ \/ False ] |- _ ] => setoid_rewrite P_or_False_left in H
     | [ |- context [ False \/ _ ] ] => setoid_rewrite P_or_False_right
     | [ H : context [ False \/ _ ] |- _ ] => setoid_rewrite P_or_False_left in H
     | [ |- context [ not (_ \/ _) ] ] => setoid_rewrite not_or_dist
     | [ H : context [ not (_ \/ _) ] |- _ ] => setoid_rewrite not_or_dist in H
     | [ |- context [ not False ] ] => setoid_rewrite not_False_is_True
     | [ H : context [ not False ] |- _ ] => setoid_rewrite not_False_is_True in H
     | [ |- context [ not (not _) ] ] => setoid_rewrite dneg_dec
     | [ H : context [ not (not (_)) ] |- _ ] => setoid_rewrite dneg_dec in H
     | [ |- context [ (_ -> False) -> False ] ] => setoid_rewrite dneg_dec
     | [ H : context [ (_ -> False) -> False ] |- _ ] => setoid_rewrite dneg_dec' in H
     | [ |- context [ not (_ /\ _) ] ] => setoid_rewrite de_morgan_dec
     | [ H : context [ not (_ /\ _) ] |- _ ] => setoid_rewrite de_morgan_dec in H
     | [ |- context [ (_ /\ _) -> False ] ] => rewrite de_morgan_dec'
     | [ H : context [ (_ /\ _) -> False ] |- _ ] => rewrite de_morgan_dec in H
     | [ H : False -> _ |- _ ] => clear H
     | [ H : _ -> True |- _ ] => clear H
     | [ H : context [ _ = true ] |- _ ] => setoid_rewrite Is_true_eq_right_eq in H
     | [ |- context [ _ = true ] ] => setoid_rewrite Is_true_eq_right_eq
     | [ H : context [ true = _ ] |- _ ] => setoid_rewrite Is_true_eq_left_eq in H
     | [ |- context [ true = _] ] => setoid_rewrite Is_true_eq_left_eq
     | [ H : context [ _ = false ] |- _ ] => setoid_rewrite Is_not_true_eq_right_eq in H
     | [ |- context [ _ = false ] ] => setoid_rewrite Is_not_true_eq_right_eq
     | [ H : context [ false = _ ] |- _ ] => setoid_rewrite Is_not_true_eq_left_eq in H
     | [ |- context [ false = _] ] => setoid_rewrite Is_not_true_eq_left_eq
     end : cset.

(*
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

      | [ H : (?x ∈ ?s -> False) -> False |- _ ] =>
        lazymatch goal with
        | [ H : x ∈ s |- _ ] => fail
        | [ H : x ∉ s |- _ ] => fail
        | [ H : x ∈ s -> False |- _ ] => fail
        | _ => decide (x ∈ s)
        end
*)

Smpl Add
     match goal with
     | [ |- ?a ∈ ?s \/ _ ] =>
       lazymatch goal with
       | [ H : a ∉ s |- _ ] => right
       | [ H : a ∈ s -> False |- _ ] => right
       | _ => decide (a ∈ s); [ left; eassumption | right ]
       end
     | [ |- _ \/ ?a ∈ ?s ] =>
       lazymatch goal with
       | [ H : a ∉ s |- _ ] => left
       | [ H : a ∈ s -> False |- _ ] => left
       | _ => decide (a ∈ s); [ right; eassumption | left ]
       end
     | [ |- ?P \/ ?Q ] =>
       match P with
       | context [ ?a ∈ ?s ] =>
         match Q with
         | context [ a ∈ s -> False ] => decide (a ∈ s)
         end
       | context [ ?a === ?b ] =>
         match Q with
         | context [ a === b -> False ] => decide (a === b)
         end
       | context [ ?a ∈ ?s -> False ] =>
         match Q with
         | context [ a ∈ s ] => decide (a ∈ s)
         end
       | context [ ?a === ?b -> False ] =>
         match Q with
         | context [ a === b ] => decide (a === b)
         end
       | context [ ?A -> False ] =>
         match Q with
         | context [ A ] => decide A
         end
       | context [ ?A ] =>
         match Q with
         | context [ A -> False ] => decide A
         end
       end

(*     | [ |- ?a ∈ ?s ] =>
       lazymatch goal with
       | [ H : a ∉ s |- _ ] => exfalso
       | [ H : a ∈ s -> False |- _ ] => exfalso
       | _ => decide (a ∈ s); [ eassumption | exfalso ]
       end*)
(*
    match goal with
    | [ |- exists _, _ ] =>
      match goal with
        [ |- ?P ] => decide P; [ eassumption| exfalso]
      end
    end
*)
     end : cset.
