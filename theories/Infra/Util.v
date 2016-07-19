Require Export List SetoidList Omega AutoIndTac Computable.

Set Implicit Arguments.

Set Regular Subst Tactic.

Tactic Notation "inv" hyp(A) := inversion A; subst.
Tactic Notation "invc" hyp(A) := inversion A; subst; clear A.
Tactic Notation "invs" hyp(A) := inversion A; subst; clear_trivial_eqs.
Tactic Notation "invcs" hyp(A) := inversion A; subst; clear A; clear_trivial_eqs.

Tactic Notation "dcr" :=
  repeat (
    match goal with
      | H: _ |- _ => progress (decompose record H); clear H
    end).

Inductive protected (P:Prop) :=
  Protected (p:P) : protected P.

Lemma protect (P:Prop) : P -> protected P.
  intros. econstructor. eauto.
Qed.

Lemma unprotect (P:Prop) : protected P -> P.
  inversion 1; eauto.
Qed.

Tactic Notation "protect" hyp(H) := apply protect in H.
Tactic Notation "unprotect" hyp(H) := apply unprotect in H.

Ltac invt ty :=
  match goal with
      | h: ty |- _ => inv h
      | h: ty _ |- _ => inv h
      | h: ty _ _ |- _ => inv h
      | h: ty _ _ _ |- _ => inv h
      | h: ty _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => inv h
  end.

Ltac invts ty :=
  match goal with
      | h: ty |- _ => invs h
      | h: ty _ |- _ => invs h
      | h: ty _ _ |- _ => invs h
      | h: ty _ _ _ |- _ => invs h
      | h: ty _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => invs h
  end.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Notation "A <=> B" := (iffT A B) (at level 95, no associativity) : type_scope.

Class Defaulted (V:Type) := {
  default_el : V
}.

Ltac eq e := assert e; eauto; subst; trivial.

Ltac crush := intros; subst; simpl in *; solve [
    eauto
  | contradiction
  | match goal with [H : ?s |- _] => now(inversion H; eauto) end
  | (constructor; eauto)
  | (constructor 2; eauto)
  | (constructor 3; eauto)
  | intuition
  ].

Tactic Notation "You are here" := fail.

(** * Reflecting boolean statements to Prop *)

Require Import Basics Containers.Tactics Morphisms Morphisms_Prop.

Lemma bool_extensionality (x y:bool)
  : (x -> y) -> (y -> x) -> x = y.
Proof.
  destruct x,y; intros; eauto. destruct H; eapply I.  destruct H0; eapply I.
Qed.

Lemma toImpl (A B: Prop)
  : (A -> B) -> impl A B.
Proof.
  eauto.
Qed.

Ltac bool_to_prop_assumption H :=
  match goal with
    | [ H : context [Is_true (?x && ?y)] |- _ ]
      => rewrite (toImpl (@andb_prop_elim x y)) in H
    | [ H : context [Is_true (?x || ?y)] |- _ ]
      => rewrite (toImpl (@orb_prop_elim x y)) in H
    | [ H : Is_true (false) |- _ ] => inv H
    | [ H : context [not (?t)] |- _ ] =>
      match t with
        | context [Is_true (?x && ?y)] =>
          rewrite <- (toImpl (@andb_prop_intro x y)) in H
        | context [Is_true (?x || ?y)] =>
          rewrite <- (toImpl (@orb_prop_intro x y)) in H
        | context [Is_true (negb ?x)] =>
          rewrite <- (toImpl (@negb_prop_intro x)) in H
      end
    | [ H : context [Is_true (negb ?x)] |- _ ]
      => rewrite (toImpl (@negb_prop_elim x)) in H
    | _ => fail
  end.

Lemma true_prop_intro
  : Is_true (true) = True.
Proof.
  eauto.
Qed.

Lemma false_prop_intro
  : Is_true (false) = False.
Proof.
  eauto.
Qed.

Ltac bool_to_prop_goal :=
  match goal with
   | [ _ : _ |- context [Is_true (?x && ?y)] ]
     => rewrite <- (toImpl (@andb_prop_intro x y))
   | [ _ : _ |- context [not (Is_true (?x && ?y))] ]
     => rewrite (toImpl (@andb_prop_elim x y))
   | [ _ : _ |- context [Is_true (?x || ?y)] ]
     => rewrite <- (toImpl (@orb_prop_intro x y))
   | [ _ : _ |- context [not (Is_true (?x || ?y))] ]
     => rewrite (toImpl (@orb_prop_elim x y))
   | [  _ : _ |- context [Is_true (negb ?x)] ]
     => rewrite <- (toImpl (@negb_prop_intro x))
   | [  _ : _ |- context [Is_true (true)] ]
     => rewrite true_prop_intro
   | [  _ : _ |- context [Is_true (false)] ]
     => rewrite false_prop_intro
   | _ => fail
  end.

Tactic Notation "bool_to_prop" :=
  repeat bool_to_prop_goal.

Tactic Notation "bool_to_prop" "in" hyp (H) :=
  repeat (bool_to_prop_assumption H).

Tactic Notation "bool_to_prop" "in" "*" :=
  repeat (match goal with
    | [ H : _ |- _ ] => bool_to_prop in H
  end).

Ltac destr_assumption H :=
  repeat match goal with
           | [ H : _ /\ _  |- _ ] => destruct H
         end.

Ltac destr :=
  intros; repeat match goal with
                   | |- _ /\ _  => split
                 end.

Tactic Notation "destr" "in" hyp(H) :=
  destr_assumption H.

Tactic Notation "destr" "in" "*" :=
  repeat (match goal with
    | [ H : _ |- _ ] => destr in H
  end).

Tactic Notation "beq_to_prop" :=
  match goal with
    | [ H : ?Q = true |- Is_true ?Q] => rewrite H; eapply I
    | [ H : Is_true ?Q |- ?Q = true] => destruct Q; try destruct H; reflexivity
    | [ H : Is_true ?Q, H' : ?Q = false |- _ ] => rewrite H' in H; destruct H
    | [ H : Is_true ?Q |- not ((?Q) = false) ] => let X:= fresh "H" in
      intro X; rewrite X in H; destruct H
    | [ H : ?Q = false |- not (Is_true (?Q)) ] => rewrite H; cbv; trivial
    | [ H : ?Q, H' : not (?Q) |- _ ] => exfalso; apply H'; apply H
    | [ H : not (?Q = false) |- Is_true (?Q) ] =>
      destruct Q; solve [ apply I | exfalso; eapply H; trivial ]
    | |- Is_true true => eapply I
    | [ H : not (Is_true (?Q)) |- ?Q = false ] =>
      destruct Q; solve [ exfalso; eapply H; eapply I | reflexivity ]
  end.


Tactic Notation "cbool" :=
  simpl in *; bool_to_prop in *; destr in *; bool_to_prop; destr; beq_to_prop.

(** * Omega Rewrite *)

Tactic Notation "orewrite" constr(A) :=
  let X := fresh "OX" in assert A as X by omega; rewrite X; clear X.

Tactic Notation "orewrite" constr(A) "in" hyp(H) :=
  let X := fresh "OX" in assert A as X by omega; rewrite X in H; clear X.


(** * Misc. Tactics *)

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

Tactic Notation "simplify" "if" :=
  match goal with
    | [ H : Is_true (?P) |- context [if ?P then _ else _]] =>
      let X := fresh in assert (P = true) as X by cbool; rewrite X; clear X
    | [ H : not (Is_true (?P)) |- context [if ?P then _ else _]] =>
      let X := fresh in assert (P = false) as X by cbool; rewrite X; clear X
  end.

Tactic Notation "simplify" "if" "in" "*" :=
  match goal with
    | [ H : Is_true (?P), H' : context [if ?P then _ else _] |- _ ] =>
      let X := fresh in assert (P = true) as X by cbool; rewrite X in H'; clear X
    | [ H : not (Is_true (?P)), H' : context [if ?P then _ else _] |- _ ] =>
      let X := fresh in assert (P = false) as X by cbool; rewrite X in H'; clear X
  end.


Ltac eqassumption :=
  match goal with
    | [ H : ?C ?t |- ?C ?t' ] =>
      let X := fresh in
        cut (C t' = C t);
          [ rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 |- ?C ?t1' ?t2' ] =>
      let X := fresh in
        cut (C t1' t2' = C t1 t2);
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 ?t3 |- ?C ?t1' ?t2' ?t3'  ] =>
      let X := fresh in
        cut (C t1' t2' t3' = C t1 t2 t3);
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 ?t3 ?t4 |- ?C ?t1' ?t2' ?t3' ?t4' ] =>
      let X := fresh in
        cut (C t1' t2' t3' t4' = C t1 t2 t3 t4);
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
  end.


Definition fresh {X} `{Equivalence X} (x:X) (Y:list X) : Prop :=
  ~InA R x Y.

Fixpoint unique X `{Equivalence X} (Y:list X) : Prop :=
  match Y with
    | nil => True
    | cons x Y' => ~InA R x Y' /\ unique Y'
  end.

Lemma unique_decons X (R : relation X) (H : Equivalence R) x L
    : unique (x::L) -> unique L.
Proof.
  intros [A B]; eapply B.
Qed.

Hint Resolve unique_decons.

Ltac let_case_eq :=
  match goal with
    | [ H : context [let (_, _) := ?e in _] |- _ ] =>
      let a := fresh "a" in let b := fresh "b" in let eq := fresh "eq" in
        case_eq e; intros a b eq; rewrite eq in H
  end.

Ltac let_pair_case_eq :=
  match goal with
    | [ |- context [let (_, _) := ?e in _] ] => case_eq e; intros
    | [ H : ?x = (?s, ?t) |- _ ] =>
      assert (fst x = s) by (rewrite H; eauto);
      assert (snd x = t) by (rewrite H; eauto); clear H
  end.

Ltac simpl_pair_eqs :=
  match goal with
  | [ H : ?P = (?x, ?y) |- _ ] => assert (fst P = x) by (rewrite H; eauto);
                                assert (snd P = y) by (rewrite H; eauto); clear H
  | [ H : (?x, ?y) = ?P |- _ ] => assert (fst P = x) by (rewrite <- H; eauto);
                                assert (snd P = y) by (rewrite <- H; eauto); clear H
  end.


Ltac scofix :=
repeat match goal with
           [H : _ |- _] =>
           match H with
             | _ => revert H
           end
       end; cofix; intros.

Lemma modus_ponens P Q
: P -> (P -> Q) -> Q.
tauto.
Defined.

Tactic Notation "exploiT" tactic(tac) :=
  eapply modus_ponens;[ tac | intros].

Ltac exploit H :=
  eapply modus_ponens;
  [
    let H' := fresh "exploitH" in
    pose proof H as H'; hnf in H';
      eapply H'; clear H'
  | intros].

Tactic Notation "exploiT" constr(ty) :=
  match goal with
      | H: ty |- _ => exploit H
      | H: ty _ |- _ => exploit H
      | H: ty _ _ |- _ => exploit H
      | H: ty _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ _ _ _ _ |- _ => exploit H
      | H: ty _ _ _ _ _ _ _ _ _ |- _ => exploit H
  end.


Ltac exploit2 H H' :=
  eapply modus_ponens;
  [
    let H' := fresh "exploitH" in
    pose proof H as H'; hnf in H';
      eapply H'; clear H'
  | intros H'].


Tactic Notation "exploit" uconstr(X) := exploit X.
Tactic Notation "exploit" uconstr(X) "as" ident(H) := exploit2 X H.


Definition foo A B C := (A -> ~ B \/ C).

Lemma test (A B C D : Prop) (a:A) (b:B)

: foo A B C
  -> (C -> D)
  ->  D.
Proof.
  intros. exploiT foo. eauto. exploit H. eauto. firstorder.
Qed.

Fixpoint iter A n (s:A) (f: A -> A) :=
  match n with
  | 0 => s
  | S n => iter n (f s) f
  end.

Lemma iter_comm n A (a:A) (f:A -> A)
  : iter (S n) a f = f (iter n a f).
Proof.
  general induction n.
  - simpl; eauto.
  - change (iter (S (S n)) a f) with (iter (S n) (f a) f).
    rewrite IHn; eauto.
Qed.

Require Le Arith.Compare_dec.

Instance le_comp (a b: nat) : Computable (lt a b).
eapply Arith.Compare_dec.lt_dec.
Defined.

Hint Extern 20 => match goal with
                   | [ H: ?a /\ ?b |- ?b ] => eapply H
                   | [ H: ?a /\ ?b |- ?a ] => eapply H
                 end.

Instance plus_le_morpism
: Proper (Peano.le ==> Peano.le ==> Peano.le) Peano.plus.
Proof.
  unfold Proper, respectful.
  intros. omega.
Qed.

Instance plus_S_morpism
: Proper (Peano.le ==> Peano.le) S.
Proof.
  unfold Proper, respectful.
  intros. omega.
Qed.

Instance le_lt_morph
: Proper (Peano.ge ==> Peano.le ==> impl) Peano.lt.
Proof.
  unfold Proper, respectful, impl; intros; try omega.
Qed.

Instance le_lt_morph'
: Proper (eq ==> Peano.le ==> impl) Peano.lt.
Proof.
  unfold Proper, respectful, flip, impl; intros; try omega.
Qed.

Instance le_lt_morph''
: Proper (Peano.le ==> eq ==> flip impl) Peano.lt.
Proof.
  unfold Proper, respectful, flip, impl; intros; try omega.
Qed.

(** ** List Length automation *)

Lemma length_map_2 X Y Z (L:list X) (L':list Y) (f:Y->Z)
: length L = length L'
  -> length L = length (List.map f L').
Proof.
  intros. rewrite map_length; eauto.
Qed.

Lemma length_map_1 X Y Z (L:list Y) (L':list X) (f:Y->Z)
: length L = length L'
  -> length (List.map f L) = length L'.
Proof.
  intros. rewrite map_length; eauto.
Qed.

Create HintDb len discriminated.

Hint Resolve length_map_1 length_map_2 : len.

Lemma rev_swap X (L L':list X)
: rev L = L'
  -> L = rev L'.
Proof.
  intros. subst. rewrite rev_involutive; eauto.
Qed.

Inductive already_swapped (P:Prop) := AlreadySwapped.
Lemma mark_swapped P : already_swapped P.
Proof.
  constructor.
Qed.

Hint Extern 1000 =>
match goal with
  | [ H : already_swapped (?a = ?b) |- ?a = ?b ] => fail 1
  | [ |- ?a = ?b ] => eapply eq_sym; pose proof (mark_swapped (a = b))
end : len.

Hint Immediate eq_trans : len.
Hint Immediate eq_sym : len.

Hint Extern 10 =>
match goal with
  [ H : ?a = ?b, H': ?b = ?c |- ?c = ?a ] => eapply eq_sym; eapply (eq_trans H H')
end : len.

Lemma map_length_ass_both X X' Y Y' (L:list X) (L':list Y) (f:X->X') (g:Y->Y')
  : length L = length L'
    -> length (List.map f L) = length (List.map g L').
Proof.
  repeat rewrite map_length; eauto.
Qed.

Lemma app_length_ass_both X Y (L1 L2:list X) (L1' L2':list Y)
  : length L1 = length L1'
    -> length L2 = length L2'
    -> length (L1 ++ L2) = length (L1' ++ L2').
Proof.
  repeat rewrite app_length; eauto.
Qed.

Hint Resolve map_length_ass_both app_length_ass_both | 2 : len.

Lemma app_length_ass X (L:list X) L' k
  : length L + length L' = k
    -> length (L ++ L') = k.
Proof.
  intros; subst. rewrite app_length; eauto.
Qed.

Lemma app_length_ass_right X (L:list X) L' k
  : length L + length L' = k
    -> k = length (L ++ L').
Proof.
  intros; subst. rewrite app_length; eauto.
Qed.

Lemma map_length_ass X Y (L:list X) (f:X->Y) k
  : length L = k
    -> length (List.map f L) = k.
Proof.
  intros; subst. rewrite map_length; eauto.
Qed.

Lemma map_length_ass_right X Y (L:list X) (f:X->Y) k
  : length L = k
    -> k = length (List.map f L).
Proof.
  intros; subst. rewrite map_length; eauto.
Qed.

Lemma length_tl X (l:list X)
  : length (tl l) = length l - 1.
Proof.
  destruct l; simpl; eauto; omega.
Qed.


Lemma pair_eta (X Y:Type) (p:X * Y)
  : p = (fst p, snd p).
Proof.
  destruct p; eauto.
Qed.

Hint Resolve map_length_ass app_length_ass | 4 : len.

Notation "❬ L ❭" := (length L) (at level 9, format "'❬' L '❭'").
Notation "f ⊝ L" := (List.map f L) (at level 50, L at level 50, left associativity).
Notation "'tab' s '‖' L '‖'" := (List.map (fun _ => s) L)
                                 (at level 50, format "'tab'  s  '‖' L '‖'", s at level 0, L at level 200).

Notation "〔 X 〕" := (list X) (format "'〔' X '〕'") : type_scope.
Notation "؟" := option.

Lemma len_le_app X Y Z (A:list X) (B:list Y) (C D:list Z) n
  : n < length B
    -> length A = length (C ++ D)
    -> length B = length C
    -> n < length A.
Proof.
  intros LE EQ1 EQ2. rewrite EQ1. rewrite app_length. omega.
Qed.

Hint Resolve len_le_app : len.

Lemma map_length_lt_ass_right X Y (L:list X) (f:X->Y) k
  : k < length L
    -> k < length (List.map f L).
Proof.
  intros; subst. rewrite map_length; eauto.
Qed.

Hint Resolve map_length_lt_ass_right : len.

Hint Extern 10 =>
match goal with
| [ H : length ?A = length ?B, H' : ?n < length ?B  |- ?n < length ?A] =>
  rewrite H; eapply H'
| [ H : length ?B = length ?A, H' : ?n < length ?B  |- ?n < length ?A] =>
  rewrite <- H; eapply H'
end : len.

Lemma length_le_plus X Y (A:list X) (B:list Y) k
  : length A = length B
    -> length A <= length B + k.
Proof.
  omega.
Qed.

Hint Resolve length_le_plus : len.

Instance instance_impl_2 x
  : Proper (impl ==> impl) (impl x).
Proof.
  unfold Proper, respectful, impl. intros.
  eauto.
Qed.

Instance instance_impl_3
  : Proper (impl --> impl ==> impl) impl.
Proof.
  unfold Proper, respectful, impl, flip. intros.
  eauto.
Qed.

Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) (x : X)
  : (forall x, (forall y, f y  < f x -> p y)  -> p x) -> p x.
Proof.
  intros A. apply A.
  induction (f x); intros y B.
  exfalso; omega.
  apply A. intros z C. apply IHn. omega.
Qed.

Definition size_recursion (X : Type) (f : X -> nat) (p: X -> Type) (x : X)
  : (forall x, (forall y, f y  < f x -> p y) -> p x) -> p x.
Proof.
  intros A. apply A.
  induction (f x); intros y B.
  exfalso; destruct (f y); inv B.
  apply A. intros z C. apply IHn. cbv in B,C. cbv.
  inv B. assumption. eapply le_S in C. eapply le_trans; eauto.
Defined.

Ltac simpl_minus :=
  repeat match goal with
  | [ H : context [?n - ?n] |- _ ]
    => orewrite (n - n = 0) in H
  end.

Hint Extern 5 (Is_true true) => eapply I.

Instance map_m_eq A B
  : Proper (@pointwise_relation A B eq ==> eq ==> eq) (@List.map A B).
Proof.
  unfold Proper, respectful, pointwise_relation; intros; subst.
  eapply map_ext; eauto.
Qed.

Instance app_m_eq A
  : Proper (eq ==> eq ==> eq) (@app A).
Proof.
  unfold Proper, respectful; intros; subst; eauto.
Qed.

Lemma app_length_le_ass X (L:list X) L' k
  : length L + length L' <= k
    -> length (L ++ L') <= k.
Proof.
  intros; subst. rewrite app_length; eauto.
Qed.

Lemma app_length_le_ass_right X (L:list X) L' k
  : k <= length L + length L'
    -> k <= length (L ++ L').
Proof.
  intros; subst. rewrite app_length; eauto.
Qed.

Lemma map_length_le_ass X Y (L:list X) (f:X->Y) k
  : length L <= k
    -> length (List.map f L) <= k.
Proof.
  intros; subst. rewrite map_length; eauto.
Qed.

Lemma map_length_le_ass_right X Y (L:list X) (f:X->Y) k
  : k <= length L
    -> k <= length (List.map f L).
Proof.
  intros; subst. rewrite map_length; eauto.
Qed.

Hint Resolve app_length_le_ass app_length_le_ass_right map_length_le_ass map_length_le_ass_right
  : len.

Lemma min_idempotent_ass n m k
  : n = k
    -> n = m
    -> min n m = k.
Proof.
  intros. repeat subst. eapply Nat.min_idempotent.
Qed.

Hint Resolve min_idempotent_ass : len.

Definition impb (a b:bool) : Prop := if a then b else True.

Instance impb_refl : Reflexive impb.
Proof.
  hnf; destruct x; simpl; eauto.
Qed.

Instance impb_trans : Transitive impb.
Proof.
  hnf; intros [] [] []; eauto.
Qed.

Hint Extern 5 (impb ?a ?a') =>
progress (first [has_evar a | has_evar a' | reflexivity]).

Hint Extern 5 =>
match goal with
  [ H : impb ?a ?b, H' : impb ?b ?c |- impb ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
end.

Instance Is_true_impb
  : Proper (impb ==> impl) Is_true.
Proof.
  unfold Proper, respectful; intros.
  destruct x,y; simpl in *; hnf; eauto.
Qed.


Ltac destr_sig H :=
  match type of H with
  | context [proj1_sig ?x] => destruct x; simpl in H
  end.

Tactic Notation "destr_sig" :=
  match goal with
  | [ |- context [proj1_sig (proj1_sig ?x)] ] => destruct x; simpl
  | [ |- context [proj1_sig ?x] ] => destruct x; simpl
  end.
