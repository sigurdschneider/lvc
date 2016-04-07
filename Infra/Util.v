Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega Containers.OrderedTypeEx.
Require Export Infra.Option EqDec AutoIndTac Computable.

Set Implicit Arguments.

Set Regular Subst Tactic.

Tactic Notation "inv" hyp(A) := inversion A; subst.
Tactic Notation "invc" hyp(A) := inversion A; subst; clear A.
Tactic Notation "invs" hyp(A) := inversion A; subst; clear_trivial_eqs.
Tactic Notation "invcs" hyp(A) := inversion A; subst; clear A; clear_trivial_eqs.

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

Require Export Basics Tactics Morphisms Morphisms_Prop.

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

Ltac isabsurd :=
  try now (hnf; intros; match goal with
                 [ H : _ |- _ ] => exfalso; inversion H; try congruence
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
  simpl in *; bool_to_prop in *; destr in *; bool_to_prop; destr; beq_to_prop; isabsurd.

Global Instance inst_eq_dec_list {A} `{EqDec A eq} : EqDec (list A) eq.
hnf. eapply list_eq_dec. eapply equiv_dec.
Defined.


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
    | cons x Y' => fresh x Y' /\ unique Y'
  end.

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
  end.


Ltac scofix :=
repeat match goal with
           [H : _ |- _] =>
           match H with
             | _ => revert H
           end
       end; cofix; intros.

Ltac stuck :=
  let A := fresh "A" in let v := fresh "v" in intros [v A]; inv A; isabsurd.

Ltac stuck2 :=
  let A := fresh "A" in
  let v := fresh "v" in
  let evt := fresh "evt" in
  intros [v [evt A]]; inv A; isabsurd.


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

Instance prod_eq_fst_morphism X Y R R'
: Proper (@prod_eq X Y R R' ==> R) fst.
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Instance prod_eq_snd_morphism X Y R R'
: Proper (@prod_eq X Y R R' ==> R') snd.
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Lemma list_eq_length A R l l'
  : @list_eq A R l l' -> length l = length l'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Inductive option_R (A B : Type) (eqA : A -> B -> Prop)
: option A -> option B -> Prop :=
| option_R_Some a b : eqA a b -> option_R eqA ⎣a⎦ ⎣b⎦.


Lemma option_R_refl A R `{Reflexive A R} : forall x, option_R R ⎣x⎦ ⎣x⎦.
intros; eauto using option_R.
Qed.

Instance option_R_sym A R `{Symmetric A R} : Symmetric (option_R R).
hnf; intros ? [] []; eauto using option_R.
Qed.

Instance option_R_trans A R `{Transitive A R} : Transitive (option_R R).
hnf; intros. inv H0; inv H1; econstructor; eauto.
Qed.

Section PolyIter.
  Variable A : Type.

  Fixpoint iter n (s:A) (f: nat -> A-> A) :=
    match n with
        | 0 => s
        | S n => iter n (f n s) f
    end.

End PolyIter.

Require Le Arith.Compare_dec.

Instance le_comp (a b: nat) : Computable (lt a b).
eapply Arith.Compare_dec.lt_dec.
Defined.

Hint Extern 20 => match goal with
                   | [ H: ?a /\ ?b |- ?b ] => eapply H
                   | [ H: ?a /\ ?b |- ?a ] => eapply H
                 end.

Instance instance_option_eq_trans_R X {R: relation X} `{Transitive _ R}
 : Transitive (option_eq R).
Proof.
  hnf; intros. inv H0; inv H1.
  + econstructor.
  + econstructor; eauto.
Qed.

Instance instance_option_eq_refl_R X {R: relation X} `{Reflexive _ R}
 : Reflexive (option_eq R).
Proof.
  hnf; intros. destruct x.
  + econstructor; eauto.
  + econstructor.
Qed.

Instance instance_option_eq_sym_R X {R: relation X} `{Symmetric _ R}
 : Symmetric (option_eq R).
Proof.
  hnf; intros. inv H0.
  + econstructor.
  + econstructor; eauto.
Qed.

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
Notation "؟ X" := (option X) (format "'؟' X", at level 50, X at level 0) : type_scope.

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
