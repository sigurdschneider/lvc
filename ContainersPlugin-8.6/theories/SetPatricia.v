Require Import NArith Bool List.
Require Import OrderedTypeEx.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(**
   This file implements finite sets of positive integers
   as Patricia sets. All operations for sets are provided
   but no specifications. It is just to demonstrate one
   instance of [FSet] which is specific to a certain type
   and a certain order relation (left to right bit comparison).

   More comments on the implementation should be added soon.
   *)

Definition prefix := N.
Inductive tree :=
| Empty
| Leaf (k : positive)
| Branch (p : prefix) (m : nat) (l r : tree).

Inductive In (k : positive) : tree -> Prop :=
| In_Leaf : In k (Leaf k)
| In_Branch_1 : forall p m l r, In k l -> In k (Branch p m l r)
| In_Branch_2 : forall p m l r, In k r -> In k (Branch p m l r).

Definition empty := Empty.
Definition is_empty (t : tree) :=
  match t with | Empty => true | _ => false end.

Definition singleton k := Leaf k.

Fixpoint zero_bit k m {struct m} :=
  match m with
    | O =>
      match k with
        | xO _ => false
        | _ => true
      end
    | S m' =>
      match k with
        | xO k' => zero_bit k' m'
        | xI k' => zero_bit k' m'
        | xH => true
      end
  end.

Fixpoint mem k (t : tree) :=
  match t with
    | Empty => false
    | Leaf j => j == k
    | Branch _ m l r => mem k (if zero_bit k m then l else r)
  end.

Fixpoint first_one (p : positive) : nat :=
  match p with
    | xH => 0
    | xO p' => S (first_one p')
    | xI _ => 0
  end.

Fixpoint mask_and_branching_bit_p (p q : positive) : prefix * nat * bool :=
  match p, q with
    | xH, xH => (N0, O, true) (* arbitrary *)
    | xO p', xO q' =>
      let '(mask, b, dir) := mask_and_branching_bit_p p' q' in
        (Ndouble mask, S b, dir)
    | xI p', xI q' =>
      let '(mask, b, dir) := mask_and_branching_bit_p p' q' in
        (Ndouble_plus_one mask, S b, dir)
    | xO _, xI _ | xO _, xH => (N0, O, true)
    | xI _, xO _ | xH, xO _ => (N0, O, false)
    | xI p, xH => (Npos xH, S (first_one p), false)
    | xH, xI p' => (Npos xH, S (first_one p'), true)
  end.

Definition mask_and_branching_bit (p q : prefix) : prefix * nat * bool :=
  match p, q with
    | N0, N0 => (N0, 0, true) (* arbitrary *)
    | N0, Npos q => (N0, first_one q, true)
    | Npos p, N0 => (N0, first_one p, false)
    | Npos p, Npos q => mask_and_branching_bit_p p q
  end.

Definition join (p p' : prefix) (t t' : tree) :=
  let '(mask, b, dir) := mask_and_branching_bit p p' in
    if dir then
      Branch mask b t t'
    else
      Branch mask b t' t.

Inductive matched_prefix :=
| MatchLeft
| MatchRight
| Disagree.

Fixpoint match_all_zeros k m r1 r2 :=
  match m with
    | O =>
      match k with
        | xO _ => r1
        | _ => r2
      end
    | S m' =>
      match k with
        | xO k' => match_all_zeros k' m' r1 r2
        | _ => Disagree
      end
  end.

Fixpoint match_prefix_p k p m :=
  match m with
    | O =>
      match k with
        | xO _ => MatchLeft
        | _ => MatchRight
      end
    | S m' =>
      match k, p with
        | xH, xH => MatchLeft
        | xO k', xO p' => match_prefix_p k' p' m'
        | xI k', xI p' => match_prefix_p k' p' m'
        | xI k', xH => match_all_zeros k' m' MatchLeft MatchRight
        | xH, xI k' => match_all_zeros k' m' MatchRight MatchLeft
        | _, _ => Disagree
      end
  end.

Definition match_prefix k p m :=
  match k, p with
    | N0, N0 => MatchLeft
    | N0, _ => Disagree
    | Npos k, N0 =>
      match k with
        | xO _ => MatchLeft
        | _ => MatchRight
      end
    | Npos k, Npos p => match_prefix_p k p m
  end.

Section Add.
  Variable k : positive.
  Fixpoint add (t : tree) :=
    match t with
      | Empty => Leaf k
      | Leaf j =>
        if j == k then t else join (Npos k) (Npos j) (Leaf k) t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (add l) r
          | MatchRight => Branch p m l (add r)
          | Disagree => join (Npos k) p (Leaf k) t
        end
    end.
End Add.

Definition branch p m l r :=
  match l with
    | Empty => r
    | _ =>
      match r with
        | Empty => l
        | _ => Branch p m l r
      end
  end.

Section Remove.
  Variable k : positive.
  Fixpoint remove (t : tree) :=
    match t with
      | Empty => Empty
      | Leaf j => if k == j then Empty else t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (remove l) r
          | MatchRight => Branch p m l (remove r)
          | Disagree => t
        end
    end.
End Remove.

Module Example1.
  Local Open Scope positive_scope.

  Definition s := add 5 (add 1 (add 4 empty)).
  Time Eval vm_compute in s.
  Definition s' :=
    add 7 (add 2 (add 1 (add 3 empty))).
  Time Eval vm_compute in s'.
End Example1.

Section PairRecursion.
  Fixpoint size (t : tree) :=
    match t with
      | Empty => 1
      | Leaf _ => 1
      | Branch _ _ l r => S (size l + size r)
    end.

  Inductive lt_pair : tree * tree -> tree * tree -> Prop :=
  | lt_left1 :
    forall p m l r t', lt_pair (l, t') (Branch p m l r, t')
  | lt_right1 :
    forall p m l r t', lt_pair (r, t') (Branch p m l r, t')
  | lt_left2 :
    forall t p' m' l' r', lt_pair (t, l') (t, Branch p' m' l' r')
  | lt_right2 :
    forall t p' m' l' r', lt_pair (t, r') (t, Branch p' m' l' r')
  | lt_left_left :
    forall p m l r p' m' l' r',
      lt_pair (l, l') (Branch p m l r, Branch p' m' l' r')
  | lt_right_right :
    forall p m l r p' m' l' r',
      lt_pair (r, r') (Branch p m l r, Branch p' m' l' r').

  Definition sz_pair q := size (fst q) + size (snd q).
  Lemma lt_pair_decrease :
    forall s t s' t', lt_pair (s, t) (s', t') ->
      sz_pair (s, t) < sz_pair (s', t').
  Proof.
    intros; inversion H; subst; unfold sz_pair; simpl; omega.
  Qed.
  Corollary wf_lt_pair : well_founded lt_pair.
  Proof.
    apply Wf_nat.well_founded_lt_compat with sz_pair.
    intros [? ?] [? ?]; apply lt_pair_decrease.
  Qed.

  Fixpoint guard (n : nat) (wfR : well_founded lt_pair) {struct n} :
    well_founded lt_pair :=
    match n with
      | 0 => wfR
      | S n' =>
        fun x => Acc_intro x (fun y _ => guard n' (guard n' wfR) y)
    end.

  Variable A : Type.
  Definition combinator :=
    Fix (guard 100 wf_lt_pair) (fun _ => A).
  Check combinator.
End PairRecursion.

Definition merge (p : tree * tree) : tree :=
  combinator
  (fun p F =>
    match p as a return a = p -> tree with
      | (Empty, t') => fun _ => t'
      | (t, Empty) => fun _ => t
      | (Leaf k, t') => fun _ => add k t'
      | (t, Leaf k') => fun _ => add k' t
      | (Branch p m l r as t, Branch p' m' l' r' as t') =>
        fun Heq =>
          match m =?= m' with
            | Eq =>
              match match_prefix p' p m with
                | Disagree => join p p' t t'
                | _ =>
                  let H1 := eq_rect _ (lt_pair _)
                    (lt_left_left p m l r p' m' l' r') _ Heq in
                  let H2 := eq_rect _ (lt_pair _)
                    (lt_right_right p m l r p' m' l' r') _ Heq in
                      Branch p m (F (l, l') H1) (F (r, r') H2)
              end
            | Lt =>
              match match_prefix p' p m with
                | MatchLeft =>
                  let H := eq_rect _ (lt_pair _) (lt_left1 p m l r t') _ Heq in
                    Branch p m (F (l, t') H) r
                | MatchRight =>
                  let H := eq_rect _ (lt_pair _) (lt_right1 p m l r t') _ Heq in
                    Branch p m l (F (r, t') H)
                | Disagree => join p p' t t'
              end
            | Gt =>
              match match_prefix p p' m' with
                | MatchLeft =>
                  let H :=
                    eq_rect _ (lt_pair _) (lt_left2 t p' m' l' r') _ Heq in
                    Branch p' m' (F (t, l') H) r'
                | MatchRight =>
                  let H :=
                    eq_rect _ (lt_pair _) (lt_right2 t p' m' l' r') _ Heq in
                    Branch p' m' l' (F (t, r') H)
                | Disagree => join p p' t t'
              end
          end
    end (refl_equal _))
  p.

Require Recdef.
Function merge' (p : tree * tree) {wf lt_pair} : tree :=
  match p with
    | (Empty, t') => t'
    | (t, Empty) => t
    | (Leaf k, t') => add k t'
    | (t, Leaf k') => add k' t
    | (Branch p m l r as t, Branch p' m' l' r' as t') =>
      match m =?= m' with
        | Eq =>
          match match_prefix p' p m with
            | Disagree => join p p' t t'
            | _ => Branch p m (merge' (l, l')) (merge' (r, r'))
          end
        | Lt =>
          match match_prefix p' p m with
            | MatchLeft => Branch p m (merge' (l, t')) r
            | MatchRight => Branch p m l (merge' (r, t'))
            | Disagree => join p p' t t'
          end
        | Gt =>
          match match_prefix p p' m' with
            | MatchLeft => Branch p' m' (merge' (t, l')) r'
            | MatchRight => Branch p' m' l' (merge' (t, r'))
            | Disagree => join p p' t t'
          end
      end
  end.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  exact (guard 100 wf_lt_pair).
Defined.
Check R_merge'_correct.
Check merge'_equation.

(* Theorem merge_fix : *)
(*   forall p, merge p = *)
(*     match p with *)
(*       | (Empty, t') => t' *)
(*       | (t, Empty) => t *)
(*       | (Leaf k, t') => add k t' *)
(*       | (t, Leaf k') => add k' t *)
(*       | (Branch p m l r as t, Branch p' m' l' r' as t') => *)
(*         match m =?= m' with *)
(*           | Eq => *)
(*             match match_prefix p' p m with *)
(*               | Disagree => join p p' t t' *)
(*               | _ => Branch p m (merge (l, l')) (merge (r, r')) *)
(*             end *)
(*           | Lt =>  *)
(*             match match_prefix p' p m with *)
(*               | MatchLeft => Branch p m (merge (l, t')) r *)
(*               | MatchRight => Branch p m l (merge (r, t')) *)
(*               | Disagree => join p p' t t' *)
(*             end *)
(*           | Gt => *)
(*             match match_prefix p p' m' with *)
(*               | MatchLeft => Branch p' m' (merge (t, l')) r' *)
(*               | MatchRight => Branch p' m' l' (merge (t, r')) *)
(*               | Disagree => join p p' t t' *)
(*             end *)
(*         end *)
(*     end. *)
(* Proof. *)
(*   intro p; unfold merge at 1. *)
(*   unfold combinator. *)
(* Admitted. *)

Module Example2.
  Export Example1.

  Definition m := merge (s, s').
  Eval vm_compute in m.
  Definition m' := merge' (s, s').
  Eval vm_compute in m'.

  Fixpoint complet (acc : tree) (n : nat) :=
    match n with
      | O => acc
      | 1 => acc
      | S (S n') => complet (add (P_of_succ_nat n') acc) n'
    end.
  Time Definition c100 := Eval vm_compute in complet empty 100.
  Time Definition c101 := Eval vm_compute in complet empty 101.
  Print c100. Print c101.

  Time Eval vm_compute in (merge (c100, c101)). (* 0.012 *)
  Time Eval vm_compute in (merge' (c100, c101)). (* pareil *)
End Example2.

Definition union t t' := merge (t, t').
Definition union' t t' := merge' (t, t').

Fixpoint subset (t t' : tree) : bool :=
  match t, t' with
    | Empty, _ => true
    | _, Empty => false
    | Leaf k, _ => mem k t'
    | Branch _ _ _ _ , Leaf _ => false
    | Branch p m l r, Branch p' m' l' r' =>
      match m =?= m' with
        | Eq => (p == p') &&& subset l l' &&& subset r r'
        | Lt => false
        | Gt =>
          match match_prefix p p' m' with
            | MatchLeft => subset l l' &&& subset r l'
            | MatchRight => subset l r' && subset r r'
            | Disagree => false
          end
      end
  end.

Module Example3.
  Export Example2.
  Time Eval vm_compute in subset c100 c101.
  Time Eval vm_compute in subset c100 (complet empty 102).
End Example3.

Function intersects' (p : tree * tree) {wf lt_pair p} : tree :=
  match p with
    | (Empty, _) => Empty
    | (_, Empty) => Empty
    | (Leaf k as t, t') => if mem k t' then t else Empty
    | (t, Leaf k' as t') => if mem k' t then t' else Empty
    | (Branch p m l r as t, Branch p' m' l' r' as t') =>
      match m =?= m' with
        | Eq =>
          if p == p' then union (intersects' (l, l')) (intersects' (r, r'))
            else Empty
        | Lt =>
          match match_prefix p' p m with
            | MatchLeft => intersects' (l, t')
            | MatchRight => intersects' (r, t')
            | Disagree => Empty
          end
        | Gt =>
          match match_prefix p p' m' with
            | MatchLeft => intersects' (t, l')
            | MatchRight => intersects' (t, r')
            | Disagree => Empty
          end
      end
  end.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  exact (guard 100 wf_lt_pair).
Defined.
Definition inter' t t' := intersects' (t, t').

Function difference' (p : tree * tree) {wf lt_pair p} : tree :=
  match p with
    | (Empty, _) => Empty
    | (t, Empty) => t
    | (Leaf k as t, t') => if mem k t' then Empty else t
    | (t, Leaf k') => remove k' t
    | (Branch p m l r as t, Branch p' m' l' r' as t') =>
      match m =?= m' with
        | Eq =>
          if p == p' then union (difference' (l, l')) (difference' (r, r'))
            else t
        | Lt =>
          match match_prefix p' p m with
            | MatchLeft => union (difference' (l, t')) r
            | MatchRight => union t (difference' (r, t'))
            | Disagree => t
          end
        | Gt =>
          match match_prefix p p' m' with
            | MatchLeft => difference' (t, l')
            | MatchRight => difference' (t, r')
            | Disagree => t
          end
      end
  end.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  exact (guard 100 wf_lt_pair).
Defined.
Definition diff' t t' := difference' (t, t').

Module Example4.
  Export Example3.
  Time Eval vm_compute in inter' c100 c101.
  Time Eval vm_compute in inter' c100 (complet empty 102).
  Time Eval vm_compute in diff' c100 (complet empty 102).
  Time Eval vm_compute in diff' (complet empty 102) c100.
End Example4.

Fixpoint cardinal (t : tree) :=
  match t with
    | Empty => O
    | Leaf _ => 1
    | Branch _ _ l r => cardinal l + cardinal r
  end.

Section Fold.
  Variable A : Type.
  Variable f : positive -> A -> A.
  Fixpoint fold t acc :=
    match t with
      | Empty => acc
      | Leaf k => f k acc
      | Branch _ _ l r => fold l (fold r acc)
    end.
End Fold.

Section WithPred.
  Variable P : positive -> bool.

  Fixpoint for_all t :=
    match t with
      | Empty => true
      | Leaf k => P k
      | Branch _ _ l r => for_all l &&& for_all r
    end.

  Fixpoint exists_ t :=
    match t with
      | Empty => false
      | Leaf k => P k
      | Branch _ _ l r => exists_ l ||| exists_ r
    end.

  Fixpoint filter t :=
    match t with
      | Empty => Empty
      | Leaf k => if P k then t else Empty
      | Branch p m l r =>
        branch p m (filter l) (filter r)
    end.

  Fixpoint part (acc : tree * tree) (t : tree) :=
    let '(a1, a2) := acc in
      match t with
        | Empty => acc
        | Leaf k => if P k then (add k a1, a2) else (a1, add k a2)
        | Branch _ _ l r => part (part acc l) r
      end.
  Definition partition t := part (Empty, Empty) t.
End WithPred.

Fixpoint choose t :=
  match t with
    | Empty => None
    | Leaf k => Some k
    | Branch _ _ l _ => choose l
  end.

Fixpoint elements t := fold (@cons _) t nil. (* ATTENTION NON TRIES ! *)

Definition split x s :=
  let coll k trip :=
    let '(l, b, r) := trip in
      match k =?= x with
        | Lt => (add k l, b, r)
        | Gt => (l, b, add k r)
        | Eq => (l, true, r)
      end
  in
  fold coll s (Empty, false, Empty).

Fixpoint min_elt t :=
  match t with
    | Empty => None
    | Leaf k => Some k
    | Branch _ _ l r =>
      match min_elt l, min_elt r with
        | Some ml, Some mr => Some (if ml << mr then ml else mr)
        | _, _ => None (* arbitrary *)
      end
  end.

Fixpoint max_elt t :=
  match t with
    | Empty => None
    | Leaf k => Some k
    | Branch _ _ l r =>
      match max_elt l, max_elt r with
        | Some ml, Some mr => Some (if ml << mr then mr else ml)
        | _, _ => None (* arbitrary *)
      end
  end.

(** OrderedType *)
Generate OrderedType tree.
Definition equal (x y : tree) := x == y.