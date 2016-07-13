Require Import NArith Bool List.
Require Import OrderedTypeEx.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(**
   This file implements finite dictionaries from positive integers to
   any elements as Patricia sets. All maps' operations are provided
   but no specifications.

   More comments on the implementation should be added soon.
   *)
Section Elt.
Variable elt : Type.
Definition prefix := N.
Inductive tree :=
| Empty
| Leaf (k : positive) (v : elt)
| Branch (p : prefix) (m : nat) (l r : tree).

Inductive MapsTo (k : positive) (v : elt) : tree -> Prop :=
| MapsTo_Leaf : MapsTo k v (Leaf k v)
| MapsTo_Branch_1 : forall p m l r, MapsTo k v l -> MapsTo k v (Branch p m l r)
| MapsTo_Branch_2 : forall p m l r, MapsTo k v r -> MapsTo k v (Branch p m l r).

Definition empty := Empty.
Definition is_empty (t : tree) :=
  match t with | Empty => true | _ => false end.

Definition singleton k v := Leaf k v.

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
    | Leaf j _ => j == k
    | Branch _ m l r => mem k (if zero_bit k m then l else r)
  end.

Fixpoint find k (t : tree) :=
  match t with
    | Empty => None
    | Leaf j v => if j == k then Some v else None
    | Branch _ m l r => find k (if zero_bit k m then l else r)
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
  Variable v : elt.
  Fixpoint add (t : tree) :=
    match t with
      | Empty => Leaf k v
      | Leaf j _ =>
        if j == k then Leaf k v else join (Npos k) (Npos j) (Leaf k v) t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (add l) r
          | MatchRight => Branch p m l (add r)
          | Disagree => join (Npos k) p (Leaf k v) t
        end
    end.
End Add.

(** Extra map update operations using combining functions *)
Section Insert.
  Variable k : positive.
  Variable v : elt.
  Variable f : elt -> elt.
  Fixpoint insert (t : tree) :=
    match t with
      | Empty => Leaf k v
      | Leaf j v' =>
        if j == k then Leaf k (f v') else join (Npos k) (Npos j) (Leaf k v) t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (insert l) r
          | MatchRight => Branch p m l (insert r)
          | Disagree => join (Npos k) p (Leaf k v) t
        end
    end.
End Insert.

Section Adjust.
  Variable k : positive.
  Variable f : elt -> elt.
  Fixpoint adjust (t : tree) :=
    match t with
      | Empty => Empty
      | Leaf j v' =>
        if j == k then Leaf k (f v') else t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (adjust l) r
          | MatchRight => Branch p m l (adjust r)
          | Disagree => t
        end
    end.
End Adjust.

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
      | Leaf j _ => if k == j then Empty else t
      | Branch p m l r =>
        match match_prefix (Npos k) p m with
          | MatchLeft => Branch p m (remove l) r
          | MatchRight => Branch p m l (remove r)
          | Disagree => t
        end
    end.
End Remove.

Section PairRecursion.
  Fixpoint size (t : tree) :=
    match t with
      | Empty => 1
      | Leaf _ _ => 1
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

Fixpoint cardinal (t : tree) :=
  match t with
    | Empty => O
    | Leaf _ _ => 1
    | Branch _ _ l r => cardinal l + cardinal r
  end.

Section Fold.
  Variable A : Type.
  Variable f : positive -> elt -> A -> A.
  Fixpoint fold t acc :=
    match t with
      | Empty => acc
      | Leaf k v => f k v acc
      | Branch _ _ l r => fold l (fold r acc)
    end.
End Fold.

Fixpoint elements t := fold (fun k v l => (k,v)::l) t nil.
End Elt.

Section Map.
  Variables elt elt' : Type.
  Variable f : elt -> elt'.
  Fixpoint map (t : tree elt) :=
    match t with
      | Empty => Empty elt'
      | Leaf k v => Leaf k (f v)
      | Branch p m l r => Branch p m (map l) (map r)
    end.
End Map.
Section Mapi.
  Variables elt elt' : Type.
  Variable f : positive -> elt -> elt'.
  Fixpoint mapi (t : tree elt) :=
    match t with
      | Empty => Empty elt'
      | Leaf k v => Leaf k (f k v)
      | Branch p m l r => Branch p m (mapi l) (mapi r)
    end.
End Mapi.
Section Map2.
  Variables elt elt' elt'' : Type.
  Variable f : option elt -> option elt' -> option elt''.
  (** a very unclever implementation ... *)
  Definition map2 (t : tree elt) (u : tree elt') : tree elt'' :=
    let u' := fold (fun k v m =>
      match f None (Some v) with Some v' => add k v' m | None => m end)
      u (empty _)
    in
    fold (fun k v m =>
      match f (Some v) (find k u) with
        | Some v' => add k v' m
        | None => remove k m
      end) t u'.
End Map2.

(** OrderedType *)
Section Equal.
  Variable elt : Type.
  Variable cmp_elt : elt -> elt -> bool.

  Fixpoint equal (t t' : tree elt) :=
    match t, t' with
      | Empty, Empty => true
      | Leaf k v, Leaf k' v' => (k == k') &&& cmp_elt v v'
      | Branch p m l r, Branch p' m' l' r' =>
        (p == p') &&& (m == m') &&& equal l l' &&& equal r r'
      | _, _ => false
    end.
End Equal.