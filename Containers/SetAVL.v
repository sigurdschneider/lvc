Require Import OrderedTypeEx.
Require Import SetInterface ZArith Program.Basics.

Generalizable All Variables.

(** This file corresponds to [FSetAVL.v] in the standard library
   and implements finite sets as AVL trees. The corresponding
   [FSet] and [FSetSpecs] instances are defined in
   the file [SetAVLInstance.v].

   Note that there is one limitation with respect to the original
   [FSetAVL] : the construction here is not parameterized by the
   integer type used to store heights in the tree, [Z] is used
   instead.
   *)

(** Notations and helper lemma about pairs *)
Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

(** * Raw

   Functor of pure functions + a posteriori proofs of invariant
   preservation *)
Module SetAVL.
  Open Local Scope pair_scope.
  Open Local Scope lazy_bool_scope.
  Open Local Scope Z_scope.
  Local Notation int := Z.

  Set Implicit Arguments.
  Unset Strict Implicit.
  (** * Trees
     The fourth field of [Node] is the height of the tree *)
  Inductive tree (elt : Type) `{OrderedType elt} :=
  | Leaf : tree
  | Node : tree -> elt -> tree -> int -> tree.

  Section Definitions.
    Context `{OrderedType elt}.

    Notation t := tree.

    (** * Basic functions on trees: height and cardinal *)
    Definition height (s : tree) :  int :=
      match s with
        | Leaf => 0
        | Node _ _ _ h => h
      end.

    Fixpoint cardinal (s : tree) : nat :=
      match s with
        | Leaf => 0%nat
        | Node l _ r _ => S (cardinal l + cardinal r)
      end.

    (** * Empty Set *)
    Definition empty := Leaf.

    (** * Emptyness test *)

    Definition is_empty s :=
      match s with Leaf => true | _ => false end.

    (** * Appartness *)

    (** The [mem] function is deciding appartness. It exploits the
       binary search tree invariant to achieve logarithmic complexity. *)

    Fixpoint mem x s :=
      match s with
        |  Leaf => false
        |  Node l y r _ =>
          match x =?= y with
            | Lt => mem x l
            | Eq => true
            | Gt => mem x r
          end
      end.

    (** * Singleton set *)

    Definition singleton x := Node Leaf x Leaf 1.

    (** * Helper functions *)

    (** [create l x r] creates a node, assuming [l] and [r]
       to be balanced and [|height l - height r| <= 2]. *)
    Notation max := Zmax.
    Definition create l x r :=
      Node l x r (max (height l) (height r) + 1).

    (** [bal l x r] acts as [create], but performs one step of
       rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

    Definition assert_false := create.

    Notation gt_le_dec := Z_gt_le_dec.
    Notation ge_lt_dec := Z_ge_lt_dec.
    Definition bal l x r :=
      let hl := height l in
        let hr := height r in
          if gt_le_dec hl (hr+2) then
            match l with
              | Leaf => assert_false l x r
              | Node ll lx lr _ =>
                if ge_lt_dec (height ll) (height lr) then
                  create ll lx (create lr x r)
                  else
                    match lr with
                      | Leaf => assert_false l x r
                      | Node lrl lrx lrr _ =>
                        create (create ll lx lrl) lrx (create lrr x r)
                    end
            end
            else
              if gt_le_dec hr (hl+2) then
                match r with
                  | Leaf => assert_false l x r
                  | Node rl rx rr _ =>
                    if ge_lt_dec (height rr) (height rl) then
                      create (create l x rl) rx rr
                      else
                        match rl with
                          | Leaf => assert_false l x r
                          | Node rll rlx rlr _ =>
                            create (create l x rll) rlx (create rlr rx rr)
                        end
                end
                else
                  create l x r.

    (** * Insertion *)

    Fixpoint add x s :=
      match s with
        | Leaf => Node Leaf x Leaf 1
        | Node l y r h =>
          match x =?= y with
            | Lt => bal (add x l) y r
            | Eq => Node l y r h
            | Gt => bal l y (add x r)
          end
      end.

    (** * Join

       Same as [bal] but does not assume anything regarding heights
       of [l] and [r].
       *)

    Fixpoint join l : elt -> t -> t :=
      match l with
        | Leaf => add
        | Node ll lx lr lh => fun x =>
          fix join_aux (r:t) : t :=
          match r with
            | Leaf =>  add x l
            | Node rl rx rr rh =>
              if gt_le_dec lh (rh+2) then bal ll lx (join lr x r)
                else if gt_le_dec rh (lh+2) then bal (join_aux rl) rx rr
                  else create l x r
          end
      end.

    (** * Extraction of minimum element

       Morally, [remove_min] is to be applied to a non-empty tree
       [t = Node l x r h]. Since we can't deal here with [assert false]
       for [t=Leaf], we pre-unpack [t] (and forget about [h]).
       *)

    Fixpoint remove_min l x r : t*elt :=
      match l with
        | Leaf => (r,x)
        | Node ll lx lr lh =>
          let (l',m) := remove_min ll lx lr in (bal l' x r, m)
      end.

    (** * Merging two trees

       [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
       of [t1] to be smaller than all elements of [t2], and
       [|height t1 - height t2| <= 2].
       *)

    Definition merge s1 s2 :=
      match s1,s2 with
        | Leaf, _ => s2
        | _, Leaf => s1
        | _, Node l2 x2 r2 h2 =>
          let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
      end.

    (** * Deletion *)

    Fixpoint remove x s :=
      match s with
        | Leaf => Leaf
        | Node l y r h =>
          match x =?= y with
            | Lt => bal (remove x l) y r
            | Eq => merge l r
            | Gt => bal l  y (remove x r)
          end
      end.

    (** * Minimum element *)

    Fixpoint min_elt s :=
      match s with
        | Leaf => None
        | Node Leaf y _  _ => Some y
        | Node l _ _ _ => min_elt l
      end.

    (** * Maximum element *)
    Fixpoint max_elt s :=
      match s with
        | Leaf => None
        | Node _ y Leaf  _ => Some y
        | Node _ _ r _ => max_elt r
      end.

    (** * Any element *)

    Definition choose := min_elt.

    (** * Concatenation

       Same as [merge] but does not assume anything about heights.
       *)

    Definition concat s1 s2 :=
      match s1, s2 with
        | Leaf, _ => s2
        | _, Leaf => s1
        | _, Node l2 x2 r2 _ =>
          let (s2',m) := remove_min l2 x2 r2 in
            join s1 m s2'
      end.

    (** * Splitting

       [split x s] returns a triple [(l, present, r)] where
       - [l] is the set of elements of [s] that are [< x]
       - [r] is the set of elements of [s] that are [> x]
       - [present] is [true] if and only if [s] contains  [x].
       *)

    Record triple := mktriple { t_left:t; t_in:bool; t_right:t }.
    Notation "<( l , b , r )>" := (mktriple l b r) (at level 9).
    Notation "t #l" := (t_left t) (at level 9, format "t '#l'").
    Notation "t #b" := (t_in t) (at level 9, format "t '#b'").
    Notation "t #r" := (t_right t) (at level 9, format "t '#r'").

    Fixpoint split x s : triple :=
      match s with
        | Leaf => <( Leaf, false, Leaf )>
        | Node l y r h =>
          match x =?= y with
            | Lt => let (ll,b,rl) := split x l in <( ll, b, join rl y r )>
            | Eq => <( l, true, r )>
            | Gt => let (rl,b,rr) := split x r in <( join l y rl, b, rr )>
          end
      end.

    (** * Intersection *)

    Fixpoint inter s1 s2 :=
      match s1, s2 with
        | Leaf, _ => Leaf
        | _, Leaf => Leaf
        | Node l1 x1 r1 h1, _ =>
          let (l2',pres,r2') := split x1 s2 in
            if pres then join (inter l1 l2') x1 (inter r1 r2')
              else concat (inter l1 l2') (inter r1 r2')
      end.

    (** * Difference *)

    Fixpoint diff s1 s2 :=
      match s1, s2 with
        | Leaf, _ => Leaf
        | _, Leaf => s1
        | Node l1 x1 r1 h1, _ =>
          let (l2',pres,r2') := split x1 s2 in
            if pres then concat (diff l1 l2') (diff r1 r2')
              else join (diff l1 l2') x1 (diff r1 r2')
      end.

    (** * Union *)

    (** In ocaml, heights of [s1] and [s2] are compared each time in order
       to recursively perform the split on the smaller set.
       Unfortunately, this leads to a non-structural algorithm. The
       following code is a simplification of the ocaml version: no
       comparison of heights. It might be slightly slower, but
       experimentally all the tests I've made in ocaml have shown this
       potential slowdown to be non-significant. Anyway, the exact code
       of ocaml has also been formalized thanks to Function+measure, see
       [ocaml_union] in [FSetFullAVL].
       *)
    Fixpoint union s1 s2 :=
      match s1, s2 with
        | Leaf, _ => s2
        | _, Leaf => s1
        | Node l1 x1 r1 h1, _ =>
          let (l2',_,r2') := split x1 s2 in
            join (union l1 l2') x1 (union r1 r2')
      end.

    (** * Elements *)

    (** [elements_tree_aux acc t] catenates the elements of [t] in infix
       order to the list [acc] *)

    Fixpoint elements_aux (acc : list elt) (t : tree) : list elt :=
      match t with
        | Leaf => acc
        | Node l x r _ => elements_aux (x :: elements_aux acc r) l
      end.

    (** then [elements] is an instanciation with an empty [acc] *)

    Definition elements := elements_aux nil.

    (** * Filter *)

    Fixpoint filter_acc (f:elt->bool) acc s :=
      match s with
        | Leaf => acc
        | Node l x r h =>
          filter_acc f (filter_acc f (if f x then add x acc else acc) l) r
      end.

    Definition filter f := filter_acc f Leaf.


    (** * Partition *)

    Fixpoint partition_acc (f:elt->bool)(acc : t*t)(s : t) : t*t :=
      match s with
        | Leaf => acc
        | Node l x r _ =>
          let (acct,accf) := acc in
            partition_acc f
            (partition_acc f
              (if f x then (add x acct, accf) else (acct, add x accf)) l) r
      end.

    Definition partition f := partition_acc f (Leaf,Leaf).

    (** * [for_all] and [exists] *)
    Require Import Bool.
    Fixpoint for_all (f:elt->bool) s :=
      match s with
        | Leaf => true
        | Node l x r _ => f x &&& for_all f l &&& for_all f r
      end.

    Fixpoint exists_ (f:elt->bool) s :=
      match s with
        | Leaf => false
        | Node l x r _ => f x ||| exists_ f l ||| exists_ f r
      end.

    (** * Map *)
    Fixpoint map_monotonic `{HB : OrderedType B} (f : elt -> B)
      `{Proper _ (_lt ==> _lt) f} (s : @tree elt H) : @tree B HB :=
      match s with
        | Leaf => Leaf
        | Node l x r h => Node (map_monotonic l) (f x) (map_monotonic r) h
      end.

    (** * Fold *)

    Fixpoint fold (A : Type) (f : elt -> A -> A)(s : tree) : A -> A :=
      fun a => match s with
                 | Leaf => a
                 | Node l x r _ => fold f r (f x (fold f l a))
               end.
    Implicit Arguments fold [A].

    (** * Subset *)

    (** In ocaml, recursive calls are made on "half-trees" such as
       (Node l1 x1 Leaf _) and (Node Leaf x1 r1 _). Instead of these
       non-structural calls, we propose here two specialized functions for
       these situations. This version should be almost as efficient as
       the one of ocaml (closures as arguments may slow things a bit),
       it is simply less compact. The exact ocaml version has also been
       formalized (thanks to Function+measure), see [ocaml_subset] in
       [FSetFullAVL].
       *)

    Fixpoint subsetl (subset_l1:t->bool) x1 s2 : bool :=
      match s2 with
        | Leaf => false
        | Node l2 x2 r2 h2 =>
          match x1 =?= x2 with
            | Eq => subset_l1 l2
            | Lt => subsetl subset_l1 x1 l2
            | Gt => mem x1 r2 &&& subset_l1 s2
          end
      end.

    Fixpoint subsetr (subset_r1:t->bool) x1 s2 : bool :=
      match s2 with
        | Leaf => false
        | Node l2 x2 r2 h2 =>
          match x1 =?= x2 with
            | Eq => subset_r1 r2
            | Lt => mem x1 l2 &&& subset_r1 s2
            | Gt => subsetr subset_r1 x1 r2
          end
      end.

    Fixpoint subset s1 s2 : bool :=
      match s1, s2 with
        | Leaf, _ => true
        | Node _ _ _ _, Leaf => false
        | Node l1 x1 r1 h1, Node l2 x2 r2 h2 =>
          match x1 =?= x2 with
            | Eq => subset l1 l2 &&& subset r1 r2
            | Lt => subsetl (subset l1) x1 l2 &&& subset r1 s2
            | Gt => subsetr (subset r1) x1 r2 &&& subset l1 s2
          end
      end.

    (** * A new comparison algorithm suggested by Xavier Leroy

       Transformation in C.P.S. suggested by Benjamin Grégoire.
       The original ocaml code (with non-structural recursive calls)
       has also been formalized (thanks to Function+measure), see
       [ocaml_compare] in [FSetFullAVL]. The following code with
       continuations computes dramatically faster in Coq, and
       should be almost as efficient after extraction.
       *)

    (** Enumeration of the elements of a tree *)

    Inductive enumeration :=
    | End : enumeration
    | More : elt -> tree -> enumeration -> enumeration.


    (** [cons t e] adds the elements of tree [t] on the head of
       enumeration [e]. *)

    Fixpoint cons s e : enumeration :=
      match s with
        | Leaf => e
        | Node l x r h => cons l (More x r e)
      end.

    (** One step of comparison of elements *)

    Definition compare_more x1 (cont:enumeration->comparison) e2 :=
      match e2 with
        | End => Gt
        | More x2 r2 e2 =>
          match x1 =?= x2 with
            | Eq => cont (cons r2 e2)
            | Lt => Lt
            | Gt => Gt
          end
    end.

    (** Comparison of left tree, middle element, then right tree *)

    Fixpoint compare_cont s1 (cont:enumeration->comparison) e2 :=
      match s1 with
        | Leaf => cont e2
        | Node l1 x1 r1 _ =>
          compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
      end.

    (** Initial continuation *)

    Definition compare_end e2 :=
      match e2 with End => Eq | _ => Lt end.

    (** The complete comparison *)

    Definition compare s1 s2 := compare_cont s1 compare_end (cons s2 End).

    (** * Equality test *)

    Definition equal s1 s2 : bool :=
      match compare s1 s2 with
        | Eq => true
        | _ => false
      end.

    (** ** Occurrence in a tree *)

    Inductive In (x : elt) : tree -> Prop :=
    | IsRoot : forall l r h y, x === y -> In x (Node l y r h)
    | InLeft : forall l r h y, In x l -> In x (Node l y r h)
    | InRight : forall l r h y, In x r -> In x (Node l y r h).

    (** Induction principles *)
    Functional Scheme mem_ind := Induction for mem Sort Prop.
    Functional Scheme bal_ind := Induction for bal Sort Prop.
    Functional Scheme add_ind := Induction for add Sort Prop.
    Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
    Functional Scheme merge_ind := Induction for merge Sort Prop.
    Functional Scheme remove_ind := Induction for remove Sort Prop.
    Functional Scheme min_elt_ind := Induction for min_elt Sort Prop.
    Functional Scheme max_elt_ind := Induction for max_elt Sort Prop.
    Functional Scheme concat_ind := Induction for concat Sort Prop.
    Functional Scheme split_ind := Induction for split Sort Prop.
    Functional Scheme inter_ind := Induction for inter Sort Prop.
    Functional Scheme diff_ind := Induction for diff Sort Prop.
    Functional Scheme union_ind := Induction for union Sort Prop.
  End Definitions.

  Arguments In {elt} {H} x t.


  (** ** Binary search trees *)

  (** [lt_tree x s]: all elements in [s] are smaller than [x]  *)
  (*    (resp. greater for [gt_tree]) *)

  Definition lt_tree `{Helt : OrderedType elt} x s :=
    forall y, In y s -> y <<< x.
  Definition gt_tree `{Helt : OrderedType elt} x s :=
    forall y, In y s -> x <<< y.

  (** [bst t] : [t] is a binary search tree *)

  Inductive bst `{Helt : OrderedType elt} : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x l r h, bst l -> bst r ->
    lt_tree x l -> gt_tree x r -> bst (Node l x r h).

  (** * Some shortcuts *)
  Definition Equal `{Helt : OrderedType elt} s s' :=
    forall a : elt, In a s <-> In a s'.
  Definition Subset `{Helt : OrderedType elt} s s' :=
    forall a : elt, In a s -> In a s'.
  Definition Empty `{Helt : OrderedType elt} s :=
    forall a : elt, ~ In a s.
  Definition For_all `{Helt : OrderedType elt} (P : elt -> Prop) s :=
    forall x, In x s -> P x.
  Definition Exists `{Helt : OrderedType elt} (P : elt -> Prop) s :=
    exists x, In x s /\ P x.

  (** * Correctness proofs, isolated in a sub-module *)

  Section Proofs.
    Context `{Helt : OrderedType elt}.
    (* Module MX := OrderedTypeFacts X. *)
    (* Module L := FSetList.Raw X. *)

    Notation "<( l , b , r )>" := (mktriple l b r) (at level 9).
    Notation "t #l" := (t_left t) (at level 9, format "t '#l'").
    Notation "t #b" := (t_in t) (at level 9, format "t '#b'").
    Notation "t #r" := (t_right t) (at level 9, format "t '#r'").

    (** * Automation and dedicated tactics *)
    Hint Constructors In bst.
    Hint Unfold lt_tree gt_tree.

    Tactic Notation "factornode" ident(l) ident(x) ident(r) ident(h)
    "as" ident(s) :=
      set (s:=Node l x r h) in *; clearbody s; clear l x r h.

    (** A tactic to repeat [inversion_clear] on all hyps of the  *)
    (*     form [(f (Node _ _ _ _))] *)

    Ltac inv f :=
      match goal with
        | H:f Leaf |- _ => inversion_clear H; inv f
        | H:f _ Leaf |- _ => inversion_clear H; inv f
        | H:f (Node _ _ _ _) |- _ => inversion_clear H; inv f
        | H:f _ (Node _ _ _ _) |- _ => inversion_clear H; inv f
        | _ => idtac
      end.

    Ltac intuition_in :=
      (repeat progress intuition (inv (@In elt Helt))).

    (** Helper tactic concerning order of elements. *)

    Ltac order_ followon :=
      match goal with
        | U: lt_tree _ ?s, V: In _ ?s |- _ =>
          generalize (U _ V); clear U; order_ followon
        | U: gt_tree _ ?s, V: In _ ?s |- _ =>
          generalize (U _ V); clear U; order_ followon
        | _ => followon
      end.
    Ltac order := order_ OrderedType.order.

    (** * Basic results about [In], [lt_tree], [gt_tree], [height] *)

    (** [In] is compatible with [X.eq] *)

    Lemma In_1 :
      forall s (x y : elt), x === y -> In x s -> In y s.
    Proof.
      induction s; simpl; intuition_in; eauto.
      constructor; transitivity x; eauto.
    Qed.
    Hint Immediate In_1.

    Lemma In_node_iff :
      forall l (x:elt) r h y,
        In y (Node l x r h) <-> In y l \/ y === x \/ In y r.
    Proof.
      intuition_in; eauto.
    Qed.

    (** Results about [lt_tree] and [gt_tree] *)

    Lemma lt_leaf : forall x : elt, lt_tree x Leaf.
    Proof.
      red; inversion 1.
    Qed.

    Lemma gt_leaf : forall x : elt, gt_tree x Leaf.
    Proof.
      red; inversion 1.
    Qed.

    Lemma lt_tree_node :
      forall (x y : elt) (l r : tree) (h : int),
        lt_tree x l -> lt_tree x r -> y <<< x -> lt_tree x (Node l y r h).
    Proof.
      unfold lt_tree; intuition_in; order.
    Qed.

    Lemma gt_tree_node :
      forall (x y : elt) (l r : tree) (h : int),
        gt_tree x l -> gt_tree x r -> x <<< y -> gt_tree x (Node l y r h).
    Proof.
      unfold gt_tree; intuition_in; order.
    Qed.

    Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

    Lemma lt_tree_not_in :
      forall (x : elt) (t : tree), lt_tree x t -> ~ In x t.
    Proof.
      intros; intro; order.
    Qed.

    Lemma lt_tree_trans :
      forall (x y : elt), x <<< y -> forall t, lt_tree x t -> lt_tree y t.
    Proof.
      intros; intro; intros; transitivity x; eauto.
    Qed.

    Lemma gt_tree_not_in :
      forall (x : elt) (t : tree), gt_tree x t -> ~ In x t.
    Proof.
      intros; intro; order.
    Qed.

    Lemma gt_tree_trans :
      forall (x y : elt), y <<< x -> forall t, gt_tree x t -> gt_tree y t.
    Proof.
      intros; intro; intros; transitivity x; eauto.
    Qed.

    Hint Resolve @lt_tree_not_in @lt_tree_trans @gt_tree_not_in @gt_tree_trans.

    (** * Inductions principles *)
    Let t := tree.
    Theorem mem_ind' :
      forall (x : elt) (P : t -> bool -> Prop),
        (forall s : t, s = Leaf -> P Leaf false) ->
       (forall (s l : t) (y : elt) (r : t) (_x : int),
         s = Node l y r _x -> x === y -> P (Node l y r _x) true) ->
       (forall (s l : t) (y : elt) (r : t) (_x : int),
         s = Node l y r _x -> x <<< y ->
         P l (mem x l) -> P (Node l y r _x) (mem x l)) ->
       (forall (s l : t) (y : elt) (r : t) (_x : int),
        s = Node l y r _x -> x >>> y ->
        P r (mem x r) -> P (Node l y r _x) (mem x r)) ->
       forall s : t, P s (mem x s).
    Proof.
      intros x P Hleaf Heq Hlt Hgt s.
      functional induction mem x s; eauto;
        destruct (compare_dec x y); eauto; try discriminate.
    Qed.
(*     Functional Scheme bal_ind := Induction for bal Sort Prop. *)
(*     Functional Scheme add_ind := Induction for add Sort Prop. *)
(*     Functional Scheme remove_min_ind := Induction for remove_min Sort Prop. *)
(*     Functional Scheme merge_ind := Induction for merge Sort Prop. *)
(*     Functional Scheme remove_ind := Induction for remove Sort Prop. *)
(*     Functional Scheme min_elt_ind := Induction for min_elt Sort Prop. *)
(*     Functional Scheme max_elt_ind := Induction for max_elt Sort Prop. *)
(*     Functional Scheme concat_ind := Induction for concat Sort Prop. *)
(*     Functional Scheme split_ind := Induction for split Sort Prop. *)
(*     Functional Scheme inter_ind := Induction for inter Sort Prop. *)
(*     Functional Scheme diff_ind := Induction for diff Sort Prop. *)
(*     Functional Scheme union_ind := Induction for union Sort Prop. *)

    Implicit Types x : elt.
    Implicit Types s : tree (elt:=elt).

    (** * Empty set *)

    Lemma empty_1 : Empty empty.
    Proof.
      intro; intro.
      inversion H.
    Qed.

    Lemma empty_bst : bst empty.
    Proof.
      constructor.
    Qed.

    (** * Emptyness test *)

    Lemma is_empty_1 : forall s, Empty s -> is_empty s = true.
    Proof.
      destruct s as [|r x l h]; simpl; auto.
      intro H; elim (H x); auto.
    Qed.

    Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
    Proof.
      destruct s; simpl; intros; try discriminate; red; auto.
    Qed.

    (** * Appartness *)

    Lemma mem_1 : forall s x, bst s -> In x s -> mem x s = true.
    Proof.
      intros s x; functional induction mem x s; auto; intros;
        inv bst; intuition_in;
        destruct (compare_dec x y); try discriminate; order.
    Qed.

    Lemma mem_2 : forall s x, mem x s = true -> In x s.
    Proof.
      intros s x; functional induction mem x s; auto; intros;
        try (destruct (compare_dec x y)); try discriminate; auto.
    Qed.

    (** * Singleton set *)

    Lemma singleton_1 : forall x y, In y (singleton x) -> x === y.
    Proof.
      unfold singleton; intros; inv In; order.
    Qed.

    Lemma singleton_2 : forall x y, x === y -> In y (singleton x).
    Proof.
      unfold singleton; auto.
    Qed.

    Lemma singleton_bst : forall x : elt, bst (singleton x).
    Proof.
      unfold singleton; auto.
    Qed.

    (** * Helper functions *)

    Lemma create_in :
      forall l x r y,  In y (create l x r) <-> y === x \/ In y l \/ In y r.
    Proof.
      unfold create; split; [ inversion_clear 1 | ]; intuition.
    Qed.

    Lemma create_bst :
      forall l x r, bst l -> bst r -> lt_tree x l -> gt_tree x r ->
        bst (create l x r).
    Proof.
      unfold create; auto.
    Qed.
    Hint Resolve create_bst.

    Lemma bal_in : forall l x r y,
      In y (bal l x r) <-> y === x \/ In y l \/ In y r.
    Proof.
      intros l x r; functional induction bal l x r; intros; try clear e0;
        rewrite !create_in; intuition_in; eauto.
    Qed.

    Lemma bal_bst : forall l x r, bst l -> bst r ->
      lt_tree x l -> gt_tree x r -> bst (bal l x r).
    Proof.
      intros l x r; functional induction bal l x r; intros;
        inv bst; repeat apply create_bst; auto; unfold create;
          (apply lt_tree_node || apply gt_tree_node); auto;
            (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
    Qed.
    Hint Resolve @bal_bst.

    (** * Insertion *)

    Lemma add_in : forall s x y,
      In y (add x s) <-> y === x \/ In y s.
    Proof.
      intros s x; functional induction (add x s); auto; intros;
        try (destruct (compare_dec x y)); try discriminate;
          try rewrite !bal_in, !IHt0; intuition_in; eauto.
      constructor; transitivity x; auto.
    Qed.

    Lemma add_bst : forall s x, bst s -> bst (add x s).
    Proof.
      intros s x; functional induction (add x s); auto; intros;
        inv bst; apply bal_bst; auto;
          try (destruct (compare_dec x y)); try discriminate.
      (* lt_tree -> lt_tree (add ...) *)
      red; red in H3.
      intros.
      rewrite add_in in H4.
      intuition; order.
      (* gt_tree -> gt_tree (add ...) *)
      red; red in H3.
      intros.
      rewrite add_in in H4.
      intuition; order.
    Qed.
    Hint Resolve @add_bst.

    (** * Join *)

    (* Function/Functional Scheme can't deal with internal fix.  *)
    (*    Let's do its job by hand: *)

    Ltac join_tac :=
      intro l; induction l as [| ll _ lx lr Hlr lh];
        [ | intros x r; induction r as [| rl Hrl rx rr _ rh]; unfold join;
          [ | destruct (Z_gt_le_dec lh (rh+2)) as [z|z];
            [ match goal with |- context b [ bal ?a ?b ?c] =>
                replace (bal a b c)
                with (bal ll lx (join lr x (Node rl rx rr rh))); [ | auto]
              end
              | destruct (Z_gt_le_dec rh (lh+2)) as [z0|z0];
                [ match goal with |- context b [ bal ?a ?b ?c] =>
                    replace (bal a b c)
                    with (bal (join (Node ll lx lr lh) x rl) rx rr); [ | auto]
                  end
                  | ] ] ] ]; intros.

    Lemma join_in : forall l x r y,
      In y (join l x r) <-> y === x \/ In y l \/ In y r.
    Proof.
      join_tac.
      simpl.
      rewrite add_in; intuition_in.
      rewrite add_in; intuition_in.
      rewrite bal_in, Hlr; clear Hlr Hrl; intuition_in; eauto.
      rewrite bal_in, Hrl; clear Hlr Hrl; intuition_in; eauto.
      apply create_in.
    Qed.

    Lemma join_bst : forall l x r, bst l -> bst r ->
      lt_tree x l -> gt_tree x r -> bst (join l x r).
    Proof.
      join_tac; auto; try solve [simpl; auto];
        inv bst; apply bal_bst; auto;
          clear Hrl Hlr z; intro; intros; rewrite join_in in H;
            (intuition; [order |]); transitivity x; eauto.
    Qed.
    Hint Resolve @join_bst.

    (** * Extraction of minimum element *)

    Lemma remove_min_in : forall l (x:elt) r h y,
      In y (Node l x r h) <->
      y === (remove_min l x r)#2 \/ In y (remove_min l x r)#1.
    Proof.
      intros l x r; functional induction (remove_min l x r); simpl in *; intros.
      intuition_in; eauto.
      rewrite bal_in, In_node_iff, IHp, e0; simpl; intuition.
    Qed.

    Lemma remove_min_bst : forall l x r h,
      bst (Node l x r h) -> bst (remove_min l x r)#1.
    Proof.
      intros l x r; functional induction (remove_min l x r); simpl; intros.
      inv bst; auto.
      inversion_clear H.
      specialize IHp with (1:=H0); rewrite e0 in IHp; auto.
      apply bal_bst; auto.
      intro y; specialize (H2 y).
      rewrite remove_min_in, e0 in H2; simpl in H2; intuition.
    Qed.

    Lemma remove_min_gt_tree : forall l x r h,
      bst (Node l x r h) ->
      gt_tree (remove_min l x r)#2 (remove_min l x r)#1.
    Proof.
      intros l x r; functional induction (remove_min l x r); simpl; intros.
      inv bst; auto.
      inversion_clear H.
      specialize IHp with (1:=H0); rewrite e0 in IHp; simpl in IHp.
      intro y; rewrite bal_in; intuition;
        specialize (H2 m); rewrite remove_min_in, e0 in H2; simpl in H2;
          [ apply lt_eq with x | ]; eauto; transitivity x; eauto.
    Qed.
    Hint Resolve @remove_min_bst @remove_min_gt_tree.

    (** * Merging two trees *)

    Lemma merge_in : forall s1 s2 y,
      In y (merge s1 s2) <-> In y s1 \/ In y s2.
    Proof.
      intros s1 s2; functional induction (merge s1 s2); intros;
        try factornode _x _x0 _x1 _x2 as s1.
      intuition_in.
      intuition_in.
      rewrite bal_in, remove_min_in, e1; simpl; intuition.
    Qed.

    Lemma merge_bst : forall s1 s2, bst s1 -> bst s2 ->
      (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> y1 <<< y2) ->
      bst (merge s1 s2).
    Proof.
      intros s1 s2; functional induction (merge s1 s2); intros; auto;
        try factornode _x _x0 _x1 _x2 as s1.
      apply bal_bst; auto.
      change s2' with ((s2',m)#1); rewrite <-e1; eauto.
      intros y Hy.
      apply H1; auto.
      rewrite remove_min_in, e1; simpl; auto.
      change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
    Qed.
    Hint Resolve @merge_bst.


    (** * Deletion *)

    Lemma remove_in : forall s x y, bst s ->
      (In y (remove x s) <-> ~ y === x /\ In y s).
    Proof.
      intros s x; functional induction remove x s; intros;
        try solve [intuition_in];
          destruct (compare_dec x y); try discriminate; inv bst.
      rewrite merge_in; intuition; [order|order|intuition_in]; eauto.
      elim H5; transitivity y; auto.
      rewrite bal_in, IHt0; clear IHt0; auto;
        intuition; [order|order|intuition_in].
      rewrite bal_in, IHt0; clear e0 IHt0;
        intuition; [order|order|intuition_in].
    Qed.

    Lemma remove_bst : forall s x, bst s -> bst (remove x s).
    Proof.
      intros s x; functional induction (remove x s); intros;
        try (destruct (compare_dec x y)); try discriminate; inv bst.
      auto.
      (* EQ *)
      apply merge_bst; eauto; intros; transitivity y; auto.
      (* LT *)
      apply bal_bst; auto.
      intro z; rewrite remove_in; auto; destruct 1; eauto.
      (* GT *)
      apply bal_bst; auto.
      intro z; rewrite remove_in; auto; destruct 1; eauto.
    Qed.
    Hint Resolve @remove_bst.

    (** * Minimum element *)

    Lemma min_elt_1 : forall s x, min_elt s = Some x -> In x s.
    Proof.
      intro s; functional induction (min_elt s); auto; inversion 1; auto.
    Qed.

    Lemma min_elt_2 : forall s x y, bst s ->
      min_elt s = Some x -> In y s -> ~ y <<< x.
    Proof.
      intro s; functional induction (min_elt s);
        try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
      inversion_clear 2.
      inversion_clear 1.
      inversion 1; subst.
      inversion_clear 1; order.
      inversion_clear H5.
      inversion_clear 1.
      simpl.
      destruct l1.
      inversion 1; subst.
      assert (x <<< y) by (apply H2; auto).
      inversion_clear 1; auto; order.
      assert (x1 <<< y) by auto.
      inversion_clear 2; auto;
        (assert (~ x1 <<< x) by auto); order.
    Qed.

    Lemma min_elt_3 : forall s, min_elt s = None -> Empty s.
    Proof.
      intro s; functional induction (min_elt s).
      red; red; inversion 2.
      inversion 1.
      intro H0.
      destruct (IHo0 H0 _x2); auto.
    Qed.

    (** * Maximum element *)

    Lemma max_elt_1 : forall s x, max_elt s = Some x -> In x s.
    Proof.
      intro s; functional induction (max_elt s); auto; inversion 1; auto.
    Qed.

    Lemma max_elt_2 : forall s x y, bst s ->
      max_elt s = Some x -> In y s -> ~ x <<< y.
    Proof.
      intro s; functional induction (max_elt s);
        try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
      inversion_clear 2.
      inversion_clear 1.
      inversion 1; subst.
      inversion_clear 1; order.
      inversion_clear H5.
      inversion_clear 1.
      assert (y <<< x1) by auto.
      inversion_clear 2; auto;
        (assert (~ x <<< x1) by auto); order.
    Qed.

    Lemma max_elt_3 : forall s, max_elt s = None -> Empty s.
    Proof.
      intro s; functional induction (max_elt s).
      red; auto.
      inversion 1.
      intros H0; destruct (IHo0 H0 _x2); auto.
    Qed.

    (** * Any element *)

    Lemma choose_1 : forall s x, choose s = Some x -> In x s.
    Proof.
      exact min_elt_1.
    Qed.

    Lemma choose_2 : forall s, choose s = None -> Empty s.
    Proof.
      exact min_elt_3.
    Qed.

    Lemma choose_3 : forall s s', bst s -> bst s' ->
      forall x x', choose s = Some x -> choose s' = Some x' ->
        Equal s s' -> x === x'.
    Proof.
      unfold choose, Equal; intros s s' Hb Hb' x x' Hx Hx' H.
      assert (~x <<< x').
      apply min_elt_2 with s'; auto.
      rewrite <-H; auto using min_elt_1.
      assert (~x' <<< x).
      apply min_elt_2 with s; auto.
      rewrite H; auto using min_elt_1.
      destruct (compare_dec x x'); intuition.
    Qed.

    (** * Concatenation *)

    Lemma concat_in : forall s1 s2 y,
      In y (concat s1 s2) <-> In y s1 \/ In y s2.
    Proof.
      intros s1 s2; functional induction (concat s1 s2); intros;
        try factornode _x _x0 _x1 _x2 as s1.
      intuition_in.
      intuition_in.
      rewrite join_in, remove_min_in, e1; simpl; intuition.
    Qed.

    Lemma concat_bst : forall s1 s2, bst s1 -> bst s2 ->
      (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> y1 <<< y2) ->
      bst (concat s1 s2).
    Proof.
      intros s1 s2; functional induction (concat s1 s2); intros; auto;
        try factornode _x _x0 _x1 _x2 as s1.
      apply join_bst; auto.
      change (bst (s2',m)#1); rewrite <-e1; eauto.
      intros y Hy.
      apply H1; auto.
      rewrite remove_min_in, e1; simpl; auto.
      change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
    Qed.
    Hint Resolve @concat_bst.

    (** * Splitting *)

    Lemma split_in_1 : forall s x y, bst s ->
      (In y (split x s)#l <-> In y s /\ y <<< x).
    Proof.
      intros s x; functional induction split x s; simpl; intros;
        inv bst; try solve [intuition_in];
          destruct (compare_dec x y); try discriminate.
      intuition_in; order.
      rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; intuition_in; order.
      rewrite join_in; rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; auto.
      intuition_in; try solve [order]; constructor; auto.
    Qed.

    Lemma split_in_2 : forall s x y, bst s ->
      (In y (split x s)#r <-> In y s /\ x <<< y).
    Proof.
      intros s x; functional induction (split x s); subst; simpl; intros;
        inv bst; try solve [intuition_in];
          destruct (compare_dec x y); try discriminate.
      intuition_in; order.
      rewrite join_in.
      rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; intuition_in;
        eauto; order.
      rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; intuition_in; order.
    Qed.

    Lemma split_in_3 : forall s x, bst s ->
      ((split x s)#b = true <-> In x s).
    Proof.
      intros s x; functional induction (split x s); subst; simpl; intros;
        inv bst; try solve [intuition_in; try discriminate];
          destruct (compare_dec x y); try discriminate.
      intuition.
      rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; intuition_in;
        auto; order.
      rewrite e1 in IHt0; simpl in IHt0; rewrite IHt0; intuition_in;
        auto; order.
    Qed.

    Lemma split_bst : forall s x, bst s ->
      bst (split x s)#l /\ bst (split x s)#r.
    Proof.
      intros s x; functional induction (split x s); subst; simpl; intros;
        inv bst; try (destruct (compare_dec x y)); try discriminate;
          try rewrite e1 in *; simpl in *; intuition;
            apply join_bst; auto.
      intros y0.
      generalize (split_in_2 x y0 H0); rewrite e1; simpl; intuition.
      intros y0.
      generalize (split_in_1 x y0 H1); rewrite e1; simpl; intuition.
    Qed.

    (** * Intersection *)

    Lemma inter_bst_in : forall s1 s2, bst s1 -> bst s2 ->
      bst (inter s1 s2) /\
      (forall y, In y (inter s1 s2) <-> In y s1 /\ In y s2).
    Proof.
      intros s1 s2; functional induction inter s1 s2; intros B1 B2;
        [intuition_in|intuition_in | | ];
        factornode _x0 _x1 _x2 _x3 as s2;
          generalize (split_bst x1 B2);
            rewrite e1; simpl; destruct 1; inv bst;
              destruct IHt0 as (IHb1,IHi1); auto;
                destruct IHt1 as (IHb2,IHi2); auto;
                  generalize (@split_in_1 s2 x1)(@split_in_2 s2 x1)
                    (split_in_3 x1 B2)(split_bst x1 B2);
                    rewrite e1; simpl; split; intros.
      (* bst join *)
      apply join_bst; auto; intro y; [rewrite IHi1|rewrite IHi2]; intuition.
      (* In join *)
      rewrite join_in, IHi1, IHi2, H5, H6; auto; intuition_in; eauto.
      apply In_1 with x1; auto.
      intuition. intuition.
      (* bst concat *)
      apply concat_bst; auto;
        intros y1 y2; rewrite IHi1, IHi2; intuition; order.
      (* In concat *)
      rewrite concat_in, IHi1, IHi2, H5, H6; auto.
      assert (~In x1 s2) by (rewrite <- H7; auto).
      intuition_in; eauto.
      elim H9.
      apply In_1 with y; auto.
    Qed.

    Lemma inter_in : forall s1 s2 y, bst s1 -> bst s2 ->
      (In y (inter s1 s2) <-> In y s1 /\ In y s2).
    Proof.
      intros s1 s2 y B1 B2; destruct (inter_bst_in B1 B2); auto.
    Qed.

    Lemma inter_bst : forall s1 s2, bst s1 -> bst s2 -> bst (inter s1 s2).
    Proof.
      intros s1 s2 B1 B2; destruct (inter_bst_in B1 B2); auto.
    Qed.

    (** * Difference *)

    Lemma diff_bst_in : forall s1 s2, bst s1 -> bst s2 ->
      bst (diff s1 s2) /\ (forall y, In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
    Proof.
      intros s1 s2; functional induction diff s1 s2; intros B1 B2;
        [intuition_in|intuition_in | | ];
        factornode _x0 _x1 _x2 _x3 as s2;
          generalize (split_bst x1 B2);
            rewrite e1; simpl; destruct 1;
              inv avl; inv bst;
              destruct IHt0 as (IHb1,IHi1); auto;
                destruct IHt1 as (IHb2,IHi2); auto;
                  generalize (@split_in_1 s2 x1)(@split_in_2 s2 x1)
                    (split_in_3 x1 B2)(split_bst x1 B2);
                    rewrite e1; simpl; split; intros.
      (* bst concat *)
      apply concat_bst; auto; intros y1 y2; rewrite IHi1, IHi2;
        intuition; order.
      (* In concat *)
      rewrite concat_in, IHi1, IHi2, H5, H6; intuition_in; eauto.
      elim H13.
      apply In_1 with x1; auto.
      (* bst join *)
      apply join_bst; auto; intro y; [rewrite IHi1|rewrite IHi2]; intuition.
      (* In join *)
      rewrite join_in, IHi1, IHi2, H5, H6; auto.
      assert (~In x1 s2) by (rewrite <- H7; auto).
      intuition_in; eauto.
    Qed.

    Lemma diff_in : forall s1 s2 y, bst s1 -> bst s2 ->
      (In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
    Proof.
      intros s1 s2 y B1 B2; destruct (diff_bst_in B1 B2); auto.
    Qed.

    Lemma diff_bst : forall s1 s2, bst s1 -> bst s2 -> bst (diff s1 s2).
    Proof.
      intros s1 s2 B1 B2; destruct (diff_bst_in B1 B2); auto.
    Qed.

    (** * Union *)

    Lemma union_in : forall s1 s2 y, bst s1 -> bst s2 ->
      (In y (union s1 s2) <-> In y s1 \/ In y s2).
    Proof.
      intros s1 s2; functional induction union s1 s2; intros y B1 B2.
      intuition_in.
      intuition_in.
      factornode _x0 _x1 _x2 _x3 as s2.
      generalize (split_in_1 x1 y B2)(split_in_2 x1 y B2)(split_bst x1 B2).
      rewrite e1; simpl.
      destruct 3; inv bst.
      rewrite join_in, IHt0, IHt1, H, H0; auto.
      destruct (compare_dec y x1); intuition_in; eauto.
    Qed.

    Lemma union_bst : forall s1 s2, bst s1 -> bst s2 ->
      bst (union s1 s2).
    Proof.
      intros s1 s2; functional induction union s1 s2; intros B1 B2; auto.
      factornode _x0 _x1 _x2 _x3 as s2.
      generalize (@split_in_1 s2 x1)(@split_in_2 s2 x1)(split_bst x1 B2).
      rewrite e1; simpl; destruct 3.
      inv bst.
      apply join_bst; auto.
      intro y; rewrite union_in, H; intuition_in; eauto.
      intro y; rewrite union_in, H0; intuition_in; eauto.
    Qed.

    (** * Elements *)

    Lemma elements_aux_in : forall s acc x,
      InA _eq x (elements_aux acc s) <-> In x s \/ InA _eq x acc.
    Proof.
      induction s as [ | l Hl x r Hr h ]; simpl; auto.
      intuition.
      inversion H0.
      intros.
      rewrite Hl.
      destruct (Hr acc x0); clear Hl Hr.
      intuition; inversion_clear H3; intuition.
    Qed.

    Lemma elements_in : forall s x, InA _eq x (elements s) <-> In x s.
    Proof.
      intros; generalize (elements_aux_in s nil x); intuition.
      inversion_clear H0.
    Qed.

    Lemma elements_aux_sort : forall s acc, bst s -> sort _lt acc ->
      (forall x y : elt, InA _eq x acc -> In y s -> y <<< x) ->
      sort _lt (elements_aux acc s).
    Proof.
      induction s as [ | l Hl y r Hr h]; simpl; intuition.
      inv bst.
      apply Hl; auto.
      constructor.
      apply Hr; auto.
      apply In_Inf; intros.
      destruct (elements_aux_in r acc y0); intuition.
      intros.
      inversion_clear H.
      order.
      destruct (elements_aux_in r acc x); intuition eauto.
      transitivity y; eauto.
    Qed.

    Lemma elements_sort : forall s : tree, bst s -> sort _lt (elements s).
    Proof.
      intros; unfold elements; apply elements_aux_sort; auto.
      intros; inversion H0.
    Qed.
    Hint Resolve elements_sort.

    Lemma elements_nodup : forall s : tree, bst s -> NoDupA _eq (elements s).
    Proof.
      auto.
    Qed.

    Lemma elements_aux_cardinal :
      forall s acc, (length acc + cardinal s)%nat = length (elements_aux acc s).
    Proof.
      simple induction s; simpl in |- *; intuition.
      rewrite <- H.
      simpl in |- *.
      rewrite <- H0; omega.
    Qed.

    Lemma elements_cardinal : forall s : tree, cardinal s = length (elements s).
    Proof.
      exact (fun s => elements_aux_cardinal s nil).
    Qed.

    Lemma elements_app :
      forall s acc, elements_aux acc s = app (elements s) acc.
    Proof.
      induction s; simpl; intros; auto.
      rewrite IHs1, IHs2.
      unfold elements; simpl.
      rewrite 2 IHs1, IHs2, <- !app_nil_end, !app_ass; auto.
    Qed.

    Lemma elements_node :
      forall l x r h acc,
        (elements l ++ x :: elements r ++ acc =
        elements (Node l x r h) ++ acc)%list.
    Proof.
      unfold elements; simpl; intros; auto.
      rewrite !elements_app, <- !app_nil_end, !app_ass; auto.
    Qed.

    (** * Filter *)
    Section F.
      Variable f : elt -> bool.

      Lemma filter_acc_in : forall s acc
        `{Proper _ (_eq ==> @eq bool) f}, forall x : elt,
          In x (filter_acc f acc s) <-> In x acc \/ In x s /\ f x = true.
      Proof.
        induction s; simpl; intros.
        intuition_in.
        rewrite IHs2, IHs1 by (destruct (f e); auto).
        case_eq (f e); intros.
        rewrite (add_in); auto.
        intuition_in; eauto.
        rewrite (H _ _ H2).
        intuition.
        intuition_in; eauto.
        rewrite (H _ _ H2) in H3.
        rewrite H0 in H3; discriminate.
      Qed.

      Lemma filter_acc_bst : forall s acc, bst s -> bst acc ->
        bst (filter_acc f acc s).
      Proof.
        induction s; simpl; auto.
        intros.
        inv bst.
        destruct (f e); auto.
      Qed.

      Lemma filter_in : forall s `{Proper _ (_eq ==> @eq bool) f},
        forall x : elt, In x (filter f s) <-> In x s /\ f x = true.
      Proof.
        unfold filter; intros; rewrite filter_acc_in; intuition_in.
      Qed.

      Lemma filter_bst : forall s, bst s -> bst (filter f s).
      Proof.
        unfold filter; intros; apply filter_acc_bst; auto.
      Qed.

      (** * Partition *)

      Lemma partition_acc_in_1 :
        forall s acc `{Proper _ (_eq ==> @eq bool) f},
          forall x : elt, In x (partition_acc f acc s)#1 <->
            In x acc#1 \/ In x s /\ f x = true.
      Proof.
        induction s; simpl; intros.
        intuition_in.
        destruct acc as [acct accf]; simpl in *.
        rewrite IHs2 by
          (destruct (f e); auto; apply partition_acc_avl_1; simpl; auto).
        rewrite IHs1 by (destruct (f e); simpl; auto).
        case_eq (f e); simpl; intros.
        rewrite (add_in); auto.
        intuition_in; eauto.
        rewrite (H _ _ H2).
        intuition.
        intuition_in; eauto.
        rewrite (H _ _ H2) in H3.
        rewrite H0 in H3; discriminate.
      Qed.

      Lemma partition_acc_in_2 :
        forall s acc `{Proper _ (_eq ==> @eq bool) f},
          forall x : elt, In x (partition_acc f acc s)#2 <->
            In x acc#2 \/ In x s /\ f x = false.
      Proof.
        induction s; simpl; intros.
        intuition_in.
        destruct acc as [acct accf]; simpl in *.
        rewrite IHs2 by
          (destruct (f e); auto; apply partition_acc_avl_2; simpl; auto).
        rewrite IHs1 by (destruct (f e); simpl; auto).
        case_eq (f e); simpl; intros.
        intuition.
        intuition_in; eauto.
        rewrite (H _ _ H2) in H3.
        rewrite H0 in H3; discriminate.
        rewrite (add_in); auto.
        intuition_in; eauto.
        rewrite (H _ _ H2).
        intuition.
      Qed.

      Lemma partition_in_1 :
        forall s `{Proper _ (_eq ==> @eq bool) f},
          forall x : elt, In x (partition f s)#1 <-> In x s /\ f x = true.
      Proof.
        unfold partition; intros; rewrite partition_acc_in_1;
          simpl in *; intuition_in.
      Qed.

      Lemma partition_in_2 :
        forall s `{Proper _ (_eq ==> @eq bool) f},
          forall x : elt, In x (partition f s)#2 <-> In x s /\ f x = false.
      Proof.
        unfold partition; intros; rewrite partition_acc_in_2;
          simpl in *; intuition_in.
      Qed.

      Lemma partition_acc_bst_1 : forall s acc, bst s -> bst acc#1 ->
        bst (partition_acc f acc s)#1.
      Proof.
        induction s; simpl; auto.
        destruct acc as [acct accf]; simpl in *.
        intros.
        inv bst.
        destruct (f e); auto.
        apply IHs2; simpl; auto.
        apply IHs1; simpl; auto.
      Qed.

      Lemma partition_acc_bst_2 : forall s acc, bst s -> bst acc#2 ->
        bst (partition_acc f acc s)#2.
      Proof.
        induction s; simpl; auto.
        destruct acc as [acct accf]; simpl in *.
        intros.
        inv bst.
        destruct (f e); auto.
        apply IHs2; simpl; auto.
        apply IHs1; simpl; auto.
      Qed.

      Lemma partition_bst_1 : forall s, bst s -> bst (partition f s)#1.
      Proof.
        unfold partition; intros; apply partition_acc_bst_1; auto.
        constructor.
      Qed.

      Lemma partition_bst_2 : forall s, bst s -> bst (partition f s)#2.
      Proof.
        unfold partition; intros; apply partition_acc_bst_2; auto; constructor.
      Qed.

      (** * [for_all] and [exists] *)

      Lemma for_all_1 : forall s `{Proper _ (_eq ==> @eq bool) f},
        For_all (fun x => f x = true) s -> for_all f s = true.
      Proof.
        induction s; simpl; auto.
        intros.
        rewrite IHs1; try red; auto.
        rewrite IHs2; try red; auto.
        generalize (H0 e).
        destruct (f e); simpl; auto.
      Qed.

      Lemma for_all_2 : forall s `{Proper _ (_eq ==> @eq bool) f},
        for_all f s = true -> For_all (fun x => f x = true) s.
      Proof.
        induction s; simpl; auto; intros; red; intros; inv In.
        destruct (andb_prop _ _ H0); auto.
        destruct (andb_prop _ _ H1); eauto.
        apply IHs1; auto.
        destruct (andb_prop _ _ H0); auto.
        destruct (andb_prop _ _ H1); auto.
        apply IHs2; auto.
        destruct (andb_prop _ _ H0); auto.
      Qed.

      Require Import Bool.
      Lemma exists_1 : forall s `{Proper _ (_eq ==> @eq bool) f},
        Exists (fun x => f x = true) s -> exists_ f s = true.
      Proof.
        induction s; simpl; destruct 2 as (x,(U,V));
          inv In; rewrite <- ?orb_lazy_alt.
        rewrite (H _ _ (symmetry H0)); rewrite V; auto.
        apply orb_true_intro; left.
        apply orb_true_intro; right; apply IHs1; auto; exists x; auto.
        apply orb_true_intro; right; apply IHs2; auto; exists x; auto.
      Qed.

      Lemma exists_2 : forall s `{Proper _ (_eq ==> @eq bool) f},
        exists_ f s = true -> Exists (fun x => f x = true) s.
      Proof.
        induction s; simpl; intros; rewrite <- ?orb_lazy_alt in *.
        discriminate.
        destruct (orb_true_elim _ _ H0) as [H1|H1].
        destruct (orb_true_elim _ _ H1) as [H2|H2].
        exists e; auto.
        destruct (IHs1 H H2); auto; exists x; intuition.
        destruct (IHs2 H H1); auto; exists x; intuition.
      Qed.

    End F.

    (** * Map *)

    Lemma map_monotonic_in `{HB : OrderedType B} :
      forall (f : elt -> B) `{Proper _ (_lt ==> _lt) f} s b,
        In b (map_monotonic (f:=f) s) ->
        exists a, exists b', b' === b /\ b' = f a /\ In a s.
    Proof.
      induction s; intros b Hb; inversion Hb; subst.
      exists e; exists (f e); intuition.
      destruct (IHs1 b H1) as [a [b' [B1 [B2 B3]]]]; subst.
      exists a; exists (f a); intuition.
      destruct (IHs2 b H1) as [a [b' [B1 [B2 B3]]]]; subst.
      exists a; exists (f a); intuition.
    Qed.

    Lemma map_monotonic_bst `{HB : OrderedType B} :
      forall (f : elt -> B) `{Proper _ (_lt ==> _lt) f} s,
        bst s -> bst (map_monotonic (f:=f) s).
    Proof.
      induction s; intros Hbst; inversion Hbst; subst;
        constructor; auto; fold map_monotonic in *;
          intros b Hb; simpl in Hb;
            destruct (map_monotonic_in Hb) as [a [b' [B1 [B2 B3]]]]; subst.
      rewrite <- B1; apply H; apply H6; auto.
      rewrite <- B1; apply H; apply H7; auto.
    Qed.

    (** * Fold *)
    Require SetList. Require Import Bool.
    Definition fold' (A : Type) (f : elt -> A -> A)(s : tree) :=
      SetList.SetList.fold f (elements s).
    Implicit Arguments fold' [A].

    Lemma fold_equiv_aux :
      forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
        SetList.SetList.fold f (elements_aux acc s) a =
          SetList.SetList.fold f acc (fold f s a).
    Proof.
      simple induction s.
      simpl in |- *; intuition.
      simpl in |- *; intros.
      rewrite H.
      simpl.
      apply H0.
    Qed.

    Lemma fold_equiv :
      forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A),
        fold f s a = fold' f s a.
    Proof.
      unfold fold', elements in |- *.
      simple induction s; simpl in |- *; auto; intros.
      rewrite fold_equiv_aux.
      rewrite H0.
      simpl in |- *; auto.
    Qed.

    Lemma fold_1 :
      forall (s:t)(Hs:bst s)(A : Type)(f : elt -> A -> A)(i : A),
        fold f s i = fold_left (fun a e => f e a) (elements s) i.
    Proof.
      intros.
      rewrite fold_equiv.
      unfold fold'.
      rewrite SetList.SetList.fold_1.
      unfold SetList.SetList.elements; auto.
      apply elements_sort; auto.
    Qed.

    (** * Subset *)

    Lemma subsetl_12 : forall subset_l1 l1 x1 h1 s2,
      bst (Node l1 x1 Leaf h1) -> bst s2 ->
      (forall s, bst s -> (subset_l1 s = true <-> Subset l1 s)) ->
      (subsetl subset_l1 x1 s2 = true <-> Subset (Node l1 x1 Leaf h1) s2 ).
    Proof.
      induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
      unfold Subset; intuition; try discriminate.
      assert (H': In x1 Leaf) by auto; inversion H'.
      inversion_clear H0.
      specialize (IHl2 H H2 H1).
      specialize (IHr2 H H3 H1).
      inv bst. clear H8.
      destruct (compare_dec x1 x2).

      rewrite IHl2; clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; eauto; order.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; eauto; order.

      rewrite H1 by auto; clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (a === x2) by order; intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

      rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto; clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (H':=mem_2 H8); apply In_1 with x1; auto.
      apply mem_1; auto.
      assert (In x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.
    Qed.


    Lemma subsetr_12 : forall subset_r1 r1 x1 h1 s2,
      bst (Node Leaf x1 r1 h1) -> bst s2 ->
      (forall s, bst s -> (subset_r1 s = true <-> Subset r1 s)) ->
      (subsetr subset_r1 x1 s2 = true <-> Subset (Node Leaf x1 r1 h1) s2).
    Proof.
      induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
      unfold Subset; intuition; try discriminate.
      assert (H': In x1 Leaf) by auto; inversion H'.
      inversion_clear H0.
      specialize (IHl2 H H2 H1).
      specialize (IHr2 H H3 H1).
      inv bst. clear H7.
      destruct (compare_dec x1 x2).

      rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto;  clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (H':=mem_2 H7); apply In_1 with x1; auto.
      apply mem_1; auto.
      assert (In x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.

      rewrite H1 by auto; clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (a === x2) by order; intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

      rewrite IHr2; clear H1 IHl2 IHr2.
      unfold Subset. intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
    Qed.


    Lemma subset_12 : forall s1 s2, bst s1 -> bst s2 ->
      (subset s1 s2 = true <-> Subset s1 s2).
    Proof.
      induction s1 as [|l1 IHl1 x1 r1 IHr1 h1]; simpl; intros.
      unfold Subset; intuition_in; eauto.
      destruct s2 as [|l2 x2 r2 h2]; simpl; intros.
      unfold Subset; intuition_in; try discriminate.
      assert (H': In x1 Leaf) by auto; inversion H'.
      inv bst.
      destruct (compare_dec x1 x2).

      rewrite <-andb_lazy_alt, andb_true_iff, IHr1 by auto.
      rewrite (@subsetl_12 (subset l1) l1 x1 h1) by auto.
      clear IHl1 IHr1.
      unfold Subset; intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

      rewrite <-andb_lazy_alt, andb_true_iff, IHl1, IHr1 by auto.
      clear IHl1 IHr1.
      unfold Subset; intuition_in; eauto.
      assert (a === x2) by order; intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

      rewrite <-andb_lazy_alt, andb_true_iff, IHl1 by auto.
      rewrite (@subsetr_12 (subset r1) r1 x1 h1) by auto.
      clear IHl1 IHr1.
      unfold Subset; intuition_in; eauto.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
      assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
    Qed.

    (** * Comparison *)

    (** ** Relations [eq] and [lt] over trees *)

    Definition eq := Equal.
    Definition lt (s1 s2 : t) : Prop :=
      list_lt _lt _eq (elements s1) (elements s2).

    Lemma eq_refl : forall s : t, Equal s s.
    Proof.
      unfold Equal; intuition.
    Qed.
    Lemma eq_sym : forall s s' : t, Equal s s' -> Equal s' s.
    Proof.
      unfold Equal; intros s s' H x; destruct (H x); split; auto.
    Qed.
    Lemma eq_trans : forall s s' s'' : t,
      Equal s s' -> Equal s' s'' -> Equal s s''.
    Proof.
      unfold Equal; intros s s' s'' H1 H2 x;
        destruct (H1 x); destruct (H2 x); split; auto.
    Qed.

    Lemma eq_L_eq :
      forall s s' : t, Equal s s' ->
        SetList.SetList.Equal (elements s) (elements s').
    Proof.
      unfold Equal, SetList.SetList.Equal;
        intros; do 2 rewrite elements_in; auto.
    Qed.

    Lemma L_eq_eq :
      forall s s' : t, SetList.SetList.Equal (elements s) (elements s') ->
        Equal s s'.
    Proof.
      unfold Equal, SetList.SetList.Equal; intros;
        do 2 rewrite <-elements_in; auto.
    Qed.
    Hint Resolve eq_L_eq L_eq_eq.

    Definition lt_trans (s s' s'' : t) (h : lt s s')
      (h' : lt s' s'') : lt s s''.
    Proof.
      unfold lt in *.
      etransitivity; eauto.
    Qed.

    Lemma lt_not_eq : forall s s' : t,
      bst s -> bst s' -> lt s s' -> ~ Equal s s'.
    Proof.
      unfold lt in |- *; intros; intro.
      apply (@StrictOrder_Irreflexive _ _ _ _ (list_StrictOrder Helt) (elements s) (elements s') H1).
      assert (Hs : sort _lt (elements s)) by auto.
      assert (Hs' : sort _lt (elements s')) by auto.
      set (S := SetList.Build_set Hs). set (S' := SetList.Build_set Hs').
      change (SetList.SetList.set_eq (SetList.this S) (SetList.this S')).
      rewrite <- (SetList.Equal_set_eq S S').
      unfold SetList.Equal, SetList.In; simpl.
      apply eq_L_eq; auto.
    Qed.

    Lemma L_eq_cons :
      forall (l1 l2 : list elt) (x y : elt),
        x === y -> SetList.SetList.Equal l1 l2 ->
        SetList.SetList.Equal (x :: l1) (y :: l2).
    Proof.
      unfold SetList.SetList.Equal in |- *; intuition.
      inversion_clear H1; generalize (H0 a); clear H0; intuition.
      constructor; order.
      inversion_clear H1; generalize (H0 a); clear H0; intuition.
      constructor; order.
    Qed.
    Hint Resolve L_eq_cons.

    (** * A new comparison algorithm suggested by Xavier Leroy *)

    (** [flatten_e e] returns the list of elements of [e] i.e. the list *)
    (*     of elements actually compared *)

    Fixpoint flatten_e (e : enumeration) : list elt :=
      match e with
        | End => nil
        | More x t r => (x :: elements t ++ flatten_e r)%list
      end.

    Lemma flatten_e_elements :
      forall l x r h e,
        (elements l ++ flatten_e (More x r e) =
          elements (Node l x r h) ++ flatten_e e)%list.
    Proof.
      intros; simpl; apply elements_node.
    Qed.

    Lemma cons_1 : forall s e,
      flatten_e (cons s e) = (elements s ++ flatten_e e)%list.
    Proof.
      induction s; simpl; auto; intros.
      rewrite IHs1; apply flatten_e_elements.
    Qed.

    (** Correctness of this comparison *)

    Definition Cmp c : list elt -> list elt -> Prop :=
      match c with
        | Eq => SetList.SetList.Equal
        | Lt => list_lt _lt _eq
        | Gt => flip (list_lt _lt _eq)
      end.

    Lemma cons_Cmp : forall c x1 x2 l1 l2, x1 === x2 ->
      Cmp c l1 l2 -> Cmp c (x1::l1) (x2::l2).
    Proof.
      destruct c; simpl; unfold flip; intros; eauto; constructor 3; auto.
    Qed.
    Hint Resolve cons_Cmp.

    Lemma compare_end_Cmp :
      forall e2, Cmp (compare_end e2) nil (flatten_e e2).
    Proof.
      destruct e2; simpl; auto.
      intro; reflexivity.
      constructor.
    Qed.

    Lemma compare_more_Cmp : forall x1 cont x2 r2 e2 l,
      Cmp (cont (cons r2 e2)) l (elements r2 ++ flatten_e e2) ->
      Cmp (compare_more x1 cont (More x2 r2 e2)) (x1::l)
      (flatten_e (More x2 r2 e2)).
    Proof.
      simpl; intros; destruct (compare_dec x1 x2); simpl; auto;
        constructor 2; auto.
    Qed.

    Lemma compare_cont_Cmp : forall s1 cont e2 l,
      (forall e, Cmp (cont e) l (flatten_e e)) ->
      Cmp (compare_cont s1 cont e2) (elements s1 ++ l) (flatten_e e2).
    Proof.
      induction s1 as [|l1 Hl1 x1 r1 Hr1 h1]; simpl; intros; auto.
      rewrite <- elements_node; simpl.
      apply Hl1; auto. clear e2. intros [|x2 r2 e2].
      simpl; auto; constructor.
      apply compare_more_Cmp.
      rewrite <- cons_1; auto.
    Qed.

    Lemma compare_Cmp : forall s1 s2,
      Cmp (compare s1 s2) (elements s1) (elements s2).
    Proof.
      intros; unfold compare.
      rewrite (app_nil_end (elements s1)).
      replace (elements s2) with (flatten_e (cons s2 End)) by
      (rewrite cons_1; simpl; rewrite <- app_nil_end; auto).
      apply compare_cont_Cmp; auto.
      intros.
      apply compare_end_Cmp; auto.
    Qed.

    (** * Equality test *)

    Lemma equal_1 : forall s1 s2, bst s1 -> bst s2 ->
      Equal s1 s2 -> equal s1 s2 = true.
    Proof.
      unfold equal; intros s1 s2 B1 B2 E.
      generalize (compare_Cmp s1 s2).
      destruct (compare s1 s2); simpl in *; auto; intros.
      elim (lt_not_eq B1 B2 H E); auto.
      elim (lt_not_eq B2 B1 H (eq_sym E)); auto.
    Qed.

    Lemma equal_2 : forall s1 s2,
      equal s1 s2 = true -> Equal s1 s2.
    Proof.
      unfold equal; intros s1 s2 E.
      generalize (compare_Cmp s1 s2);
        destruct compare; auto; discriminate.
    Qed.

  End Proofs.
End SetAVL.

(** * Encapsulation *)

(*    Now, in order to really provide a functor implementing [S], we  *)
(*    need to encapsulate everything into a type of binary search trees.  *)
(*    They also happen to be well-balanced, but this has no influence  *)
(*    on the correctness of operations, so we won't state this here,  *)
(*    see [FSetFullAVL] if you need more than just the FSet interface. *)
(* *)
Module S := SetAVL.

Structure set (elt : Type) `{Helt : OrderedType elt}
  := Bst {this :> @S.tree elt Helt; is_bst : S.bst this}.
Implicit Arguments this [[elt] [Helt]].
Implicit Arguments Bst [[elt] [Helt] [this]].
Implicit Arguments is_bst [[elt] [Helt]].

Section SetDefinitions.
  Context `{Helt : OrderedType elt}.
  Let t := set elt.

  Definition In (x : elt) (s : t) := S.In x s.
  Definition Equal (s s':t) := forall a : elt, In a s <-> In a s'.
  Definition Subset (s s':t) := forall a : elt, In a s -> In a s'.
  Definition Empty (s:t) := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s:t) := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s:t) := exists x, In x s /\ P x.

  Lemma In_1 : forall (s:t)(x y:elt), x === y -> In x s -> In y s.
  Proof. intro s; exact (@S.In_1 _ _ s). Qed.

  Definition mem (x:elt)(s:t) : bool := S.mem x s.

  Definition empty : t := Bst S.empty_bst.
  Definition is_empty (s:t) : bool := S.is_empty s.
  Definition singleton (x:elt) : t := Bst (S.singleton_bst x).
  Definition add (x:elt)(s:t) : t := Bst (S.add_bst x (is_bst s)).
  Definition remove (x:elt)(s:t) : t := Bst (S.remove_bst x (is_bst s)).
  Definition inter (s s':t) : t := Bst (S.inter_bst (is_bst s) (is_bst s')).
  Definition union (s s':t) : t := Bst (S.union_bst (is_bst s) (is_bst s')).
  Definition diff (s s':t) : t := Bst (S.diff_bst (is_bst s) (is_bst s')).
  Definition elements (s:t) : list elt := S.elements s.
  Definition min_elt (s:t) : option elt := S.min_elt s.
  Definition max_elt (s:t) : option elt := S.max_elt s.
  Definition choose (s:t) : option elt := S.choose s.
  Definition map_monotonic `{HB : OrderedType B} (f : elt -> B)
    `{Proper _ (_lt ==> _lt) f} (s : t) : set B :=
    Bst (S.map_monotonic_bst (is_bst s)).
  Definition fold (B : Type) (f : elt -> B -> B) (s:t) : B -> B := S.fold f s.
  Definition cardinal (s:t) : nat := S.cardinal s.
  Definition filter (f : elt -> bool) (s:t) : t :=
    Bst (S.filter_bst f (is_bst s)).
  Definition for_all (f : elt -> bool) (s:t) : bool := S.for_all f s.
  Definition exists_ (f : elt -> bool) (s:t) : bool := S.exists_ f s.
  Definition partition (f : elt -> bool) (s:t) : t * t :=
    let p := S.partition f s in
      (@Bst _ _ (fst p) (S.partition_bst_1 f (is_bst s)),
        @Bst _ _ (snd p) (S.partition_bst_2 f (is_bst s))).

  Definition equal (s s':t) : bool := S.equal s s'.
  Definition subset (s s':t) : bool := S.subset s s'.

  Definition eq (s s':t) : Prop := S.Equal s s'.
  Definition lt (s s':t) : Prop := S.lt s s'.

(*   Definition compare (s s':t) : Compare lt eq s s'. *)
(*   Proof. *)
(*     intros (s,b) (s',b'). *)
(*     generalize (compare_Cmp s s'). *)
(*     destruct Raw.compare; intros; [apply EQ|apply LT|apply GT]; red; auto. *)
(*   Defined. *)

(*   Definition eq_dec (s s':t) : { eq s s' } + { ~ eq s s' }. *)
(*   Proof. *)
(*     intros (s,b) (s',b'); unfold eq; simpl. *)
(*     case_eq (Raw.equal s s'); intro H; [left|right]. *)
(*     apply equal_2; auto. *)
(*     intro H'; rewrite equal_1 in H; auto; discriminate. *)
(*   Defined. *)

  (* specs *)
  Section Specs.
    Variable s s' s'': t.
    Variable x y : elt.

    Hint Resolve is_bst.

    Lemma mem_1 : In x s -> mem x s = true.
    Proof. exact (S.mem_1 (is_bst s)). Qed.
    Lemma mem_2 : mem x s = true -> In x s.
    Proof. exact (@S.mem_2 _ _ s x). Qed.

    Lemma equal_1 : Equal s s' -> equal s s' = true.
    Proof. exact (S.equal_1 (is_bst s) (is_bst s')). Qed.
    Lemma equal_2 : equal s s' = true -> Equal s s'.
    Proof. exact (@S.equal_2 _ _ s s'). Qed.

    Ltac wrap t H := unfold t, In; simpl; rewrite H; auto; intuition.

    Lemma subset_1 : Subset s s' -> subset s s' = true.
    Proof. wrap subset S.subset_12. Qed.
    Lemma subset_2 : subset s s' = true -> Subset s s'.
    Proof. wrap subset S.subset_12. Qed.

    Lemma empty_1 : Empty empty.
    Proof. exact S.empty_1. Qed.

    Lemma is_empty_1 : Empty s -> is_empty s = true.
    Proof. exact (@S.is_empty_1 _ _ s). Qed.
    Lemma is_empty_2 : is_empty s = true -> Empty s.
    Proof. exact (@S.is_empty_2 _ _ s). Qed.

    Lemma add_1 : x === y -> In y (add x s).
    Proof. wrap add S.add_in. Qed.
    Lemma add_2 : In y s -> In y (add x s).
    Proof. wrap add S.add_in. Qed.
    Lemma add_3 : x =/= y -> In y (add x s) -> In y s.
    Proof. wrap add S.add_in. elim H; auto. Qed.

    Lemma remove_1 : x === y -> ~ In y (remove x s).
    Proof. wrap remove S.remove_in. Qed.
    Lemma remove_2 : ~ x === y -> In y s -> In y (remove x s).
    Proof. wrap remove S.remove_in. Qed.
    Lemma remove_3 : In y (remove x s) -> In y s.
    Proof. wrap remove S.remove_in. Qed.

    Lemma singleton_1 : In y (singleton x) -> x === y.
    Proof. exact (@S.singleton_1 _ _ x y). Qed.
    Lemma singleton_2 : x === y -> In y (singleton x).
    Proof. exact (@S.singleton_2 _ _ x y). Qed.

    Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
    Proof. wrap union S.union_in. Qed.
    Lemma union_2 : In x s -> In x (union s s').
    Proof. wrap union S.union_in. Qed.
    Lemma union_3 : In x s' -> In x (union s s').
    Proof. wrap union S.union_in. Qed.

    Lemma inter_1 : In x (inter s s') -> In x s.
    Proof. wrap inter S.inter_in. Qed.
    Lemma inter_2 : In x (inter s s') -> In x s'.
    Proof. wrap inter S.inter_in. Qed.
    Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
    Proof. wrap inter S.inter_in. Qed.

    Lemma diff_1 : In x (diff s s') -> In x s.
    Proof. wrap diff S.diff_in. Qed.
    Lemma diff_2 : In x (diff s s') -> ~ In x s'.
    Proof. wrap diff S.diff_in. Qed.
    Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
    Proof. wrap diff S.diff_in. Qed.

    Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold A f s i = fold_left (fun a e => f e a) (elements s) i.
    Proof. unfold fold, elements; intros; apply S.fold_1; auto. Qed.

    Lemma cardinal_1 : cardinal s = length (elements s).
    Proof.
      unfold cardinal, elements; intros; apply S.elements_cardinal; auto.
    Qed.

    Section Filter.
      Variable f : elt -> bool.

      Lemma filter_1 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        In x (filter f s) -> In x s.
      Proof. wrap filter S.filter_in. Qed.
      Lemma filter_2 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        In x (filter f s) -> f x = true.
      Proof. wrap filter S.filter_in. Qed.
      Lemma filter_3 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        In x s -> f x = true -> In x (filter f s).
      Proof. wrap filter S.filter_in. Qed.

      Lemma for_all_1 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        For_all (fun x => f x = true) s -> for_all f s = true.
      Proof. apply (@S.for_all_1 _ _ f s H). Qed.
      Lemma for_all_2 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        for_all f s = true -> For_all (fun x => f x = true) s.
      Proof. apply (@S.for_all_2 _ _ f s H). Qed.

      Lemma exists_1 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        Exists (fun x => f x = true) s -> exists_ f s = true.
      Proof. apply (@S.exists_1 _ _ f s H). Qed.
      Lemma exists_2 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        exists_ f s = true -> Exists (fun x => f x = true) s.
      Proof. apply (@S.exists_2 _ _ f s H). Qed.

      Lemma partition_1 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        Equal (fst (partition f s)) (filter f s).
      Proof.
        unfold partition, filter, Equal, In; simpl; intros a.
        rewrite S.partition_in_1, S.filter_in; intuition.
      Qed.

      Lemma partition_2 `{Proper _ (_eq ==> @Logic.eq bool) f} :
        Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
      Proof.
        unfold partition, filter, Equal, In; simpl; intros a.
        rewrite S.partition_in_2, S.filter_in; intuition.
        rewrite H2; auto.
        destruct (f a); auto.
        repeat intro; f_equal.
        rewrite (H _ _ H0); auto.
      Qed.

    End Filter.

    Lemma elements_1 : In x s -> InA _eq x (elements s).
    Proof. wrap elements S.elements_in. Qed.
    Lemma elements_2 : InA _eq x (elements s) -> In x s.
    Proof. wrap elements S.elements_in. Qed.
    Lemma elements_3 : sort _lt (elements s).
    Proof. exact (S.elements_sort (is_bst s)). Qed.
    Lemma elements_3w : NoDupA _eq (elements s).
    Proof. exact (S.elements_nodup (is_bst s)). Qed.

    Lemma min_elt_1 : min_elt s = Some x -> In x s.
    Proof. exact (@S.min_elt_1 _ _ s x). Qed.
    Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ y <<< x.
    Proof. exact (@S.min_elt_2 _ _ s x y (is_bst s)). Qed.
    Lemma min_elt_3 : min_elt s = None -> Empty s.
    Proof. exact (@S.min_elt_3 _ _ s). Qed.

    Lemma max_elt_1 : max_elt s = Some x -> In x s.
    Proof. exact (@S.max_elt_1 _ _ s x). Qed.
    Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ x <<< y.
    Proof. exact (@S.max_elt_2 _ _ s x y (is_bst s)). Qed.
    Lemma max_elt_3 : max_elt s = None -> Empty s.
    Proof. exact (@S.max_elt_3 _ _ s). Qed.

    Lemma choose_1 : choose s = Some x -> In x s.
    Proof. exact (@S.choose_1 _ _ s x). Qed.
    Lemma choose_2 : choose s = None -> Empty s.
    Proof. exact (@S.choose_2 _ _ s). Qed.
    Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
      Equal s s' -> x === y.
    Proof. exact (@S.choose_3 _ _ _ _ (is_bst s) (is_bst s') x y). Qed.

(*     Lemma eq_refl : eq s s. *)
(*     Proof. exact ( s). Qed. *)
(*     Lemma eq_sym : eq s s' -> eq s' s. *)
(*     Proof. exact (@S.eq_sym s s'). Qed. *)
(*     Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''. *)
(*     Proof. exact (@S.eq_trans s s' s''). Qed. *)

(*     Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''. *)
(*     Proof. exact (@S.lt_trans s s' s''). Qed. *)
(*     Lemma lt_not_eq : lt s s' -> ~eq s s'. *)
(*     Proof. exact (@S.lt_not_eq _ _ (is_bst s) (is_bst s')). Qed. *)
 End Specs.
End SetDefinitions.

(** Sets seen as an OrderedType with equality the pointwise equality [Equal] *)
Definition Equal_Equivalence `{OrderedType A} : Equivalence (@Equal A _) :=
  SetInterface.Equal_pw_Equivalence (set A) A (@In _ H).

(* Lemma Equal_set_eq `{OrderedType A} s s' : Equal s s' <-> S.set_eq s s'. *)
(* Proof. *)
(*   intros A HA [s Hs] [s' Hs']; simpl. *)
(*   unfold Equal, In; simpl; unfold SetList.set_eq. *)
(*   revert s' Hs Hs'; induction s; destruct s'; intros Hs Hs'; split; intro H. *)
(*   constructor. *)
(*   intro; split; intro abs; inversion abs. *)
(*   assert (abs : InA _eq a nil). rewrite H; constructor; auto. inversion abs. *)
(*   inversion H. *)
(*   assert (abs : InA _eq a nil). rewrite <-H; constructor; auto. inversion abs. *)
(*   inversion H. *)

(*   inversion Hs; inversion Hs'; subst. *)
(*   rewrite Inf_alt in H3 by auto; rewrite Inf_alt in H7 by auto. *)
(*   assert (Heq : a === a0). *)
(*   assert (Ha : InA _eq a (a0 :: s')). rewrite <- H; constructor; auto. *)
(*   assert (Ha' : InA _eq a0 (a :: s)). rewrite H; constructor; auto. *)
(*   inversion Ha; inversion Ha'; subst; auto. *)
(*   apply False_rec; apply (lt_not_gt (x:=a) (y:=a0)); auto. *)
(*   constructor; auto; rewrite <- IHs; auto. *)
(*   intro z; split; intro Hz. *)
(*   assert (Rz : InA _eq z (a0::s')). rewrite <- H; constructor 2; auto. *)
(*   inversion Rz; subst; auto; *)
(*     contradiction (lt_not_eq (H3 z Hz)); transitivity a0; auto. *)
(*   assert (Rz : InA _eq z (a::s)). rewrite H; constructor 2; auto. *)
(*   inversion Rz; subst; auto; *)
(*     contradiction (lt_not_eq (H7 z Hz)); transitivity a; auto. *)

(*   inversion H; subst; inversion Hs; inversion Hs'; subst. *)
(*   rewrite Inf_alt in H4 by auto; rewrite Inf_alt in H9 by auto. *)
(*   rewrite <- IHs in H5 by auto. *)
(*   intro z; split; intro Hz; inversion Hz; subst. *)
(*   constructor; transitivity a; auto. *)
(*   constructor 2; rewrite <- H5; auto. *)
(*   constructor; transitivity a0; auto. *)
(*   constructor 2; rewrite H5; auto. *)
(* Qed. *)

(* Definition set_lt `{OrderedType A} : relation (set A) := S.lt. *)
(* Program Definition set_StrictOrder `{OrderedType A} :  *)
(*   @StrictOrder _ set_lt (@Equal A _) Equal_Equivalence :=  *)
(*   Build_StrictOrder _ _ _ _ _ _. *)
(* Next Obligation. *)
(*   exact (fun x y z H1 H2 => transitivity (y:=this y) H1 H2). *)
(* Qed. *)
(* Next Obligation. *)
(*   change (~Equal x y); rewrite Equal_set_eq. *)
(*   apply lt_not_eq; auto. *)
(* Qed. *)

Definition set_compare `{OrderedType A} : set A -> set A -> comparison :=
  S.compare.

Program Instance set_OrderedType `{OrderedType A} :
  SpecificOrderedType (set A) (@Equal A _) := {
    SOT_Equivalence := Equal_Equivalence;
    SOT_lt := S.lt;
    SOT_StrictOrder := Build_StrictOrder _ _ _ _ _ _;
    SOT_cmp := set_compare
}.
Next Obligation. (* lt is transitive *)
  repeat intro; eauto using S.lt_trans.
Qed.
Next Obligation. (* lt is irreflexive *)
  apply S.lt_not_eq; auto; apply is_bst.
Qed.
Next Obligation.
  change (compare_spec (@Equal _ _) S.lt x y (S.compare x y)).
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  assert (R := SetAVL.compare_Cmp x y).
  case_eq (SetAVL.compare x y); intro Hcomp; constructor;
    rewrite Hcomp in R; unfold SetAVL.Cmp in R.
  apply S.L_eq_eq; auto.
  exact R. exact R.
Qed.