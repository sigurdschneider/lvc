Require Import Bool.
Require Import ZArith.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import MapInterface.

Set Implicit Arguments.
Generalizable All Variables.

Open Local Scope positive_scope.

(** * An implementation of [FMapInterface.S] for positive keys. *)

(** This file is an adaptation to the [FMap] framework of a work by
  Xavier Leroy and Sandrine Blazy (used for building certified compilers).
  Keys are of type [positive], and maps are binary trees: the sequence
  of binary digits of a positive number corresponds to a path in such a tree.
  This is quite similar to the [IntMap] library, except that no path compression
  is implemented, and that the current file is simple enough to be
  self-contained. *)

Module PositiveOrderedTypeBitsInstance.
  Definition t:=positive.
  Definition eq:=@eq positive.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Fixpoint bits_lt (p q:positive) { struct p } : Prop :=
   match p, q with
   | xH, _ => False
   | xO _, xH => True
   | xO p, xO q => bits_lt p q
   | xO _, xI _ => False
   | xI p, xI q => bits_lt p q
   | _, _ => True
   end.
  Definition lt := bits_lt.

  Lemma bits_lt_trans : forall x y z : positive, bits_lt x y -> bits_lt y z -> bits_lt x z.
  Proof.
  induction x.
  induction y; destruct z; simpl; eauto; intuition.
  induction y; destruct z; simpl; eauto; intuition.
  induction y; destruct z; simpl; eauto; intuition.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
  exact bits_lt_trans.
  Qed.

  Lemma bits_lt_antirefl : forall x : positive, ~ bits_lt x x.
  Proof.
  induction x; simpl; auto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros; intro.
  rewrite <- H0 in H; clear H0 y.
  unfold lt in H.
  exact (bits_lt_antirefl x H).
  Qed.

  Fixpoint compare (p q : t) : comparison :=
    match p, q with
      | xH, xH => Eq
      | xH, _ => Gt
      | xO _, xH => Lt
      | xO p, xO q => compare p q
      | xO _, xI _ => Gt
      | xI p, xI q => compare p q
      | _, _ => Lt
    end.
  Property compare_spec :
    forall p q, compare_spec (@Logic.eq _) lt p q (compare p q).
  Proof.
    induction p; destruct q; simpl; try (constructor; simpl; auto).
    destruct (IHp q); constructor; simpl; auto; congruence.
    destruct (IHp q); constructor; simpl; auto; congruence.
  Qed.

  Instance positive_rev_StrictOrder : StrictOrder lt (@Logic.eq positive) := {
    StrictOrder_Transitive := lt_trans;
    StrictOrder_Irreflexive := lt_not_eq
  }.
  Program Instance positive_rev_OrderedType : UsualOrderedType positive | 4 := {
    SOT_lt := lt;
    SOT_cmp := compare;
    SOT_StrictOrder := positive_rev_StrictOrder;
    SOT_compare_spec := compare_spec
  }.
End PositiveOrderedTypeBitsInstance.

(** Other positive stuff *)
Fixpoint reverse_positive_aux (i : positive) (j : positive) : positive :=
  match i with
  | xH => j
  | xI i' => reverse_positive_aux i' (xI j)
  | xO i' => reverse_positive_aux i' (xO j)
  end.
Definition append_positive (i : positive) (j : positive) : positive :=
  (fix apa (i : positive) :=
  match i with
  | xH => j
  | xI i' => xI (apa i')
  | xO i' => xO (apa i')
  end) i.
Definition reverse_positive (i : positive) :=
  reverse_positive_aux i xH.

Lemma simpl_rev : forall i j k,
  reverse_positive_aux (reverse_positive_aux i j) k =
  reverse_positive_aux j (append_positive i k).
Proof.
  induction i; simpl; intro j; auto.
  intro k; rewrite IHi; simpl; auto.
  intro k; rewrite IHi; simpl; auto.
Qed.

Lemma simpl_app : forall i j k,
  reverse_positive_aux (append_positive i j) k =
  reverse_positive_aux j (reverse_positive_aux i k).
Proof.
  induction i; simpl; auto; intro j; auto.
Qed.

Lemma append_positive_alt : forall i j,
  append_positive i j =
  reverse_positive_aux (reverse_positive i) j.
Proof.
  unfold reverse_positive; intros; rewrite simpl_rev; simpl; auto.
Qed.

Lemma lt_reverse_aux : forall (i j k : positive),
  PositiveOrderedTypeBitsInstance.lt j k ->
  PositiveOrderedTypeBitsInstance.lt
  (reverse_positive_aux i j) (reverse_positive_aux i k).
Proof.
  induction i; simpl; auto.
Qed.

Lemma reverse_positive_involutive_aux :
 forall (i j : positive),
 reverse_positive (reverse_positive_aux i j) =
 reverse_positive_aux j i.
Proof.
  induction i; simpl; auto; intro j; rewrite IHi; simpl; auto.
Qed.

Lemma append_positive_assoc : forall x y z,
 append_positive (append_positive x y) z =
 append_positive x (append_positive y z).
Proof.
  induction x; simpl; auto; intros; rewrite IHx; auto.
Qed.

(** The module of maps over positive keys *)

Module CPositiveMap.
  Module E.
    Definition eq (x y : positive) := @_eq positive
      (@SOT_as_OT positive _
        PositiveOrderedTypeBitsInstance.positive_rev_OrderedType) x y.
    Definition lt (x y : positive) := @_lt positive
      (@SOT_as_OT positive _
        PositiveOrderedTypeBitsInstance.positive_rev_OrderedType) x y.
  End E.
  Hint Unfold E.eq E.lt.
  Module ME := KeyOrderedType.
  Definition key := positive.

  Inductive tree (A : Type) :=
    | Leaf : A -> tree A
    | OINode : tree A -> option A -> tree A -> tree A
    | ONode : tree A -> option A -> tree A
    | INode : option A -> tree A -> tree A.

  Definition t (A : Type) := option (tree A).

  Section A.
  Variable A:Type.

  Definition empty : t A := None.

  Fixpoint is_empty (m : t A) {struct m} : bool :=
   match m with
    | None => true
    | _ => false
   end.

  Fixpoint find_aux (i : positive) (m : tree A) {struct i} : option A :=
    match i with
    | xH => match m with
            | Leaf a => Some a
            | OINode _ o _ => o
            | ONode _ o => o
            | INode o _ => o
            end
    | xI k => match m with
            | OINode _ _ r => find_aux k r
            | INode _ r => find_aux k r
            | _ => None
            end
    | xO k => match m with
            | OINode l _ _ => find_aux k l
            | ONode l _ => find_aux k l
            | _ => None
            end
    end.
  Definition find (i : positive) (m : t A) : option A :=
    match m with
    | None => None
    | Some t => find_aux i t
    end.

  Fixpoint mem_aux (i : positive) (m : tree A) {struct i} : bool :=
    match i, m with
    | xH, Leaf _ => true
    | xH, OINode _ (Some _) _ => true
    | xH, INode (Some _) _ => true
    | xH, ONode _ (Some _) => true
    | xI k, OINode _ _ r => mem_aux k r
    | xI k, INode _ r => mem_aux k r
    | xO k, OINode l _ _ => mem_aux k l
    | xO k, ONode l _ => mem_aux k l
    | _, _ => false
    end.
  Definition mem (i : positive) (m : t A) : bool :=
    match m with
    | None => false
    | Some t => mem_aux i t
    end.

  Definition make_branch (v : A) : positive -> tree A :=
  fix mb (i : positive) :=
  match i with
  | xH => Leaf v
  | xO k => ONode (mb k) None
  | xI k => INode None (mb k)
  end.
  Definition add_aux (v : A) : positive -> tree A -> tree A :=
  fix aa (i : positive) (m : tree A) {struct i} : tree A :=
    match i, m with
    | xH, Leaf _ => Leaf v
    | xH, OINode l _ r => OINode l (Some v) r
    | xH, INode _ r => INode (Some v) r
    | xH, ONode l _ => ONode l (Some v)
    | xI k, Leaf a => INode (Some a) (make_branch v k)
    | xI k, OINode l o r => OINode l o (aa k r)
    | xI k, ONode l o => OINode l o (make_branch v k)
    | xI k, INode o r => INode o (aa k r)
    | xO k, Leaf a => ONode (make_branch v k) (Some a)
    | xO k, OINode l o r => OINode (aa k l) o r
    | xO k, ONode l o => ONode (aa k l) o
    | xO k, INode o r => OINode (make_branch v k) o r
    end.
  Definition add (i : positive) (v : A) (m : t A) : t A :=
    match m with
    | None => Some (make_branch v i)
    | Some t => Some (add_aux v i t)
    end.

  (* A faire en un seul parcours *)
  Definition insert (i : positive) (v : A) (f : A -> A) (m : t A) : t A :=
    match find i m with
      | Some c => add i (f c) m
      | None => add i v m
    end.
  Definition adjust (i : positive) (f : A -> A) (m : t A) : t A :=
    match find i m with
      | Some c => add i (f c) m
      | None => m
    end.

  Fixpoint remove_aux (i : positive) (m : tree A) : option (tree A) :=
    match i, m with
    | xH, Leaf _ => None
    | xH, OINode l _ r => Some (OINode l None r)
    | xH, INode _ r => Some (INode None r)
    | xH, ONode l _ => Some (ONode l None)
    | xI k, Leaf a => Some (Leaf a)
    | xI k, OINode l o r => match remove_aux k r with
                            | None => Some (ONode l o)
                            | Some r' => Some (OINode l o r')
                            end
    | xI k, ONode l o => Some (ONode l o)
    | xI k, INode o r => match remove_aux k r with
                         | None => match o with
                                   | None => None
                                   | Some a => Some (Leaf a)
                                   end
                         | Some r' => Some (INode o r')
                         end
    | xO k, Leaf a => Some (Leaf a)
    | xO k, OINode l o r => match remove_aux k l with
                            | None => Some (INode o r)
                            | Some l' => Some (OINode l' o r)
                            end
    | xO k, ONode l o => match remove_aux k l with
                         | None => match o with
                                   | None => None
                                   | Some a => Some (Leaf a)
                                   end
                         | Some l' => Some (ONode l' o)
                         end
    | xO k, INode o r => Some (INode o r)
    end.
  Definition remove (i : positive) (m : t A) : t A :=
    match m with
    | None => None
    | Some t => remove_aux i t
    end.

  (** [elements] *)
  Definition op_cons (a : option A) (i : positive) (l : list (positive * A))
    := match a with None => l | Some a => (reverse_positive i, a)::l end.
  Fixpoint xelements_aux (m : tree A) (i : positive)
                         (acc : list (positive * A)) {struct m}
             : list (positive * A) :=
      match m with
      | Leaf a => (reverse_positive i, a)::acc
      | OINode l o r => xelements_aux r (xI i)
                          (xelements_aux l (xO i) (op_cons o i acc))
      | ONode l o => xelements_aux l (xO i) (op_cons o i acc)
      | INode o r => xelements_aux r (xI i) (op_cons o i acc)
      end.
  (* Note: function [xelements] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)
  Definition elements (m : t A) :=
    match m with
    | None => nil
    | Some t => xelements_aux t xH nil
    end.

  (** [cardinal] *)
  Definition op_add (a : option A) (n : nat)
    := match a with None => n | Some a => S n end.
  Fixpoint cardinal_aux (m : tree A) (n : nat) : nat :=
    match m with
      | Leaf _ => S n
      | OINode l o r => cardinal_aux r (cardinal_aux l (op_add o n))
      | ONode l o => cardinal_aux l (op_add o n)
      | INode o r => cardinal_aux r (op_add o n)
    end.
  Definition cardinal (m : t A) : nat :=
    match m with
    | None => O
    | Some t => cardinal_aux t O
    end.

  Section CompcertSpec.

  Theorem gempty:
    forall (i: positive), find i empty = None.
  Proof.
    destruct i; simpl; auto.
  Qed.

  Lemma gss_aux:
    forall (i: positive) (x: A),
      find_aux i (make_branch x i) = Some x.
  Proof.
    induction i; simpl; auto.
  Qed.
  Theorem gss:
    forall (i: positive) (x: A) (m: t A), find i (add i x m) = Some x.
  Proof.
    destruct m as [treeA|]; simpl;
    (revert treeA; induction i; destruct treeA; simpl; auto)||idtac;
    apply gss_aux.
  Qed.

  Lemma gso_aux:
    forall (i j: positive) (x: A),
    i <> j -> find_aux i (make_branch x j) = None.
  Proof.
    induction i; intros; destruct j; simpl; auto; try apply IHi; congruence.
  Qed.
  Theorem gso:
    forall (i j: positive) (x: A) (m: t A),
    i <> j -> find i (add j x m) = find i m.
  Proof.
    destruct m as [treeA|]; simpl; auto.
    revert j treeA; induction i; destruct j; destruct treeA; simpl;
    intro H; apply gso_aux||apply IHi||idtac; congruence.
    apply gso_aux; congruence.
  Qed.

  Lemma grs_aux:
    forall (i: positive) (m: tree A), find i (remove_aux i m) = None.
  Proof.
    induction i; destruct m; simpl; auto.
    assert (H' := IHi m2); destruct (remove_aux i m2); simpl in *; auto.
    assert (H' := IHi m); destruct (remove_aux i m); simpl in *; auto;
    destruct o; simpl in *; auto.
    assert (H' := IHi m1); destruct (remove_aux i m1); simpl in *; auto.
    assert (H' := IHi m); destruct (remove_aux i m); simpl in *; auto;
    destruct o; simpl in *; auto.
  Qed.
  Theorem grs:
    forall (i: positive) (m: t A), find i (remove i m) = None.
  Proof.
    destruct m as [treeA|]; simpl; auto; apply grs_aux.
  Qed.

  Lemma gro_aux:
    forall (i j: positive) (m: tree A),
    i <> j -> find i (remove_aux j m) = find_aux i m.
  Proof.
    induction i; destruct j; destruct m; simpl; auto; intro diff;
    (destruct (remove_aux j m1); simpl; easy)||
    (destruct (remove_aux j m2); simpl; easy)||
    (destruct (remove_aux j m); simpl; auto; destruct o; simpl; easy)||
    congruence||idtac.
    assert (H' := IHi j m2); destruct (remove_aux j m2); simpl in *;
      apply H'; congruence.
    assert (H' := IHi j m); destruct (remove_aux j m); simpl in *.
      apply H'; congruence.
      destruct o; simpl; apply H'; congruence.
    assert (H' := IHi j m1); destruct (remove_aux j m1); simpl in *;
      apply H'; congruence.
    assert (H' := IHi j m); destruct (remove_aux j m); simpl in *.
      apply H'; congruence.
      destruct o; simpl; apply H'; congruence.
  Qed.
  Theorem gro:
    forall (i j: positive) (m: t A),
    i <> j -> find i (remove j m) = find i m.
  Proof.
    destruct m as [treeA|]; simpl; auto; apply gro_aux.
  Qed.

  Lemma xelements_conservation:
      forall (k : positive * A) (m: tree A) (j : positive)
             (l : list (positive * A)),
      List.In k l ->
      List.In k (xelements_aux m j l).
  Proof.
    induction m; simpl; intuition;
    [apply IHm2; apply IHm1 | apply IHm | apply IHm];
    destruct o; simpl; auto.
  Qed.
  Lemma xelements_correct:
      forall (v : A) (m: tree A) (i j : positive) (l : list (positive * A)),
      find_aux i m = Some v ->
       List.In (reverse_positive_aux j i, v) (xelements_aux m j l).
    Proof.
      induction m; destruct i; simpl; intros;
      try discriminate H; try rewrite H; simpl;

      (inversion_clear H; left; easy)||
      refine (IHm2 i (xI j) _ H)||
      refine (IHm i (xO j) _ H)||
      refine (IHm i (xI j) _ H)||
      idtac;

      apply xelements_conservation;
      (left; easy)||
      (refine (IHm1 i (xO j) _ H))||
      apply xelements_conservation;
      left; easy.
   Qed.

  Theorem elements_correct:
    forall (m: t A) (i: positive) (v: A),
    find i m = Some v -> List.In (i, v) (elements m).
  Proof.
    intros m i v H.
    destruct m as [treeA|]; simpl.
    exact (xelements_correct treeA i xH nil H).
    discriminate H.
  Qed.

  Lemma xelements_complete:
      forall (v: A) (m: tree A) (j k : positive) (l : list (positive * A)),
      List.In (k, v) (xelements_aux m j l) ->
      ((exists i, find_aux i m = Some v /\ k = reverse_positive_aux j i) \/
       List.In (k, v) l).
  Proof.
    induction m; simpl; intros;

    (destruct (IHm2 (xI _) _ _ H) as [[i [Hfind Heq]]|HIn'];
      [|destruct (IHm1 (xO _) _ _ HIn') as [[i [Hfind Heq]]|HIn]])||
    destruct (IHm (xO _) _ _ H) as [[i [Hfind Heq]]|HIn]||
    destruct (IHm (xI _) _ _ H) as [[i [Hfind Heq]]|HIn]||
    assert (HIn := H);

    (left; exists (xI i); simpl in *; split; easy)||
    (left; exists (xO i); simpl in *; split; easy)||
    (destruct o; simpl in HIn; auto)||
    idtac;

    (destruct HIn as [H'|K];
      [inversion H'; left; exists xH; simpl; easy
      |right; exact K]).
  Qed.

  Theorem elements_complete:
    forall (m: t A) (i: positive) (v: A),
    List.In (i, v) (elements m) -> find i m = Some v.
  Proof.
    intros m i v H.
    destruct m as [treeA|]; simpl.
    destruct (xelements_complete v treeA xH i nil H) as [[i' [Hfind Heq]]|abs].
      simpl in Heq; rewrite Heq; assumption.
      simpl in abs; destruct abs.
    destruct H.
  Qed.

  Lemma cardinal_op :
    forall (o : option A) (i : positive) (l : list (positive * A)),
      op_add o (length l) = length (op_cons o i l).
  Proof.
    destruct o; easy.
  Qed.
  Lemma cardinal_1_aux :
   forall (m: tree A) (i : positive) (l : list (positive * A)),
   cardinal_aux m (length l) = length (xelements_aux m i l).
  Proof.
    induction m; intros i l; simpl; auto;
    rewrite (cardinal_op _ i); auto.
    rewrite (IHm1 (xO i)); rewrite (IHm2 (xI i)); easy.
  Qed.
  Lemma cardinal_1 :
   forall (m: t A), cardinal m = length (elements m).
  Proof.
    destruct m as [treeA|]; simpl; auto.
    exact (cardinal_1_aux treeA xH nil).
  Qed.

  End CompcertSpec.

  Definition MapsTo (i:positive)(v:A)(m:t A) := find i m = Some v.

  Definition In (i:positive)(m:t A) := exists e:A, MapsTo i e m.

  Definition Empty m := forall (a : positive)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':positive*A) := E.eq (fst p) (fst p').

  Definition eq_key_elt (p p':positive*A) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':positive*A) :=
    @ME.ltk positive (@SOT_as_OT _ _
      PositiveOrderedTypeBitsInstance.positive_rev_OrderedType) _ p p'.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
  destruct m as [treeA|]; simpl; auto;
  induction treeA; destruct x; simpl; auto.
  Qed.

  Section FMapSpec.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct (find x m).
  exists a; auto.
  intros; discriminate.
  Qed.

  Lemma MapsTo_1 : forall m x y e,
     E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : forall m x e,
     MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : forall m x e,
     find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  unfold Empty, MapsTo; simpl.
  congruence.
  Qed.

  Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
  Proof.
  unfold Empty, MapsTo; destruct m as [treeA|]; simpl; auto.
  intro H; induction treeA; simpl in *.
  destruct (H xH a); simpl; auto.
  apply (IHtreeA1 (fun a e => H (xO a) e)).
  apply (IHtreeA (fun a e => H (xO a) e)).
  apply (IHtreeA (fun a e => H (xI a) e)).
  Qed.

  Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
  Proof.
  destruct m as [treeA|]; simpl.
  congruence.
  unfold Empty, MapsTo; simpl; congruence.
  Qed.

  Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
  Proof.
  unfold MapsTo.
  intros; rewrite H; clear H.
  apply gss.
  Qed.

  Lemma add_2 : forall m x y e e',
    ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
  unfold MapsTo.
  intros; rewrite gso; auto.
  Qed.

  Lemma add_3 : forall m x y e e',
    ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  intros x y e e' m H; rewrite gso; auto.
  Qed.

  Lemma insert_1 : forall m x y e d f, E.eq x y -> MapsTo y e m ->
    MapsTo y (f e) (insert x d f m).
  Proof.
    unfold MapsTo, insert; intros m x y e d f H; rewrite !H; clear H.
    intro H; rewrite H; apply find_1; apply add_1; reflexivity.
  Qed.

  Lemma insert_2 : forall m x y d f, E.eq x y -> ~ In y m ->
    MapsTo y d (insert x d f m).
  Proof.
    unfold MapsTo, insert.
    intros m x y d f H abs; rewrite !H; auto.
    case_eq (find y m); auto; intros.
    contradiction abs; exists a; auto.
    apply find_1; apply add_1; reflexivity.
  Qed.

  Lemma insert_3 : forall m x y e d f, ~ E.eq x y -> MapsTo y e m ->
    MapsTo y e (insert x d f m).
  Proof.
    unfold MapsTo, insert; intros.
    case_eq (find x m); intros; apply find_1; apply add_2; auto.
  Qed.

  Lemma insert_4 : forall m x y e d f,
    ~ E.eq x y -> MapsTo y e (insert x d f m) -> MapsTo y e m.
  Proof.
    unfold MapsTo, insert; intros.
    case_eq (find x m); intros; rewrite H1 in H0;
    apply find_1; eapply add_3; eauto.
  Qed.

  Lemma adjust_1 : forall m x y e f, E.eq x y -> MapsTo y e m ->
    MapsTo y (f e) (adjust x f m).
  Proof.
    unfold MapsTo, adjust; intros m x y e f H; rewrite !H; clear H.
    intro H; rewrite H; apply find_1; apply add_1; reflexivity.
  Qed.

  Lemma adjust_2 : forall m x y e f, ~ E.eq x y -> MapsTo y e m ->
    MapsTo y e (adjust x f m).
  Proof.
    unfold MapsTo, adjust; intros m x y e f E H.
    case_eq (find x m); intros; apply find_1.
    apply add_2; auto. auto.
  Qed.

  Lemma adjust_3 : forall m x y e f, ~ E.eq x y -> MapsTo y e (adjust x f m) ->
    MapsTo y e m.
  Proof.
    unfold MapsTo, adjust; intros.
    case_eq (find x m); intros; rewrite H1 in H0; apply find_1.
    eapply add_3; eauto.
    auto.
  Qed.

  Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
  Proof.
  intros; intro.
  generalize (mem_1 H0).
  rewrite mem_find.
  red in H.
  rewrite H.
  rewrite grs.
  intros; discriminate.
  Qed.

  Lemma remove_2 : forall m x y e,
    ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
  unfold MapsTo.
  intros m x y e H; rewrite gro; auto.
  Qed.

  Lemma remove_3 : forall m x y e,
    MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  intros m x y e.
  destruct (eq_dec x y).
  rewrite H in *.
  rewrite grs; intros; discriminate.
  rewrite gro; auto.
  Qed.

  Lemma elements_1 : forall m x e,
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
  unfold MapsTo.
  intros m x e.
  rewrite InA_alt.
  intro H.
  exists (x,e).
  split.
  red; simpl; unfold E.eq; auto.
  apply elements_correct; auto.
  Qed.

  Lemma elements_2 : forall m x e,
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
  unfold MapsTo.
  intros m x e.
  rewrite InA_alt.
  intros ((e0,a),(H,H0)).
  red in H; simpl in H; unfold E.eq in H; destruct H; subst.
  rewrite H in *.
  apply elements_complete; auto.
  Qed.

  (** The following theorem should occur in the Sorting module *)
  Theorem lelistA_weakening :
    forall (A : Type) (leA : A -> A -> Prop)
           (leA_trans : forall x y z:A, leA x y -> leA y z -> leA x z)
           (x y : A), leA x y ->
           forall (l : list A), lelistA leA y l -> lelistA leA x l.
  Proof.
    intros T leT leTtrans X Y HleT l.
    induction l as [|head tail]; simpl; intros.
      apply nil_leA.
      apply cons_leA.
      apply leTtrans with Y; auto.
      apply (lelistA_inv H).
  Qed.

  Lemma lt_key_trans : forall x y z, lt_key x y -> lt_key y z -> lt_key x z.
  Proof.
    intros kx ky kz;
    destruct kx; destruct ky; destruct kz; unfold lt_key; simpl.
    apply transitivity.
  Qed.

  Lemma lelistA_op_consO : forall E i a l,
     lelistA lt_key (reverse_positive i, E) l ->
     lelistA lt_key (reverse_positive_aux i 2, E) (op_cons a i l).
  Proof.
    intros.
    destruct a; simpl;
    [apply cons_leA
    |refine (lelistA_weakening lt_key_trans _ _ H)];
    exact (lt_reverse_aux i 2 1 I).
  Qed.

  Lemma lelistA_op_consI : forall E i a l,
     lelistA lt_key (reverse_positive i, E) l ->
     lelistA lt_key (reverse_positive_aux i 3, E) (op_cons a i l).
  Proof.
    intros.
    destruct a; simpl;
    [apply cons_leA
    |refine (lelistA_weakening lt_key_trans _ _ H)];
    exact (lt_reverse_aux i 3 1 I).
  Qed.

  Lemma xelements_sort_1 :
    forall (e : A) (t : tree A) (i : positive) (l : list (positive * A)),
    (lelistA lt_key (reverse_positive i, e) l ->
     forall a, lelistA lt_key (reverse_positive_aux i 3, e)
                       (xelements_aux t (xO i) (op_cons a i l))) /\
    (forall j, lelistA lt_key
                    (reverse_positive_aux (reverse_positive_aux i (xO j)) 3, e)
                    l ->
               lelistA lt_key (reverse_positive_aux j 3, e)
                      (xelements_aux t (xI (reverse_positive_aux i (xO j))) l))
.
  Proof.
    intros E treeA; induction treeA; simpl; intros.
    (* Leaf case *)
    split; intros.
      apply cons_leA; exact (lt_reverse_aux i 3 2 I).
      apply cons_leA; unfold reverse_positive; simpl;
      rewrite simpl_rev; simpl; exact (lt_reverse_aux j 3 (xO _) I).
    (* IO case *)
    assert (IHO := fun i l => proj1 (IHtreeA1 i l)); clear IHtreeA1.
    assert (IHI := fun i l => proj2 (IHtreeA2 i l)); clear IHtreeA2.
    split; intros.
      exact (IHI 1 _ _ (IHO (xO _) _ (lelistA_op_consO _ _ H) _)).
      assert (IHI' := fun l => IHI (append_positive i 3) l j); clear IHI.
      rewrite simpl_app in IHI';simpl in IHI';exact(IHI' _(IHO (xI _)_ H o)).
    (* O case *)
    assert (IHO := fun i l => proj1 (IHtreeA i l)); clear IHtreeA.
    split; intros.
      refine (lelistA_weakening lt_key_trans _ _ (IHO (xO _) _
                                (lelistA_op_consO _ _ H) o)).
        exact (lt_reverse_aux i 3 6 I).
      assert (IHO' := IHO (reverse_positive_aux i j~0)~1 l H o).
        simpl in IHO'; rewrite simpl_rev in IHO'; simpl in IHO'.
        refine (lelistA_weakening lt_key_trans _ _ IHO').
        exact (lt_reverse_aux j 3 (xO _) I).
    (* I case *)
    assert (IHI := fun i l => proj2 (IHtreeA i l)); clear IHtreeA.
    split; intros.
      apply (IHI 1 _ i); rewrite simpl_rev; simpl;
        exact (lelistA_op_consI (xO i) o (lelistA_op_consO i a H)).
      assert (IHI' := fun l => IHI (append_positive i 3) l j); clear IHI.
        rewrite <- reverse_positive_involutive_aux in H.
        assert (H' := lelistA_op_consI _ o H); clear H.
        simpl in *; rewrite simpl_rev in *;
        rewrite append_positive_assoc in IHI'.
        rewrite simpl_app in *; simpl in *; exact (IHI' _ H').
  Qed.

  Lemma xelements_sort :
    forall (treeA : tree A) (i : positive) (l : list (positive * A)),
        sort lt_key l ->
        (forall e, lelistA lt_key (reverse_positive i, e) l) ->
        sort lt_key (xelements_aux treeA i l).
  Proof.
  induction treeA; simpl; intros.
  (* Leaf case *)
  apply cons_sort; auto.
  (* IO case *)
  apply IHtreeA2.
  apply IHtreeA1.
  destruct o; simpl; auto.
  exact (fun e => lelistA_op_consO _ _ (H0 e)).
  exact (fun e => proj1 (xelements_sort_1 e treeA1 i l) (H0 e) _).
  (* O case *)
  apply IHtreeA.
  destruct o; simpl; auto.
  exact (fun e => lelistA_op_consO _ _ (H0 e)).
  (* I case *)
  apply IHtreeA.
  destruct o; simpl; auto.
  exact (fun e => lelistA_op_consI _ _ (H0 e)).
  Qed.

  Lemma elements_3 : forall m, sort lt_key (elements m).
  Proof.
  destruct m as [treeA|]; simpl; auto.
  exact (xelements_sort treeA xH (nil_sort lt_key)(fun _ => nil_leA lt_key _)).
  Qed.

  Lemma elements_3w : forall m, NoDupA eq_key (elements m).
  Proof.
  intro m.
  apply ME.Sort_NoDupA; apply elements_3; auto.
  Qed.

  End FMapSpec.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : positive -> A -> B.

    Fixpoint xmapi (m : tree A) (i : positive) {struct m} : tree B :=
       match m with
        | Leaf a => Leaf (f (reverse_positive i) a)
        | OINode l o r => OINode (xmapi l (xO i))
                                 (option_map (f (reverse_positive i)) o)
                                 (xmapi r (xI i))
        | ONode l o => ONode (xmapi l (xO i))
                             (option_map (f (reverse_positive i)) o)
        | INode o r => INode (option_map (f (reverse_positive i)) o)
                             (xmapi r (xI i))
       end.

    Definition mapi m :=
      match m with
      | None => None
      | Some treeA => Some (xmapi treeA xH)
      end.

  End Mapi.

  Definition map (f : A -> B) m := mapi (fun _ => f) m.

  End A.

  Lemma xgmapi:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: tree A),
      find_aux i (xmapi f m j) = option_map (f (reverse_positive_aux j i))
                 (find_aux i m).
  Proof.
  induction i; intros; destruct m; simpl; auto; apply IHi.
  Qed.

  Theorem gmapi:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof.
  destruct m; simpl; auto; apply xgmapi.
  Qed.

  Lemma mapi_1 :
    forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
    MapsTo x e m ->
    exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
  intros.
  exists x.
  split; [red; auto|].
  apply find_2.
  generalize (find_1 H); clear H; intros.
  rewrite gmapi.
  rewrite H.
  simpl; auto.
  Qed.

  Lemma mapi_2 :
    forall (elt elt':Type)(m: t elt)(x:key)(f:key->elt->elt'),
    In x (mapi f m) -> In x m.
  Proof.
  intros.
  apply mem_2.
  rewrite mem_find.
  destruct H as (v,H).
  generalize (find_1 H); clear H; intros.
  rewrite gmapi in H.
  destruct (find x m); auto.
  simpl in *; discriminate.
  Qed.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
  intros; unfold map.
  destruct (mapi_1 (fun _ => f) H); intuition.
  Qed.

  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
    In x (map f m) -> In x m.
  Proof.
  intros; unfold map in *; eapply mapi_2; eauto.
  Qed.

  Section map2.

  Definition option_map2 A B (f : A -> option B) (o : option A) : option B :=
     match o with
     | Some a => f a
     | None => None
     end.

  Definition Leaf_map_ A B (f : A -> option B) (a : A) : t B :=
     match f a with
     | Some b => Some (Leaf b)
     | None => None
     end.

  Definition xmap2_ A B (f : A -> option B) : tree A -> t B :=
    fix x2_ (m : tree A) {struct m} : t B :=
      match m with
      | Leaf a => Leaf_map_ f a
      | OINode l o r =>
         match x2_ l, x2_ r with
         | Some l, Some r => Some (OINode l (option_map2 f o) r)
         | Some l, None => Some (ONode l (option_map2 f o))
         | None, Some r => Some (INode (option_map2 f o) r)
         | None, None => option_map2 (Leaf_map_ f) o
         end
      | ONode l o => match x2_ l with
                     | Some l => Some (ONode l (option_map2 f o))
                     | None => option_map2 (Leaf_map_ f) o
                     end
      | INode o r => match x2_ r with
                     | Some r => Some (INode (option_map2 f o) r)
                     | None => option_map2 (Leaf_map_ f) o
                     end
      end.

  Variable A B C : Type.
  Variable f : option A -> option B -> option C.

  Definition xmap2_l := xmap2_ (fun a => f (Some a) None).
  Definition xmap2_r := xmap2_ (fun a => f None (Some a)).
  Definition f_car := fun a b =>
    match a, b with
    | None, None => None
    | _, _ => f a b
    end.

  Lemma xgmap2_l :
          forall (i : positive) (m : tree A),
          match find_aux i m with
          | Some _ => f (find_aux i m) None
          | None => None
          end =
          find i (xmap2_l m).
    Proof.
      unfold xmap2_l; simpl.
      induction i; simpl; destruct m; simpl;
      unfold Leaf_map_, option_map2||idtac;
      (rewrite IHi; clear IHi)||idtac;
      repeat
      match goal with |- _ = find _ match ?T with | Some _ => _ | None => _ end
       => destruct T; simpl; auto end;
       destruct o; easy.
    Qed.

  Lemma xgmap2_r :
          forall (i : positive) (m : tree B),
          match find_aux i m with
          | Some _ => f None (find_aux i m)
          | None => None
          end =
          find i (xmap2_r m).
    Proof.
      unfold xmap2_r; simpl.
      induction i; simpl; destruct m; simpl;
      unfold Leaf_map_, option_map2||idtac;
      (rewrite IHi; clear IHi)||idtac;
      repeat
      match goal with |- _ = find _ match ?T with | Some _ => _ | None => _ end
       => destruct T; simpl; auto end;
       destruct o; easy.
    Qed.

  Definition mk_t_
     (left : t C) (v1 : option A) (v2 : option B) (right : t C) : t C :=
    match left, right with
    | Some l, Some r => Some (OINode l (f_car v1 v2) r)
    | Some l, None => Some (ONode l (f_car v1 v2))
    | None, Some r => Some (INode (f_car v1 v2) r)
    | None, None => match f_car v1 v2 with
                    | Some v => Some (Leaf v)
                    | _ => None
                    end
    end.

  Fixpoint _map2 (m1 : tree A)(m2 : tree B) {struct m1} : t C :=
    match m1, m2 with
    | Leaf a, Leaf b => match f_car (Some a) (Some b) with
                        Some v=>Some (Leaf v)|_=> None end
    | Leaf a, OINode l v r => mk_t_ (xmap2_r l) (Some a) v (xmap2_r r)
    | Leaf a, ONode l v => mk_t_ (xmap2_r l) (Some a) v None
    | Leaf a, INode v r => mk_t_ None (Some a) v (xmap2_r r)
    | OINode l v r, Leaf b => mk_t_ (xmap2_l l) v (Some b) (xmap2_l r)
    | OINode ll lv lr, OINode rl rv rr =>
        mk_t_ (_map2 ll rl) lv rv (_map2 lr rr)
    | OINode ll lv r, ONode rl rv => mk_t_ (_map2 ll rl) lv rv (xmap2_l r)
    | OINode l lv lr, INode rv rr => mk_t_ (xmap2_l l) lv rv (_map2 lr rr)
    | ONode l v, Leaf b => mk_t_ (xmap2_l l) v (Some b) None
    | ONode ll lv, OINode rl rv r => mk_t_ (_map2 ll rl) lv rv (xmap2_r r)
    | ONode ll lv, ONode rl rv => mk_t_ (_map2 ll rl) lv rv None
    | ONode l lv, INode rv r => mk_t_ (xmap2_l l) lv rv (xmap2_r r)
    | INode v r, Leaf b => mk_t_ None v (Some b) (xmap2_l r)
    | INode lv lr, OINode l rv rr => mk_t_ (xmap2_r l) lv rv (_map2 lr rr)
    | INode lv r, ONode l rv => mk_t_ (xmap2_r l) lv rv (xmap2_l r)
    | INode lv lr, INode rv rr => mk_t_ None lv rv (_map2 lr rr)
    end.

    Lemma gmap2:
      forall (i: positive)(m1:tree A)(m2: tree B),
      f_car (find_aux i m1) (find_aux i m2) = find i (_map2 m1 m2).
    Proof.
      unfold f_car.
      induction i; simpl; destruct m1; destruct m2;
      simpl; try unfold mk_t_; simpl; try unfold f_car;
      rewrite xgmap2_r || rewrite xgmap2_l || rewrite IHi || idtac;
      repeat
      match goal with |- _ = find _ match ?T with | Some _ => _ | None => _ end
       => destruct T; simpl; auto end.
    Qed.

  End map2.

  Definition map2 (elt elt' elt'':Type)
     (f: option elt -> option elt' -> option elt'')
     (m1: t elt) (m2: t elt') : t elt'' :=
     match m1, m2 with
     | None, None => None
     | None, Some t2 => xmap2_r f t2
     | Some t1, None => xmap2_l f t1
     | Some t1, Some t2 => _map2 f t1 t2
     end.

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m').
  Proof.
  unfold In, MapsTo.
  intros.
  destruct H as [[e He]|[e He]].
    destruct m; try discriminate He;
      destruct m'; simpl in *;
      [ rewrite <- gmap2 | rewrite <- xgmap2_l ];
      rewrite He; easy.
    destruct m'; try discriminate He;
      destruct m; simpl in *;
      [ rewrite <- gmap2 | rewrite <- xgmap2_r ];
      rewrite He; auto.
     destruct (find_aux x t1); easy.
  Qed.

  Lemma  map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
  unfold In, MapsTo.
  intros.
  destruct H as [e He].
  destruct m; destruct m'; simpl in *;
  [rewrite <- gmap2 in He
  |rewrite <- xgmap2_l in He
  |rewrite <- xgmap2_r in He
  |discriminate He];
  destruct (find_aux x t0);
  try discriminate He;
  [left |right;destruct (find_aux x t1); try discriminate He |left |right];
  eexists; auto.
  Qed.

  Section Fold.

    Variables A B : Type.
    Variable f : positive -> A -> B -> B.

    Definition op_f i (o : option A) (a : B) : B :=
      match o with
      | Some a' => f (reverse_positive i) a' a
      | _ => a
      end.

    Fixpoint xfoldi (m : tree A) (v : B) (i : positive) :=
      match m with
        | Leaf a => f (reverse_positive i) a v
        | OINode l o r => op_f i o (xfoldi l (xfoldi r v (xI i)) (xO i))
        | ONode l o => op_f i o (xfoldi l v (xO i))
        | INode o r => op_f i o (xfoldi r v (xI i))
      end.

    Lemma xfoldi_1 :
      forall m v i l,
      fold_left (fun a p => f (fst p) (snd p) a) l (xfoldi m v i) =
      fold_left (fun a p => f (fst p) (snd p) a) (xelements_aux m i l) v.
    Proof.
      induction m; simpl in *; auto; intros.
      rewrite <- IHm2; rewrite <- IHm1; destruct o; simpl; auto.
      rewrite <- IHm; destruct o; simpl; auto.
      rewrite <- IHm; destruct o; simpl; auto.
    Qed.

    Definition fold m i :=
      match m with
      | Some m => xfoldi m i 1
      | _ => i
      end.

  End Fold.

  Lemma fold_1 :
    forall (A:Type)(m:t A)(B:Type)(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; unfold fold, elements.
    destruct m; simpl; auto.
    exact (xfoldi_1 f t0 i xH nil).
  Qed.

  Definition option_cmp (A:Type)(cmp: A -> A -> bool)(oa ob: option A): bool :=
    match oa, ob with
    | Some a, Some b => cmp a b
    | None, None => true
    | _, _ => false
    end.

  Definition equal_aux (A:Type) (cmp : A -> A -> bool): tree A->tree A->bool :=
    fix ea (m1 m2 : tree A) {struct m1} : bool :=
    match m1, m2 with
      | Leaf a, Leaf b => cmp a b
      | OINode ll lv lr, OINode rl rv rr =>
          option_cmp cmp lv rv && ea ll rl && ea lr rr
      | ONode ll lv, ONode rl rv =>
          option_cmp cmp lv rv && ea ll rl
      | INode lv lr, INode rv rr =>
          option_cmp cmp lv rv && ea lr rr
      | _, _ => false
     end.

  Definition equal (A : Type) (cmp : A -> A -> bool) : t A -> t A -> bool :=
    option_cmp (equal_aux cmp).

  Definition Equal (A:Type)(m m':t A) :=
    forall y, find y m = find y m'.
  Definition Equiv (A:Type)(eq_elt:A->A->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma some (A : Type) (t : tree A) :
    {a : positive * A | find_aux (fst a) t = Some (snd a) }.
  Proof.
    induction t; simpl.
      exists (xH, a); easy.
      destruct IHt1 as [[i a] P]; exists (xO i, a); easy.
      destruct IHt as [[i a] P]; exists (xO i, a); easy.
      destruct IHt as [[i a] P]; exists (xI i, a); easy.
  Qed.

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    unfold Equivb, Equiv, In, MapsTo, Cmp.
    intros A m m' cmp H.
    destruct H as [E H].
    destruct m as [T|]; destruct m' as [T'|]; simpl in *; auto; intros.
    (* non empty cases *)
      assert (E1 : forall k e,
         find_aux k T = Some e -> find_aux k T' = None -> False).
        intros k e L K; destruct (proj1 (E k) (ex_intro _ e L)) as [X rw];
        rewrite rw in K; discriminate K.
      assert (E2 : forall k e,
         find_aux k T' = Some e -> find_aux k T = None -> False).
        intros k e L K; destruct (proj2 (E k) (ex_intro _ e L)) as [X rw];
        rewrite rw in K; discriminate K.
      clear E.
      revert T' H E1 E2.
      induction T as [a|l Hl o r Hr|l Hl o|o r Hr];
      destruct T' as [a'|l' o' r'|l' o'|o' r'];
      intros H E1 E2; simpl in *; auto;
      (destruct (some l) as [[i v] P]; simpl in *;
       destruct (E1 (xO i) v P (refl_equal _)))||
      (destruct (some r) as [[i v] P]; simpl in *;
       destruct (E1 (xI i) v P (refl_equal _)))||
      (destruct (some l') as [[i v] P]; simpl in *;
       destruct (E2 (xO i) v P (refl_equal _)))||
      (destruct (some r') as [[i v] P]; simpl in *;
       destruct (E2 (xI i) v P (refl_equal _)))||
       idtac.
      apply (H 1); easy.
      rewrite (Hl _ (fun k => H (xO k)) (fun k => E1 (xO k))
                    (fun k => E2 (xO k))).
      rewrite (Hr _ (fun k => H (xI k)) (fun k => E1 (xI k))
                    (fun k => E2 (xI k))).
      assert (H' := H 1); assert (E1' := E1 1); assert (E2' := E2 1).
      clear H Hl Hr E1 E2; simpl in *.
      destruct o as [o|]; destruct o' as [o'|];
      [simpl; rewrite H'|destruct (E1' o)|destruct (E2' o')|]; easy.
      rewrite (Hl _ (fun k => H (xO k)) (fun k => E1 (xO k))
                    (fun k => E2 (xO k))).
      assert (H' := H 1); assert (E1' := E1 1); assert (E2' := E2 1).
      clear H Hl E1 E2; simpl in *.
      destruct o as [o|]; destruct o' as [o'|];
      [simpl; rewrite H'|destruct (E1' o)|destruct (E2' o')|]; easy.
      rewrite (Hr _ (fun k => H (xI k)) (fun k => E1 (xI k))
                    (fun k => E2 (xI k))).
      assert (H' := H 1); assert (E1' := E1 1); assert (E2' := E2 1).
      clear H Hr E1 E2; simpl in *.
      destruct o as [o|]; destruct o' as [o'|];
      [simpl; rewrite H'|destruct (E1' o)|destruct (E2' o')|]; easy.
    (**)
      destruct (some T) as [[i v] P]; simpl in *.
      destruct (proj1 (E i) (ex_intro _ v P)) as [o abs].
      discriminate abs.
    (**)
      destruct (some T') as [[i v] P]; simpl in *.
      destruct (proj2 (E i) (ex_intro _ v P)) as [o abs].
      discriminate abs.
  Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    unfold Equivb, Equiv, In, MapsTo, Cmp.
    intros A m m' cmp H.
    destruct m as [T|]; destruct m' as [T'|]; simpl in *; auto; intros.
    (* non empty cases *)
      assert (forall k, match find_aux k T with
                        | Some e => exists e', find_aux k T' = Some e' /\
                                               cmp e e' = true
                        | None => find_aux k T' = None
                        end).
        intro k; revert T T' H; induction k;
        destruct T; destruct T'; simpl; intro H; auto; try discriminate H;
        apply IHk ||
        (destruct o; destruct o0; simpl in *; auto; try discriminate H;
         exists a0; destruct (cmp a a0); [eexists; eauto|discriminate H])||
        idtac.
        destruct (option_cmp cmp o o0); destruct (equal_aux cmp T1 T'1);
        destruct (equal_aux cmp T2 T'2); auto.
        destruct (option_cmp cmp o o0); discriminate H||exact H.
        destruct (option_cmp cmp o o0); destruct (equal_aux cmp T1 T'1); auto.
        destruct (option_cmp cmp o o0); discriminate H||exact H.
        eexists; eauto.
      split; intro k; assert (H' := H0 k); clear H0.
      destruct (find_aux k T).
        destruct H' as [e' [He'1 He'2]].
        rewrite He'1; clear He'1.
        intuition; (eexists; eauto)||idtac.
        rewrite H'. firstorder.
      intros e e' Hk Hk'. rewrite Hk in H'.
       destruct H' as [e'' [He'1 He'2]]. congruence.
    (**)
    discriminate H.
    discriminate H.
    intuition; discriminate H0.
  Qed.

(*   Inductive tree (A : Type) := *)
(*     | Leaf : A -> tree A *)
(*     | OINode : tree A -> option A -> tree A -> tree A *)
(*     | ONode : tree A -> option A -> tree A *)
(*     | INode : option A -> tree A -> tree A. *)

(*   Definition t (A : Type) := option (tree A). *)
  Section MapAsOT.
    Context `{Helt : OrderedType elt}.

    Inductive tree_eq : tree elt -> tree elt -> Prop :=
    | tree_eq_Leaf :
      forall x y, x === y -> tree_eq (Leaf x) (Leaf y)
    | tree_eq_OINode :
      forall l l' o o' r r', tree_eq l l' -> o === o' -> tree_eq r r' ->
        tree_eq (OINode l o r) (OINode l' o' r')
    | tree_eq_ONode :
      forall l l' o o', tree_eq l l' -> o === o' ->
        tree_eq (ONode l o) (ONode l' o')
    | tree_eq_INode :
      forall o o' r r', o === o' -> tree_eq r r' ->
        tree_eq (INode o r) (INode o' r').
    Property tree_eq_refl : forall x, tree_eq x x.
    Proof. Tactics.minductive_refl. Qed.
    Property tree_eq_sym : forall x y, tree_eq x y -> tree_eq y x.
    Proof. Tactics.minductive_sym. Qed.
    Property tree_eq_trans : forall x y z, tree_eq x y -> tree_eq y z -> tree_eq x z.
    Proof. Tactics.minductive_trans. Qed.

    Inductive tree_lt : tree elt -> tree elt -> Prop :=
    | tree_lt_Leaf_OINode : forall x l o r, tree_lt (Leaf x) (OINode l o r)
    | tree_lt_Leaf_ONode : forall x l o, tree_lt (Leaf x) (ONode l o)
    | tree_lt_Leaf_INode : forall x o r, tree_lt (Leaf x) (INode o r)
    | tree_lt_Leaf_Leaf_1 : forall x y, x <<< y -> tree_lt (Leaf x) (Leaf y)
    | tree_lt_OINode_ONode : forall l o r l' o', tree_lt (OINode l o r) (ONode l' o')
    | tree_lt_OINode_INode : forall l o r o' r', tree_lt (OINode l o r) (INode o' r')
    | tree_lt_OINode_OINode_1 :
      forall l l' o o' r r', o <<< o' -> tree_lt (OINode l o r) (OINode l' o' r')
    | tree_lt_OINode_OINode_2 :
      forall l l' o o' r r', tree_lt l l' -> o === o' ->
        tree_lt (OINode l o r) (OINode l' o' r')
    | tree_lt_OINode_OINode_3 :
      forall l l' o o' r r', tree_eq l l' -> o === o' -> tree_lt r r' ->
        tree_lt (OINode l o r) (OINode l' o' r')
    | tree_lt_ONode_INode : forall l o o' r', tree_lt (ONode l o) (INode o' r')
    | tree_lt_ONode_ONode_1 :
      forall l l' o o', o <<< o' -> tree_lt (ONode l o) (ONode l' o')
    | tree_lt_ONode_ONode_2 :
      forall l l' o o', tree_lt l l' -> o === o'->
        tree_lt (ONode l o) (ONode l' o')
    | tree_lt_INode_INode_1 :
      forall o o' r r', o <<< o' -> tree_lt (INode o r) (INode o' r')
    | tree_lt_INode_INode_2 :
      forall o o' r r', o === o' -> tree_lt r r' ->
        tree_lt (INode o r) (INode o' r').

    Property tree_lt_irrefl : forall x y, tree_lt x y -> ~tree_eq x y.
    Proof. Tactics.minductive_irrefl. Qed.
    Property tree_eq_lt : forall x x' y, tree_eq x x' -> tree_lt x y -> tree_lt x' y.
    Proof. Tactics.rinductive_eq_lt tree_eq_sym tree_eq_trans. Qed.
    Property tree_eq_gt : forall x x' y, tree_eq x x' -> tree_lt y x -> tree_lt y x'.
    Proof. Tactics.rinductive_eq_gt tree_eq_trans. Qed.
    Property tree_lt_trans : forall x y z, tree_lt x y -> tree_lt y z -> tree_lt x z.
    Proof.
      Tactics.rinductive_lexico_trans tree_eq_sym tree_eq_trans tree_eq_gt tree_eq_lt.
    Qed.

    Fixpoint tree_cmp (m m' : tree elt) : comparison :=
      match m, m' with
        | Leaf k, Leaf k' => k =?= k'
        | Leaf _, _ => Lt
        | _, Leaf _ => Gt
        | OINode l o r, OINode l' o' r' =>
          match o =?= o' with
            | Eq =>
              match tree_cmp l l' with
                | Eq => tree_cmp r r'
                | Lt => Lt
                | Gt => Gt
              end
            | Lt => Lt
            | Gt => Gt
          end
        | OINode _ _ _, _ => Lt
        | _, OINode _ _ _ => Gt
        | ONode l o, ONode l' o' =>
          match o =?= o' with
            | Eq => tree_cmp l l'
            | Lt => Lt
            | Gt => Gt
          end
        | ONode _ _, _ => Lt
        | _, ONode _ _ => Gt
        | INode o r, INode o' r' =>
          match o =?= o' with
            | Eq => tree_cmp r r'
            | Lt => Lt
            | Gt => Gt
          end
      end.
    Property tree_cmp_spec : forall x y,
      compare_spec tree_eq tree_lt x y (tree_cmp x y).
    Proof.
      induction x; destruct y; try (tconstructor (constructor)).
      simpl; destruct (compare_dec a e); try (tconstructor (tconstructor (auto))).
      simpl; destruct (compare_dec o o0); try (constructor; tconstructor (auto)).
      destruct (IHx1 y1); try constructor.
      tconstructor (assumption).
      destruct (IHx2 y2); try constructor;
        tconstructor (solve [auto using tree_eq_sym]).
      tconstructor (solve [auto using tree_eq_sym]).
      simpl; destruct (compare_dec o o0); try (constructor; tconstructor (auto)).
      destruct (IHx y); try constructor;
        tconstructor (solve [auto using tree_eq_sym]).
      simpl; destruct (compare_dec o o0); try (constructor; tconstructor (auto)).
      destruct (IHx y); try constructor;
        tconstructor (solve [auto using tree_eq_sym]).
    Qed.

    Program Instance tree_OrderedType : OrderedType (tree elt) := {
      _eq := tree_eq;
      OT_Equivalence := @Build_Equivalence _ _ tree_eq_refl tree_eq_sym tree_eq_trans;
      _lt := tree_lt;
      OT_StrictOrder := @Build_StrictOrder _ _ _ _ tree_lt_trans tree_lt_irrefl;
      _cmp := tree_cmp;
      _compare_spec := tree_cmp_spec
    }.
    Definition Map_OrderedType : OrderedType (t elt) :=
      option_OrderedType tree_OrderedType.
  End MapAsOT.

End CPositiveMap.

(** Here come some additionnal facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)


Module CPositiveMapAdditionalFacts.
  Import CPositiveMap.

  (* Derivable from the Map interface *)
  Theorem gsspec:
    forall (A:Type)(i j: positive) (x: A) (m: t A),
    find i (add j x m) = if i == j then Some x else find i m.
  Proof.
    intros.
    destruct (eq_dec i j); [ rewrite H ; apply gss | apply gso; auto ].
  Qed.

   (* Not derivable from the Map interface *)
  Theorem gsident:
    forall (A:Type)(i: positive) (m: t A) (v: A),
    find i m = Some v -> add i v m = m.
  Proof.
    destruct m.
    intros; assert (add_aux v i t0 = t0).
    revert t0 H.
    induction i; intros; destruct t0; simpl; simpl in *; try congruence;
      try (rewrite (IHi t0 H); congruence).
      rewrite (IHi t0_2 H); congruence.
      rewrite (IHi t0_1 H); congruence.
    simpl; rewrite H0; auto.
    intros v H; discriminate H.
  Qed.

  Lemma xmap2_lr :
      forall (A B : Type)(f g: option A -> option A -> option B),
      (forall (i j : option A), f i j = g j i) ->
      forall m, xmap2_l f m = xmap2_r g m.
    Proof.
      intros A B f g H.
      assert (forall a, Leaf_map_ (fun a0 : A => f (Some a0) None) a =
                        Leaf_map_ (fun a0 : A => g None (Some a0)) a).
              intro a; unfold Leaf_map_; rewrite H; auto.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      destruct o; simpl; auto.
      rewrite H0; rewrite H; auto.
      rewrite IHm; auto.
      destruct o; simpl; auto.
      rewrite H0; rewrite H; auto.
      rewrite IHm; auto.
      destruct o; simpl; auto.
      rewrite H0; rewrite H; auto.
    Qed.

  Theorem map2_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: tree A),
    _map2 f m1 m2 = _map2 g m2 m1.
  Proof.
    intros A B f g Eq1.
    assert (Eq2: forall (i j: option A), g i j = f j i).
      intros; auto.
    induction m1; intros; destruct m2; simpl; unfold mk_t_, f_car;
      try rewrite Eq1; try destruct o; try destruct o0;
      repeat rewrite (xmap2_lr f g);
      repeat rewrite (xmap2_lr g f);
      try easy;
      try rewrite IHm1_1;
      try rewrite IHm1_2;
      try rewrite IHm1;
      try rewrite IHm2;
      auto.
  Qed.

  Theorem CanonicalMap :
    forall A (cmp : A -> A -> bool) (Hcmp : forall a b, cmp a b = true -> a = b)
    m1 m2, equal cmp m1 m2 = true -> m1 = m2.
  Proof.
    intros.
    destruct m1; destruct m2; simpl in *; auto; try discriminate H.
    assert (HH : t0 = t1);[|rewrite HH; auto].
    revert t1 H; induction t0; destruct t1; simpl in *; auto;
      intro K; try discriminate K;
      try (rewrite (Hcmp _ _ K); auto);
      (assert (L : o = o0);
       [destruct o; destruct o0; simpl in *; auto; try discriminate K;
        assert (Hcmp' := Hcmp a a0); clear Hcmp;
        destruct (cmp a a0); [rewrite Hcmp'; auto|discriminate K]|
        destruct (option_cmp cmp o o0);
        [simpl in K; rewrite L; clear o L
        |discriminate K]])||
        idtac.
      assert (IHt0_1' := IHt0_1 t1_1); clear IHt0_1;
      assert (IHt0_2' := IHt0_2 t1_2); clear IHt0_2.
      destruct (equal_aux cmp t0_1 t1_1); try discriminate K;
      destruct (equal_aux cmp t0_2 t1_2); try discriminate K;
      rewrite IHt0_1'; [rewrite IHt0_2'|]; auto.
      assert (IHt0' := IHt0 t1); clear IHt0;
      destruct (equal_aux cmp t0 t1); try discriminate K;
      rewrite IHt0'; auto.
      assert (IHt0' := IHt0 t1); clear IHt0;
      destruct (equal_aux cmp t0 t1); try discriminate K;
      rewrite IHt0'; auto.
Qed.

End CPositiveMapAdditionalFacts.

