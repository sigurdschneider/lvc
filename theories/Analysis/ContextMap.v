Require Import Max Nat CMap Infra.Lattice Infra.PartialOrder CMapPartialOrder.

Set Implicit Arguments.

Record ctxmap X := {
                     ctxmap_M : Map [nat, X];
                     ctxmap_len : nat
                   }.

Definition ctxmap_to_idx X (m:ctxmap X) (n:nat) :=
  ctxmap_len m - S n.

Definition ctxmap_emp X : ctxmap X :=
  Build_ctxmap (@MapInterface.empty nat _ _ X) 0.

Definition ctxmap_update_at X (m:ctxmap X) (n:nat) (x:X)
  := if [n >= ctxmap_len m] then m
    else Build_ctxmap (add (ctxmap_to_idx m n) x (ctxmap_M m)) (ctxmap_len m).

Definition ctxmap_join_at X `{JoinSemiLattice X} (m:ctxmap X) (n:nat) (x:X)
  := let k := ctxmap_to_idx m n in
    let v := match MapInterface.find k (ctxmap_M m) with
            | Some y => join x y
            | None => x
            end in
    Build_ctxmap (add k v (ctxmap_M m)) (ctxmap_len m).

Fixpoint range (n d:nat) :=
  match d with
  | 0 => nil
  | S d => n::range (S n) d
  end.

Definition ctxmap_app X (L:list X) (m:ctxmap X)
  := let l := length L in
    Build_ctxmap ((ctxmap_M m)[-range (ctxmap_len m) l <-- L -]) (ctxmap_len m + l).

Fixpoint ctxmap_erase X (m:Map [nat, X]) Z : Map [nat, X]
  := match Z with
    | nil => m
    | x::Z => MapInterface.remove x (@ctxmap_erase X m Z)
    end.

Definition ctxmap_extend X (m:ctxmap X) (n:nat) :=
  Build_ctxmap (ctxmap_erase (ctxmap_M m) (range (ctxmap_len m) n))
               (ctxmap_len m + n).


Definition ctxmap_at X m n : option X
  := if [n >= ctxmap_len m] then None
    else MapInterface.find (ctxmap_to_idx m n) (ctxmap_M m).

Definition ctxmap_at_def X `{LowerBounded X} m n : X
  := if [n >= ctxmap_len m] then bottom
    else match MapInterface.find (ctxmap_to_idx m n) (ctxmap_M m) with
         | Some x => x
         | None => bottom
         end.

Definition ctxmap_to_list X  `{LowerBounded X} (m:ctxmap X) : list X :=
  map (@ctxmap_at_def X _ _ m) (range 0 (ctxmap_len m)).


Lemma range_len k n
  : ❬range k n❭ = n.
Proof.
  general induction n; simpl; eauto.
Qed.

Smpl Add rewrite range_len : len.

Lemma ctxmap_to_list_len X `{LowerBounded X} (m:ctxmap X)
  : ❬ctxmap_to_list m❭ = ctxmap_len m.
Proof.
  unfold ctxmap_to_list. len_simpl; eauto.
Qed.

Lemma ctxmap_len_app (X:Type) A (B:ctxmap X)
  : ctxmap_len (ctxmap_app A B) = ❬A❭ + ctxmap_len B.
Proof.
  general induction A; simpl; omega.
Qed.

Ltac ctxmap_len_simpl :=
  match goal with
  | [ H : context [ ❬@ctxmap_to_list ?X ?PO ?LB ?m❭ ] |- _ ] =>
    rewrite (@ctxmap_to_list_len X PO LB m) in H
  | [ |- context [ ❬@ctxmap_to_list ?X ?PO ?LB ?m❭ ] ] =>
    rewrite (@ctxmap_to_list_len X PO LB m)
  | [ H : context [ ctxmap_len (@ctxmap_app ?X ?L ?m) ] |- _ ] =>
    rewrite (@ctxmap_len_app X L m) in H
  | [ |- context [ ctxmap_len (@ctxmap_app ?X ?L ?m) ] ] =>
    rewrite (@ctxmap_len_app X L m)
  end.

Smpl Add ctxmap_len_simpl : len.

Lemma ctxmap_at_gt X m x
  : x >= ctxmap_len m ->  @ctxmap_at X m x = None.
Proof.
  unfold ctxmap_at. intros; cases. reflexivity.
Qed.

Definition ctxmap_drop (n:nat) X (m:ctxmap X)  :=
  Build_ctxmap (ctxmap_M m) (ctxmap_len m - n).

Definition ctxmap_poLe X `{PartialOrder X} (m m':ctxmap X) :=
  ctxmap_len m = ctxmap_len m'
  /\ forall x, x < ctxmap_len m -> poLe (MapInterface.find x (ctxmap_M m))
                                 (MapInterface.find x (ctxmap_M m')).

Definition ctxmap_poEq X `{PartialOrder X} (m m':ctxmap X) :=
  ctxmap_len m = ctxmap_len m'
  /\ forall x, x < ctxmap_len m -> poEq (MapInterface.find x (ctxmap_M m))
                                 (MapInterface.find x (ctxmap_M m')).

Fixpoint nat_quant_dec P `{H:forall x, Computable (P x) } k : bool  :=
  match k with
  | 0 => true
  | S k => if [P k] then nat_quant_dec P k else false
  end.


Instance nat_quant_computable k P
         `{forall x, Computable (P x) } :
  Computable (forall x, x < k -> P x).
Proof.
  hnf. remember (nat_quant_dec P k).
  induction k;
    simpl in *; repeat cases in Heqb; clear_trivial_eqs.
  - left. intros. inv H0.
  - edestruct IHk; eauto.
    + left. intros. inv H0; eauto.
    + right. intro. eapply n; intros. eapply H0. omega.
  - right. intro. eapply NOTCOND. eapply H0. eauto.
Qed.

Instance ctxmap_poLe_dec X `{PartialOrder X} m m'
  : Computable (ctxmap_poLe m m').
Proof.
  hnf. decide (ctxmap_len m = ctxmap_len m');[|right; inversion 1; eauto].
  unfold ctxmap_poLe.
  enough ({(forall x : nat, x < ctxmap_len m ->
                     MapInterface.find x (ctxmap_M m)
                                       ⊑ MapInterface.find x (ctxmap_M m'))} +
          {~ (forall x : nat, x < ctxmap_len m ->
                       MapInterface.find x (ctxmap_M m)
                                         ⊑ MapInterface.find x (ctxmap_M m'))}). {
    destruct H0; eauto.
  }
  eapply nat_quant_computable.
  intros. eapply poLe_dec.
Qed.

Instance ctxmap_poEq_dec X `{PartialOrder X} m m'
  : Computable (ctxmap_poEq m m').
Proof.
  hnf. decide (ctxmap_len m = ctxmap_len m');[|right; inversion 1; eauto].
  unfold ctxmap_poLe.
  enough ({(forall x : nat, x < ctxmap_len m ->
                     MapInterface.find x (ctxmap_M m)
                                       ≣ MapInterface.find x (ctxmap_M m'))} +
          {~ (forall x : nat, x < ctxmap_len m ->
                       MapInterface.find x (ctxmap_M m)
                                         ≣ MapInterface.find x (ctxmap_M m'))}). {
    destruct H0; eauto 20.
    left. split. eauto. eauto.
    right. inversion 1. eauto.
  }
  eapply nat_quant_computable.
  intros. eapply poEq_dec.
Qed.

Instance ctxmap_poEq_refl X `{PartialOrder X}
  : Reflexive (ctxmap_poEq (X:=X)).
Proof.
  hnf; intros; unfold ctxmap_poEq; intros.
  eauto.
Qed.

Instance ctxmap_poEq_sym X `{PartialOrder X}
  : Symmetric (ctxmap_poEq (X:=X)).
Proof.
  hnf; intros; unfold ctxmap_poEq; intros.
  exploit H0; dcr. rewrite H2 in *. split; eauto.
  intros. rewrite H3; eauto.
Qed.

Instance ctxmap_poEq_trans X `{PartialOrder X}
  : Transitive (ctxmap_poEq (X:=X)).
Proof.
  unfold ctxmap_poEq.
  hnf; intros; dcr. split; intros; eauto.
  - congruence.
  - rewrite H4; eauto. rewrite H3; eauto. omega.
Qed.


Instance ctxmap_poLe_trans X `{PartialOrder X}
  : Transitive (ctxmap_poLe(X:=X)).
Proof.
  unfold ctxmap_poLe.
  hnf; intros; dcr. split; intros; eauto.
  - congruence.
  - rewrite H4; eauto. rewrite H3; eauto. omega.
Qed.

Instance ctxmap_poEq_Equivalene X `{PartialOrder X}
  :  Equivalence (ctxmap_poEq (X:=X)).
Proof.
  econstructor; eauto with typeclass_instances.
Defined.

Instance ctxmap_poLe_anti X `{PartialOrder X}
  : Antisymmetric (ctxmap X) (ctxmap_poEq (X:=X)) (ctxmap_poLe (X:=X)).
Proof.
  unfold ctxmap_poEq, ctxmap_poLe.
  hnf; intros; dcr. split.
  - congruence.
  - intros. rewrite H2 in *.
    eapply antisymmetry; eauto.
Qed.

Instance ctxmap_po X `{PartialOrder X} : PartialOrder (ctxmap X) :=
  {
    poLe := @ctxmap_poLe X _;
    poEq := @ctxmap_poEq X _
  }.
Proof.
  unfold ctxmap_poLe. intros.
  - destruct H0. split; eauto.
Defined.


Lemma ctxmap_at_poLe X `{PartialOrder X} m m' x
  : m ⊑ m'
    -> ctxmap_at m x ⊑ ctxmap_at m' x.
Proof.
  intros. destruct H0.
  unfold ctxmap_at; repeat cases; try rewrite H0; eauto;
    try now (exfalso; omega).
  unfold ctxmap_to_idx. rewrite H0.
  eapply H1. omega.
Qed.


Lemma ctxmap_at_poEq X `{PartialOrder X} m m' x
  : m ≣ m'
    -> ctxmap_at m x ≣ ctxmap_at m' x.
Proof.
  intros. destruct H0.
  unfold ctxmap_at; repeat cases; try rewrite H0; eauto;
    try now (exfalso; omega).
  unfold ctxmap_to_idx. rewrite H0.
  eapply H1; eauto. omega.
Qed.

Hint Resolve ctxmap_at_poLe ctxmap_at_poEq.

Lemma ctxmap_at_def_poLe X `{LowerBounded X} m m' x
  : m ⊑ m'
    -> ctxmap_at_def m x ⊑ ctxmap_at_def m' x.
Proof.
  intros. destruct H1.
  decide (x < ctxmap_len m).
  - exploit (H2 (ctxmap_to_idx m x)). unfold ctxmap_to_idx. omega.
    unfold ctxmap_at_def,ctxmap_to_idx in *; rewrite H1 in *;
      repeat cases; try rewrite H1; eauto;
        try now (exfalso; omega). eapply bottom_least; eauto.
  - unfold ctxmap_at_def,ctxmap_to_idx in *; rewrite H1 in *;
      repeat cases; try rewrite H1; eauto;
        try now (exfalso; omega).
Qed.

Lemma ctxmap_at_def_poEq X `{LowerBounded X} m m' x
  : m ≣ m'
    -> ctxmap_at_def m x ≣ ctxmap_at_def m' x.
Proof.
  intros. destruct H1.
  decide (x < ctxmap_len m).
  - exploit (H2 (ctxmap_to_idx m x)). unfold ctxmap_to_idx. omega.
    unfold ctxmap_at_def,ctxmap_to_idx in *; rewrite H1 in *;
      repeat cases; try rewrite H1; eauto;
        try now (exfalso; omega).
  - unfold ctxmap_at_def,ctxmap_to_idx in *; rewrite H1 in *;
      repeat cases; try rewrite H1; eauto;
        try now (exfalso; omega).
Qed.

Hint Resolve ctxmap_at_def_poLe ctxmap_at_def_poEq.

Instance ctxmap_len_proper X `{PartialOrder X}
  : Proper (poEq ==> eq) (@ctxmap_len X).
Proof.
  unfold Proper, respectful; intros.
  inv H0; eauto.
Qed.

Instance ctxmap_len_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> eq) (@ctxmap_len X).
Proof.
  unfold Proper, respectful; intros.
  inv H0; eauto.
Qed.

Instance ctxmap_to_list_proper_poLe X `{LowerBounded X}
  : Proper (poLe ==> poLe) (@ctxmap_to_list X _ _).
Proof.
  unfold Proper, respectful; intros.
  unfold ctxmap_to_list. rewrite H1 at 2.
  eapply poLe_map_nd.
  - intros. eapply ctxmap_at_def_poLe. eauto.
Qed.

Instance ctxmap_to_list_proper_poEq X `{LowerBounded X}
  : Proper (poEq ==> poEq) (@ctxmap_to_list X _ _).
Proof.
  unfold Proper, respectful; intros.
  unfold ctxmap_to_list. rewrite H1 at 2.
  eapply poEq_map_nd.
  - intros. eapply ctxmap_at_def_poEq. eauto.
Qed.

Lemma ctxmap_update_at_poLe X `{PartialOrder X} m m' v v' x
  : m ⊑ m'
    -> v ⊑ v'
    -> ctxmap_update_at m x v ⊑ ctxmap_update_at m' x v'.
Proof.
  intros.
  unfold poLe; simpl. destruct H0.
  unfold ctxmap_update_at, ctxmap_poLe, ctxmap_at, ctxmap_to_idx; simpl.
  repeat cases; eauto; intros; repeat cases; eauto; simpl in *;
    try now (exfalso; omega).
  split; eauto.
  intros; eauto.
  decide (x = x0); subst.
  + mlud; eauto. exfalso. rewrite H0 in *. eauto.
    exfalso. rewrite H0 in *. eauto.
  + mlud; eauto.
    exfalso. rewrite H0 in *; eauto.
    exfalso. rewrite H0 in *; eauto.
Qed.

Hint Resolve ctxmap_update_at_poLe.

Lemma ctxmap_update_at_poEq X `{PartialOrder X} m m' v v' x
  : m ≣ m'
    -> v ≣ v'
    -> ctxmap_update_at m x v ≣ ctxmap_update_at m' x v'.
Proof.
  intros.
  unfold poEq; simpl. destruct H0.
  unfold ctxmap_update_at, ctxmap_poEq, ctxmap_at, ctxmap_to_idx; simpl.
  repeat cases; eauto; intros; repeat cases; eauto; simpl in *;
    try now (exfalso; omega).
  split; eauto.
  intros; repeat cases; eauto; try now (exfalso; omega).
  decide (x = x0); subst.
  + mlud; eauto. econstructor. eauto.
    exfalso. rewrite H0 in *. eauto.
    exfalso. rewrite H0 in *. eauto.
  + mlud; eauto. econstructor; eauto.
    exfalso; rewrite H0 in *; eauto.
    exfalso; rewrite H0 in *; eauto.
Qed.

Hint Resolve ctxmap_update_at_poEq.


Lemma ctxmap_join_at_poLe X `{JoinSemiLattice X} (m m':ctxmap X) v v' x
  : m ⊑ m'
    -> v ⊑ v'
    -> ctxmap_join_at m x v ⊑ ctxmap_join_at m' x v'.
Proof.
  intros.
  unfold poLe; simpl. destruct H1.
  unfold ctxmap_join_at, ctxmap_poLe, ctxmap_at, ctxmap_to_idx; simpl.
  split; eauto.
  intros.
  mlud; eauto.
  + exploit (H3 (ctxmap_len m - S x)). omega.
    rewrite <- H1 in *.
    revert H5; repeat cases; simpl; intros; clear_trivial_eqs; eauto.
    econstructor. rewrite H5, H2. reflexivity.
    econstructor. rewrite H2. eapply join_poLe.
  + exfalso. rewrite H1 in *. eauto.
  + exfalso. rewrite H1 in *. eauto.
Qed.

Lemma ctxmap_join_at_poEq X `{JoinSemiLattice X} m m' v v' x
  : m ≣ m'
    -> v ≣ v'
    -> ctxmap_join_at m x v ≣ ctxmap_join_at m' x v'.
Proof.
  intros.
  unfold poEq; simpl. destruct H1.
  unfold ctxmap_join_at, ctxmap_poEq, ctxmap_at, ctxmap_to_idx; simpl.
  split; eauto.
  intros.
  mlud; eauto.
  + exploit (H3 (ctxmap_len m - S x)). omega.
    rewrite <- H1 in *.
    revert H5; repeat cases; simpl; intros; clear_trivial_eqs; eauto.
    econstructor. rewrite H5, H2. reflexivity.
    econstructor. rewrite H2. eauto.
  + exfalso. rewrite H1 in *. eauto.
  + exfalso. rewrite H1 in *. eauto.
Qed.

Hint Resolve ctxmap_join_at_poLe ctxmap_join_at_poEq.


Lemma ctxmap_drop_poLe X `{PartialOrder X} n m m'
  : m ⊑ m'
    -> ctxmap_drop n m ⊑ ctxmap_drop n m'.
Proof.
  intros. destruct H0.
  unfold ctxmap_drop; hnf. simpl.
  split; eauto. intros. eapply H1. omega.
Qed.

Lemma ctxmap_drop_poEq X `{PartialOrder X} n m m'
  : m ≣ m'
    -> ctxmap_drop n m ≣ ctxmap_drop n m'.
Proof.
  intros. destruct H0.
  unfold ctxmap_drop; hnf. simpl.
  split; eauto. intros.
  eapply H1; eauto. omega.
Qed.

Hint Resolve ctxmap_drop_poLe ctxmap_drop_poEq.

Lemma ctxmap_erase_poLe_single X `{PartialOrder X} n m m' x
  : MapInterface.find x m ⊑ MapInterface.find x m'
    -> MapInterface.find x (ctxmap_erase m n)
                        ⊑ MapInterface.find x (ctxmap_erase m' n).
Proof.
  intros. general induction n; simpl; eauto.
  mlud; eauto.
Qed.

Lemma ctxmap_erase_poEq_single X `{PartialOrder X} n m m' x
  : MapInterface.find x m ≣ MapInterface.find x m'
    -> MapInterface.find x (ctxmap_erase m n)
                        ≣ MapInterface.find x (ctxmap_erase m' n).
Proof.
  intros. general induction n; simpl; eauto.
  mlud; eauto.
Qed.

Lemma ctxmap_erase_poLe X `{PartialOrder X} n m m'
  : m ⊑ m'
    -> ctxmap_erase m n ⊑ ctxmap_erase m' n.
Proof.
  intros. general induction n; simpl; eauto.
  eapply leMap_remove. eapply IHn. eauto.
Qed.

Instance remove_poEq X `{PartialOrder X} (x:nat)
  : Proper (poEq ==> poEq) (MapInterface.remove x).
Proof.
  unfold Proper, respectful; intros.
  hnf; intros. mlud; eauto.
Qed.

Lemma remove_remove X `{PartialOrder X} m (a b:nat)
  : MapInterface.remove a (MapInterface.remove b m)
                        ≣ MapInterface.remove b (MapInterface.remove a m).
Proof.
  hnf; intros.
  repeat mlud; eauto.
Qed.

Lemma remove_erase X `{PartialOrder X} m Z a
  : MapInterface.remove a (ctxmap_erase m Z) ≣ (ctxmap_erase (MapInterface.remove a m) Z).
Proof.
  general induction Z; simpl; eauto.
  rewrite remove_remove. rewrite IHZ. reflexivity.
Qed.

Lemma ctxmap_erase_poEq X `{PartialOrder X} Z m m' x
  : x ∈ of_list Z
    -> MapInterface.find x (ctxmap_erase m Z)
                        ≣  MapInterface.find x (ctxmap_erase m' Z).
Proof.
  intros. general induction Z; simpl in *; eauto.
  - simpl in *. cset_tac.
  - cset_tac'.
    + mlud; eauto. exfalso; eauto.
    + rewrite !remove_erase. eapply IHZ. eauto.
Qed.


Lemma x_notin_range x k n
  : x ∉ of_list (range k n)
    -> x < k \/ k+n <= x.
Proof.
  general induction n; simpl in *.
  - decide (x < k); omega.
  - decide (x = k); subst;
      cset_tac'. eapply IHn in H1. destruct H1.
    omega. omega.
Qed.

Lemma x_in_range x k n
  : x >= k /\ k+n > x -> x ∈ of_list (range k n).
Proof.
  general induction n; simpl in *; dcr.
  - exfalso; omega.
  - decide (x = k); subst;
      cset_tac'. eapply IHn. omega.
Qed.

Lemma in_range_x x k n
  : x ∈ of_list (range k n) -> x >= k /\ k+n > x.
Proof.
  general induction n; simpl in *; dcr.
  - cset_tac.
  - decide (x = k); subst; try omega.
    cset_tac'; eapply IHn in H0; omega.
Qed.

Lemma ctxmap_extend_poLe X `{PartialOrder X} n m m'
  : m ⊑ m'
    -> ctxmap_extend m n ⊑ ctxmap_extend m' n.
Proof.
  intros. destruct H0.
  unfold ctxmap_extend; hnf. simpl.
  split; eauto. intros.
  decide (x < ctxmap_len m).
  - rewrite H0.
    eapply ctxmap_erase_poLe_single. eauto.
  - rewrite H0. rewrite ctxmap_erase_poEq. reflexivity.
    eapply x_in_range. split. omega. omega.
Qed.

Lemma ctxmap_extend_poEq X `{PartialOrder X} n m m'
  : m ≣ m'
    -> ctxmap_extend m n ≣ ctxmap_extend m' n.
Proof.
  intros. destruct H0.
  unfold ctxmap_extend; hnf. simpl.
  split; eauto. intros.
  decide (x < ctxmap_len m).
  - rewrite H0.
    eapply ctxmap_erase_poEq_single. eauto.
  - rewrite H0. rewrite ctxmap_erase_poEq. reflexivity.
    eapply x_in_range. split. omega. omega.
Qed.

Hint Resolve ctxmap_extend_poLe ctxmap_extend_poEq.

Lemma ctxmap_erase_find X `{PartialOrder X} m Z x
  : x ∉ of_list Z
    -> MapInterface.find x (ctxmap_erase m Z) ≣ MapInterface.find x m.
Proof.
  intros. general induction Z; simpl in *; eauto.
  decide (x = a); subst.
  - mlud; cset_tac.
  - mlud. cset_tac.
    rewrite IHZ; eauto. cset_tac.
Qed.

Lemma ctxmap_drop_eta X `{PartialOrder X} m n
  : ctxmap_drop n (ctxmap_extend m n) ≣ m.
Proof.
  hnf; intros. split; eauto.
  - simpl. omega.
  - intros. simpl in *.
    rewrite ctxmap_erase_find; eauto.
    intro. eapply in_range_x in H1. omega.
Qed.

Lemma ctxmap_join_at_exp X `{JoinSemiLattice X} m x v
  : m ⊑ ctxmap_join_at m x v.
Proof.
  hnf; intros; simpl; split; eauto.
  intros. mlud; eauto.
  rewrite <- e.
  cases; eauto.
Qed.

Hint Resolve ctxmap_join_at_exp.

Infix "+|+" := (@ctxmap_app _) (right associativity, at level 60) : ctxmap_scope.
Delimit Scope ctxmap_scope with ctxmap.
Bind Scope ctxmap_scope with ctxmap.


Instance ctxmap_drop_proper n X `{PartialOrder X}
  : Proper (poEq ==> poEq) (@ctxmap_drop n X).
Proof.
  unfold Proper, respectful; intros.
  eapply ctxmap_drop_poEq; eauto.
Qed.

Instance ctxmap_drop_proper' n X `{PartialOrder X}
  : Proper (poLe ==> poLe) (@ctxmap_drop n X).
Proof.
  unfold Proper, respectful; intros.
  eapply ctxmap_drop_poLe; eauto.
Qed.
