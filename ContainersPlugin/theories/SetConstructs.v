Require Import SetInterface SetAVLInstance.
Require Import SetFacts SetProperties.

Unset Standard Proposition Elimination Names.

Generalizable All Variables.

Local Transparent set.

(** This module provides a couple of common set constructions.  They
   are built with and for the AVL instance and are not parameterized
   by an FSet implementation. *)

(** * Mapping a function on a set *)
Section Mapping.
  Local Open Scope set_scope.
  Context `{HA : OrderedType A, HB: OrderedType B}.
  Variable f : A -> B.

  Definition map (s : set A) : set B :=
    fold (fun a acc => add (f a) acc) s {}.

  Context `{f_m : Proper _ (_eq ==> _eq) f}.
  Property map_spec : forall s,
    forall b, In b (map s) <-> exists a, In a s /\ b === f a.
  Proof.
    intro s.
    apply fold_rec_weak with
      (P := fun s r => forall b, In b r <-> exists a, In a s /\ b === f a);
      clear s.
    (* morphism *)
    intros; rewrite H0; clear H0; split; intros [z Hz];
      exists z; [rewrite <- H | rewrite H]; exact Hz.
    (* init *)
    intros; rewrite empty_iff; firstorder; contradiction (empty_1 H).
    (* step *)
    intros; rewrite add_iff; rewrite H0; clear H0; split; intro.
    destruct H0. exists x; split; intuition.
    destruct H0 as [z Hz]; exists z; rewrite add_iff; intuition.
    destruct H0 as [z Hz]; rewrite add_iff in Hz; destruct Hz.
    destruct H0. left; rewrite H0; auto.
    right; exists z; auto.
  Qed.
  Global Opaque map.
  Local Transparent In FSet_OrderedType.

  Instance map_m : Proper (_eq ==> _eq) map.
  Proof.
    intros s s' H z.
    setoid_rewrite map_spec; firstorder.
  Qed.
  Corollary map_1 : forall a s, In a s -> In (f a) (map s).
  Proof.
    intros; rewrite map_spec; firstorder.
  Qed.
  Corollary map_2 : forall b s, In b (map s) -> exists a, In a s /\ b === f a.
    intros; rewrite map_spec in H; assumption.
  Qed.
  Definition map_iff := map_spec.
End Mapping.

(** * Cartesian product *)
Section CartesianProduct.
  Local Open Scope set_scope.
  Context `{HA : OrderedType A, HB: OrderedType B}.

  (** [map_add s' a acc] extends [acc] with all the pairs [(a, b)]
     where [b] belongs to [s']. *)
  Definition map_add (s' : set B) (a : A) (acc : set (A * B)) :=
    fold (fun b acc => add (a, b) acc) s' acc.
  (** [cart_prod s s'] returns the cartesian product of [s] and [s']. *)
  Definition cart_prod (s : set A) (s' : set B) : set (A * B) :=
    fold (map_add s') s {}.

  (** Specs for [map_add] and [cart_prod] *)
  Property map_add_spec : forall s' a acc,
    forall x, In x (map_add s' a acc) <->
      In x acc \/ (fst x === a /\ In (snd x) s').
  Proof.
    intros s' a acc.
    apply fold_rec_weak with
      (P := fun svu r => forall x,
        In x r <-> (In x acc \/ (fst x === a /\ In (snd x) svu))).
    (* morphism *)
    intros; rewrite H0, H; reflexivity.
    (* init *)
    intros; intuition. contradiction (empty_1 H1).
    (* step *)
    intros b m s Hb IH [xa xb]; simpl.
    rewrite add_iff, IH; clear IH; simpl; rewrite add_iff; intuition auto.
    inversion_clear H0; right; split; auto; apply add_1; auto.
    left; constructor; auto.
  Qed.

  Property cart_prod_spec : forall s s',
    forall x, In x (cart_prod s s') <-> In (fst x) s /\ In (snd x) s'.
  Proof.
    intros s s'.
    apply fold_rec_weak with
      (P := fun svu r => forall x,
        In x r <-> In (fst x ) svu /\ In (snd x) s').
    (* morphism *)
    intros; rewrite H0, !H; reflexivity.
    (* init *)
    intros [a b]; rewrite !empty_iff; tauto.
    (* step *)
    intros a acc svu Ha IH [xa xb]; simpl.
    rewrite map_add_spec, IH, add_iff; simpl; clear IH.
    intuition.
  Qed.
  (** Now that we have the specs, we hide the implementations. *)
  Global Opaque map_add cart_prod.
  Local Transparent In FSet_OrderedType.

  (** [cart_prod] is a morphism *)
  Instance cart_prod_m : Proper (_eq ==> _eq ==> _eq) cart_prod.
  Proof.
    intros s s' Hs t t' Ht z.
    setoid_rewrite cart_prod_spec. rewrite Hs, Ht; reflexivity.
  Qed.
  (** Properties of [cart_prod] in the FSetInterface style *)
  Corollary cart_prod_1 : forall s s' a b,
    In a s -> In b s' -> In (a, b) (cart_prod s s').
  Proof.
    intros; rewrite cart_prod_spec; simpl; tauto.
  Qed.
  Corollary cart_prod_2 : forall s s' a b,
    In (a, b) (cart_prod s s') -> In a s.
  Proof.
    intros; rewrite cart_prod_spec in H; simpl in H; tauto.
  Qed.
  Corollary cart_prod_3 : forall s s' a b,
    In (a, b) (cart_prod s s') -> In b s'.
  Proof.
    intros; rewrite cart_prod_spec in H; simpl in H; tauto.
  Qed.
  Definition cart_prod_iff := cart_prod_spec.
End CartesianProduct.

(** * Implementation of power sets *)
Section PowerSet.
  Local Open Scope set_scope.
  Context `{HA : OrderedType A}.

  (** [add_one x m] takes a set of sets [m] and adds [x] to
     all sets in [m], adding these new sets to [m]. *)
  Definition add_one x (m : set (set A)) : set (set A) :=
    fold (fun s acc => add {x; s} acc) m m.
  (** [powerset s] returns the power set of [s]. *)
  Definition powerset (s : set A) : set (set A) :=
    fold add_one s (singleton {}).

  Local Transparent Equal _eq.
  Local Transparent In FSet_OrderedType.

  (** Specs for [add_one] and [powerset] *)
  Property add_one_spec :
    forall x m s, In s (add_one x m) <->
      (In s m \/ exists s', In s' m /\ s [=] {x; s'}).
  Proof.
    intros x m.
    apply fold_rec_weak with
      (P := fun mvu r => forall s, In s r <->
        (In s m \/ exists s', In s' mvu /\ s [=] {x; s'})).
    (* morphism *)
    intros; rewrite ?H0, ?H; intuition; right.
    destruct H2 as [z [Hz1 Hz2]]; exists z; rewrite <-H; split; auto.
    destruct H2 as [z [Hz1 Hz2]]; exists z; rewrite H; split; auto.
    (* init *)
    intros; intuition.
    destruct H0 as [z [abs _]]; contradiction (empty_1 abs).
    (* step *)
    intros s' a mvu Hx' IH s.
    rewrite add_iff; rewrite IH; clear IH; intuition.
    right; exists s'; split; [apply add_1 | rewrite H0]; reflexivity.
    right; destruct H as [z [Hz1 Hz2]]; exists z; split; auto.
    apply add_2; auto.
    destruct H0 as [z [Hz1 Hz2]]; rewrite add_iff in Hz1;
      destruct Hz1; [left | right; right; exists z].
    rewrite H, Hz2; reflexivity.
    split; assumption.
  Qed.

  Property powerset_spec :
    forall s s', In s' (powerset s) <-> s' [<=] s.
  Proof.
    intros s.
    apply fold_rec_weak with
      (P := fun svu r => forall s', s' \In r <-> s' [<=] svu).
    (* morphism *)
    intros; rewrite H0, H; reflexivity.
    (* init *)
    intros; rewrite singleton_iff; split; intro.
    rewrite <- H; reflexivity.
    symmetry; refine (empty_is_empty_1 _).
    intros z Hz; contradiction (empty_1 (H z Hz)).
    (* step *)
    intros x m svu Hx IH s'.
    rewrite add_one_spec, IH.
    split; intro H.
    destruct H.
    exact (fun z Hz => add_2 _ (H z Hz)).
    destruct H as [z [Hz1 Hz2]].
    rewrite Hz2; rewrite IH in Hz1; rewrite Hz1; reflexivity.
    destruct (subset_dec s' svu) as [Hsub|Hnsub]; [left | right].
    exact Hsub.
    exists (remove x s'); split.
    rewrite IH.
    intros z Hz; rewrite remove_iff in Hz; destruct Hz.
    assert (Hz' := H z H0); rewrite add_iff in Hz'; destruct Hz'.
    contradiction (H1 H2). assumption.
    symmetry; apply add_remove.
    destruct (In_dec x s'); auto.
    contradiction Hnsub; intros z Hz.
    assert (Hz' := H z Hz); rewrite add_iff in Hz'; destruct Hz'.
    rewrite H0 in n; contradiction (n Hz). assumption.
  Qed.
  (** Now that we have the specs, we hide the implementations. *)
  Global Opaque add_one powerset.

  (** [powerset] is a morphism *)
  Instance powerset_m : Proper (_eq ==> _eq) powerset.
  Proof.
    intros s s' H z.
    setoid_rewrite powerset_spec. rewrite H; reflexivity.
  Qed.
  (** Properties of [powerset] in the FSetInterface style *)
  Corollary powerset_1 : forall s s', s' [<=] s -> In s' (powerset s).
  Proof.
    intros; rewrite powerset_spec; assumption.
  Qed.
  Corollary powerset_2 : forall s s', In s' (powerset s) -> s' [<=] s.
  Proof.
    intros; rewrite powerset_spec in H; assumption.
  Qed.
  Definition powerset_iff := powerset_spec.
End PowerSet.

(** * Diagonal product

   We call diagonal product of a set [s] the sets of all strictly
   ordered pairs of elements of [s], ie. unlike the cartesian product
   [cart_prod s s], any pair of different elements [(a, b)] is only
   present once (as [(a, b)] if [a <<< b] and [(b, a)] otherwise).
   It does not contain pairs of the form [(a, a)] either.
   *)
Section DiagonalProduct.
  Local Open Scope set_scope.
  Context `{HA : OrderedType A}.

  (* diag {} = {};
     diag {x; s} = diag s \cup {(x, a) | a \in s} si x < s *)
  Require Import Recdef.
  Function diag_prod (s : set A) {measure cardinal} : set (A * A) :=
      match min_elt s with
        | None => {}
        | Some x =>
          let s' := remove x s in
            map_add s' x (diag_prod s')
      end.
  Proof.
    intros.
    rewrite <- remove_cardinal_1 with s x.
    constructor.
    exact (min_elt_1 teq).
  Defined.
(*   diag_prod_ind is defined *)
(*   diag_prod_rec is defined *)
(*   diag_prod_rect is defined *)
(*   R_diag_prod_correct is defined *)
(*   R_diag_prod_complete is defined *)
(*   diag_prod is defined *)
(*   diag_prod_equation is defined *)
  Global Opaque diag_prod.

  Property diag_prod_spec : forall s,
    forall x, In x (diag_prod s) <->
      In (fst x) s /\ In (snd x) s /\ (fst x) <<< (snd x).
  Proof.
    intro s.
    apply diag_prod_ind with
      (P := fun s r => forall x, In x r <->
        (In (fst x) s /\ In (snd x) s /\ fst x <<< snd x)); clear s.
    (* init *)
    intros s' Hs' [a b]; simpl.
    apply min_elt_3 in Hs'.
    apply empty_is_empty_1 in Hs'.
    rewrite !Hs', !empty_iff; tauto.
    (* step *)
    intros s x Hx s' IH [a b]; rewrite map_add_spec, IH; simpl.
    destruct (min_elt_dec s); inversion Hx; subst; clear Hx.
    clear IH; unfold s'; clear s'; rewrite !remove_iff; intuition.
    rewrite H; assumption.
    destruct (compare_dec a b); auto.
    contradiction H2; transitivity a; auto.
    contradiction (Hmin b H0); rewrite <- H; assumption.
    destruct (eq_dec a x); [right | left].
    intuition; rewrite <- H1; exact (lt_not_eq H2).
    intuition. symmetry; assumption.
    intro abs; apply (Hmin a H0); rewrite abs; assumption.
  Qed.

  Local Transparent Equal _eq In FSet_OrderedType.

  (** [diag_prod] is a morphism *)
  Instance diag_prod_m : Proper (_eq ==> _eq) diag_prod.
  Proof.
    intros s s' H z.
    setoid_rewrite diag_prod_spec. rewrite H; reflexivity.
  Qed.
  (** Properties of [diag_prod] in the FSetInterface style *)
  Corollary diag_prod_1 : forall s x y, In x s -> In y s -> x <<< y ->
    In (x, y) (diag_prod s).
  Proof.
    intros; rewrite diag_prod_spec; tauto.
  Qed.
  Corollary diag_prod_2 : forall s x y, In (x, y) (diag_prod s) -> In x s.
  Proof.
    intros; rewrite diag_prod_spec in H; tauto.
  Qed.
  Corollary diag_prod_3 : forall s x y, In (x, y) (diag_prod s) -> In y s.
  Proof.
    intros; rewrite diag_prod_spec in H; tauto.
  Qed.
  Corollary diag_prod_4 : forall s x y, In (x, y) (diag_prod s) -> x <<< y.
  Proof.
    intros; rewrite diag_prod_spec in H; tauto.
  Qed.
  Definition diag_prod_iff := diag_prod_spec.
End DiagonalProduct.

(** * Disjoint union *)
Section DisjointUnion.
  Local Open Scope set_scope.
  Context `{HA : OrderedType A, HB: OrderedType B}.

  Definition disj_union (s : set A) (s' : set B) : set (A + B) :=
    union (map (@inl A B) s) (map (@inr A B) s').

  Property disj_union_spec : forall s s',
    forall (x : A + B), In x (disj_union s s') <->
      match x with
        | inl a => In a s
        | inr b => In b s'
      end.
  Proof.
    intros; unfold disj_union.
    rewrite union_iff, 2map_iff.
    destruct x as [a|b]; firstorder; inversion_clear H0;
      rewrite H1; assumption.
    repeat intro; Tactics.tconstructor ltac:(assumption).
    repeat intro; Tactics.tconstructor ltac:(assumption).
  Qed.
  Global Opaque disj_union.
  Local Transparent Equal _eq In FSet_OrderedType.

  Instance disj_union_m : Proper (_eq ==> _eq ==> _eq) disj_union.
  Proof.
    repeat intro.
    setoid_rewrite disj_union_spec.
    destruct a; [rewrite H | rewrite H0]; reflexivity.
  Qed.
  Property disj_union_1 :
    forall s s' a, In a s -> In (inl _ a) (disj_union s s').
  Proof.
    intros; rewrite disj_union_spec; auto.
  Qed.
  Property disj_union_2 :
    forall s s' b, In b s' -> In (inr _ b) (disj_union s s').
  Proof.
    intros; rewrite disj_union_spec; auto.
  Qed.
  Property disj_union_3 : forall s s' x, In x (disj_union s s') ->
    match x with inl a => In a s | inr b => In b s' end.
  Proof.
    intros; rewrite disj_union_spec in H; auto.
  Qed.
  Definition disj_union_iff := disj_union_spec.
End DisjointUnion.

(* Section Permutations. *)
(*   Local Open Scope set_scope. *)
(*   Context `{HA : UsualOrderedType A}. *)

(*   (* Perm({}) = []; *)
(*      Perm({x; s}) = \bigcup_{l \in Perm(s)} shuffle(x, l) *)
(*      où *)
(*      shuffle(x,[]) = [x]; *)
(*      shuffle(x,a::q) = {x::(a::q)} \cup (map (a::) shuffle (x,q)) *)
(*      *) *)
(*   Fixpoint shuffle (x : A) (l : list A) : set (list A) := *)
(*     match l with *)
(*       | nil => { cons x nil } *)
(*       | a::q => {x::l; map (cons a) (shuffle x q)} *)
(*     end. *)
(*   Definition permutations (s : set A) : set (list A) := *)
(*     fold (fun x acc =>  *)
(*       fold (fun l acc => union (shuffle x l) acc) acc {} *)
(*     ) s {nil}. *)

(*   Property shuffle_all_permutations : *)
(*     forall x l p p', In p (shuffle x l) -> In p' (shuffle x l) -> *)
(*       Permutation p p'. *)
(*   Proof. *)
(*     intros x l; revert x; induction l; intros; simpl in *. *)
(*     rewrite singleton_iff in H, H0. *)
(*     inversion_clear H; inversion_clear H0. *)
(*     rewrite <- H1, <- H. *)
(*     inversion_clear H2; inversion_clear H3. *)
(*     do 2 constructor. *)
(*     rewrite add_iff in H, H0. *)

(* End Permutations. *)
(* Require Import Pprint.PrintableEx. *)
(* PPrint (shuffle 3 (0::1::2::nil)). *)
(* PPrint (permutations (add 1 (add 2 (add 3 {})))). *)
(* PPrint (permutations (add 1 (add 2 (add 3 (add 4 {}))))). *)

(* (** * FunctionSet *) *)
(* Section FunctionSet. *)
(*   Local Open Scope set_scope. *)
(*   Context `{HA : OrderedType A, HB: OrderedType B}. *)

(*   SubClass ffunc := set (A * B). *)
(*   Global Instance ffunc_OT : OrderedType ffunc. *)
(*   Proof.  *)
(*     unfold ffunc. *)
(*     apply SOT_as_OT. *)
(*   Defined. *)

(*   Definition extend_ffunc (x : A) (s' : set B) (sf : set ffunc) := *)
(*     fold (fun b acc => *)
(*       fold (fun (f : ffunc) acc => add (add (x, b) f) acc) sf acc) *)
(*     s' {}. *)
(*   Function func_set (s : set A) (s' : set B)  *)
(*     {measure cardinal s} : set ffunc := *)
(*       match min_elt s with *)
(*         | None => { empty } *)
(*         | Some a =>  *)
(*           let fs := func_set {s ~ a} s' in *)
(*             extend_ffunc a s' fs *)
(*       end. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite <- remove_cardinal_1 with s a. *)
(*     constructor. *)
(*     exact (min_elt_1 teq). *)
(*   Defined. *)
(* (*   func_set_ind is defined *) *)
(* (*   func_set_rec is defined *) *)
(* (*   func_set_rect is defined *) *)
(* (*   R_func_set_correct is defined *) *)
(* (*   R_func_set_complete is defined *) *)
(* (*   func_set is defined *) *)
(* (*   func_set_equation is defined *) *)
(*   Global Opaque func_set. *)

(*   CoInductive IsFunc (s : set A) (s' : set B) (f : ffunc) : Prop := *)
(*   | mk_IsFunc :  *)
(*     (forall a, In a s <-> exists b, In (a, b) f) -> *)
(*     (forall a b, In (a, b) f -> In b s') -> *)
(*     IsFunc s s' f. *)

(*   Property extend_ffunc_spec : forall s' x sf, *)
(*     forall f, In f (extend_ffunc x s' sf) <-> *)
(*       exists f', In f' sf /\ *)
(*         (forall b, In b f ->  *)
(*           if (fst b) == x then In (snd b) s' else In b f'). *)
(*   Proof. *)
(* (*     intros s' x sf. *) *)
(* (*     apply fold_rec_weak with  *) *)
(* (*       (P := fun bvu r => forall f, In f r <->). *) *)
(*   Admitted. *)
(*   Corollary extend_ffunc_IsFunc : forall s x s' sf, *)
(*     In x s -> *)
(*     (forall f, In f sf <-> IsFunc {s ~ x} s' f) -> *)
(*     forall f, In f (extend_ffunc x s' sf) <-> IsFunc s s' f. *)
(*   Proof. *)
(*     intros s x s' sf Hx; intros. *)
(*     rewrite extend_ffunc_spec; split; intro H1. *)
(*     destruct H1 as [fx [Hfx Hfx']]; rewrite H in Hfx. *)
(*     inversion_clear Hfx as [Hfx1 Hfx2]. *)
(*     constructor; intros. *)
(*     assert (Hab := Hfx' (a, b) H0); simpl in Hab. *)
(*     destruct (eq_dec a x); eauto. *)
(*     inversion_clear H1 as [Hf1 Hf2]. *)
(*     destruct ((proj1 (Hf1 x)) Hx) as [bx Hbx]. *)
(*     exists {f ~ (x, bx)}; split. *)
(*     rewrite H; constructor. *)
(*     intro a; rewrite remove_iff; rewrite Hf1; split; intro HH. *)
(*     destruct HH as [[b Hb] Hxa]. *)
(*     exists b; rewrite remove_iff; split; auto.  *)
(*     intro abs; inversion_clear abs; auto. *)
(*     destruct HH as [b Hb]; rewrite remove_iff in Hb; destruct Hb. *)
(*     split; [exists b; assumption |]. *)
(*     intros; apply Hf2 with a; apply remove_3 with (x, bx); auto. *)
(*     intros [z bz]; simpl; intros. *)
(*     destruct (eq_dec z x). eauto. *)
(*     rewrite remove_iff; split; auto. *)
(*     intro abs; inversion_clear abs; auto. *)
(*   Qed. *)

(*   Property func_set_spec : forall s s', *)
(*     forall f, In f (func_set s s') <-> IsFunc s s' f. *)
(*   Proof. *)
(*     intros s s'. *)
(*     apply func_set_ind with *)
(*       (P := fun s s' sf => forall f, In f sf <-> IsFunc s s' f); clear s s'. *)
(*     (* init *) *)
(*     intros; rewrite singleton_iff; split; intro. *)
(*     apply min_elt_3 in e. apply empty_is_empty_1 in e. *)
(*     constructor. *)
(*     intros; rewrite e, empty_iff. *)
(*     intuition; destruct H0. rewrite <- H in H0; contradiction (empty_1 H0). *)
(*     intros; rewrite <- H in H0; contradiction (empty_1 H0). *)
(*     apply min_elt_3 in e. apply empty_is_empty_1 in e. *)
(*     inversion_clear H. *)
(*     intro z; rewrite empty_iff; intuition. *)
(*     assert (abs := proj2 (H0 a)). *)
(*     rewrite e, empty_iff in abs; firstorder. *)
(*     (* step *) *)
(*     intros. *)
(*     apply extend_ffunc_IsFunc. *)
(*     exact (min_elt_1 e). *)
(*     exact H. *)
(*   Qed. *)

(* End FunctionSet. *)
