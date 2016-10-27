Require Import Containers.MapInterface.
Require Import Containers.OrderedTypeEx Min.

Module RawBag.
  Section WithMap.
    Context `{A_OT: OrderedType A}.
    Context `{A_Map: @FMap A A_OT}.
    Open Scope map_scope.

    SubClass bag := Map[A, nat].
    Definition Mult (x : A) (b : bag) :=
      match b[x] with
        | None => O
        | Some n => n
      end.

    Definition empty : bag := [].
    Definition is_empty (b : bag) := MapInterface.is_empty b.
    Definition mem (x : A) (b : bag) :=
      match b[x] with
        | Some (S _) => true
        | _ => false
      end.

    Definition add (x : A) (b : bag) :=
      insert x 1 S b.
    Definition singleton (x : A) : bag :=
      [][x <- 1].
    Definition remove (x : A) (b : bag) :=
      match b[x] with
        | None => b
        | Some n =>
          match n with
            | 0 | 1 => MapInterface.remove x b
            | S p => b[x <- p]
          end
      end.
    Definition union (b b' : bag) : bag :=
      map2 (fun xo yo =>
        match xo, yo with
          | None, None => None
          | Some p, Some q => Some (p + q)
          | Some p, None => Some p
          | None, Some q => Some q
        end) b b'.
    Definition inter (b b' : bag) : bag :=
      map2 (fun xo yo =>
        match xo, yo with
          | Some p, Some q => Some (min p q)
          | _, _ => None
        end) b b'.
    Definition diff (b b' : bag) : bag :=
      map2 (fun xo yo =>
        match xo, yo with
          | Some p, Some q =>
            match p - q with
              | O => None
              | k => Some k
            end
          | Some p, None => Some p
          | None, _ => None
        end) b b'.

    Definition equal (b b' : bag) :=
      MapInterface.equal (fun n n' => n == n') b b'.
    Definition subbag (b b' : bag) :=
      MapInterface.fold (fun x n (r : bool) =>
        if r then Mult x b' << n else false) b true.

    Definition fold {B : Type} (f : A -> nat -> B -> B) (b : bag) (i : B) :=
      MapInterface.fold f b i.
    Definition for_all (f : A -> bool) (b : bag) :=
      MapInterface.fold (fun x _ (r : bool) =>
        if r then f x else false) b true.
    Definition exists_ (f : A -> bool) (b : bag) :=
      MapInterface.fold (fun x _ (r : bool) =>
        if r then true else f x) b false.
    Definition filter (f : A -> bool) (b : bag) :=
      MapInterface.fold (fun x n b =>
        if f x then b else MapInterface.remove x b) b b.
    Definition partition (f : A -> bool) (b : bag) :=
      MapInterface.fold (fun x n (acc : bag * bag) =>
        let (bin,bout) := acc in
          if f x then (bin[x <- n], bout) else (bin, bout[x <- n])
      ) b ([],[]).

    Definition cardinal (b : bag) :=
      MapInterface.fold (fun _ n c => n + c) b O.
    Definition elements (b : bag) :=
      elements b.
    Definition choose (b : bag) :=
      MapInterface.fold (fun x _ acc =>
        match acc with Some _ => acc | None => Some x end) b None.
    Definition min_elt (b : bag) :=
      MapInterface.fold (fun x _ acc =>
        match acc with Some _ => acc | None => Some x end) b None.
    Definition max_elt (b : bag) :=
      MapInterface.fold (fun x _ acc => Some x) b None.

  End WithMap.
End RawBag.
Export RawBag.

(* (* FBag_OrderedType :> *) *)
(* (* SpecificOrderedType _ (MEqual_pw bag A Mult) (MEqual_pw_Equivalence _ _ _) *) *)

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)

(* (** * [FBagSpecs] : finite bags' specification *)

(*    We provide the specifications of bag operations in a separate class *)
(*    [FBagSpecs] parameterized by an [FBag] instance.  *)
(*    *) *)
(* Class FBagSpecs_Mult `(FBag A) := { *)
(*   Mult_1 : forall s (x y : A), x === y -> Mult x s = Mult y s *)
(* (*   In_1 : forall s (x y : A), x === y -> In x s -> In y s *) *)
(* }. *)
(* Class FBagSpecs_mem `(FBag A) := { *)
(*   mem_1 : forall s x, In x s -> mem x s = true; *)
(*   mem_2 : forall s x, mem x s = true -> In x s *)
(* }. *)
(* Class FBagSpecs_equal `(FBag A) := { *)
(*   equal_1 : forall s s', Equal s s' -> equal s s' = true; *)
(*   equal_2 : forall s s',  equal s s' = true -> Equal s s' *)
(* }. *)
(* Class FBagSpecs_subbag `(FBag A) := { *)
(*   subbag_1 : forall s s', Subbag s s' -> subbag s s' = true; *)
(*   subbag_2 : forall s s', subbag s s' = true -> Subbag s s' *)
(* }. *)
(* Class FBagSpecs_empty `(FBag A) := { *)
(*   empty_1 : MEmpty empty *)
(* }. *)
(* Class FBagSpecs_is_empty `(FBag A) := { *)
(*   is_empty_1 : forall s, MEmpty s -> is_empty s = true; *)
(*   is_empty_2 : forall s, is_empty s = true -> MEmpty s *)
(* }. *)
(* Class FBagSpecs_add `(FBag A) := { *)
(*   add_mult : forall s (x y : A), Mult x (add y s) =  *)
(*     if x == y then S (Mult x s) else Mult x s *)
(* (*   add_1 : forall s (x y : A), x === y -> In y (add x s); *) *)
(* (*   add_2 : forall s x y, In y s -> In y (add x s); *) *)
(* (*   add_3 : forall s (x y : A), x =/= y -> In y (add x s) -> In y s *) *)
(* }. *)
(* Class FBagSpecs_remove `(FBag A) := { *)
(*   remove_mult : forall s (x y : A), Mult x (remove y s) = *)
(*     if x == y then pred (Mult x s) else Mult x s *)
(* (*   remove_1 : forall s (x y : A), x === y -> ~ In y (remove x s); *) *)
(* (*   remove_2 : forall s (x y : A), *) *)
(* (*     x =/= y -> In y s -> In y (remove x s); *) *)
(* (*   remove_3 : forall s x y, In y (remove x s) -> In y s *) *)
(* }. *)
(* Class FBagSpecs_singleton `(FBag A) := { *)
(*   singleton_mult : forall s (x y : A), Mult x s = *)
(*     if x == y then 1 else 0 *)
(* (*   singleton_1 : forall (x y : A), In y (singleton x) -> x === y; *) *)
(* (*   singleton_2 : forall (x y : A), x === y -> In y (singleton x) *) *)
(* }. *)
(* Class FBagSpecs_union `(FBag A) := { *)
(*   union_mult : forall s s' x, Mult x (union s s') = Mult x s + Mult x s' *)
(* (*   union_1 : forall s s' x, *) *)
(* (*     In x (union s s') -> In x s \/ In x s'; *) *)
(* (*   union_2 : forall s s' x, In x s -> In x (union s s'); *) *)
(* (*   union_3 : forall s s' x, In x s' -> In x (union s s') *) *)
(* }. *)
(* Require Import Min. *)
(* Class FBagSpecs_inter `(FBag A) := { *)
(*   inter_mult : forall s s' x, Mult x (inter s s') = min (Mult x s) (Mult x s') *)
(* (*   inter_1 : forall s s' x, In x (inter s s') -> In x s; *) *)
(* (*   inter_2 : forall s s' x, In x (inter s s') -> In x s'; *) *)
(* (*   inter_3 : forall s s' x, *) *)
(* (*     In x s -> In x s' -> In x (inter s s') *) *)
(* }. *)
(* Class FBagSpecs_diff `(FBag A) := { *)
(*   diff_mult : forall s s' x, Mult x (diff s s') = Mult x s - Mult x s' *)
(* (*   diff_1 : forall s s' x, In x (diff s s') -> In x s; *) *)
(* (*   diff_2 : forall s s' x, In x (diff s s') -> ~ In x s'; *) *)
(* (*   diff_3 : forall s s' x, *) *)
(* (*     In x s -> ~ In x s' -> In x (diff s s') *) *)
(* }. *)
(* Class FBagSpecs_fold `(FBag A) := { *)
(*   fold_1 : forall s (B : Type) (i : B) (f : A -> nat -> B -> B), *)
(*       fold f s i = fold_left (fun a en => f (fst en) (snd en) a) (elements s) i *)
(* }. *)
(* Class FBagSpecs_cardinal `(FBag A) := { *)
(*   cardinal_1 : forall s, cardinal s = length (elements s) *)
(* }. *)
(* Class FBagSpecs_filter `(FBag A) := { *)
(*   filter_mult_1 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     In x (filter f s) -> Mult x (filter f s) = Mult x s; *)
(*   filter_mult_2 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     In x (filter f s) -> f x = true; *)
(*   filter_mult_3 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     f x = true -> Mult x s = Mult x (filter f s) *)
(* (*   filter_1 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *) *)
(* (*     In x (filter f s) -> In x s; *) *)
(* (*   filter_2 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *) *)
(* (*     In x (filter f s) -> f x = true; *) *)
(* (*   filter_3 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *) *)
(* (*     In x s -> f x = true -> In x (filter f s) *) *)
(* }. *)
(* Class FBagSpecs_for_all `(FBag A) := { *)
(*   for_all_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     For_all (fun x => f x = true) s -> for_all f s = true; *)
(*   for_all_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     for_all f s = true -> For_all (fun x => f x = true) s *)
(* }. *)
(* Class FBagSpecs_exists `(FBag A) := { *)
(*   exists_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     Exists (fun x => f x = true) s -> exists_ f s = true; *)
(*   exists_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     exists_ f s = true -> Exists (fun x => f x = true) s *)
(* }. *)
(* Class FBagSpecs_partition `(FBag A) := { *)
(*   partition_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     Equal (fst (partition f s)) (filter f s); *)
(*   partition_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     Equal (snd (partition f s)) (filter (fun x => negb (f x)) s) *)
(* }. *)
(* Class FBagSpecs_elements `(FBag A) := { *)
(*   elements_1 : forall s x, In x s -> InA _eq (x, Mult x s) (elements s); *)
(*   elements_2 : forall s x n, InA _eq (x, n) (elements s) -> Mult x s =  n; *)
(*   elements_3 : forall s, sort _lt (elements s); *)
(*   elements_3w : forall s, NoDupA _eq (elements s) *)
(* }. *)
(* Class FBagSpecs_choose `(FBag A) := { *)
(*   choose_1 : forall s x, choose s = Some x -> In x s; *)
(*   choose_2 : forall s, choose s = None -> Empty s; *)
(*   choose_3 : forall s s' x y, *)
(*     choose s = Some x -> choose s' = Some y -> Equal s s' -> x === y *)
(* }. *)
(* Class FBagSpecs_min_elt `(FBag A) := { *)
(*   min_elt_1 : forall s x, min_elt s = Some x -> In x s; *)
(*   min_elt_2 : forall s x y, *)
(*     min_elt s = Some x -> In y s -> ~ y <<< x; *)
(*   min_elt_3 : forall s, min_elt s = None -> Empty s *)
(* }. *)
(* Class FBagSpecs_max_elt `(FBag A) := { *)
(*   max_elt_1 : forall s x, max_elt s = Some x -> In x s; *)
(*   max_elt_2 : forall s x y, *)
(*     max_elt s = Some x -> In y s -> ~ x <<< y; *)
(*   max_elt_3 : forall s, max_elt s = None -> Empty s *)
(* }. *)

(* Class FBagSpecs `(F : FBag A) := { *)
(*   FFBagSpecs_Mult :> FBagSpecs_Mult F; *)
(*   FFBagSpecs_mem :> FBagSpecs_mem F; *)
(*   FFBagSpecs_equal :> FBagSpecs_equal F; *)
(*   FFBagSpecs_subbag :> FBagSpecs_subbag F; *)
(*   FFBagSpecs_empty :> FBagSpecs_empty F; *)
(*   FFBagSpecs_is_empty :> FBagSpecs_is_empty F; *)
(*   FFBagSpecs_add :> FBagSpecs_add F; *)
(*   FFBagSpecs_remove :> FBagSpecs_remove F; *)
(*   FFBagSpecs_singleton :> FBagSpecs_singleton F; *)
(*   FFBagSpecs_union :> FBagSpecs_union F; *)
(*   FFBagSpecs_inter :> FBagSpecs_inter F; *)
(*   FFBagSpecs_diff :> FBagSpecs_diff F; *)
(*   FFBagSpecs_fold :> FBagSpecs_fold F; *)
(*   FFBagSpecs_cardinal :> FBagSpecs_cardinal F; *)
(*   FFBagSpecs_filter :> FBagSpecs_filter F; *)
(*   FFBagSpecs_for_all :> FBagSpecs_for_all F; *)
(*   FFBagSpecs_exists :> FBagSpecs_exists F; *)
(*   FFBagSpecs_partition :> FBagSpecs_partition F; *)
(*   FFBagSpecs_elements :> FBagSpecs_elements F; *)
(*   FFBagSpecs_choose :> FBagSpecs_choose F; *)
(*   FFBagSpecs_min_elt :> FBagSpecs_min_elt F; *)
(*   FFBagSpecs_max_elt :> FBagSpecs_max_elt F *)
(* }. *)