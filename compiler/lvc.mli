type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val bool_dec : bool -> bool -> bool

module Nat :
 sig
  
 end

val tl : 'a1 list -> 'a1 list

val nth : int -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val testbit : positive -> n -> bool

  val of_succ_nat : int -> positive

  val eq_dec : positive -> positive -> bool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> n * n

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n

  val testbit : n -> n -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val pred : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val of_nat : int -> z

  val of_N : n -> z

  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> z * z

  val quot : z -> z -> z

  val rem : z -> z -> z

  val odd : z -> bool

  val div2 : z -> z

  val testbit : z -> z -> bool

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val eq_dec : z -> z -> bool
 end

val z_lt_dec : z -> z -> bool

val z_le_dec : z -> z -> bool

val z_gt_dec : z -> z -> bool

val z_ge_dec : z -> z -> bool

val z_le_gt_dec : z -> z -> bool

val z_gt_le_dec : z -> z -> bool

val z_ge_lt_dec : z -> z -> bool

type 'a orderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_OrderedType *)

val _cmp : 'a1 orderedType -> 'a1 -> 'a1 -> comparison

val compare0 : 'a1 orderedType -> 'a1 -> 'a1 -> comparison

type 'a specificOrderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_SpecificOrderedType *)

val sOT_cmp : 'a1 specificOrderedType -> 'a1 -> 'a1 -> comparison

val sOT_as_OT : 'a1 specificOrderedType -> 'a1 orderedType

val shift_nat : int -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : int -> z

val two_power_pos : positive -> z

val two_p : z -> z

val nat_compare : int -> int -> comparison

val nat_OrderedType : int specificOrderedType

type 'a fSet = { empty : __; is_empty : (__ -> bool);
                 mem : ('a -> __ -> bool); add0 : ('a -> __ -> __);
                 singleton : ('a -> __); remove : ('a -> __ -> __);
                 union : (__ -> __ -> __); inter : (__ -> __ -> __);
                 diff : (__ -> __ -> __); equal : (__ -> __ -> bool);
                 subset : (__ -> __ -> bool);
                 fold : (__ -> ('a -> __ -> __) -> __ -> __ -> __);
                 for_all : (('a -> bool) -> __ -> bool);
                 exists_ : (('a -> bool) -> __ -> bool);
                 filter0 : (('a -> bool) -> __ -> __);
                 partition : (('a -> bool) -> __ -> __ * __);
                 cardinal : (__ -> int); elements : (__ -> 'a list);
                 choose : (__ -> 'a option); min_elt : (__ -> 'a option);
                 max_elt : (__ -> 'a option);
                 fSet_OrderedType : __ specificOrderedType }

type 'a set = __

val empty : 'a1 orderedType -> 'a1 fSet -> 'a1 set

val mem : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> bool

val add0 : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> 'a1 set

val singleton : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set

val union : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set

val inter : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set

val diff : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set

val equal : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool

val subset : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool

val elements : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 list

module SetList :
 sig
  type 'a set = 'a list

  val fold : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2
 end

module SetAVL :
 sig
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * z

  val tree_rect :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 -> z
    -> 'a2) -> 'a1 tree -> 'a2

  val tree_rec :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 -> z
    -> 'a2) -> 'a1 tree -> 'a2

  val height : 'a1 orderedType -> 'a1 tree -> z

  val cardinal : 'a1 orderedType -> 'a1 tree -> int

  val empty : 'a1 orderedType -> 'a1 tree

  val is_empty : 'a1 orderedType -> 'a1 tree -> bool

  val mem : 'a1 orderedType -> 'a1 -> 'a1 tree -> bool

  val singleton : 'a1 orderedType -> 'a1 -> 'a1 tree

  val create : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false :
    'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree

  val join : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree * 'a1

  val merge : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree

  val min_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val max_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val choose : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val concat : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_in : bool; t_right : 'elt tree }

  val t_left : 'a1 orderedType -> 'a1 triple -> 'a1 tree

  val t_in : 'a1 orderedType -> 'a1 triple -> bool

  val t_right : 'a1 orderedType -> 'a1 triple -> 'a1 tree

  val split : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 triple

  val inter : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val diff : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val union : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : 'a1 orderedType -> 'a1 list -> 'a1 tree -> 'a1 list

  val elements : 'a1 orderedType -> 'a1 tree -> 'a1 list

  val filter_acc :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val filter : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree

  val partition_acc :
    'a1 orderedType -> ('a1 -> bool) -> ('a1 tree * 'a1 tree) -> 'a1 tree ->
    'a1 tree * 'a1 tree

  val partition :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree * 'a1 tree

  val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool

  val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool

  val map_monotonic :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val fold : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  val subsetl :
    'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool

  val subsetr :
    'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool

  val subset : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool

  type 'elt enumeration =
  | End
  | More of 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
    'a2) -> 'a1 enumeration -> 'a2

  val enumeration_rec :
    'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
    'a2) -> 'a1 enumeration -> 'a2

  val cons : 'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val compare_more :
    'a1 orderedType -> 'a1 -> ('a1 enumeration -> comparison) -> 'a1
    enumeration -> comparison

  val compare_cont :
    'a1 orderedType -> 'a1 tree -> ('a1 enumeration -> comparison) -> 'a1
    enumeration -> comparison

  val compare_end : 'a1 orderedType -> 'a1 enumeration -> comparison

  val compare : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> comparison

  val equal : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt tree
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem

  val coq_R_mem_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool
    -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
    'a2

  val coq_R_mem_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool
    -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
    'a2

  type 'elt coq_R_bal =
  | R_bal_0 of 'elt tree * 'elt * 'elt tree
  | R_bal_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_2 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_3 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_4 of 'elt tree * 'elt * 'elt tree
  | R_bal_5 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_6 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_7 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_8 of 'elt tree * 'elt * 'elt tree

  val coq_R_bal_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
    -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
    'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
    -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_bal -> 'a2

  val coq_R_bal_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
    -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
    'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
    -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_bal -> 'a2

  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add

  val coq_R_add_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_add -> 'a2

  val coq_R_add_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_add -> 'a2

  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * z * ('elt tree * 'elt) * 'elt coq_R_remove_min * 'elt tree
     * 'elt

  val coq_R_remove_min_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> ('a1
    tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 -> __ ->
    'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2

  val coq_R_remove_min_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> ('a1
    tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 -> __ ->
    'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2

  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  val coq_R_merge_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

  val coq_R_merge_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
    'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2

  val coq_R_remove_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
    'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2

  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_min_elt

  val coq_R_min_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_min_elt -> 'a2

  val coq_R_min_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_min_elt -> 'a2

  type 'elt coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_max_elt

  val coq_R_max_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_max_elt -> 'a2

  val coq_R_max_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_max_elt -> 'a2

  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  val coq_R_concat_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

  val coq_R_concat_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree

  val coq_R_split_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
    'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
    -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
    triple -> 'a1 coq_R_split -> 'a2

  val coq_R_split_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
    'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
    -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
    triple -> 'a1 coq_R_split -> 'a2

  type 'elt coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter

  val coq_R_inter_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2

  val coq_R_inter_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2

  type 'elt coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff

  val coq_R_diff_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree
    -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2

  val coq_R_diff_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree
    -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2

  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_union * 'elt tree * 'elt coq_R_union

  val coq_R_union_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1
    tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2

  val coq_R_union_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1
    tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2

  val fold' : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list
 end

module S :
 sig
  type 'elt tree = 'elt SetAVL.tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * z

  val tree_rect :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 -> z
    -> 'a2) -> 'a1 tree -> 'a2

  val tree_rec :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 -> z
    -> 'a2) -> 'a1 tree -> 'a2

  val height : 'a1 orderedType -> 'a1 tree -> z

  val cardinal : 'a1 orderedType -> 'a1 tree -> int

  val empty : 'a1 orderedType -> 'a1 tree

  val is_empty : 'a1 orderedType -> 'a1 tree -> bool

  val mem : 'a1 orderedType -> 'a1 -> 'a1 tree -> bool

  val singleton : 'a1 orderedType -> 'a1 -> 'a1 tree

  val create : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false :
    'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree

  val join : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree * 'a1

  val merge : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree

  val min_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val max_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val choose : 'a1 orderedType -> 'a1 tree -> 'a1 option

  val concat : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  type 'elt triple = 'elt SetAVL.triple = { t_left : 'elt tree; t_in : 
                                            bool; t_right : 'elt tree }

  val t_left : 'a1 orderedType -> 'a1 triple -> 'a1 tree

  val t_in : 'a1 orderedType -> 'a1 triple -> bool

  val t_right : 'a1 orderedType -> 'a1 triple -> 'a1 tree

  val split : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 triple

  val inter : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val diff : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val union : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : 'a1 orderedType -> 'a1 list -> 'a1 tree -> 'a1 list

  val elements : 'a1 orderedType -> 'a1 tree -> 'a1 list

  val filter_acc :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree -> 'a1 tree

  val filter : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree

  val partition_acc :
    'a1 orderedType -> ('a1 -> bool) -> ('a1 tree * 'a1 tree) -> 'a1 tree ->
    'a1 tree * 'a1 tree

  val partition :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree * 'a1 tree

  val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool

  val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool

  val map_monotonic :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val fold : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  val subsetl :
    'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool

  val subsetr :
    'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool

  val subset : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool

  type 'elt enumeration = 'elt SetAVL.enumeration =
  | End
  | More of 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
    'a2) -> 'a1 enumeration -> 'a2

  val enumeration_rec :
    'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
    'a2) -> 'a1 enumeration -> 'a2

  val cons : 'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val compare_more :
    'a1 orderedType -> 'a1 -> ('a1 enumeration -> comparison) -> 'a1
    enumeration -> comparison

  val compare_cont :
    'a1 orderedType -> 'a1 tree -> ('a1 enumeration -> comparison) -> 'a1
    enumeration -> comparison

  val compare_end : 'a1 orderedType -> 'a1 enumeration -> comparison

  val compare : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> comparison

  val equal : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool

  type 'elt coq_R_mem = 'elt SetAVL.coq_R_mem =
  | R_mem_0 of 'elt tree
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem

  val coq_R_mem_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool
    -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
    'a2

  val coq_R_mem_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool
    -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
    'a2

  type 'elt coq_R_bal = 'elt SetAVL.coq_R_bal =
  | R_bal_0 of 'elt tree * 'elt * 'elt tree
  | R_bal_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_2 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_3 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_4 of 'elt tree * 'elt * 'elt tree
  | R_bal_5 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_6 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_7 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_8 of 'elt tree * 'elt * 'elt tree

  val coq_R_bal_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
    -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
    'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
    -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_bal -> 'a2

  val coq_R_bal_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
    -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
    'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
    -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_bal -> 'a2

  type 'elt coq_R_add = 'elt SetAVL.coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add

  val coq_R_add_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_add -> 'a2

  val coq_R_add_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_add -> 'a2

  type 'elt coq_R_remove_min = 'elt SetAVL.coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * z * ('elt tree * 'elt) * 'elt coq_R_remove_min * 'elt tree
     * 'elt

  val coq_R_remove_min_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> ('a1
    tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 -> __ ->
    'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2

  val coq_R_remove_min_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> ('a1
    tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 -> __ ->
    'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2

  type 'elt coq_R_merge = 'elt SetAVL.coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  val coq_R_merge_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

  val coq_R_merge_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

  type 'elt coq_R_remove = 'elt SetAVL.coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
    'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2

  val coq_R_remove_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
    'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2

  type 'elt coq_R_min_elt = 'elt SetAVL.coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_min_elt

  val coq_R_min_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_min_elt -> 'a2

  val coq_R_min_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_min_elt -> 'a2

  type 'elt coq_R_max_elt = 'elt SetAVL.coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_max_elt

  val coq_R_max_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_max_elt -> 'a2

  val coq_R_max_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
    -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
    option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
    'a1 coq_R_max_elt -> 'a2

  type 'elt coq_R_concat = 'elt SetAVL.coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  val coq_R_concat_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

  val coq_R_concat_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree
    -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

  type 'elt coq_R_split = 'elt SetAVL.coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree

  val coq_R_split_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
    'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
    -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
    triple -> 'a1 coq_R_split -> 'a2

  val coq_R_split_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
    'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
    -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
    triple -> 'a1 coq_R_split -> 'a2

  type 'elt coq_R_inter = 'elt SetAVL.coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter

  val coq_R_inter_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2

  val coq_R_inter_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2
    -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
    __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2

  type 'elt coq_R_diff = 'elt SetAVL.coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff

  val coq_R_diff_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree
    -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2

  val coq_R_diff_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ ->
    'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree
    -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_diff -> 'a2

  type 'elt coq_R_union = 'elt SetAVL.coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_union * 'elt tree * 'elt coq_R_union

  val coq_R_union_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1
    tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2

  val coq_R_union_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1
    tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1
    tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2

  val fold' : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list
 end

type 'elt set0 =
  'elt S.tree
  (* singleton inductive, whose constructor was Bst *)

val this : 'a1 orderedType -> 'a1 set0 -> 'a1 S.tree

val mem0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> bool

val empty0 : 'a1 orderedType -> 'a1 set0

val is_empty0 : 'a1 orderedType -> 'a1 set0 -> bool

val singleton0 : 'a1 orderedType -> 'a1 -> 'a1 set0

val add1 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0

val remove0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0

val inter0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0

val union0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0

val diff0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0

val elements0 : 'a1 orderedType -> 'a1 set0 -> 'a1 list

val min_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option

val max_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option

val choose0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option

val fold0 : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set0 -> 'a2 -> 'a2

val cardinal0 : 'a1 orderedType -> 'a1 set0 -> int

val filter1 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0

val for_all0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool

val exists_0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool

val partition0 :
  'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 * 'a1 set0

val equal0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool

val subset0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool

val set_compare : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> comparison

val set_OrderedType : 'a1 orderedType -> 'a1 set0 specificOrderedType

val setAVL_FSet : 'a1 orderedType -> 'a1 fSet

val of_list : 'a1 orderedType -> 'a1 fSet -> 'a1 list -> 'a1 set

val to_list : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 list

type 'a eqDec = 'a -> 'a -> bool

val nat_eq_eqdec : int eqDec

val bool_eqdec : bool eqDec

type computable = bool

val inst_eq_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable

val option_eq_dec : 'a1 eqDec -> 'a1 option -> 'a1 option -> bool

val inst_eq_dec_option : 'a1 eqDec -> 'a1 option eqDec

val equiv_computable : 'a1 orderedType -> 'a1 -> 'a1 -> computable

val drop : int -> 'a1 list -> 'a1 list

val take : int -> 'a1 list -> 'a1 list

type 'a counted = { counted0 : ('a -> int); incc : ('a -> int -> 'a) }

val counted0 : 'a1 counted -> 'a1 -> int

type var = int

val inst_eq_dec_var : var eqDec

type lab =
  int
  (* singleton inductive, whose constructor was LabI *)

val labN : lab -> int

val labInc : lab -> int -> lab

val inst_counted_lab : lab counted

val zeq : z -> z -> bool

val zlt : z -> z -> bool

val zle : z -> z -> bool

val proj_sumbool : bool -> bool

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : int
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : int

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_P_mod_two_p : positive -> int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> z -> z

  val coq_Zzero_ext : z -> z -> z

  val coq_Zsign_ext : z -> z -> z

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val coq_Z_one_bits : int -> z -> z -> z list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val testbit : int -> z -> bool

  val powerserie : z list -> z

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val coq_Zsize : z -> z

  val size : int -> z
 end

module Wordsize_32 :
 sig
  val wordsize : int
 end

module Int :
 sig
  val wordsize : int

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_P_mod_two_p : positive -> int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> z -> z

  val coq_Zzero_ext : z -> z -> z

  val coq_Zsign_ext : z -> z -> z

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val coq_Z_one_bits : int -> z -> z -> z list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val testbit : int -> z -> bool

  val powerserie : z list -> z

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val coq_Zsize : z -> z

  val size : int -> z
 end

type val0 = Int.int

val val_zero : val0

val inst_eq_dec_val : val0 eqDec

type binop =
| BinOpAdd
| BinOpSub
| BinOpMul
| BinOpDiv
| BinOpEq

type unop =
| UnOpToBool
| UnOpNeg

val val2bool : val0 -> bool

val comp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

type exp =
| Con of val0
| Var of var
| UnOp of unop * exp
| BinOp of binop * exp * exp

val freeVars : exp -> var set

val exp2bool : exp -> bool option

val zip : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val mapi_impl : (int -> 'a1 -> 'a2) -> int -> 'a1 list -> 'a2 list

val mapi : (int -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

type external0 = int

type 'a size0 = 'a -> int

val size1 : 'a1 size0 -> 'a1 -> int

val size_rec :
  ('a1 -> int) -> 'a1 -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a2

val def_size : 'a1 size0

val size_list : 'a1 size0 -> 'a1 list size0

type stmt =
| StmtLet of var * exp * stmt
| StmtIf of exp * stmt * stmt
| StmtApp of lab * exp list
| StmtReturn of exp
| StmtExtern of var * external0 * exp list * stmt
| StmtFun of (var list * stmt) list * stmt

val occurVars : stmt -> var set

type 'dom partialOrder = { poLe_dec : ('dom -> 'dom -> computable);
                           poEq_dec : ('dom -> 'dom -> computable) }

val poLe_dec : 'a1 partialOrder -> 'a1 -> 'a1 -> computable

val poEq_dec : 'a1 partialOrder -> 'a1 -> 'a1 -> computable

val partialOrder_sig : 'a1 partialOrder -> 'a1 partialOrder

val partialOrder_bool : bool partialOrder

val list_update_at : 'a1 list -> int -> 'a1 -> 'a1 list

type 'a ann =
| Ann0 of 'a
| Ann1 of 'a * 'a ann
| Ann2 of 'a * 'a ann * 'a ann
| AnnF of 'a * 'a ann list * 'a ann

val ann_size : 'a1 ann size0

val getAnn : 'a1 ann -> 'a1

val setTopAnn : 'a1 ann -> 'a1 -> 'a1 ann

val setAnn : 'a1 -> stmt -> 'a1 ann

val mapAnn : ('a1 -> 'a2) -> 'a1 ann -> 'a2 ann

val indexwise_R_dec' :
  'a1 list -> 'a2 list -> (int -> 'a1 -> 'a2 -> __ -> __ -> computable) ->
  computable

val ann_R_dec : ('a1 -> 'a2 -> computable) -> 'a1 ann -> 'a2 ann -> computable

val partialOrder_ann : 'a1 partialOrder -> 'a1 ann partialOrder

type 'a status =
| Success of 'a
| Error of char list

val option2status : 'a1 option -> char list -> 'a1 status

val smap : ('a1 -> 'a2 status) -> 'a1 list -> 'a2 list status

val filter_by : ('a1 -> bool) -> 'a1 list -> 'a2 list -> 'a2 list

val countTrue : bool list -> int

val mapOption : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val oget : 'a1 orderedType -> 'a1 set option -> 'a1 set

val oto_list : 'a1 orderedType -> 'a1 set option -> 'a1 list

val ounion :
  'a1 orderedType -> 'a1 set option -> 'a1 set option -> 'a1 set option

val pos : 'a1 orderedType -> 'a1 list -> 'a1 -> int -> int option

type nstmt =
| NstmtLet of var * exp * nstmt
| NstmtIf of exp * nstmt * nstmt
| NstmtApp of var * exp list
| NstmtReturn of exp
| NstmtExtern of var * external0 * exp list * nstmt
| NstmtFun of ((var * var list) * nstmt) list * nstmt

val labIndices : var list -> nstmt -> stmt status

type 'a boundedSemiLattice = { bottom : 'a; join0 : ('a -> 'a -> 'a) }

val bottom : 'a1 partialOrder -> 'a1 boundedSemiLattice -> 'a1

val join0 : 'a1 partialOrder -> 'a1 boundedSemiLattice -> 'a1 -> 'a1 -> 'a1

val bool_boundedsemilattice : bool boundedSemiLattice

val sig_R_dec : ('a1 -> 'a1 -> computable) -> 'a1 -> 'a1 -> computable

type 'dom analysis = { dom_po : 'dom partialOrder;
                       analysis_step : ('dom -> 'dom); initial_value : 
                       'dom }

val dom_po : 'a1 analysis -> 'a1 partialOrder

val analysis_step : 'a1 analysis -> 'a1 -> 'a1

val initial_value : 'a1 analysis -> 'a1

val safeFirst : 'a1 analysis -> 'a1 -> 'a1

val safeFixpoint : 'a1 analysis -> 'a1

type 'a anni =
| Anni0
| Anni1 of 'a
| Anni2 of 'a * 'a
| Anni2opt of 'a option * 'a option

val mapAnni : ('a1 -> 'a2) -> 'a1 anni -> 'a2 anni

val getAnni : 'a1 -> 'a1 anni -> 'a1

val getAnniLeft : 'a1 -> 'a1 anni -> 'a1

val getAnniRight : 'a1 -> 'a1 anni -> 'a1

val keep : int -> 'a1 list -> 'a1 option list

val backwardF :
  stmt -> (var list list -> 'a1 list -> stmt -> __ -> 'a1 ann -> 'a1 ann) ->
  var list list -> 'a1 list -> (var list * stmt) list -> 'a1 ann list -> 'a1
  ann list

val backward :
  stmt -> (stmt -> var list list -> 'a1 list -> stmt -> __ -> 'a1 anni ->
  'a1) -> var list list -> 'a1 list -> stmt -> 'a1 ann -> 'a1 ann

val makeBackwardAnalysis :
  (stmt -> 'a1 partialOrder) -> (stmt -> 'a1 boundedSemiLattice) -> (stmt ->
  var list list -> 'a1 list -> stmt -> __ -> 'a1 anni -> 'a1) -> stmt -> 'a1
  ann analysis

val partialOrder_Subset_Equal_Bounded :
  'a1 orderedType -> 'a1 set -> 'a1 set partialOrder

val set_var_semilattice_bounded : var set -> var set boundedSemiLattice

val liveness_transform :
  var list list -> var set list -> stmt -> var set anni -> var set

val liveness_transform_dep :
  stmt -> var list list -> var set list -> stmt -> var set anni -> var set

val liveness_analysis : stmt -> var set ann analysis

val livenessAnalysis : stmt -> var set ann

val compileF :
  (var list list -> stmt -> var list list ann -> stmt) -> var list list ->
  (var list * stmt) list -> var list list -> var list list -> var list list
  ann list -> (var list * stmt) list

val compile : var list list -> stmt -> var list list ann -> stmt

val addParam : var -> var set list -> var set list -> var set list

val addAdd : var set -> var set -> var set option -> var set option

val computeParameters :
  var set list -> var list list -> var set list -> stmt -> var set ann -> var
  list list ann * var set option list

val compileF0 :
  ((bool * var list) list -> stmt -> bool ann -> stmt) -> (bool * var list)
  list -> (var list * stmt) list -> bool ann list -> (var list * stmt) list

val compile0 : (bool * var list) list -> stmt -> bool ann -> stmt

val filter2 : var list -> var set -> var list

val compile1 : (var set * var list) list -> stmt -> var set ann -> stmt

val compile_live : stmt -> var set ann -> var set -> var set ann

val forwardF :
  stmt -> 'a1 partialOrder -> 'a1 boundedSemiLattice -> (var list list ->
  stmt -> __ -> 'a1 ann -> 'a1 ann * 'a1 list) -> var list list -> (var
  list * stmt) list -> 'a1 ann list -> ('a1 ann * 'a1 list) list

val forward :
  stmt -> 'a1 partialOrder -> 'a1 boundedSemiLattice -> (stmt -> var list
  list -> stmt -> __ -> 'a1 -> 'a1 anni) -> var list list -> stmt -> 'a1 ann
  -> 'a1 ann * 'a1 list

val makeForwardAnalysis :
  (stmt -> 'a1 partialOrder) -> (stmt -> 'a1 boundedSemiLattice) -> (stmt ->
  var list list -> stmt -> __ -> 'a1 -> 'a1 anni) -> stmt -> 'a1 -> 'a1 ann
  analysis

val unreachable_code_transform :
  stmt -> var list list -> stmt -> bool -> bool anni

val unreachable_code_analysis : stmt -> bool ann analysis

val unreachableCodeAnalysis : stmt -> bool ann

val additionalArguments : stmt -> var set ann -> var list list ann

val toDeBruijn : nstmt -> stmt status

val toILF : stmt -> stmt
