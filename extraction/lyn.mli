type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

val id : 'a1 -> 'a1

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a exc = 'a option

val value : 'a1 -> 'a1 option

val error : 'a1 option

val plus : Big.big_int -> Big.big_int -> Big.big_int

val max : Big.big_int -> Big.big_int -> Big.big_int

val nat_iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val nth : Big.big_int -> 'a1 list -> 'a1 -> 'a1

val nth_error : 'a1 list -> Big.big_int -> 'a1 exc

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val eq_nat_dec : Big.big_int -> Big.big_int -> bool

type 'a eqDec = 'a -> 'a -> bool

val equiv_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool

val nat_eq_eqdec : Big.big_int eqDec

type computable =
  bool
  (* singleton inductive, whose constructor was Build_Computable *)

val inst_equiv_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable

val inst_eq_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable

module Pos : 
 sig 
  type t = Big.big_int
  
  val succ : Big.big_int -> Big.big_int
  
  val add : Big.big_int -> Big.big_int -> Big.big_int
  
  val add_carry : Big.big_int -> Big.big_int -> Big.big_int
  
  val pred_double : Big.big_int -> Big.big_int
  
  val pred : Big.big_int -> Big.big_int
  
  val pred_N : Big.big_int -> Big.big_int
  
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : Big.big_int -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : Big.big_int -> Big.big_int -> mask
  
  val sub_mask_carry : Big.big_int -> Big.big_int -> mask
  
  val sub : Big.big_int -> Big.big_int -> Big.big_int
  
  val mul : Big.big_int -> Big.big_int -> Big.big_int
  
  val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : Big.big_int -> Big.big_int -> Big.big_int
  
  val square : Big.big_int -> Big.big_int
  
  val div2 : Big.big_int -> Big.big_int
  
  val div2_up : Big.big_int -> Big.big_int
  
  val size_nat : Big.big_int -> Big.big_int
  
  val size : Big.big_int -> Big.big_int
  
  val compare_cont : Big.big_int -> Big.big_int -> comparison -> comparison
  
  val compare : Big.big_int -> Big.big_int -> comparison
  
  val min : Big.big_int -> Big.big_int -> Big.big_int
  
  val max : Big.big_int -> Big.big_int -> Big.big_int
  
  val eqb : Big.big_int -> Big.big_int -> bool
  
  val leb : Big.big_int -> Big.big_int -> bool
  
  val ltb : Big.big_int -> Big.big_int -> bool
  
  val sqrtrem_step :
    (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
    (Big.big_int * mask) -> Big.big_int * mask
  
  val sqrtrem : Big.big_int -> Big.big_int * mask
  
  val sqrt : Big.big_int -> Big.big_int
  
  val gcdn : Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int
  
  val gcd : Big.big_int -> Big.big_int -> Big.big_int
  
  val ggcdn :
    Big.big_int -> Big.big_int -> Big.big_int ->
    Big.big_int * (Big.big_int * Big.big_int)
  
  val ggcd :
    Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int)
  
  val coq_Nsucc_double : Big.big_int -> Big.big_int
  
  val coq_Ndouble : Big.big_int -> Big.big_int
  
  val coq_lor : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_land : Big.big_int -> Big.big_int -> Big.big_int
  
  val ldiff : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr : Big.big_int -> Big.big_int -> Big.big_int
  
  val testbit_nat : Big.big_int -> Big.big_int -> bool
  
  val testbit : Big.big_int -> Big.big_int -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1
  
  val to_nat : Big.big_int -> Big.big_int
  
  val of_nat : Big.big_int -> Big.big_int
  
  val of_succ_nat : Big.big_int -> Big.big_int
 end

module Coq_Pos : 
 sig 
  type t = Big.big_int
  
  val succ : Big.big_int -> Big.big_int
  
  val add : Big.big_int -> Big.big_int -> Big.big_int
  
  val add_carry : Big.big_int -> Big.big_int -> Big.big_int
  
  val pred_double : Big.big_int -> Big.big_int
  
  val pred : Big.big_int -> Big.big_int
  
  val pred_N : Big.big_int -> Big.big_int
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : Big.big_int -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : Big.big_int -> Big.big_int -> mask
  
  val sub_mask_carry : Big.big_int -> Big.big_int -> mask
  
  val sub : Big.big_int -> Big.big_int -> Big.big_int
  
  val mul : Big.big_int -> Big.big_int -> Big.big_int
  
  val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : Big.big_int -> Big.big_int -> Big.big_int
  
  val square : Big.big_int -> Big.big_int
  
  val div2 : Big.big_int -> Big.big_int
  
  val div2_up : Big.big_int -> Big.big_int
  
  val size_nat : Big.big_int -> Big.big_int
  
  val size : Big.big_int -> Big.big_int
  
  val compare_cont : Big.big_int -> Big.big_int -> comparison -> comparison
  
  val compare : Big.big_int -> Big.big_int -> comparison
  
  val min : Big.big_int -> Big.big_int -> Big.big_int
  
  val max : Big.big_int -> Big.big_int -> Big.big_int
  
  val eqb : Big.big_int -> Big.big_int -> bool
  
  val leb : Big.big_int -> Big.big_int -> bool
  
  val ltb : Big.big_int -> Big.big_int -> bool
  
  val sqrtrem_step :
    (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
    (Big.big_int * mask) -> Big.big_int * mask
  
  val sqrtrem : Big.big_int -> Big.big_int * mask
  
  val sqrt : Big.big_int -> Big.big_int
  
  val gcdn : Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int
  
  val gcd : Big.big_int -> Big.big_int -> Big.big_int
  
  val ggcdn :
    Big.big_int -> Big.big_int -> Big.big_int ->
    Big.big_int * (Big.big_int * Big.big_int)
  
  val ggcd :
    Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int)
  
  val coq_Nsucc_double : Big.big_int -> Big.big_int
  
  val coq_Ndouble : Big.big_int -> Big.big_int
  
  val coq_lor : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_land : Big.big_int -> Big.big_int -> Big.big_int
  
  val ldiff : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr : Big.big_int -> Big.big_int -> Big.big_int
  
  val testbit_nat : Big.big_int -> Big.big_int -> bool
  
  val testbit : Big.big_int -> Big.big_int -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1
  
  val to_nat : Big.big_int -> Big.big_int
  
  val of_nat : Big.big_int -> Big.big_int
  
  val of_succ_nat : Big.big_int -> Big.big_int
  
  val eq_dec : Big.big_int -> Big.big_int -> bool
  
  val peano_rect : 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1
  
  val peano_rec : 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of Big.big_int * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (Big.big_int -> coq_PeanoView -> 'a1 -> 'a1) -> Big.big_int ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (Big.big_int -> coq_PeanoView -> 'a1 -> 'a1) -> Big.big_int ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : Big.big_int -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : Big.big_int -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : Big.big_int -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> coq_PeanoView -> 'a1
  
  val eqb_spec : Big.big_int -> Big.big_int -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  val ltb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : Big.big_int -> Big.big_int -> bool
    
    val min_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : Big.big_int -> Big.big_int -> bool
   end
  
  val max_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : Big.big_int -> Big.big_int -> bool
  
  val min_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : Big.big_int -> Big.big_int -> bool
 end

module N : 
 sig 
  type t = Big.big_int
  
  val zero : Big.big_int
  
  val one : Big.big_int
  
  val two : Big.big_int
  
  val succ_double : Big.big_int -> Big.big_int
  
  val double : Big.big_int -> Big.big_int
  
  val succ : Big.big_int -> Big.big_int
  
  val pred : Big.big_int -> Big.big_int
  
  val succ_pos : Big.big_int -> Big.big_int
  
  val add : Big.big_int -> Big.big_int -> Big.big_int
  
  val sub : Big.big_int -> Big.big_int -> Big.big_int
  
  val mul : Big.big_int -> Big.big_int -> Big.big_int
  
  val compare : Big.big_int -> Big.big_int -> comparison
  
  val eqb : Big.big_int -> Big.big_int -> bool
  
  val leb : Big.big_int -> Big.big_int -> bool
  
  val ltb : Big.big_int -> Big.big_int -> bool
  
  val min : Big.big_int -> Big.big_int -> Big.big_int
  
  val max : Big.big_int -> Big.big_int -> Big.big_int
  
  val div2 : Big.big_int -> Big.big_int
  
  val even : Big.big_int -> bool
  
  val odd : Big.big_int -> bool
  
  val pow : Big.big_int -> Big.big_int -> Big.big_int
  
  val square : Big.big_int -> Big.big_int
  
  val log2 : Big.big_int -> Big.big_int
  
  val size : Big.big_int -> Big.big_int
  
  val size_nat : Big.big_int -> Big.big_int
  
  val pos_div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int
  
  val div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int
  
  val div : Big.big_int -> Big.big_int -> Big.big_int
  
  val modulo : Big.big_int -> Big.big_int -> Big.big_int
  
  val gcd : Big.big_int -> Big.big_int -> Big.big_int
  
  val ggcd :
    Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int)
  
  val sqrtrem : Big.big_int -> Big.big_int * Big.big_int
  
  val sqrt : Big.big_int -> Big.big_int
  
  val coq_lor : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_land : Big.big_int -> Big.big_int -> Big.big_int
  
  val ldiff : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftl : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr : Big.big_int -> Big.big_int -> Big.big_int
  
  val testbit_nat : Big.big_int -> Big.big_int -> bool
  
  val testbit : Big.big_int -> Big.big_int -> bool
  
  val to_nat : Big.big_int -> Big.big_int
  
  val of_nat : Big.big_int -> Big.big_int
  
  val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : Big.big_int -> Big.big_int -> bool
  
  val discr : Big.big_int -> Big.big_int option
  
  val binary_rect :
    'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
    Big.big_int -> 'a1
  
  val binary_rec :
    'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
    Big.big_int -> 'a1
  
  val peano_rect : 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1
  
  val peano_rec : 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1
  
  val leb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  val ltb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : Big.big_int -> Big.big_int
  
  val log2_up : Big.big_int -> Big.big_int
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : Big.big_int -> Big.big_int -> Big.big_int
  
  val eqb_spec : Big.big_int -> Big.big_int -> reflect
  
  val b2n : bool -> Big.big_int
  
  val setbit : Big.big_int -> Big.big_int -> Big.big_int
  
  val clearbit : Big.big_int -> Big.big_int -> Big.big_int
  
  val ones : Big.big_int -> Big.big_int
  
  val lnot : Big.big_int -> Big.big_int -> Big.big_int
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : Big.big_int -> Big.big_int -> bool
    
    val min_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : Big.big_int -> Big.big_int -> bool
   end
  
  val max_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : Big.big_int -> Big.big_int -> bool
  
  val min_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : Big.big_int -> Big.big_int -> bool
 end

module Z : 
 sig 
  type t = Big.big_int
  
  val zero : Big.big_int
  
  val one : Big.big_int
  
  val two : Big.big_int
  
  val double : Big.big_int -> Big.big_int
  
  val succ_double : Big.big_int -> Big.big_int
  
  val pred_double : Big.big_int -> Big.big_int
  
  val pos_sub : Big.big_int -> Big.big_int -> Big.big_int
  
  val add : Big.big_int -> Big.big_int -> Big.big_int
  
  val opp : Big.big_int -> Big.big_int
  
  val succ : Big.big_int -> Big.big_int
  
  val pred : Big.big_int -> Big.big_int
  
  val sub : Big.big_int -> Big.big_int -> Big.big_int
  
  val mul : Big.big_int -> Big.big_int -> Big.big_int
  
  val pow_pos : Big.big_int -> Big.big_int -> Big.big_int
  
  val pow : Big.big_int -> Big.big_int -> Big.big_int
  
  val square : Big.big_int -> Big.big_int
  
  val compare : Big.big_int -> Big.big_int -> comparison
  
  val sgn : Big.big_int -> Big.big_int
  
  val leb : Big.big_int -> Big.big_int -> bool
  
  val ltb : Big.big_int -> Big.big_int -> bool
  
  val geb : Big.big_int -> Big.big_int -> bool
  
  val gtb : Big.big_int -> Big.big_int -> bool
  
  val eqb : Big.big_int -> Big.big_int -> bool
  
  val max : Big.big_int -> Big.big_int -> Big.big_int
  
  val min : Big.big_int -> Big.big_int -> Big.big_int
  
  val abs : Big.big_int -> Big.big_int
  
  val abs_nat : Big.big_int -> Big.big_int
  
  val abs_N : Big.big_int -> Big.big_int
  
  val to_nat : Big.big_int -> Big.big_int
  
  val to_N : Big.big_int -> Big.big_int
  
  val of_nat : Big.big_int -> Big.big_int
  
  val of_N : Big.big_int -> Big.big_int
  
  val to_pos : Big.big_int -> Big.big_int
  
  val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int
  
  val div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int
  
  val div : Big.big_int -> Big.big_int -> Big.big_int
  
  val modulo : Big.big_int -> Big.big_int -> Big.big_int
  
  val quotrem : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int
  
  val quot : Big.big_int -> Big.big_int -> Big.big_int
  
  val rem : Big.big_int -> Big.big_int -> Big.big_int
  
  val even : Big.big_int -> bool
  
  val odd : Big.big_int -> bool
  
  val div2 : Big.big_int -> Big.big_int
  
  val quot2 : Big.big_int -> Big.big_int
  
  val log2 : Big.big_int -> Big.big_int
  
  val sqrtrem : Big.big_int -> Big.big_int * Big.big_int
  
  val sqrt : Big.big_int -> Big.big_int
  
  val gcd : Big.big_int -> Big.big_int -> Big.big_int
  
  val ggcd :
    Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int)
  
  val testbit : Big.big_int -> Big.big_int -> bool
  
  val shiftl : Big.big_int -> Big.big_int -> Big.big_int
  
  val shiftr : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_lor : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_land : Big.big_int -> Big.big_int -> Big.big_int
  
  val ldiff : Big.big_int -> Big.big_int -> Big.big_int
  
  val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int
  
  val eq_dec : Big.big_int -> Big.big_int -> bool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  val ltb_spec0 : Big.big_int -> Big.big_int -> reflect
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : Big.big_int -> Big.big_int
  
  val log2_up : Big.big_int -> Big.big_int
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : Big.big_int -> Big.big_int -> Big.big_int
      
      val modulo : Big.big_int -> Big.big_int -> Big.big_int
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : Big.big_int -> Big.big_int -> Big.big_int
  
  val eqb_spec : Big.big_int -> Big.big_int -> reflect
  
  val b2z : bool -> Big.big_int
  
  val setbit : Big.big_int -> Big.big_int -> Big.big_int
  
  val clearbit : Big.big_int -> Big.big_int -> Big.big_int
  
  val lnot : Big.big_int -> Big.big_int
  
  val ones : Big.big_int -> Big.big_int
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : Big.big_int -> Big.big_int -> bool
    
    val min_case_strong :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> 'a1
      -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : Big.big_int -> Big.big_int -> bool
   end
  
  val max_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : Big.big_int -> Big.big_int -> bool
  
  val min_case_strong :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : Big.big_int -> Big.big_int -> bool
 end

val z_gt_dec : Big.big_int -> Big.big_int -> bool

val z_ge_dec : Big.big_int -> Big.big_int -> bool

val z_gt_le_dec : Big.big_int -> Big.big_int -> bool

val z_ge_lt_dec : Big.big_int -> Big.big_int -> bool

type 'a orderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_OrderedType *)

val _cmp : 'a1 orderedType -> 'a1 -> 'a1 -> comparison

val compare0 : 'a1 orderedType -> 'a1 -> 'a1 -> comparison

val is_compare : 'a1 orderedType -> 'a1 -> 'a1 -> comparison -> bool

type 'a specificOrderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_SpecificOrderedType *)

val sOT_cmp : 'a1 specificOrderedType -> 'a1 -> 'a1 -> comparison

val sOT_as_OT : 'a1 specificOrderedType -> 'a1 orderedType

val inst_eq_dec_list : 'a1 eqDec -> 'a1 list eqDec

val get_dec : 'a1 list -> Big.big_int -> 'a1 option

val nat_compare : Big.big_int -> Big.big_int -> comparison

val nat_OrderedType : Big.big_int specificOrderedType

val list_compare : 'a1 orderedType -> 'a1 list -> 'a1 list -> comparison

val list_OrderedType : 'a1 orderedType -> 'a1 list orderedType

type 'a fSet = { empty : __; is_empty : (__ -> bool);
                 mem : ('a -> __ -> bool); add0 : ('a -> __ -> __);
                 singleton : ('a -> __); remove : ('a -> __ -> __);
                 union : (__ -> __ -> __); inter : (__ -> __ -> __);
                 diff : (__ -> __ -> __); equal : (__ -> __ -> bool);
                 subset : (__ -> __ -> bool);
                 fold : (__ -> ('a -> __ -> __) -> __ -> __ -> __);
                 for_all : (('a -> bool) -> __ -> bool);
                 exists_ : (('a -> bool) -> __ -> bool);
                 filter : (('a -> bool) -> __ -> __);
                 partition : (('a -> bool) -> __ -> __ * __);
                 cardinal : (__ -> Big.big_int); elements : (__ -> 'a list);
                 choose : (__ -> 'a option); min_elt : (__ -> 'a option);
                 max_elt : (__ -> 'a option);
                 fSet_OrderedType : __ specificOrderedType }

type 'a set = __

val empty : 'a1 orderedType -> 'a1 fSet -> 'a1 set

val mem : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> bool

val add0 : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> 'a1 set

val singleton : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set

val union : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set

val diff : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set

val subset : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool

val fold :
  'a1 orderedType -> 'a1 fSet -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2

val for_all : 'a1 orderedType -> 'a1 fSet -> ('a1 -> bool) -> 'a1 set -> bool

val fSet_OrderedType :
  'a1 orderedType -> 'a1 fSet -> 'a1 set specificOrderedType

module SetList : 
 sig 
  type 'a set = 'a list
  
  val empty : 'a1 orderedType -> 'a1 set
  
  val is_empty : 'a1 orderedType -> 'a1 set -> bool
  
  val mem : 'a1 orderedType -> 'a1 -> 'a1 set -> bool
  
  val add : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set
  
  val singleton : 'a1 orderedType -> 'a1 -> 'a1 set
  
  val remove : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set
  
  val union : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set
  
  val inter : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set
  
  val diff : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set
  
  val equal : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool
  
  val subset : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool
  
  val fold : 'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2
  
  val map_monotonic :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set
  
  val filter : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set
  
  val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool
  
  val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool
  
  val partition :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set * 'a1 set
  
  val cardinal : 'a1 orderedType -> 'a1 set -> Big.big_int
  
  val elements : 'a1 orderedType -> 'a1 set -> 'a1 list
  
  val min_elt : 'a1 orderedType -> 'a1 set -> 'a1 option
  
  val max_elt : 'a1 orderedType -> 'a1 set -> 'a1 option
  
  val choose : 'a1 orderedType -> 'a1 set -> 'a1 option
  
  val map :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set
  
  val set_compare : 'a1 orderedType -> 'a1 set -> 'a1 set -> comparison
  
  val set_OrderedType : 'a1 orderedType -> 'a1 set orderedType
 end

module SetAVL : 
 sig 
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * Big.big_int
  
  val tree_rect :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
    Big.big_int -> 'a2) -> 'a1 tree -> 'a2
  
  val tree_rec :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
    Big.big_int -> 'a2) -> 'a1 tree -> 'a2
  
  val height : 'a1 orderedType -> 'a1 tree -> Big.big_int
  
  val cardinal : 'a1 orderedType -> 'a1 tree -> Big.big_int
  
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
  
  val triple_rect :
    'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple ->
    'a2
  
  val triple_rec :
    'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple ->
    'a2
  
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
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2
    tree
  
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
  
  val cons :
    'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
  
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
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  
  val coq_R_mem_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool -> 'a1
    coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
    tree -> bool -> 'a1 coq_R_mem -> 'a2
  
  val coq_R_mem_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool -> 'a1
    coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
    tree -> bool -> 'a1 coq_R_mem -> 'a2
  
  type 'elt coq_R_bal =
  | R_bal_0 of 'elt tree * 'elt * 'elt tree
  | R_bal_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_2 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_3 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_bal_4 of 'elt tree * 'elt * 'elt tree
  | R_bal_5 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_6 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_7 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_bal_8 of 'elt tree * 'elt * 'elt tree
  
  val coq_R_bal_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree ->
    __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
    -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ ->
    __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree
    -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
  
  val coq_R_bal_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree ->
    __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
    -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ ->
    __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree
    -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  
  val coq_R_add_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
    -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
  
  val coq_R_add_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
    -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
  
  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * Big.big_int * ('elt tree * 'elt) * 'elt coq_R_remove_min
     * 'elt tree * 'elt
  
  val coq_R_remove_min_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
    __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1
    -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2
  
  val coq_R_remove_min_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
    __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1
    -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2
  
  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  val coq_R_merge_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_merge -> 'a2
  
  val coq_R_merge_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_merge -> 'a2
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  
  val coq_R_remove_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
  
  val coq_R_remove_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
  
  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_min_elt
  
  val coq_R_min_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2
  
  val coq_R_min_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2
  
  type 'elt coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_max_elt
  
  val coq_R_max_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2
  
  val coq_R_max_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2
  
  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  val coq_R_concat_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_concat -> 'a2
  
  val coq_R_concat_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_concat -> 'a2
  
  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  
  val coq_R_split_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
    -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
    -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
  
  val coq_R_split_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
    -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
    -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
  
  type 'elt coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_inter * 'elt tree
     * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_inter * 'elt tree
     * 'elt coq_R_inter
  
  val coq_R_inter_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter
    -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2
  
  val coq_R_inter_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter
    -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2
  
  type 'elt coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_diff * 'elt tree
     * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_diff * 'elt tree
     * 'elt coq_R_diff
  
  val coq_R_diff_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
    'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 ->
    'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
    -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
  
  val coq_R_diff_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
    'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 ->
    'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
    -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
  
  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_union * 'elt tree
     * 'elt coq_R_union
  
  val coq_R_union_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2
    -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_union -> 'a2
  
  val coq_R_union_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2
    -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_union -> 'a2
  
  val fold' :
    'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
  
  val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list
 end

module S : 
 sig 
  type 'elt tree = 'elt SetAVL.tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * Big.big_int
  
  val tree_rect :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
    Big.big_int -> 'a2) -> 'a1 tree -> 'a2
  
  val tree_rec :
    'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
    Big.big_int -> 'a2) -> 'a1 tree -> 'a2
  
  val height : 'a1 orderedType -> 'a1 tree -> Big.big_int
  
  val cardinal : 'a1 orderedType -> 'a1 tree -> Big.big_int
  
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
  
  val triple_rect :
    'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple ->
    'a2
  
  val triple_rec :
    'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple ->
    'a2
  
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
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2
    tree
  
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
  
  val cons :
    'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
  
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
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  
  val coq_R_mem_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool -> 'a1
    coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
    tree -> bool -> 'a1 coq_R_mem -> 'a2
  
  val coq_R_mem_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool -> 'a1
    coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
    tree -> bool -> 'a1 coq_R_mem -> 'a2
  
  type 'elt coq_R_bal =
  | R_bal_0 of 'elt tree * 'elt * 'elt tree
  | R_bal_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_2 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_3 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_bal_4 of 'elt tree * 'elt * 'elt tree
  | R_bal_5 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_6 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_bal_7 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_bal_8 of 'elt tree * 'elt * 'elt tree
  
  val coq_R_bal_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree ->
    __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
    -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ ->
    __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree
    -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
  
  val coq_R_bal_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
    -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
    tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree ->
    __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
    -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ ->
    __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1 tree
    -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  
  val coq_R_add_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
    -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
  
  val coq_R_add_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
    -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
  
  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * Big.big_int * ('elt tree * 'elt) * 'elt coq_R_remove_min
     * 'elt tree * 'elt
  
  val coq_R_remove_min_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
    __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1
    -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2
  
  val coq_R_remove_min_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
    tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
    __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1
    -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
    coq_R_remove_min -> 'a2
  
  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  val coq_R_merge_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_merge -> 'a2
  
  val coq_R_merge_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_merge -> 'a2
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  
  val coq_R_remove_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
  
  val coq_R_remove_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree ->
    'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
  
  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_min_elt
  
  val coq_R_min_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2
  
  val coq_R_min_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2
  
  type 'elt coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_max_elt
  
  val coq_R_max_elt_rect :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2
  
  val coq_R_max_elt_rec :
    'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
    tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
    'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2
  
  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  val coq_R_concat_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_concat -> 'a2
  
  val coq_R_concat_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_concat -> 'a2
  
  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  
  val coq_R_split_rect :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
    -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
    -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
  
  val coq_R_split_rec :
    'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
    -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
    -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
  
  type 'elt coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_inter * 'elt tree
     * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_inter * 'elt tree
     * 'elt coq_R_inter
  
  val coq_R_inter_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter
    -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2
  
  val coq_R_inter_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter
    -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
    tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
    'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree ->
    __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
    coq_R_inter -> 'a2
  
  type 'elt coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_diff * 'elt tree
     * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_diff * 'elt tree
     * 'elt coq_R_diff
  
  val coq_R_diff_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
    'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 ->
    'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
    -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
  
  val coq_R_diff_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
    'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
    -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 ->
    'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool -> 'a1 tree -> __ -> __
    -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
    -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2
  
  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_union * 'elt tree
     * 'elt coq_R_union
  
  val coq_R_union_rect :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2
    -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_union -> 'a2
  
  val coq_R_union_rec :
    'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
    'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
    'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
    Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
    'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2
    -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
    'a1 tree -> 'a1 coq_R_union -> 'a2
  
  val fold' :
    'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
  
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

val cardinal0 : 'a1 orderedType -> 'a1 set0 -> Big.big_int

val filter0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0

val for_all0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool

val exists_0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool

val partition0 :
  'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 * 'a1 set0

val equal0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool

val subset0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool

val set_compare0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> comparison

val set_OrderedType0 : 'a1 orderedType -> 'a1 set0 specificOrderedType

val setAVL_FSet : 'a1 orderedType -> 'a1 fSet

val of_list : 'a1 orderedType -> 'a1 fSet -> 'a1 list -> 'a1 set

val map0 :
  'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set

val inst_eq_dec_ordered_type : 'a1 orderedType -> 'a1 eqDec

type 'a counted = { counted0 : ('a -> Big.big_int);
                    incc : ('a -> Big.big_int -> 'a) }

val counted0 : 'a1 counted -> 'a1 -> Big.big_int

type var = Big.big_int

type lab =
  Big.big_int
  (* singleton inductive, whose constructor was LabI *)

val labN : lab -> Big.big_int

val labInc : lab -> Big.big_int -> lab

val inst_counted_lab : lab counted

val lab_compare : lab -> lab -> comparison

val lab_OrderedType : lab specificOrderedType

type val0 = Big.big_int

val inst_eq_dec_val : val0 eqDec

val update : 'a1 orderedType -> ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a1 -> 'a2

val lookup_set :
  'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set

val update_with_list :
  'a1 orderedType -> 'a1 list -> 'a2 list -> ('a1 -> 'a2) -> 'a1 -> 'a2

val lookup_list : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val injective_on_step :
  'a2 orderedType -> ('a1 -> 'a2) -> 'a1 -> ('a2 set * bool) -> 'a2
  set * bool

val injective_on_compute :
  'a1 orderedType -> 'a2 orderedType -> 'a1 set -> ('a1 -> 'a2) -> bool

val injective_on_computable :
  'a1 orderedType -> 'a2 orderedType -> 'a1 set -> ('a1 -> 'a2) -> computable

val fresh_computable : 'a1 orderedType -> 'a1 -> 'a1 list -> computable

val inj_mapping_computable :
  'a1 orderedType -> 'a2 orderedType -> 'a2 set -> 'a1 list -> 'a2 list ->
  computable

type 'x env = var -> 'x

type binop =
| Add
| Sub
| Mul

type exp =
| Con of val0
| Var of var
| BinOp of binop * exp * exp

val freeVars : exp -> var set

val var_to_exp : var -> exp

val rename_exp : var env -> exp -> exp

type args = var list

type params = var list

type stmt =
| StmtExp of var * exp * stmt
| StmtIf of var * stmt * stmt
| StmtGoto of lab * args
| StmtReturn of var
| StmtLet of params * stmt * stmt

val freeVars0 : stmt -> var set

val rename : var env -> stmt -> stmt

type 'a ann =
| AnnExp of 'a * 'a ann
| AnnIf of 'a * 'a ann * 'a ann
| AnnGoto of 'a
| AnnReturn of 'a
| AnnLet of 'a * 'a ann * 'a ann

val getAnn : 'a1 ann -> 'a1

val setAnn : stmt -> 'a1 -> 'a1 ann

val annotation_dec_inst : stmt -> 'a1 ann -> computable

type live = var set

val live_sound_dec : (live * params) list -> stmt -> live ann -> computable

val live_sound_dec_inst :
  (live * params) list -> stmt -> live ann -> computable -> computable

val live_rename : var env -> live ann -> live ann

val restr : var set -> var set option -> var set option

val restrict : var set option list -> var set -> var set option list

val locally_inj_dec : var env -> stmt -> var set ann -> bool

val locally_inj_dec_inst :
  var env -> stmt -> var set ann -> computable -> computable

val fresh : var set -> var

val fresh_list : var set -> Big.big_int -> var list

val rename_apart' : var env -> var set -> stmt -> var set * stmt

val rename_apart : stmt -> stmt

val trs_dec :
  var set option list -> params list -> var set -> stmt -> var set option ann
  -> var list ann -> bool

val trs_dec_inst :
  var set option list -> params list -> var set -> stmt -> var set option ann
  -> var list ann -> computable -> computable -> computable

val compile : stmt -> var list ann -> stmt

type pmov = (var list * var list) list

val par_move : (var -> var) -> (var -> var) -> params -> args -> var -> var

val par_list : (params * args) list -> (var -> var) -> var -> var

val check_pmove : var set -> pmov -> pmov -> bool

val list_to_stmt : (var list * var list) list -> stmt -> stmt

val linearize_parallel_assignment :
  (var -> var list -> var list -> (var list * var list) list option) -> var
  set -> var list -> var list -> (var list * var list) list option

val check_is_simple_ass : (var list * var list) list -> bool

val compile_parallel_assignment :
  (var -> var list -> var list -> (var list * var list) list option) -> var
  set -> var list -> var list -> stmt -> stmt option

val lower :
  (var -> var list -> var list -> (var list * var list) list option) -> (var
  set * var list) list -> stmt -> var set ann -> stmt option

type nstmt =
| NstmtExp of var * exp * nstmt
| NstmtIf of var * nstmt * nstmt
| NstmtGoto of lab * args
| NstmtReturn of var
| NstmtLet of lab * params * nstmt * nstmt

val pos :
  'a1 orderedType -> 'a1 list -> 'a1 -> Big.big_int -> Big.big_int option

val labIndices : nstmt -> lab list -> stmt option

type 'a semiLattice = { bottom : 'a; join0 : ('a -> 'a -> 'a) }

val bottom : 'a1 orderedType -> 'a1 semiLattice -> 'a1

type ('dom, 'funDom) abstractInterpretation = { transform : ('funDom list ->
                                                            stmt -> 'dom ann
                                                            -> 'dom);
                                                mkFunDom : (params -> 'dom
                                                           ann -> 'funDom) }

val transform :
  'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation ->
  'a2 list -> stmt -> 'a1 ann -> 'a1

val mkFunDom :
  'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation ->
  params -> 'a1 ann -> 'a2

val backward :
  'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation ->
  stmt -> 'a2 list -> 'a1 ann -> 'a1 ann

val ann_lt_dec :
  ('a1 -> 'a1 -> computable) -> 'a1 ann -> 'a1 ann -> computable

val step :
  ('a1 -> 'a1 -> computable) -> 'a1 orderedType -> 'a1 semiLattice -> ('a1,
  'a2) abstractInterpretation -> stmt -> 'a1 ann -> 'a1 ann * bool

val analysis :
  ('a1 -> 'a1 -> computable) -> ('a1 ann -> ('a1 ann -> 'a1 ann * bool) ->
  'a1 ann) -> 'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2)
  abstractInterpretation -> stmt -> 'a1 ann

val set_var_semilattice : var set semiLattice

val liveness_transform : var set list -> stmt -> var set ann -> var set

val liveness_analysis : (var set, var set) abstractInterpretation

val livenessAnalysis :
  (var set ann -> (var set ann -> var set ann * bool) -> var set ann) -> stmt
  -> var set ann

val toILF :
  (stmt -> var set option ann * var list ann) -> stmt -> stmt option

val fromILF :
  (stmt -> var set -> var set -> __ -> var -> var) -> (var -> var list -> var
  list -> (var list * var list) list option) -> (var set ann -> (var set ann
  -> var set ann * bool) -> var set ann) -> stmt -> stmt option

