type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

(** val length : 'a1 list -> Big.big_int **)

let rec length = function
| [] -> Big.zero
| y :: l' -> Big.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val plus : Big.big_int -> Big.big_int -> Big.big_int **)

let rec plus = Big.add

(** val max : Big.big_int -> Big.big_int -> Big.big_int **)

let rec max = Big.max

(** val nat_iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n f x =
  Big.nat_case
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val nth : Big.big_int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  Big.nat_case
    (fun _ ->
    match l with
    | [] -> default
    | x :: l' -> x)
    (fun m ->
    match l with
    | [] -> default
    | x :: t0 -> nth m t0 default)
    n

(** val nth_error : 'a1 list -> Big.big_int -> 'a1 exc **)

let rec nth_error l n =
  Big.nat_case
    (fun _ ->
    match l with
    | [] -> error
    | x :: l0 -> value x)
    (fun n0 ->
    match l with
    | [] -> error
    | a :: l0 -> nth_error l0 n0)
    n

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] ->
    (match l' with
     | [] -> true
     | a :: l0 -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 -> if eq_dec0 y a0 then list_eq_dec eq_dec0 l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val eq_nat_dec : Big.big_int -> Big.big_int -> bool **)

let rec eq_nat_dec = Big.eq

type 'a eqDec = 'a -> 'a -> bool

(** val equiv_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let equiv_dec eqDec0 =
  eqDec0

(** val nat_eq_eqdec : Big.big_int eqDec **)

let nat_eq_eqdec =
  eq_nat_dec

type computable =
  bool
  (* singleton inductive, whose constructor was Build_Computable *)

(** val inst_equiv_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable **)

let inst_equiv_cm h x y =
  h x y

(** val inst_eq_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable **)

let inst_eq_cm h x y =
  h x y

module Pos = 
 struct 
  type t = Big.big_int
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let rec succ x =
    Big.positive_case
      (fun p -> Big.double
      (succ p))
      (fun p -> Big.doubleplusone
      p)
      (fun _ -> Big.double
      Big.one)
      x
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec add x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add p q))
        (fun q -> Big.double
        (add p q))
        (fun _ -> Big.doubleplusone
        p)
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.double
        (succ q))
        (fun q -> Big.doubleplusone
        q)
        (fun _ -> Big.double
        Big.one)
        y)
      x
  
  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)
  
  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add_carry p q))
        (fun q -> Big.double
        (add_carry p q))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (succ q))
        (fun q -> Big.double
        (succ q))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred x =
    Big.positive_case
      (fun p -> Big.double
      p)
      (fun p ->
      pred_double p)
      (fun _ ->
      Big.one)
      x
  
  (** val pred_N : Big.big_int -> Big.big_int **)
  
  let pred_N x =
    Big.positive_case
      (fun p -> (Big.double
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      Big.zero)
      x
  
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0
  
  (** val double_pred_mask : Big.big_int -> mask **)
  
  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (Big.positive_case
       (fun p0 -> IsPos
       (pred q))
       (fun p0 -> IsPos
       (pred q))
       (fun _ ->
       IsNul)
       q)
  | _ -> IsNeg
  
  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)
  
  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)
  
  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> Big.one
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec mul x y =
    Big.positive_case
      (fun p ->
      add y (Big.double (mul p y)))
      (fun p -> Big.double
      (mul p y))
      (fun _ ->
      y)
      x
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    Big.positive_case
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    iter y (mul x) Big.one
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let rec square p =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double
      (add (square p0) p0)))
      (fun p0 -> Big.double (Big.double
      (square p0)))
      (fun _ ->
      Big.one)
      p
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val div2_up : Big.big_int -> Big.big_int **)
  
  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val size_nat : Big.big_int -> Big.big_int **)
  
  let rec size_nat p =
    Big.positive_case
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun _ -> Big.succ
      Big.zero)
      p
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let rec size p =
    Big.positive_case
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      Big.one)
      p
  
  (** val compare_cont :
      Big.big_int -> Big.big_int -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        compare_cont p q r)
        (fun q ->
        compare_cont p q Gt)
        (fun _ ->
        Gt)
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        compare_cont p q Lt)
        (fun q ->
        compare_cont p q r)
        (fun _ ->
        Gt)
        y)
      (fun _ ->
      Big.positive_case
        (fun q ->
        Lt)
        (fun q ->
        Lt)
        (fun _ ->
        r)
        y)
      x
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        eqb p0 q0)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q)
      p
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
      (Big.big_int * mask) -> Big.big_int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Big.doubleplusone (Big.double s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Big.doubleplusone s), (sub_mask r' s'))
       else ((Big.double s), (IsPos r'))
     | _ ->
       ((Big.double s),
         (sub_mask (g (f Big.one)) (Big.double (Big.double Big.one)))))
  
  (** val sqrtrem : Big.big_int -> Big.big_int * mask **)
  
  let rec sqrtrem p =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x ->
          Big.doubleplusone x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.doubleplusone x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos (Big.double
        Big.one))))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos
        Big.one)))
        p0)
      (fun _ -> (Big.one,
      IsNul))
      p
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec gcdn n a b =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 ->
          gcdn n0 a b0)
          (fun _ ->
          Big.one)
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          gcdn n0 a0 b)
          (fun b0 -> Big.double
          (gcdn n0 a0 b0))
          (fun _ ->
          Big.one)
          b)
        (fun _ ->
        Big.one)
        a)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      Big.big_int -> Big.big_int -> Big.big_int ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let rec ggcdn n a b =
    Big.nat_case
      (fun _ -> (Big.one, (a,
      b)))
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (Big.one, Big.one))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa (Big.double ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb (Big.double ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, (Big.double bb))))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          let (g, p0) = ggcdn n0 a0 b in
          let (aa, bb) = p0 in (g, ((Big.double aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in ((Big.double g), p))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun _ -> (Big.one, (Big.one,
        b)))
        a)
      n
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : Big.big_int -> Big.big_int **)
  
  let coq_Nsucc_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val coq_Ndouble : Big.big_int -> Big.big_int **)
  
  let coq_Ndouble n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun _ ->
        p)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.double
        (coq_lor p0 q0))
        (fun _ -> Big.doubleplusone
        p0)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        q)
        (fun q0 -> Big.doubleplusone
        q0)
        (fun _ ->
        q)
        q)
      p
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_land p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.one)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.zero)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.one)
        (fun q0 ->
        Big.zero)
        (fun _ ->
        Big.one)
        q)
      p
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun _ ->
        p)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.zero)
        (fun q0 ->
        Big.one)
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lxor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> (Big.doubleplusone
        p0))
        q)
      (fun _ ->
      Big.positive_case
        (fun q0 -> (Big.double
        q0))
        (fun q0 -> (Big.doubleplusone
        q0))
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl_nat p n =
    nat_iter n (fun x -> Big.double x) p
  
  (** val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr_nat p n =
    nat_iter n div2 p
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 (fun x -> Big.double x) p)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 div2 p)
      n
  
  (** val testbit_nat : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit_nat p n =
    Big.positive_case
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        false)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun _ ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n0 ->
        false)
        n)
      p
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit p n =
    Big.positive_case
      (fun p0 ->
      Big.n_case
        (fun _ ->
        true)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        false)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat x =
    iter_op plus x (Big.succ Big.zero)
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let rec of_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      Big.nat_case
        (fun _ ->
        Big.one)
        (fun n0 ->
        succ (of_nat x))
        x)
      n
  
  (** val of_succ_nat : Big.big_int -> Big.big_int **)
  
  let rec of_succ_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      succ (of_succ_nat x))
      n
 end

module Coq_Pos = 
 struct 
  type t = Big.big_int
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let rec succ = Big.succ
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec add = Big.add
  
  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)
  
  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add_carry p q))
        (fun q -> Big.double
        (add_carry p q))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (succ q))
        (fun q -> Big.double
        (succ q))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = fun n -> Big.max Big.one (Big.pred n)
  
  (** val pred_N : Big.big_int -> Big.big_int **)
  
  let pred_N x =
    Big.positive_case
      (fun p -> (Big.double
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      Big.zero)
      x
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0
  
  (** val double_pred_mask : Big.big_int -> mask **)
  
  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (Big.positive_case
       (fun p0 -> IsPos
       (pred q))
       (fun p0 -> IsPos
       (pred q))
       (fun _ ->
       IsNul)
       q)
  | _ -> IsNeg
  
  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)
  
  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)
  
  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = fun n m -> Big.max Big.one (Big.sub n m)
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec mul = Big.mult
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    Big.positive_case
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    iter y (mul x) Big.one
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let rec square p =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double
      (add (square p0) p0)))
      (fun p0 -> Big.double (Big.double
      (square p0)))
      (fun _ ->
      Big.one)
      p
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val div2_up : Big.big_int -> Big.big_int **)
  
  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val size_nat : Big.big_int -> Big.big_int **)
  
  let rec size_nat p =
    Big.positive_case
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun _ -> Big.succ
      Big.zero)
      p
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let rec size p =
    Big.positive_case
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      Big.one)
      p
  
  (** val compare_cont :
      Big.big_int -> Big.big_int -> comparison -> comparison **)
  
  let rec compare_cont = fun x y c -> Big.compare_case c Lt Gt x y
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = fun x y -> Big.compare_case Eq Lt Gt x y
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        eqb p0 q0)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q)
      p
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
      (Big.big_int * mask) -> Big.big_int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Big.doubleplusone (Big.double s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Big.doubleplusone s), (sub_mask r' s'))
       else ((Big.double s), (IsPos r'))
     | _ ->
       ((Big.double s),
         (sub_mask (g (f Big.one)) (Big.double (Big.double Big.one)))))
  
  (** val sqrtrem : Big.big_int -> Big.big_int * mask **)
  
  let rec sqrtrem p =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x ->
          Big.doubleplusone x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.doubleplusone x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos (Big.double
        Big.one))))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos
        Big.one)))
        p0)
      (fun _ -> (Big.one,
      IsNul))
      p
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec gcdn n a b =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 ->
          gcdn n0 a b0)
          (fun _ ->
          Big.one)
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          gcdn n0 a0 b)
          (fun b0 -> Big.double
          (gcdn n0 a0 b0))
          (fun _ ->
          Big.one)
          b)
        (fun _ ->
        Big.one)
        a)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      Big.big_int -> Big.big_int -> Big.big_int ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let rec ggcdn n a b =
    Big.nat_case
      (fun _ -> (Big.one, (a,
      b)))
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (Big.one, Big.one))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa (Big.double ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb (Big.double ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, (Big.double bb))))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          let (g, p0) = ggcdn n0 a0 b in
          let (aa, bb) = p0 in (g, ((Big.double aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in ((Big.double g), p))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun _ -> (Big.one, (Big.one,
        b)))
        a)
      n
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : Big.big_int -> Big.big_int **)
  
  let coq_Nsucc_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val coq_Ndouble : Big.big_int -> Big.big_int **)
  
  let coq_Ndouble n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun _ ->
        p)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.double
        (coq_lor p0 q0))
        (fun _ -> Big.doubleplusone
        p0)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        q)
        (fun q0 -> Big.doubleplusone
        q0)
        (fun _ ->
        q)
        q)
      p
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_land p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.one)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.zero)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.one)
        (fun q0 ->
        Big.zero)
        (fun _ ->
        Big.one)
        q)
      p
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun _ ->
        p)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.zero)
        (fun q0 ->
        Big.one)
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lxor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> (Big.doubleplusone
        p0))
        q)
      (fun _ ->
      Big.positive_case
        (fun q0 -> (Big.double
        q0))
        (fun q0 -> (Big.doubleplusone
        q0))
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl_nat p n =
    nat_iter n (fun x -> Big.double x) p
  
  (** val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr_nat p n =
    nat_iter n div2 p
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 (fun x -> Big.double x) p)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 div2 p)
      n
  
  (** val testbit_nat : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit_nat p n =
    Big.positive_case
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        false)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun _ ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n0 ->
        false)
        n)
      p
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit p n =
    Big.positive_case
      (fun p0 ->
      Big.n_case
        (fun _ ->
        true)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        false)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat x =
    iter_op plus x (Big.succ Big.zero)
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let rec of_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      Big.nat_case
        (fun _ ->
        Big.one)
        (fun n0 ->
        succ (of_nat x))
        x)
      n
  
  (** val of_succ_nat : Big.big_int -> Big.big_int **)
  
  let rec of_succ_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      succ (of_succ_nat x))
      n
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let rec eq_dec p y0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        eq_dec p0 p1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        y0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun p1 ->
        eq_dec p0 p1)
        (fun _ ->
        false)
        y0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        y0)
      p
  
  (** val peano_rect :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 =
      peano_rect (f Big.one a) (fun p0 x ->
        f (succ (Big.double p0)) (f (Big.double p0) x))
    in
    (Big.positive_case
       (fun q ->
       f (Big.double q) (f2 q))
       (fun q ->
       f2 q)
       (fun _ ->
       a)
       p)
  
  (** val peano_rec :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of Big.big_int * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (Big.big_int -> coq_PeanoView -> 'a1 -> 'a1) -> Big.big_int ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (Big.big_int -> coq_PeanoView -> 'a1 -> 'a1) -> Big.big_int ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)
  
  (** val peanoView_xO : Big.big_int -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (Big.one, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (Big.double p0)), (PeanoSucc ((Big.double p0),
      (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : Big.big_int -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ Big.one), (PeanoSucc (Big.one, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (Big.doubleplusone p0)), (PeanoSucc ((Big.doubleplusone
      p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : Big.big_int -> coq_PeanoView **)
  
  let rec peanoView p =
    Big.positive_case
      (fun p0 ->
      peanoView_xI p0 (peanoView p0))
      (fun p0 ->
      peanoView_xO p0 (peanoView p0))
      (fun _ ->
      PeanoOne)
      p
  
  (** val coq_PeanoView_iter :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> coq_PeanoView ->
      'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : Big.big_int -> Big.big_int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : Big.big_int -> Big.big_int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : Big.big_int -> Big.big_int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : Big.big_int -> Big.big_int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = Big.big_int
  
  (** val zero : Big.big_int **)
  
  let zero =
    Big.zero
  
  (** val one : Big.big_int **)
  
  let one =
    Big.one
  
  (** val two : Big.big_int **)
  
  let two =
    (Big.double Big.one)
  
  (** val succ_double : Big.big_int -> Big.big_int **)
  
  let succ_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val double : Big.big_int -> Big.big_int **)
  
  let double n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = fun n -> Big.max Big.zero (Big.pred n)
  
  (** val succ_pos : Big.big_int -> Big.big_int **)
  
  let succ_pos n =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p ->
      Coq_Pos.succ p)
      n
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let add = Big.add
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = fun n m -> Big.max Big.zero (Big.sub n m)
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let mul = Big.mult
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun p ->
      Big.n_case
        (fun _ ->
        false)
        (fun q ->
        Coq_Pos.eqb p q)
        m)
      n
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        p)
        (fun p ->
        p)
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val even : Big.big_int -> bool **)
  
  let even n =
    Big.n_case
      (fun _ ->
      true)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      n
  
  (** val odd : Big.big_int -> bool **)
  
  let odd n =
    negb (even n)
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow n p =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q ->
        (Coq_Pos.pow q p0))
        n)
      p
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let square n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.square p))
      n
  
  (** val log2 : Big.big_int -> Big.big_int **)
  
  let log2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        (Coq_Pos.size p))
        (fun p ->
        (Coq_Pos.size p))
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let size n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.size p))
      n
  
  (** val size_nat : Big.big_int -> Big.big_int **)
  
  let size_nat n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Coq_Pos.size_nat p)
      n
  
  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      Big.n_case
        (fun _ -> (Big.zero,
        Big.one))
        (fun p ->
        Big.positive_case
          (fun p0 -> (Big.zero,
          Big.one))
          (fun p0 -> (Big.zero,
          Big.one))
          (fun _ -> (Big.one,
          Big.zero))
          p)
        b)
      a
  
  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.n_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun na ->
      Big.n_case
        (fun _ -> (Big.zero,
        a))
        (fun p ->
        pos_div_eucl na b)
        b)
      a
  
  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let div = fun a b -> if Big.eq b Big.zero then Big.zero else Big.div a b
  
  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let modulo = fun a b -> if Big.eq b Big.zero then Big.zero else Big.modulo a b
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    Big.n_case
      (fun _ ->
      b)
      (fun p ->
      Big.n_case
        (fun _ ->
        a)
        (fun q ->
        (Coq_Pos.gcd p q))
        b)
      a
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.n_case
      (fun _ -> (b, (Big.zero,
      Big.one)))
      (fun p ->
      Big.n_case
        (fun _ -> (a, (Big.one,
        Big.zero)))
        (fun q ->
        let (g, p0) = Coq_Pos.ggcd p q in let (aa, bb) = p0 in (g, (aa, bb)))
        b)
      a
  
  (** val sqrtrem : Big.big_int -> Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.n_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun p ->
      let (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> (s, r)
       | _ -> (s, Big.zero)))
      n
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.sqrt p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        (Coq_Pos.coq_lor p q))
        m)
      n
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_land n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q ->
        Coq_Pos.coq_land p q)
        m)
      n
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        Coq_Pos.ldiff p q)
        m)
      n
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lxor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        Coq_Pos.coq_lxor p q)
        m)
      n
  
  (** val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl_nat a n =
    nat_iter n double a
  
  (** val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr_nat a n =
    nat_iter n div2 a
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl a n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      (Coq_Pos.shiftl a0 n))
      a
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr a n =
    Big.n_case
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter p div2 a)
      n
  
  (** val testbit_nat : Big.big_int -> Big.big_int -> bool **)
  
  let testbit_nat a =
    Big.n_case
      (fun _ x ->
      false)
      (fun p ->
      Coq_Pos.testbit_nat p)
      a
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let testbit a n =
    Big.n_case
      (fun _ ->
      false)
      (fun p ->
      Coq_Pos.testbit p n)
      a
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat a =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Coq_Pos.to_nat p)
      a
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let of_nat n =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun n' ->
      (Coq_Pos.of_succ_nat n'))
      n
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    Big.n_case
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter p f x)
      n
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let eq_dec n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun x ->
      Big.n_case
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x p0)
        m)
      n
  
  (** val discr : Big.big_int -> Big.big_int option **)
  
  let discr n =
    Big.n_case
      (fun _ ->
      None)
      (fun p -> Some
      p)
      n
  
  (** val binary_rect :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
      Big.big_int -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n =
    let f2' = fun p -> f2 p in
    let fS2' = fun p -> fS2 p in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       let rec f p0 =
         Big.positive_case
           (fun p1 ->
           fS2' p1 (f p1))
           (fun p1 ->
           f2' p1 (f p1))
           (fun _ ->
           fS2 Big.zero f0)
           p0
       in f p)
       n)
  
  (** val binary_rec :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
      Big.big_int -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let peano_rect f0 f n =
    let f' = fun p -> f p in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       Coq_Pos.peano_rect (f Big.zero f0) f' p)
       n)
  
  (** val peano_rec :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : Big.big_int -> Big.big_int **)
  
  let sqrt_up a =
    match compare Big.zero a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Big.zero
  
  (** val log2_up : Big.big_int -> Big.big_int **)
  
  let log2_up a =
    match compare Big.one a with
    | Lt -> succ (log2 (pred a))
    | _ -> Big.zero
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> Big.big_int **)
  
  let b2n = function
  | true -> Big.one
  | false -> Big.zero
  
  (** val setbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let setbit a n =
    coq_lor a (shiftl Big.one n)
  
  (** val clearbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let clearbit a n =
    ldiff a (shiftl Big.one n)
  
  (** val ones : Big.big_int -> Big.big_int **)
  
  let ones n =
    pred (shiftl Big.one n)
  
  (** val lnot : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lnot a n =
    coq_lxor a (ones n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : Big.big_int -> Big.big_int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : Big.big_int -> Big.big_int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : Big.big_int -> Big.big_int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : Big.big_int -> Big.big_int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t = Big.big_int
  
  (** val zero : Big.big_int **)
  
  let zero =
    Big.zero
  
  (** val one : Big.big_int **)
  
  let one =
    Big.one
  
  (** val two : Big.big_int **)
  
  let two =
    (Big.double Big.one)
  
  (** val double : Big.big_int -> Big.big_int **)
  
  let double x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      (fun p -> Big.opp (Big.double
      p))
      x
  
  (** val succ_double : Big.big_int -> Big.big_int **)
  
  let succ_double x =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      (fun p -> Big.opp
      (Coq_Pos.pred_double p))
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let pred_double x =
    Big.z_case
      (fun _ -> Big.opp
      Big.one)
      (fun p ->
      (Coq_Pos.pred_double p))
      (fun p -> Big.opp (Big.doubleplusone
      p))
      x
  
  (** val pos_sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec pos_sub x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double (pos_sub p q))
        (fun q ->
        succ_double (pos_sub p q))
        (fun _ -> (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        pred_double (pos_sub p q))
        (fun q ->
        double (pos_sub p q))
        (fun _ ->
        (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.opp (Big.double
        q))
        (fun q -> Big.opp
        (Coq_Pos.pred_double q))
        (fun _ ->
        Big.zero)
        y)
      x
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let add = Big.add
  
  (** val opp : Big.big_int -> Big.big_int **)
  
  let opp = Big.opp
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = Big.pred
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = Big.sub
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let mul = Big.mult
  
  (** val pow_pos : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow_pos z n =
    Coq_Pos.iter n (mul z) Big.one
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      pow_pos x p)
      (fun p ->
      Big.zero)
      y
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let square x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.square p))
      (fun p ->
      (Coq_Pos.square p))
      x
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val sgn : Big.big_int -> Big.big_int **)
  
  let sgn z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.one)
      (fun p -> Big.opp
      Big.one)
      z
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val geb : Big.big_int -> Big.big_int -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : Big.big_int -> Big.big_int -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun q ->
        Coq_Pos.eqb p q)
        (fun p0 ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun q ->
        Coq_Pos.eqb p q)
        y)
      x
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val abs : Big.big_int -> Big.big_int **)
  
  let abs = Big.abs
  
  (** val abs_nat : Big.big_int -> Big.big_int **)
  
  let abs_nat z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      Coq_Pos.to_nat p)
      z
  
  (** val abs_N : Big.big_int -> Big.big_int **)
  
  let abs_N = Big.abs
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      Big.zero)
      z
  
  (** val to_N : Big.big_int -> Big.big_int **)
  
  let to_N z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      p)
      (fun p ->
      Big.zero)
      z
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let of_nat n =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun n0 ->
      (Coq_Pos.of_succ_nat n0))
      n
  
  (** val of_N : Big.big_int -> Big.big_int **)
  
  let of_N = fun p -> p
  
  (** val to_pos : Big.big_int -> Big.big_int **)
  
  let to_pos z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      p)
      (fun p ->
      Big.one)
      z
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    Big.z_case
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter p f x)
      (fun p ->
      x)
      n
  
  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun _ ->
      if leb (Big.double Big.one) b
      then (Big.zero, Big.one)
      else (Big.one, Big.zero))
      a
  
  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun p -> ((opp (add q Big.one)),
           (add b r)))
           (fun p -> ((opp (add q Big.one)),
           (add b r)))
           r))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        let (q, r) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun p0 -> ((opp (add q Big.one)),
           (sub b r)))
           (fun p0 -> ((opp (add q Big.one)),
           (sub b r)))
           r))
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a
  
  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let div a b =
    let (q, x) = div_eucl a b in q
  
  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let modulo a b =
    let (x, r) = div_eucl a b in r
  
  (** val quotrem :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let quotrem a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a
  
  (** val quot : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : Big.big_int -> bool **)
  
  let even z =
    Big.z_case
      (fun _ ->
      true)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      z
  
  (** val odd : Big.big_int -> bool **)
  
  let odd z =
    Big.z_case
      (fun _ ->
      false)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      z
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p -> Big.opp
      (Coq_Pos.div2_up p))
      z
  
  (** val quot2 : Big.big_int -> Big.big_int **)
  
  let quot2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 -> Big.opp
        (Coq_Pos.div2 p))
        (fun p0 -> Big.opp
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      z
  
  (** val log2 : Big.big_int -> Big.big_int **)
  
  let log2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        (Coq_Pos.size p))
        (fun p ->
        (Coq_Pos.size p))
        (fun _ ->
        Big.zero)
        p0)
      (fun p ->
      Big.zero)
      z
  
  (** val sqrtrem : Big.big_int -> Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun p ->
      let (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> (s, r)
       | _ -> (s, Big.zero)))
      (fun p -> (Big.zero,
      Big.zero))
      n
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt n =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.sqrt p))
      (fun p ->
      Big.zero)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    Big.z_case
      (fun _ ->
      abs b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      a
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.z_case
      (fun _ -> ((abs b), (Big.zero,
      (sgn b))))
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, (Big.opp bb))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), (Big.opp bb))))
        b)
      a
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let testbit a n =
    Big.z_case
      (fun _ ->
      odd a)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun a0 ->
        Coq_Pos.testbit a0 p)
        (fun a0 ->
        negb (N.testbit (Coq_Pos.pred_N a0) p))
        a)
      (fun p ->
      false)
      n
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl a n =
    Big.z_case
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter p (mul (Big.double Big.one)) a)
      (fun p ->
      Coq_Pos.iter p div2 a)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr a n =
    shiftl a (opp n)
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_land a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 ->
        of_N (N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let ldiff a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.ldiff a0 b0))
        (fun b0 ->
        of_N (N.coq_land a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
        b)
      a
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lxor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.coq_lxor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor a0 (Coq_Pos.pred_N b0))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
        b)
      a
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        (fun p0 ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        y)
      x
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  (** val sqrt_up : Big.big_int -> Big.big_int **)
  
  let sqrt_up a =
    match compare Big.zero a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Big.zero
  
  (** val log2_up : Big.big_int -> Big.big_int **)
  
  let log2_up a =
    match compare Big.one a with
    | Lt -> succ (log2 (pred a))
    | _ -> Big.zero
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let div =
        quot
      
      (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> Big.big_int **)
  
  let b2z = function
  | true -> Big.one
  | false -> Big.zero
  
  (** val setbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let setbit a n =
    coq_lor a (shiftl Big.one n)
  
  (** val clearbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let clearbit a n =
    ldiff a (shiftl Big.one n)
  
  (** val lnot : Big.big_int -> Big.big_int **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : Big.big_int -> Big.big_int **)
  
  let ones n =
    pred (shiftl Big.one n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : Big.big_int -> Big.big_int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : Big.big_int -> Big.big_int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : Big.big_int -> Big.big_int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : Big.big_int -> Big.big_int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val z_gt_dec : Big.big_int -> Big.big_int -> bool **)

let z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val z_ge_dec : Big.big_int -> Big.big_int -> bool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val z_gt_le_dec : Big.big_int -> Big.big_int -> bool **)

let z_gt_le_dec x y =
  z_gt_dec x y

(** val z_ge_lt_dec : Big.big_int -> Big.big_int -> bool **)

let z_ge_lt_dec x y =
  z_ge_dec x y

type 'a orderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_OrderedType *)

(** val _cmp : 'a1 orderedType -> 'a1 -> 'a1 -> comparison **)

let _cmp orderedType0 =
  orderedType0

(** val compare0 : 'a1 orderedType -> 'a1 -> 'a1 -> comparison **)

let compare0 h =
  _cmp h

(** val is_compare : 'a1 orderedType -> 'a1 -> 'a1 -> comparison -> bool **)

let is_compare h x y c =
  match compare0 h x y with
  | Eq ->
    (match c with
     | Eq -> true
     | _ -> false)
  | Lt ->
    (match c with
     | Lt -> true
     | _ -> false)
  | Gt ->
    (match c with
     | Gt -> true
     | _ -> false)

type 'a specificOrderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_SpecificOrderedType *)

(** val sOT_cmp : 'a1 specificOrderedType -> 'a1 -> 'a1 -> comparison **)

let sOT_cmp specificOrderedType0 =
  specificOrderedType0

(** val sOT_as_OT : 'a1 specificOrderedType -> 'a1 orderedType **)

let sOT_as_OT h =
  sOT_cmp h

(** val inst_eq_dec_list : 'a1 eqDec -> 'a1 list eqDec **)

let inst_eq_dec_list h =
  list_eq_dec (equiv_dec h)

(** val get_dec : 'a1 list -> Big.big_int -> 'a1 option **)

let get_dec l n =
  match nth_error l n with
  | Some x -> Some x
  | None -> None

(** val nat_compare : Big.big_int -> Big.big_int -> comparison **)

let rec nat_compare n m =
  Big.nat_case
    (fun _ ->
    Big.nat_case
      (fun _ ->
      Eq)
      (fun n0 ->
      Lt)
      m)
    (fun n0 ->
    Big.nat_case
      (fun _ ->
      Gt)
      (fun m0 ->
      nat_compare n0 m0)
      m)
    n

(** val nat_OrderedType : Big.big_int specificOrderedType **)

let nat_OrderedType =
  nat_compare

(** val list_compare :
    'a1 orderedType -> 'a1 list -> 'a1 list -> comparison **)

let rec list_compare h x y =
  match x with
  | [] ->
    (match y with
     | [] -> Eq
     | a :: l -> Lt)
  | a :: l ->
    (match y with
     | [] -> Gt
     | a' :: l' ->
       (match compare0 h a a' with
        | Eq -> list_compare h l l'
        | x0 -> x0))

(** val list_OrderedType : 'a1 orderedType -> 'a1 list orderedType **)

let list_OrderedType h =
  list_compare h

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

(** val empty : 'a1 orderedType -> 'a1 fSet -> 'a1 set **)

let empty _ x = x.empty

(** val mem : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> bool **)

let mem _ x = x.mem

(** val add0 : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> 'a1 set **)

let add0 _ x = x.add0

(** val singleton : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set **)

let singleton _ x = x.singleton

(** val union :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set **)

let union _ x = x.union

(** val diff :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set **)

let diff _ x = x.diff

(** val subset :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool **)

let subset _ x = x.subset

(** val fold :
    'a1 orderedType -> 'a1 fSet -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 ->
    'a2 **)

let fold h fSet0 x x0 x1 =
  let { empty = empty1; is_empty = is_empty1; mem = mem1; add0 = add2;
    singleton = singleton1; remove = remove1; union = union1; inter = inter1;
    diff = diff1; equal = equal1; subset = subset1; fold = fold1; for_all =
    for_all1; exists_ = exists_1; filter = filter1; partition = partition1;
    cardinal = cardinal1; elements = elements1; choose = choose1; min_elt =
    min_elt1; max_elt = max_elt1; fSet_OrderedType = fSet_OrderedType0 } =
    fSet0
  in
  Obj.magic fold1 __ x x0 x1

(** val for_all :
    'a1 orderedType -> 'a1 fSet -> ('a1 -> bool) -> 'a1 set -> bool **)

let for_all _ x = x.for_all

(** val fSet_OrderedType :
    'a1 orderedType -> 'a1 fSet -> 'a1 set specificOrderedType **)

let fSet_OrderedType _ x = x.fSet_OrderedType

module SetList = 
 struct 
  type 'a set = 'a list
  
  (** val empty : 'a1 orderedType -> 'a1 set **)
  
  let empty comparedec =
    []
  
  (** val is_empty : 'a1 orderedType -> 'a1 set -> bool **)
  
  let is_empty comparedec = function
  | [] -> true
  | x :: x0 -> false
  
  (** val mem : 'a1 orderedType -> 'a1 -> 'a1 set -> bool **)
  
  let rec mem comparedec x = function
  | [] -> false
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> true
     | Lt -> false
     | Gt -> mem comparedec x l)
  
  (** val add : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set **)
  
  let rec add comparedec x s = match s with
  | [] -> x :: []
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> s
     | Lt -> x :: s
     | Gt -> y :: (add comparedec x l))
  
  (** val singleton : 'a1 orderedType -> 'a1 -> 'a1 set **)
  
  let singleton comparedec x =
    x :: []
  
  (** val remove : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set **)
  
  let rec remove comparedec x s = match s with
  | [] -> []
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> l
     | Lt -> s
     | Gt -> y :: (remove comparedec x l))
  
  (** val union : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec union comparedec s = match s with
  | [] -> (fun s' -> s')
  | x :: l ->
    let rec union_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> x :: (union comparedec l l')
       | Lt -> x :: (union comparedec l s')
       | Gt -> x' :: (union_aux l'))
    in union_aux
  
  (** val inter : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec inter comparedec = function
  | [] -> (fun x -> [])
  | x :: l ->
    let rec inter_aux s' = match s' with
    | [] -> []
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> x :: (inter comparedec l l')
       | Lt -> inter comparedec l s'
       | Gt -> inter_aux l')
    in inter_aux
  
  (** val diff : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec diff comparedec s = match s with
  | [] -> (fun x -> [])
  | x :: l ->
    let rec diff_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> diff comparedec l l'
       | Lt -> x :: (diff comparedec l s')
       | Gt -> diff_aux l')
    in diff_aux
  
  (** val equal : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool **)
  
  let rec equal comparedec s s' =
    match s with
    | [] ->
      (match s' with
       | [] -> true
       | e :: l -> false)
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' ->
         (match compare0 comparedec x x' with
          | Eq -> equal comparedec l l'
          | _ -> false))
  
  (** val subset : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool **)
  
  let rec subset comparedec s s' =
    match s with
    | [] -> true
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' ->
         (match compare0 comparedec x x' with
          | Eq -> subset comparedec l l'
          | Lt -> false
          | Gt -> subset comparedec s l'))
  
  (** val fold :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2 **)
  
  let rec fold comparedec f s i =
    match s with
    | [] -> i
    | x :: l -> fold comparedec f l (f x i)
  
  (** val map_monotonic :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2
      set **)
  
  let map_monotonic comparedec h f s =
    map f s
  
  (** val filter : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set **)
  
  let rec filter comparedec f = function
  | [] -> []
  | x :: l ->
    if f x then x :: (filter comparedec f l) else filter comparedec f l
  
  (** val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool **)
  
  let rec for_all comparedec f = function
  | [] -> true
  | x :: l -> if f x then for_all comparedec f l else false
  
  (** val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool **)
  
  let rec exists_ comparedec f = function
  | [] -> false
  | x :: l -> if f x then true else exists_ comparedec f l
  
  (** val partition :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set * 'a1 set **)
  
  let rec partition comparedec f = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition comparedec f l in
    if f x then ((x :: s1), s2) else (s1, (x :: s2))
  
  (** val cardinal : 'a1 orderedType -> 'a1 set -> Big.big_int **)
  
  let cardinal comparedec s =
    length s
  
  (** val elements : 'a1 orderedType -> 'a1 set -> 'a1 list **)
  
  let elements comparedec x =
    x
  
  (** val min_elt : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let min_elt comparedec = function
  | [] -> None
  | x :: l -> Some x
  
  (** val max_elt : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let rec max_elt comparedec = function
  | [] -> None
  | x :: l ->
    (match l with
     | [] -> Some x
     | e :: l0 -> max_elt comparedec l)
  
  (** val choose : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let choose comparedec =
    min_elt comparedec
  
  (** val map :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2
      set **)
  
  let map h h0 f s =
    fold h (fun a sb -> add h0 (f a) sb) s (empty h0)
  
  (** val set_compare :
      'a1 orderedType -> 'a1 set -> 'a1 set -> comparison **)
  
  let set_compare h =
    list_compare h
  
  (** val set_OrderedType : 'a1 orderedType -> 'a1 set orderedType **)
  
  let set_OrderedType h =
    list_OrderedType h
 end

module SetAVL = 
 struct 
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * Big.big_int
  
  (** val tree_rect :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      Big.big_int -> 'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rect h f f0 = function
  | Leaf -> f
  | Node (t1, y, t2, z) ->
    f0 t1 (tree_rect h f f0 t1) y t2 (tree_rect h f f0 t2) z
  
  (** val tree_rec :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      Big.big_int -> 'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rec h f f0 = function
  | Leaf -> f
  | Node (t1, y, t2, z) ->
    f0 t1 (tree_rec h f f0 t1) y t2 (tree_rec h f f0 t2) z
  
  (** val height : 'a1 orderedType -> 'a1 tree -> Big.big_int **)
  
  let height h = function
  | Leaf -> Big.zero
  | Node (t0, e, t1, h0) -> h0
  
  (** val cardinal : 'a1 orderedType -> 'a1 tree -> Big.big_int **)
  
  let rec cardinal h = function
  | Leaf -> Big.zero
  | Node (l, e, r, z) -> Big.succ (plus (cardinal h l) (cardinal h r))
  
  (** val empty : 'a1 orderedType -> 'a1 tree **)
  
  let empty h =
    Leaf
  
  (** val is_empty : 'a1 orderedType -> 'a1 tree -> bool **)
  
  let is_empty h = function
  | Leaf -> true
  | Node (t0, y, t1, z) -> false
  
  (** val mem : 'a1 orderedType -> 'a1 -> 'a1 tree -> bool **)
  
  let rec mem h x = function
  | Leaf -> false
  | Node (l, y, r, z) ->
    (match compare0 h x y with
     | Eq -> true
     | Lt -> mem h x l
     | Gt -> mem h x r)
  
  (** val singleton : 'a1 orderedType -> 'a1 -> 'a1 tree **)
  
  let singleton h x =
    Node (Leaf, x, Leaf, Big.one)
  
  (** val create :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let create h l x r =
    Node (l, x, r, (Z.add (Z.max (height h l) (height h r)) Big.one))
  
  (** val assert_false :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let assert_false h =
    create h
  
  (** val bal :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let bal h l x r =
    let hl = height h l in
    let hr = height h r in
    if z_gt_le_dec hl (Z.add hr (Big.double Big.one))
    then (match l with
          | Leaf -> assert_false h l x r
          | Node (ll, lx, lr, z) ->
            if z_ge_lt_dec (height h ll) (height h lr)
            then create h ll lx (create h lr x r)
            else (match lr with
                  | Leaf -> assert_false h l x r
                  | Node (lrl, lrx, lrr, z0) ->
                    create h (create h ll lx lrl) lrx (create h lrr x r)))
    else if z_gt_le_dec hr (Z.add hl (Big.double Big.one))
         then (match r with
               | Leaf -> assert_false h l x r
               | Node (rl, rx, rr, z) ->
                 if z_ge_lt_dec (height h rr) (height h rl)
                 then create h (create h l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false h l x r
                       | Node (rll, rlx, rlr, z0) ->
                         create h (create h l x rll) rlx (create h rlr rx rr)))
         else create h l x r
  
  (** val add : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec add h x = function
  | Leaf -> Node (Leaf, x, Leaf, Big.one)
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> Node (l, y, r, h0)
     | Lt -> bal h (add h x l) y r
     | Gt -> bal h l y (add h x r))
  
  (** val join :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec join h l = match l with
  | Leaf -> add h
  | Node (ll, lx, lr, lh) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add h x l
      | Node (rl, rx, rr, rh) ->
        if z_gt_le_dec lh (Z.add rh (Big.double Big.one))
        then bal h ll lx (join h lr x r)
        else if z_gt_le_dec rh (Z.add lh (Big.double Big.one))
             then bal h (join_aux rl) rx rr
             else create h l x r
      in join_aux)
  
  (** val remove_min :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree * 'a1 **)
  
  let rec remove_min h l x r =
    match l with
    | Leaf -> (r, x)
    | Node (ll, lx, lr, lh) ->
      let (l', m) = remove_min h ll lx lr in ((bal h l' x r), m)
  
  (** val merge : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let merge h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, y, t1, z) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, h2) ->
         let (s2', m) = remove_min h l2 x2 r2 in bal h s1 m s2')
  
  (** val remove : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec remove h x = function
  | Leaf -> Leaf
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> merge h l r
     | Lt -> bal h (remove h x l) y r
     | Gt -> bal h l y (remove h x r))
  
  (** val min_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let rec min_elt h = function
  | Leaf -> None
  | Node (l, y, t0, z) ->
    (match l with
     | Leaf -> Some y
     | Node (t1, y0, t2, z0) -> min_elt h l)
  
  (** val max_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let rec max_elt h = function
  | Leaf -> None
  | Node (t0, y, r, z) ->
    (match r with
     | Leaf -> Some y
     | Node (t1, y0, t2, z0) -> max_elt h r)
  
  (** val choose : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let choose h =
    min_elt h
  
  (** val concat : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let concat h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, y, t1, z) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, z0) ->
         let (s2', m) = remove_min h l2 x2 r2 in join h s1 m s2')
  
  type 'elt triple = { t_left : 'elt tree; t_in : bool; t_right : 'elt tree }
  
  (** val triple_rect :
      'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple
      -> 'a2 **)
  
  let triple_rect h f t0 =
    let { t_left = x; t_in = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val triple_rec :
      'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple
      -> 'a2 **)
  
  let triple_rec h f t0 =
    let { t_left = x; t_in = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val t_left : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)
  
  let t_left _ x = x.t_left
  
  (** val t_in : 'a1 orderedType -> 'a1 triple -> bool **)
  
  let t_in _ x = x.t_in
  
  (** val t_right : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)
  
  let t_right _ x = x.t_right
  
  (** val split : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 triple **)
  
  let rec split h x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split h x l in
       { t_left = ll; t_in = b; t_right = (join h rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split h x r in
       { t_left = (join h l y rl); t_in = b; t_right = rr })
  
  (** val inter : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec inter h s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (t0, y, t1, z) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then join h (inter h l1 l2') x1 (inter h r1 r2')
         else concat h (inter h l1 l2') (inter h r1 r2'))
  
  (** val diff : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec diff h s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, y, t1, z) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then concat h (diff h l1 l2') (diff h r1 r2')
         else join h (diff h l1 l2') x1 (diff h r1 r2'))
  
  (** val union : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec union h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, y, t1, z) ->
         let { t_left = l2'; t_in = x; t_right = r2' } = split h x1 s2 in
         join h (union h l1 l2') x1 (union h r1 r2'))
  
  (** val elements_aux :
      'a1 orderedType -> 'a1 list -> 'a1 tree -> 'a1 list **)
  
  let rec elements_aux h acc = function
  | Leaf -> acc
  | Node (l, x, r, z) -> elements_aux h (x :: (elements_aux h acc r)) l
  
  (** val elements : 'a1 orderedType -> 'a1 tree -> 'a1 list **)
  
  let elements h =
    elements_aux h []
  
  (** val filter_acc :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec filter_acc h f acc = function
  | Leaf -> acc
  | Node (l, x, r, h0) ->
    filter_acc h f (filter_acc h f (if f x then add h x acc else acc) l) r
  
  (** val filter :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree **)
  
  let filter h f =
    filter_acc h f Leaf
  
  (** val partition_acc :
      'a1 orderedType -> ('a1 -> bool) -> ('a1 tree * 'a1 tree) -> 'a1 tree
      -> 'a1 tree * 'a1 tree **)
  
  let rec partition_acc h f acc = function
  | Leaf -> acc
  | Node (l, x, r, z) ->
    let (acct, accf) = acc in
    partition_acc h f
      (partition_acc h f
        (if f x then ((add h x acct), accf) else (acct, (add h x accf))) l) r
  
  (** val partition :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree * 'a1 tree **)
  
  let partition h f =
    partition_acc h f (Leaf, Leaf)
  
  (** val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool **)
  
  let rec for_all h f = function
  | Leaf -> true
  | Node (l, x, r, z) ->
    if if f x then for_all h f l else false then for_all h f r else false
  
  (** val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool **)
  
  let rec exists_ h f = function
  | Leaf -> false
  | Node (l, x, r, z) ->
    if if f x then true else exists_ h f l then true else exists_ h f r
  
  (** val map_monotonic :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2
      tree **)
  
  let rec map_monotonic h hB f = function
  | Leaf -> Leaf
  | Node (l, x, r, h0) ->
    Node ((map_monotonic h hB f l), (f x), (map_monotonic h hB f r), h0)
  
  (** val fold :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let rec fold h f s x =
    match s with
    | Leaf -> x
    | Node (l, x0, r, z) -> fold h f r (f x0 (fold h f l x))
  
  (** val subsetl :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)
  
  let rec subsetl h subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl h subset_l1 x1 l2
     | Gt -> if mem h x1 r2 then subset_l1 s2 else false)
  
  (** val subsetr :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)
  
  let rec subsetr h subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem h x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr h subset_r1 x1 r2)
  
  (** val subset : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool **)
  
  let rec subset h s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> false
       | Node (l2, x2, r2, h2) ->
         (match compare0 h x1 x2 with
          | Eq -> if subset h l1 l2 then subset h r1 r2 else false
          | Lt ->
            if subsetl h (subset h l1) x1 l2 then subset h r1 s2 else false
          | Gt ->
            if subsetr h (subset h r1) x1 r2 then subset h l1 s2 else false))
  
  type 'elt enumeration =
  | End
  | More of 'elt * 'elt tree * 'elt enumeration
  
  (** val enumeration_rect :
      'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
      'a2) -> 'a1 enumeration -> 'a2 **)
  
  let rec enumeration_rect h f f0 = function
  | End -> f
  | More (e0, t0, e1) -> f0 e0 t0 e1 (enumeration_rect h f f0 e1)
  
  (** val enumeration_rec :
      'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
      'a2) -> 'a1 enumeration -> 'a2 **)
  
  let rec enumeration_rec h f f0 = function
  | End -> f
  | More (e0, t0, e1) -> f0 e0 t0 e1 (enumeration_rec h f f0 e1)
  
  (** val cons :
      'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)
  
  let rec cons h s e =
    match s with
    | Leaf -> e
    | Node (l, x, r, h0) -> cons h l (More (x, r, e))
  
  (** val compare_more :
      'a1 orderedType -> 'a1 -> ('a1 enumeration -> comparison) -> 'a1
      enumeration -> comparison **)
  
  let compare_more h x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match compare0 h x1 x2 with
     | Eq -> cont (cons h r2 e3)
     | x -> x)
  
  (** val compare_cont :
      'a1 orderedType -> 'a1 tree -> ('a1 enumeration -> comparison) -> 'a1
      enumeration -> comparison **)
  
  let rec compare_cont h s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (l1, x1, r1, z) ->
      compare_cont h l1 (compare_more h x1 (compare_cont h r1 cont)) e2
  
  (** val compare_end : 'a1 orderedType -> 'a1 enumeration -> comparison **)
  
  let compare_end h = function
  | End -> Eq
  | More (e, t0, e0) -> Lt
  
  (** val compare : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> comparison **)
  
  let compare h s1 s2 =
    compare_cont h s1 (compare_end h) (cons h s2 End)
  
  (** val equal : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool **)
  
  let equal h s1 s2 =
    match compare h s1 s2 with
    | Eq -> true
    | _ -> false
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt tree
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int * 
     bool * 'elt coq_R_mem
  
  (** val coq_R_mem_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool ->
      'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rect h x f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_mem_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_mem_rect h x f f0 f1 f2 l res r1)
  | R_mem_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_mem_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_mem_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> bool ->
      'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rec h x f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_mem_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_mem_rec h x f f0 f1 f2 l res r1)
  | R_mem_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_mem_rec h x f f0 f1 f2 r0 res r1)
  
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
  
  (** val coq_R_bal_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int
      -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
      tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
      -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1
      coq_R_bal -> 'a2 **)
  
  let coq_R_bal_rect h f f0 f1 f2 f3 f4 f5 f6 f7 l x r t0 = function
  | R_bal_0 (x0, x1, x2) -> f x0 x1 x2 __ __ __
  | R_bal_1 (x0, x1, x2, x3, x4, x5, x6) ->
    f0 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __
  | R_bal_2 (x0, x1, x2, x3, x4, x5, x6) ->
    f1 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f2 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_4 (x0, x1, x2) -> f3 x0 x1 x2 __ __ __ __ __
  | R_bal_5 (x0, x1, x2, x3, x4, x5, x6) ->
    f4 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __
  | R_bal_6 (x0, x1, x2, x3, x4, x5, x6) ->
    f5 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f6 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_8 (x0, x1, x2) -> f7 x0 x1 x2 __ __ __ __
  
  (** val coq_R_bal_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int
      -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1
      tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __
      -> __ -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1
      coq_R_bal -> 'a2 **)
  
  let coq_R_bal_rec h f f0 f1 f2 f3 f4 f5 f6 f7 l x r t0 = function
  | R_bal_0 (x0, x1, x2) -> f x0 x1 x2 __ __ __
  | R_bal_1 (x0, x1, x2, x3, x4, x5, x6) ->
    f0 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __
  | R_bal_2 (x0, x1, x2, x3, x4, x5, x6) ->
    f1 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f2 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_4 (x0, x1, x2) -> f3 x0 x1 x2 __ __ __ __ __
  | R_bal_5 (x0, x1, x2, x3, x4, x5, x6) ->
    f4 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __
  | R_bal_6 (x0, x1, x2, x3, x4, x5, x6) ->
    f5 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f6 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_8 (x0, x1, x2) -> f7 x0 x1 x2 __ __ __ __
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_add
  
  (** val coq_R_add_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree
      -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rect h x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, l, y, r0, h0) -> f0 s0 l y r0 h0 __ __
  | R_add_2 (s0, l, y, r0, h0, res, r1) ->
    f1 s0 l y r0 h0 __ __ res r1 (coq_R_add_rect h x f f0 f1 f2 l res r1)
  | R_add_3 (s0, l, y, r0, h0, res, r1) ->
    f2 s0 l y r0 h0 __ __ res r1 (coq_R_add_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_add_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree
      -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rec h x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, l, y, r0, h0) -> f0 s0 l y r0 h0 __ __
  | R_add_2 (s0, l, y, r0, h0, res, r1) ->
    f1 s0 l y r0 h0 __ __ res r1 (coq_R_add_rec h x f f0 f1 f2 l res r1)
  | R_add_3 (s0, l, y, r0, h0, res, r1) ->
    f2 s0 l y r0 h0 __ __ res r1 (coq_R_add_rec h x f f0 f1 f2 r0 res r1)
  
  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * Big.big_int * ('elt tree * 'elt) * 'elt coq_R_remove_min
     * 'elt tree * 'elt
  
  (** val coq_R_remove_min_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int
      -> __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
      'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) ->
      'a1 coq_R_remove_min -> 'a2 **)
  
  let rec coq_R_remove_min_rect h f f0 l x r p = function
  | R_remove_min_0 (l0, x0, r1) -> f l0 x0 r1 __
  | R_remove_min_1 (l0, x0, r1, ll, lx, lr, _x, res, r2, l', m) ->
    f0 l0 x0 r1 ll lx lr _x __ res r2
      (coq_R_remove_min_rect h f f0 ll lx lr res r2) l' m __
  
  (** val coq_R_remove_min_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int
      -> __ -> ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
      'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) ->
      'a1 coq_R_remove_min -> 'a2 **)
  
  let rec coq_R_remove_min_rec h f f0 l x r p = function
  | R_remove_min_0 (l0, x0, r1) -> f l0 x0 r1 __
  | R_remove_min_1 (l0, x0, r1, ll, lx, lr, _x, res, r2, l', m) ->
    f0 l0 x0 r1 ll lx lr _x __ res r2
      (coq_R_remove_min_rec h f f0 ll lx lr res r2) l' m __
  
  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  (** val coq_R_merge_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_merge -> 'a2 **)
  
  let coq_R_merge_rect h f f0 f1 s1 s2 t0 = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  (** val coq_R_merge_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_merge -> 'a2 **)
  
  let coq_R_merge_rec h f f0 f1 s1 s2 t0 = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt coq_R_remove
  
  (** val coq_R_remove_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree
      -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rect h x f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_remove_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_remove_rect h x f f0 f1 f2 l res r1)
  | R_remove_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_remove_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_remove_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree
      -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 ->
      'a1 tree -> Big.big_int -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rec h x f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_remove_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_remove_rec h x f f0 f1 f2 l res r1)
  | R_remove_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_remove_rec h x f f0 f1 f2 r0 res r1)
  
  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_min_elt
  
  (** val coq_R_min_elt_rect :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 **)
  
  let rec coq_R_min_elt_rect h f f0 f1 s o = function
  | R_min_elt_0 s0 -> f s0 __
  | R_min_elt_1 (s0, l, y, _x, _x0) -> f0 s0 l y _x _x0 __ __
  | R_min_elt_2 (s0, l, y, _x, _x0, _x1, _x2, _x3, _x4, res, r0) ->
    f1 s0 l y _x _x0 __ _x1 _x2 _x3 _x4 __ res r0
      (coq_R_min_elt_rect h f f0 f1 l res r0)
  
  (** val coq_R_min_elt_rec :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_min_elt -> 'a2 **)
  
  let rec coq_R_min_elt_rec h f f0 f1 s o = function
  | R_min_elt_0 s0 -> f s0 __
  | R_min_elt_1 (s0, l, y, _x, _x0) -> f0 s0 l y _x _x0 __ __
  | R_min_elt_2 (s0, l, y, _x, _x0, _x1, _x2, _x3, _x4, res, r0) ->
    f1 s0 l y _x _x0 __ _x1 _x2 _x3 _x4 __ res r0
      (coq_R_min_elt_rec h f f0 f1 l res r0)
  
  type 'elt coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt option
     * 'elt coq_R_max_elt
  
  (** val coq_R_max_elt_rect :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 **)
  
  let rec coq_R_max_elt_rect h f f0 f1 s o = function
  | R_max_elt_0 s0 -> f s0 __
  | R_max_elt_1 (s0, _x, y, r0, _x0) -> f0 s0 _x y r0 _x0 __ __
  | R_max_elt_2 (s0, _x, y, r0, _x0, _x1, _x2, _x3, _x4, res, r1) ->
    f1 s0 _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ res r1
      (coq_R_max_elt_rect h f f0 f1 r0 res r1)
  
  (** val coq_R_max_elt_rec :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1
      tree -> Big.big_int -> __ -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_max_elt -> 'a2 **)
  
  let rec coq_R_max_elt_rec h f f0 f1 s o = function
  | R_max_elt_0 s0 -> f s0 __
  | R_max_elt_1 (s0, _x, y, r0, _x0) -> f0 s0 _x y r0 _x0 __ __
  | R_max_elt_2 (s0, _x, y, r0, _x0, _x1, _x2, _x3, _x4, res, r1) ->
    f1 s0 _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ res r1
      (coq_R_max_elt_rec h f f0 f1 r0 res r1)
  
  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * 'elt
  
  (** val coq_R_concat_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_concat -> 'a2 **)
  
  let coq_R_concat_rect h f f0 f1 s1 s2 t0 = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  (** val coq_R_concat_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_concat -> 'a2 **)
  
  let coq_R_concat_rec h f f0 f1 s1 s2 t0 = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * Big.big_int
     * 'elt triple * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  
  (** val coq_R_split_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __
      -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree
      -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
  
  let rec coq_R_split_rect h x f f0 f1 f2 s t0 = function
  | R_split_0 s0 -> f s0 __
  | R_split_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_split_2 (s0, l, y, r0, _x, res, r1, ll, b, rl) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_split_rect h x f f0 f1 f2 l res r1)
      ll b rl __
  | R_split_3 (s0, l, y, r0, _x, res, r1, rl, b, rr) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_split_rect h x f f0 f1 f2 r0 res r1)
      rl b rr __
  
  (** val coq_R_split_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __
      -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree
      -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
  
  let rec coq_R_split_rec h x f f0 f1 f2 s t0 = function
  | R_split_0 s0 -> f s0 __
  | R_split_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_split_2 (s0, l, y, r0, _x, res, r1, ll, b, rl) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_split_rec h x f f0 f1 f2 l res r1) ll
      b rl __
  | R_split_3 (s0, l, y, r0, _x, res, r1, rl, b, rr) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_split_rec h x f f0 f1 f2 r0 res r1)
      rl b rr __
  
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
  
  (** val coq_R_inter_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
      __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
      bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 ->
      'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_inter -> 'a2 **)
  
  let rec coq_R_inter_rect h f f0 f1 f2 s1 s2 t0 = function
  | R_inter_0 (s3, s4) -> f s3 s4 __
  | R_inter_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_inter_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' res r2)
  | R_inter_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' res r2)
  
  (** val coq_R_inter_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int ->
      __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree ->
      bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 ->
      'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_inter -> 'a2 **)
  
  let rec coq_R_inter_rec h f f0 f1 f2 s1 s2 t0 = function
  | R_inter_0 (s3, s4) -> f s3 s4 __
  | R_inter_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_inter_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' res r2)
  | R_inter_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' res r2)
  
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
  
  (** val coq_R_diff_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
      'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool ->
      'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree
      -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_diff -> 'a2 **)
  
  let rec coq_R_diff_rect h f f0 f1 f2 s1 s2 t0 = function
  | R_diff_0 (s3, s4) -> f s3 s4 __
  | R_diff_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_diff_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' res r2)
  | R_diff_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' res r2)
  
  (** val coq_R_diff_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ ->
      'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> 'a1 tree -> bool ->
      'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree
      -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_diff -> 'a2 **)
  
  let rec coq_R_diff_rec h f f0 f1 f2 s1 s2 t0 = function
  | R_diff_0 (s3, s4) -> f s3 s4 __
  | R_diff_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_diff_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' res r2)
  | R_diff_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' res r2)
  
  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree
     * Big.big_int * 'elt tree * 'elt * 'elt tree * Big.big_int * 'elt tree
     * bool * 'elt tree * 'elt tree * 'elt coq_R_union * 'elt tree
     * 'elt coq_R_union
  
  (** val coq_R_union_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union ->
      'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2 **)
  
  let rec coq_R_union_rect h f f0 f1 s1 s2 t0 = function
  | R_union_0 (s3, s4) -> f s3 s4 __
  | R_union_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_union_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ res0 r0
      (coq_R_union_rect h f f0 f1 l1 l2' res0 r0) res r2
      (coq_R_union_rect h f f0 f1 r1 r2' res r2)
  
  (** val coq_R_union_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree ->
      Big.big_int -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> Big.big_int -> __
      -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a1 tree -> 'a1 coq_R_union ->
      'a2 -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_union -> 'a2 **)
  
  let rec coq_R_union_rec h f f0 f1 s1 s2 t0 = function
  | R_union_0 (s3, s4) -> f s3 s4 __
  | R_union_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_union_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ res0 r0
      (coq_R_union_rec h f f0 f1 l1 l2' res0 r0) res r2
      (coq_R_union_rec h f f0 f1 r1 r2' res r2)
  
  (** val fold' :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let fold' helt f s =
    SetList.fold helt f (elements helt s)
  
  (** val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list **)
  
  let rec flatten_e helt = function
  | End -> []
  | More (x, t0, r) -> x :: (app (elements helt t0) (flatten_e helt r))
 end

module S = SetAVL

type 'elt set0 =
  'elt S.tree
  (* singleton inductive, whose constructor was Bst *)

(** val this : 'a1 orderedType -> 'a1 set0 -> 'a1 S.tree **)

let this helt s =
  s

(** val mem0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> bool **)

let mem0 helt x s =
  S.mem helt x (this helt s)

(** val empty0 : 'a1 orderedType -> 'a1 set0 **)

let empty0 helt =
  S.empty helt

(** val is_empty0 : 'a1 orderedType -> 'a1 set0 -> bool **)

let is_empty0 helt s =
  S.is_empty helt (this helt s)

(** val singleton0 : 'a1 orderedType -> 'a1 -> 'a1 set0 **)

let singleton0 helt x =
  S.singleton helt x

(** val add1 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0 **)

let add1 helt x s =
  S.add helt x (this helt s)

(** val remove0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0 **)

let remove0 helt x s =
  S.remove helt x (this helt s)

(** val inter0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let inter0 helt s s' =
  S.inter helt (this helt s) (this helt s')

(** val union0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let union0 helt s s' =
  S.union helt (this helt s) (this helt s')

(** val diff0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let diff0 helt s s' =
  S.diff helt (this helt s) (this helt s')

(** val elements0 : 'a1 orderedType -> 'a1 set0 -> 'a1 list **)

let elements0 helt s =
  S.elements helt (this helt s)

(** val min_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let min_elt0 helt s =
  S.min_elt helt (this helt s)

(** val max_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let max_elt0 helt s =
  S.max_elt helt (this helt s)

(** val choose0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let choose0 helt s =
  S.choose helt (this helt s)

(** val fold0 :
    'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set0 -> 'a2 -> 'a2 **)

let fold0 helt f s x =
  S.fold helt f (this helt s) x

(** val cardinal0 : 'a1 orderedType -> 'a1 set0 -> Big.big_int **)

let cardinal0 helt s =
  S.cardinal helt (this helt s)

(** val filter0 :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 **)

let filter0 helt f s =
  S.filter helt f (this helt s)

(** val for_all0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool **)

let for_all0 helt f s =
  S.for_all helt f (this helt s)

(** val exists_0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool **)

let exists_0 helt f s =
  S.exists_ helt f (this helt s)

(** val partition0 :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 * 'a1 set0 **)

let partition0 helt f s =
  let p = S.partition helt f (this helt s) in ((fst p), (snd p))

(** val equal0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool **)

let equal0 helt s s' =
  S.equal helt (this helt s) (this helt s')

(** val subset0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool **)

let subset0 helt s s' =
  S.subset helt (this helt s) (this helt s')

(** val set_compare0 :
    'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> comparison **)

let set_compare0 h s1 s2 =
  S.compare h (this h s1) (this h s2)

(** val set_OrderedType0 :
    'a1 orderedType -> 'a1 set0 specificOrderedType **)

let set_OrderedType0 h =
  set_compare0 h

(** val setAVL_FSet : 'a1 orderedType -> 'a1 fSet **)

let setAVL_FSet helt =
  { empty = (Obj.magic (empty0 helt)); is_empty =
    (Obj.magic (is_empty0 helt)); mem = (Obj.magic (mem0 helt)); add0 =
    (Obj.magic (add1 helt)); singleton = (Obj.magic (singleton0 helt));
    remove = (Obj.magic (remove0 helt)); union = (Obj.magic (union0 helt));
    inter = (Obj.magic (inter0 helt)); diff = (Obj.magic (diff0 helt));
    equal = (Obj.magic (equal0 helt)); subset = (Obj.magic (subset0 helt));
    fold = (Obj.magic (fun _ -> fold0 helt)); for_all =
    (Obj.magic (for_all0 helt)); exists_ = (Obj.magic (exists_0 helt));
    filter = (Obj.magic (filter0 helt)); partition =
    (Obj.magic (partition0 helt)); cardinal = (Obj.magic (cardinal0 helt));
    elements = (Obj.magic (elements0 helt)); choose =
    (Obj.magic (choose0 helt)); min_elt = (Obj.magic (min_elt0 helt));
    max_elt = (Obj.magic (max_elt0 helt)); fSet_OrderedType =
    (Obj.magic (set_OrderedType0 helt)) }

(** val of_list : 'a1 orderedType -> 'a1 fSet -> 'a1 list -> 'a1 set **)

let of_list hA f l =
  fold_right f.add0 f.empty l

(** val map0 :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set **)

let map0 hA hB f s =
  fold hA (setAVL_FSet hA) (fun a acc -> (setAVL_FSet hB).add0 (f a) acc) s
    (setAVL_FSet hB).empty

(** val inst_eq_dec_ordered_type : 'a1 orderedType -> 'a1 eqDec **)

let inst_eq_dec_ordered_type h x y =
  match h x y with
  | Eq -> true
  | _ -> false

type 'a counted = { counted0 : ('a -> Big.big_int);
                    incc : ('a -> Big.big_int -> 'a) }

(** val counted0 : 'a1 counted -> 'a1 -> Big.big_int **)

let counted0 x = x.counted0

type var = Big.big_int

type lab =
  Big.big_int
  (* singleton inductive, whose constructor was LabI *)

(** val labN : lab -> Big.big_int **)

let labN x =
  x

(** val labInc : lab -> Big.big_int -> lab **)

let labInc l d =
  plus d l

(** val inst_counted_lab : lab counted **)

let inst_counted_lab =
  { counted0 = labN; incc = labInc }

(** val lab_compare : lab -> lab -> comparison **)

let rec lab_compare l l' =
  nat_compare l l'

(** val lab_OrderedType : lab specificOrderedType **)

let lab_OrderedType =
  lab_compare

type val0 = Big.big_int

(** val inst_eq_dec_val : val0 eqDec **)

let inst_eq_dec_val x y =
  nat_eq_eqdec x y

(** val update :
    'a1 orderedType -> ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let update h f x y x' =
  if inst_equiv_cm (inst_eq_dec_ordered_type h) x x' then y else f x'

(** val lookup_set :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set **)

let lookup_set h h0 m s =
  map0 h h0 m s

(** val update_with_list :
    'a1 orderedType -> 'a1 list -> 'a2 list -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let rec update_with_list h xL yL m =
  match xL with
  | [] -> m
  | x :: xL0 ->
    (match yL with
     | [] -> m
     | y :: yL0 -> update h (update_with_list h xL0 yL0 m) x y)

(** val lookup_list : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec lookup_list m = function
| [] -> []
| x :: l0 -> (m x) :: (lookup_list m l0)

(** val injective_on_step :
    'a2 orderedType -> ('a1 -> 'a2) -> 'a1 -> ('a2 set * bool) -> 'a2
    set * bool **)

let injective_on_step h f x p =
  (((setAVL_FSet h).add0 (f x) (fst p)),
    (if snd p then negb ((setAVL_FSet h).mem (f x) (fst p)) else false))

(** val injective_on_compute :
    'a1 orderedType -> 'a2 orderedType -> 'a1 set -> ('a1 -> 'a2) -> bool **)

let injective_on_compute h h0 d f =
  snd
    (fold h (setAVL_FSet h) (injective_on_step h0 f) d
      ((setAVL_FSet h0).empty, true))

(** val injective_on_computable :
    'a1 orderedType -> 'a2 orderedType -> 'a1 set -> ('a1 -> 'a2) ->
    computable **)

let injective_on_computable h h0 d f =
  if injective_on_compute h h0 d f then true else false

(** val fresh_computable :
    'a1 orderedType -> 'a1 -> 'a1 list -> computable **)

let rec fresh_computable h x = function
| [] -> true
| y :: l0 ->
  let s = fresh_computable h x l0 in
  if s
  then let s0 = inst_equiv_cm (inst_eq_dec_ordered_type h) x y in
       if s0 then false else true
  else false

(** val inj_mapping_computable :
    'a1 orderedType -> 'a2 orderedType -> 'a2 set -> 'a1 list -> 'a2 list ->
    computable **)

let rec inj_mapping_computable h h0 lV l l' =
  match l with
  | [] ->
    (match l' with
     | [] -> true
     | y :: l'0 -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | y0 :: l'0 ->
       let s = inj_mapping_computable h h0 lV l0 l'0 in
       if s
       then let s0 = fresh_computable h y l0 in
            if s0
            then let s1 = fresh_computable h0 y0 l'0 in
                 if s1
                 then let s2 =
                        if (setAVL_FSet h0).mem y0 lV then true else false
                      in
                      if s2 then false else true
                 else false
            else false
       else false)

type 'x env = var -> 'x

type binop =
| Add
| Sub
| Mul

type exp =
| Con of val0
| Var of var
| BinOp of binop * exp * exp

(** val freeVars : exp -> var set **)

let rec freeVars = function
| Con v -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
| Var v -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton v
| BinOp (o, e1, e2) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union (freeVars e1) (freeVars e2)

(** val var_to_exp : var -> exp **)

let var_to_exp x =
  Var x

(** val rename_exp : var env -> exp -> exp **)

let rec rename_exp __U03f1_ = function
| Con v -> Con v
| Var v -> Var (__U03f1_ v)
| BinOp (o, e1, e2) ->
  BinOp (o, (rename_exp __U03f1_ e1), (rename_exp __U03f1_ e2))

type args = var list

type params = var list

type stmt =
| StmtExp of var * exp * stmt
| StmtIf of var * stmt * stmt
| StmtGoto of lab * args
| StmtReturn of var
| StmtLet of params * stmt * stmt

(** val freeVars0 : stmt -> var set **)

let rec freeVars0 = function
| StmtExp (x, e, s0) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff (freeVars0 s0)
      ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
        (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)) (freeVars e)
| StmtIf (x, s1, s2) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union (freeVars0 s1)
      (freeVars0 s2))
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
      (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
| StmtGoto (l, y) ->
  of_list (sOT_as_OT nat_OrderedType)
    (setAVL_FSet (sOT_as_OT nat_OrderedType)) y
| StmtReturn x ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
    (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
| StmtLet (z, s1, s2) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff (freeVars0 s1)
      (of_list (sOT_as_OT nat_OrderedType)
        (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)) (freeVars0 s2)

(** val rename : var env -> stmt -> stmt **)

let rec rename __U03f1_ = function
| StmtExp (x, e, s0) ->
  StmtExp ((__U03f1_ x), (rename_exp __U03f1_ e), (rename __U03f1_ s0))
| StmtIf (x, s0, t0) ->
  StmtIf ((__U03f1_ x), (rename __U03f1_ s0), (rename __U03f1_ t0))
| StmtGoto (l, y) -> StmtGoto (l, (lookup_list __U03f1_ y))
| StmtReturn x -> StmtReturn (__U03f1_ x)
| StmtLet (z, s0, t0) ->
  StmtLet ((lookup_list __U03f1_ z), (rename __U03f1_ s0),
    (rename __U03f1_ t0))

type 'a ann =
| AnnExp of 'a * 'a ann
| AnnIf of 'a * 'a ann * 'a ann
| AnnGoto of 'a
| AnnReturn of 'a
| AnnLet of 'a * 'a ann * 'a ann

(** val getAnn : 'a1 ann -> 'a1 **)

let getAnn = function
| AnnExp (a0, sa) -> a0
| AnnIf (a0, sa, ta) -> a0
| AnnGoto a0 -> a0
| AnnReturn a0 -> a0
| AnnLet (a0, sa, ta) -> a0

(** val setAnn : stmt -> 'a1 -> 'a1 ann **)

let rec setAnn s a =
  match s with
  | StmtExp (x, e, s') -> AnnExp (a, (setAnn s' a))
  | StmtIf (x, s1, s2) -> AnnIf (a, (setAnn s1 a), (setAnn s2 a))
  | StmtGoto (l, y) -> AnnGoto a
  | StmtReturn x -> AnnReturn a
  | StmtLet (z, s1, s2) -> AnnLet (a, (setAnn s1 a), (setAnn s2 a))

(** val annotation_dec_inst : stmt -> 'a1 ann -> computable **)

let rec annotation_dec_inst s a =
  match s with
  | StmtExp (x, e, s0) ->
    (match a with
     | AnnExp (a0, a1) -> annotation_dec_inst s0 a1
     | _ -> false)
  | StmtIf (x, s0, t0) ->
    (match a with
     | AnnIf (a1, a2, a3) ->
       let s1 = annotation_dec_inst s0 a2 in
       if s1 then annotation_dec_inst t0 a3 else false
     | _ -> false)
  | StmtGoto (l, y) ->
    (match a with
     | AnnGoto a0 -> true
     | _ -> false)
  | StmtReturn x ->
    (match a with
     | AnnReturn a0 -> true
     | _ -> false)
  | StmtLet (z, s0, t0) ->
    (match a with
     | AnnLet (a1, a2, a3) ->
       let s1 = annotation_dec_inst s0 a2 in
       if s1 then annotation_dec_inst t0 a3 else false
     | _ -> false)

type live = var set

(** val live_sound_dec :
    (live * params) list -> stmt -> live ann -> computable **)

let rec live_sound_dec lv s slv =
  match s with
  | StmtExp (x, e, s0) ->
    (match slv with
     | AnnExp (a, slv0) ->
       if live_sound_dec lv s0 slv0
       then let s1 =
              if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                   ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff
                     (getAnn slv0)
                     ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
                       (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)) a
              then true
              else false
            in
            if s1
            then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                      (freeVars e) a
                 then true
                 else false
            else false
       else false
     | _ -> assert false (* absurd case *))
  | StmtIf (x, s0, t0) ->
    (match slv with
     | AnnIf (a, slv1, slv2) ->
       if live_sound_dec lv s0 slv1
       then if live_sound_dec lv t0 slv2
            then let s1 =
                   if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x a
                   then true
                   else false
                 in
                 if s1
                 then let s2 =
                        if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                             (getAnn slv1) a
                        then true
                        else false
                      in
                      if s2
                      then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                                (getAnn slv2) a
                           then true
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> assert false (* absurd case *))
  | StmtGoto (l, y) ->
    (match slv with
     | AnnGoto a ->
       let s0 = get_dec lv (inst_counted_lab.counted0 l) in
       (match s0 with
        | Some s1 ->
          let (blv, z) = s1 in
          let s2 =
            if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                 ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff blv
                   (of_list (sOT_as_OT nat_OrderedType)
                     (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)) a
            then true
            else false
          in
          if s2
          then let s3 =
                 if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                      (of_list (sOT_as_OT nat_OrderedType)
                        (setAVL_FSet (sOT_as_OT nat_OrderedType)) y) a
                 then true
                 else false
               in
               if s3
               then inst_eq_cm inst_eq_dec_val (length y) (length z)
               else false
          else false
        | None -> false)
     | _ -> assert false (* absurd case *))
  | StmtReturn x ->
    (match slv with
     | AnnReturn a ->
       if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x a
       then true
       else false
     | _ -> assert false (* absurd case *))
  | StmtLet (z, s0, t0) ->
    (match slv with
     | AnnLet (a, slv1, slv2) ->
       if live_sound_dec (((getAnn slv1), z) :: lv) s0 slv1
       then if live_sound_dec (((getAnn slv1), z) :: lv) t0 slv2
            then let s1 =
                   if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                        (of_list (sOT_as_OT nat_OrderedType)
                          (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)
                        (getAnn slv1)
                   then true
                   else false
                 in
                 if s1
                 then let s2 =
                        if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                             ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff
                               (getAnn slv1)
                               (of_list (sOT_as_OT nat_OrderedType)
                                 (setAVL_FSet (sOT_as_OT nat_OrderedType)) z))
                             a
                        then true
                        else false
                      in
                      if s2
                      then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                                (getAnn slv2) a
                           then true
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> assert false (* absurd case *))

(** val live_sound_dec_inst :
    (live * params) list -> stmt -> live ann -> computable -> computable **)

let live_sound_dec_inst lv s slv = function
| true -> live_sound_dec lv s slv
| false -> false

(** val live_rename : var env -> live ann -> live ann **)

let rec live_rename __U03f1_ = function
| AnnExp (a, an0) ->
  AnnExp
    ((lookup_set (sOT_as_OT nat_OrderedType) (sOT_as_OT nat_OrderedType)
       __U03f1_ a), (live_rename __U03f1_ an0))
| AnnIf (a, ans, ant) ->
  AnnIf
    ((lookup_set (sOT_as_OT nat_OrderedType) (sOT_as_OT nat_OrderedType)
       __U03f1_ a), (live_rename __U03f1_ ans), (live_rename __U03f1_ ant))
| AnnGoto a ->
  AnnGoto
    (lookup_set (sOT_as_OT nat_OrderedType) (sOT_as_OT nat_OrderedType)
      __U03f1_ a)
| AnnReturn a ->
  AnnReturn
    (lookup_set (sOT_as_OT nat_OrderedType) (sOT_as_OT nat_OrderedType)
      __U03f1_ a)
| AnnLet (a, ans, ant) ->
  AnnLet
    ((lookup_set (sOT_as_OT nat_OrderedType) (sOT_as_OT nat_OrderedType)
       __U03f1_ a), (live_rename __U03f1_ ans), (live_rename __U03f1_ ant))

(** val restr : var set -> var set option -> var set option **)

let restr g = function
| Some g' ->
  if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset g' g
  then Some g'
  else None
| None -> None

(** val restrict : var set option list -> var set -> var set option list **)

let restrict dL g =
  map (restr g) dL

(** val locally_inj_dec : var env -> stmt -> var set ann -> bool **)

let rec locally_inj_dec __U03f1_ s lv =
  match s with
  | StmtExp (x, e, s0) ->
    (match lv with
     | AnnExp (a, lv0) ->
       let s1 =
         injective_on_computable (sOT_as_OT nat_OrderedType)
           (sOT_as_OT nat_OrderedType) a __U03f1_
       in
       if s1
       then let s2 =
              injective_on_computable (sOT_as_OT nat_OrderedType)
                (sOT_as_OT nat_OrderedType)
                ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union (getAnn lv0)
                  ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
                    (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty))
                __U03f1_
            in
            if s2 then locally_inj_dec __U03f1_ s0 lv0 else false
       else false
     | _ -> assert false (* absurd case *))
  | StmtIf (x, s0, t0) ->
    (match lv with
     | AnnIf (a, lv1, lv2) ->
       let s1 =
         injective_on_computable (sOT_as_OT nat_OrderedType)
           (sOT_as_OT nat_OrderedType) a __U03f1_
       in
       if s1
       then if locally_inj_dec __U03f1_ s0 lv1
            then locally_inj_dec __U03f1_ t0 lv2
            else false
       else false
     | _ -> assert false (* absurd case *))
  | StmtGoto (l, y) ->
    (match lv with
     | AnnGoto a ->
       injective_on_computable (sOT_as_OT nat_OrderedType)
         (sOT_as_OT nat_OrderedType) a __U03f1_
     | _ -> assert false (* absurd case *))
  | StmtReturn x ->
    (match lv with
     | AnnReturn a ->
       injective_on_computable (sOT_as_OT nat_OrderedType)
         (sOT_as_OT nat_OrderedType) a __U03f1_
     | _ -> assert false (* absurd case *))
  | StmtLet (z, s0, t0) ->
    (match lv with
     | AnnLet (a, lv1, lv2) ->
       let s1 =
         injective_on_computable (sOT_as_OT nat_OrderedType)
           (sOT_as_OT nat_OrderedType) a __U03f1_
       in
       if s1
       then let s2 =
              injective_on_computable (sOT_as_OT nat_OrderedType)
                (sOT_as_OT nat_OrderedType)
                ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union (getAnn lv1)
                  (of_list (sOT_as_OT nat_OrderedType)
                    (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)) __U03f1_
            in
            if s2
            then let s3 =
                   inj_mapping_computable (sOT_as_OT nat_OrderedType)
                     (sOT_as_OT nat_OrderedType)
                     (lookup_set (sOT_as_OT nat_OrderedType)
                       (sOT_as_OT nat_OrderedType) __U03f1_
                       ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff
                         (getAnn lv1)
                         (of_list (sOT_as_OT nat_OrderedType)
                           (setAVL_FSet (sOT_as_OT nat_OrderedType)) z))) z
                     (lookup_list __U03f1_ z)
                 in
                 if s3
                 then if locally_inj_dec __U03f1_ s0 lv1
                      then locally_inj_dec __U03f1_ t0 lv2
                      else false
                 else false
            else false
       else false
     | _ -> assert false (* absurd case *))

(** val locally_inj_dec_inst :
    var env -> stmt -> var set ann -> computable -> computable **)

let locally_inj_dec_inst __U03f1_ s lv = function
| true -> locally_inj_dec __U03f1_ s lv
| false -> false

(** val fresh : var set -> var **)

let fresh s =
  Big.succ
    (fold (sOT_as_OT nat_OrderedType)
      (setAVL_FSet (sOT_as_OT nat_OrderedType)) max s Big.zero)

(** val fresh_list : var set -> Big.big_int -> var list **)

let rec fresh_list g n =
  Big.nat_case
    (fun _ ->
    [])
    (fun n0 ->
    let x = fresh g in
    x :: (fresh_list
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g
             ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
               (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)) n0))
    n

(** val rename_apart' : var env -> var set -> stmt -> var set * stmt **)

let rec rename_apart' __U03f1_ g = function
| StmtExp (x, e, s0) ->
  let y = fresh g in
  let __U03f1_' = update (sOT_as_OT nat_OrderedType) __U03f1_ x y in
  let (g', s') =
    rename_apart' __U03f1_'
      ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g
        ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 y
          (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)) s0
  in
  (g', (StmtExp (y, (rename_exp __U03f1_ e), s')))
| StmtIf (x, s1, s2) ->
  let (g', s1') = rename_apart' __U03f1_ g s1 in
  let (g'', s2') = rename_apart' __U03f1_ g' s2 in
  (g'', (StmtIf ((__U03f1_ x), s1', s2')))
| StmtGoto (l, y) -> (g, (StmtGoto (l, (lookup_list __U03f1_ y))))
| StmtReturn x -> (g, (StmtReturn (__U03f1_ x)))
| StmtLet (z, s1, s2) ->
  let y = fresh_list g (length z) in
  let __U03f1_Z = update_with_list (sOT_as_OT nat_OrderedType) z y __U03f1_
  in
  let (g', s1') =
    rename_apart' __U03f1_Z
      ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g
        (of_list (sOT_as_OT nat_OrderedType)
          (setAVL_FSet (sOT_as_OT nat_OrderedType)) y)) s1
  in
  let (g'', s2') = rename_apart' __U03f1_ g' s2 in
  (g'', (StmtLet (y, s1', s2')))

(** val rename_apart : stmt -> stmt **)

let rename_apart s =
  snd (rename_apart' id (freeVars0 s) s)

(** val trs_dec :
    var set option list -> params list -> var set -> stmt -> var set option
    ann -> var list ann -> bool **)

let rec trs_dec dL zL g s ans_lv ans =
  match s with
  | StmtExp (x, e, s0) ->
    (match ans with
     | AnnExp (a, ans0) ->
       (match ans_lv with
        | AnnExp (a0, ans_lv0) ->
          let s1 =
            if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset (freeVars e)
                 g
            then true
            else false
          in
          if s1
          then let s2 = inst_eq_cm (inst_eq_dec_list inst_eq_dec_val) a [] in
               if s2
               then (match a0 with
                     | Some s3 -> false
                     | None ->
                       trs_dec
                         (restrict dL
                           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff g
                             ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0
                               x
                               (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)))
                         zL
                         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g
                           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
                             (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty))
                         s0 ans_lv0 ans0)
               else false
          else false
        | _ -> assert false (* absurd case *))
     | _ -> assert false (* absurd case *))
  | StmtIf (x, s0, t0) ->
    (match ans with
     | AnnIf (a, ans1, ans2) ->
       (match ans_lv with
        | AnnIf (a0, ans_lv1, ans_lv2) ->
          let s1 =
            if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x g
            then true
            else false
          in
          if s1
          then let s2 = inst_eq_cm (inst_eq_dec_list inst_eq_dec_val) a [] in
               if s2
               then (match a0 with
                     | Some s3 -> false
                     | None ->
                       if trs_dec dL zL g s0 ans_lv1 ans1
                       then trs_dec dL zL g t0 ans_lv2 ans2
                       else false)
               else false
          else false
        | _ -> assert false (* absurd case *))
     | _ -> assert false (* absurd case *))
  | StmtGoto (l, y) ->
    (match ans with
     | AnnGoto a ->
       (match ans_lv with
        | AnnGoto a0 ->
          let s0 = get_dec dL (inst_counted_lab.counted0 l) in
          (match s0 with
           | Some s1 ->
             (match s1 with
              | Some g' ->
                let s2 = get_dec zL (inst_counted_lab.counted0 l) in
                (match s2 with
                 | Some s3 ->
                   let s4 =
                     inst_eq_cm (inst_eq_dec_list inst_eq_dec_val) a s3
                   in
                   if s4
                   then (match a0 with
                         | Some s5 -> false
                         | None ->
                           let s5 =
                             if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                                  g' g
                             then true
                             else false
                           in
                           if s5
                           then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                                     (of_list (sOT_as_OT nat_OrderedType)
                                       (setAVL_FSet
                                         (sOT_as_OT nat_OrderedType))
                                       (app y s3)) g
                                then true
                                else false
                           else false)
                   else false
                 | None -> false)
              | None -> false)
           | None -> false)
        | _ -> assert false (* absurd case *))
     | _ -> assert false (* absurd case *))
  | StmtReturn x ->
    (match ans with
     | AnnReturn a ->
       (match ans_lv with
        | AnnReturn a0 ->
          let s0 =
            if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x g
            then true
            else false
          in
          if s0
          then let s1 = inst_eq_cm (inst_eq_dec_list inst_eq_dec_val) a [] in
               if s1
               then (match a0 with
                     | Some s2 -> false
                     | None -> true)
               else false
          else false
        | _ -> assert false (* absurd case *))
     | _ -> assert false (* absurd case *))
  | StmtLet (z, s0, t0) ->
    (match ans with
     | AnnLet (a, ans1, ans2) ->
       (match ans_lv with
        | AnnLet (a0, ans_lv1, ans_lv2) ->
          (match a0 with
           | Some g' ->
             let s1 =
               if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset g'
                    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff g
                      (of_list (sOT_as_OT nat_OrderedType)
                        (setAVL_FSet (sOT_as_OT nat_OrderedType)) (app z a)))
               then true
               else false
             in
             if s1
             then if trs_dec (restrict ((Some g') :: dL) g') (a :: zL)
                       ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g'
                         (of_list (sOT_as_OT nat_OrderedType)
                           (setAVL_FSet (sOT_as_OT nat_OrderedType))
                           (app z a))) s0 ans_lv1 ans1
                  then trs_dec ((Some g') :: dL) (a :: zL) g t0 ans_lv2 ans2
                  else false
             else false
           | None -> false)
        | _ -> assert false (* absurd case *))
     | _ -> assert false (* absurd case *))

(** val trs_dec_inst :
    var set option list -> params list -> var set -> stmt -> var set option
    ann -> var list ann -> computable -> computable -> computable **)

let trs_dec_inst dL zL g s lv args0 h h0 =
  if h then if h0 then trs_dec dL zL g s lv args0 else false else false

(** val compile : stmt -> var list ann -> stmt **)

let rec compile s an =
  match s with
  | StmtExp (x, e, s0) ->
    (match an with
     | AnnExp (a, an0) -> StmtExp (x, e, (compile s0 an0))
     | _ -> s)
  | StmtIf (x, s0, t0) ->
    (match an with
     | AnnIf (a, ans, ant) -> StmtIf (x, (compile s0 ans), (compile t0 ant))
     | _ -> s)
  | StmtGoto (f, y) ->
    (match an with
     | AnnGoto za -> StmtGoto (f, (app y za))
     | _ -> s)
  | StmtReturn x ->
    (match an with
     | AnnReturn a -> StmtReturn x
     | _ -> s)
  | StmtLet (z, s0, t0) ->
    (match an with
     | AnnLet (za, ans, ant) ->
       StmtLet ((app z za), (compile s0 ans), (compile t0 ant))
     | _ -> s)

type pmov = (var list * var list) list

(** val par_move :
    (var -> var) -> (var -> var) -> params -> args -> var -> var **)

let rec par_move e e' z y =
  match z with
  | [] -> e
  | y0 :: z' ->
    (match y with
     | [] -> e
     | a :: y' ->
       (fun x ->
         if inst_eq_cm inst_eq_dec_val x y0
         then e' a
         else par_move e e' z' y' x))

(** val par_list : (params * args) list -> (var -> var) -> var -> var **)

let rec par_list p m =
  match p with
  | [] -> m
  | y :: p' -> let (l1, l2) = y in par_list p' (par_move m m l1 l2)

(** val check_pmove : var set -> pmov -> pmov -> bool **)

let check_pmove vars p1 p2 =
  let m1 = par_list p1 (fun x -> x) in
  let m2 = par_list p2 (fun x -> x) in
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).for_all (fun x ->
    if inst_eq_cm inst_eq_dec_val (m1 x) (m2 x) then true else false) vars

(** val list_to_stmt : (var list * var list) list -> stmt -> stmt **)

let rec list_to_stmt p s =
  match p with
  | [] -> s
  | p0 :: p' ->
    let (l, l0) = p0 in
    (match l with
     | [] -> s
     | x :: l1 ->
       (match l1 with
        | [] ->
          (match l0 with
           | [] -> s
           | y :: l2 ->
             (match l2 with
              | [] -> StmtExp (x, (var_to_exp y), (list_to_stmt p' s))
              | v :: l3 -> s))
        | v :: l2 -> s))

(** val linearize_parallel_assignment :
    (var -> var list -> var list -> (var list * var list) list option) -> var
    set -> var list -> var list -> (var list * var list) list option **)

let linearize_parallel_assignment parallel_move vars l1 l2 =
  parallel_move (fresh vars) l1 l2

(** val check_is_simple_ass : (var list * var list) list -> bool **)

let rec check_is_simple_ass = function
| [] -> true
| p0 :: p' ->
  let (l, l0) = p0 in
  (match l with
   | [] -> false
   | v :: l1 ->
     (match l1 with
      | [] ->
        (match l0 with
         | [] -> false
         | v0 :: l2 ->
           (match l2 with
            | [] -> check_is_simple_ass p'
            | v1 :: l3 -> false))
      | v0 :: l2 -> false))

(** val compile_parallel_assignment :
    (var -> var list -> var list -> (var list * var list) list option) -> var
    set -> var list -> var list -> stmt -> stmt option **)

let compile_parallel_assignment parallel_move vars l1 l2 s =
  match linearize_parallel_assignment parallel_move vars l1 l2 with
  | Some a ->
    if check_pmove vars a ((l1, l2) :: [])
    then if check_is_simple_ass a then Some (list_to_stmt a s) else None
    else None
  | None -> None

(** val lower :
    (var -> var list -> var list -> (var list * var list) list option) ->
    (var set * var list) list -> stmt -> var set ann -> stmt option **)

let rec lower parallel_move dL s an =
  match s with
  | StmtExp (x, e, s0) ->
    (match an with
     | AnnExp (lv, ans) ->
       (match lower parallel_move dL s0 ans with
        | Some a -> Some (StmtExp (x, e, a))
        | None -> None)
     | _ -> None)
  | StmtIf (x, s0, t0) ->
    (match an with
     | AnnIf (lv, ans, ant) ->
       (match lower parallel_move dL s0 ans with
        | Some a ->
          (match lower parallel_move dL t0 ant with
           | Some a0 -> Some (StmtIf (x, a, a0))
           | None -> None)
        | None -> None)
     | _ -> None)
  | StmtGoto (l, y) ->
    (match an with
     | AnnGoto lv ->
       (match nth_error dL (inst_counted_lab.counted0 l) with
        | Some a ->
          let (lv0, z) = a in
          compile_parallel_assignment parallel_move lv0 z y (StmtGoto (l,
            []))
        | None -> None)
     | _ -> None)
  | StmtReturn x ->
    (match an with
     | AnnReturn lv -> Some (StmtReturn x)
     | _ -> None)
  | StmtLet (z, s0, t0) ->
    (match an with
     | AnnLet (lv, ans, ant) ->
       (match lower parallel_move (((getAnn ans), z) :: dL) s0 ans with
        | Some a ->
          (match lower parallel_move (((getAnn ans), z) :: dL) t0 ant with
           | Some a0 -> Some (StmtLet ([], a, a0))
           | None -> None)
        | None -> None)
     | _ -> None)

type nstmt =
| NstmtExp of var * exp * nstmt
| NstmtIf of var * nstmt * nstmt
| NstmtGoto of lab * args
| NstmtReturn of var
| NstmtLet of lab * params * nstmt * nstmt

(** val pos :
    'a1 orderedType -> 'a1 list -> 'a1 -> Big.big_int -> Big.big_int option **)

let rec pos h l x n =
  match l with
  | [] -> None
  | y :: l0 ->
    if is_compare h x y Eq then Some n else pos h l0 x (Big.succ n)

(** val labIndices : nstmt -> lab list -> stmt option **)

let rec labIndices s symb =
  match s with
  | NstmtExp (x, e, s0) ->
    (match labIndices s0 symb with
     | Some a -> Some (StmtExp (x, e, a))
     | None -> None)
  | NstmtIf (x, s1, s2) ->
    (match labIndices s1 symb with
     | Some a ->
       (match labIndices s2 symb with
        | Some a0 -> Some (StmtIf (x, a, a0))
        | None -> None)
     | None -> None)
  | NstmtGoto (l, y) ->
    (match pos (sOT_as_OT lab_OrderedType) symb l Big.zero with
     | Some a -> Some (StmtGoto (a, y))
     | None -> None)
  | NstmtReturn x -> Some (StmtReturn x)
  | NstmtLet (l, z, s1, s2) ->
    (match labIndices s1 (l :: symb) with
     | Some a ->
       (match labIndices s2 (l :: symb) with
        | Some a0 -> Some (StmtLet (z, a, a0))
        | None -> None)
     | None -> None)

type 'a semiLattice = { bottom : 'a; join0 : ('a -> 'a -> 'a) }

(** val bottom : 'a1 orderedType -> 'a1 semiLattice -> 'a1 **)

let bottom _ x = x.bottom

type ('dom, 'funDom) abstractInterpretation = { transform : ('funDom list ->
                                                            stmt -> 'dom ann
                                                            -> 'dom);
                                                mkFunDom : (params -> 'dom
                                                           ann -> 'funDom) }

(** val transform :
    'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation
    -> 'a2 list -> stmt -> 'a1 ann -> 'a1 **)

let transform _ _ x = x.transform

(** val mkFunDom :
    'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation
    -> params -> 'a1 ann -> 'a2 **)

let mkFunDom _ _ x = x.mkFunDom

(** val backward :
    'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2) abstractInterpretation
    -> stmt -> 'a2 list -> 'a1 ann -> 'a1 ann **)

let rec backward h h0 aI st aL a =
  match st with
  | StmtExp (x, e, s) ->
    (match a with
     | AnnExp (d, ans) ->
       let ans' = backward h h0 aI s aL ans in
       let d' = AnnExp (d, ans') in AnnExp ((aI.transform aL st d'), ans')
     | _ -> a)
  | StmtIf (x, s, t0) ->
    (match a with
     | AnnIf (d, ans, ant) ->
       let ans' = backward h h0 aI s aL ans in
       let ant' = backward h h0 aI t0 aL ant in
       let an' = AnnIf (d, ans', ant') in
       AnnIf ((aI.transform aL st an'), ans', ant')
     | _ -> a)
  | StmtGoto (f, y) ->
    (match a with
     | AnnGoto d -> AnnGoto (aI.transform aL st a)
     | _ -> a)
  | StmtReturn x ->
    (match a with
     | AnnReturn d -> AnnReturn (aI.transform aL st a)
     | _ -> a)
  | StmtLet (z, s, t0) ->
    (match a with
     | AnnLet (d, ans, ant) ->
       let ans' = backward h h0 aI s ((aI.mkFunDom z ans) :: aL) ans in
       let ant' = backward h h0 aI t0 ((aI.mkFunDom z ans') :: aL) ant in
       let d' = AnnLet (d, ans', ant') in
       AnnLet ((aI.transform ((aI.mkFunDom z ans') :: aL) st d'), ans', ant')
     | _ -> a)

(** val ann_lt_dec :
    ('a1 -> 'a1 -> computable) -> 'a1 ann -> 'a1 ann -> computable **)

let rec ann_lt_dec h a b =
  match a with
  | AnnExp (a0, a1) ->
    (match b with
     | AnnExp (a2, b0) ->
       let s = h a0 a2 in if s then ann_lt_dec h a1 b0 else false
     | _ -> false)
  | AnnIf (a1, a2, a3) ->
    (match b with
     | AnnIf (a0, b1, b2) ->
       let s = h a1 a0 in
       if s
       then if ann_lt_dec h a2 b1 then ann_lt_dec h a3 b2 else false
       else false
     | _ -> false)
  | AnnGoto a0 ->
    (match b with
     | AnnGoto a1 -> h a0 a1
     | _ -> false)
  | AnnReturn a0 ->
    (match b with
     | AnnReturn a1 -> h a0 a1
     | _ -> false)
  | AnnLet (a1, a2, a3) ->
    (match b with
     | AnnLet (a0, b1, b2) ->
       let s = h a1 a0 in
       if s
       then let s0 = ann_lt_dec h a2 b1 in
            if s0 then ann_lt_dec h a3 b2 else false
       else false
     | _ -> false)

(** val step :
    ('a1 -> 'a1 -> computable) -> 'a1 orderedType -> 'a1 semiLattice -> ('a1,
    'a2) abstractInterpretation -> stmt -> 'a1 ann -> 'a1 ann * bool **)

let step lt_dec h h0 aI s d =
  let d' = backward h h0 aI s [] d in
  (d', (if ann_lt_dec lt_dec d' d then false else true))

(** val analysis :
    ('a1 -> 'a1 -> computable) -> ('a1 ann -> ('a1 ann -> 'a1 ann * bool) ->
    'a1 ann) -> 'a1 orderedType -> 'a1 semiLattice -> ('a1, 'a2)
    abstractInterpretation -> stmt -> 'a1 ann **)

let analysis lt_dec first h h0 aI s =
  first (setAnn s h0.bottom) (step lt_dec h h0 aI s)

(** val set_var_semilattice : var set semiLattice **)

let set_var_semilattice =
  { bottom = (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty; join0 =
    (setAVL_FSet (sOT_as_OT nat_OrderedType)).union }

(** val liveness_transform :
    var set list -> stmt -> var set ann -> var set **)

let liveness_transform dL st a =
  match st with
  | StmtExp (x, e, s) ->
    (match a with
     | AnnExp (d, ans) ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff (getAnn ans)
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
             (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)) (freeVars e)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtIf (x, s, t0) ->
    (match a with
     | AnnIf (d, ans, ant) ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
             (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty) (getAnn ans))
         (getAnn ant)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtGoto (f, y) ->
    (match a with
     | AnnGoto d ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         (nth (inst_counted_lab.counted0 f) dL
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
         (of_list (sOT_as_OT nat_OrderedType)
           (setAVL_FSet (sOT_as_OT nat_OrderedType)) y)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtReturn x ->
    (match a with
     | AnnReturn d ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x
         (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtLet (z, s, t0) ->
    (match a with
     | AnnLet (d, ans, ant) ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff (getAnn ans)
           (of_list (sOT_as_OT nat_OrderedType)
             (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)) (getAnn ant)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)

(** val liveness_analysis : (var set, var set) abstractInterpretation **)

let liveness_analysis =
  { transform = liveness_transform; mkFunDom = (fun z an ->
    (setAVL_FSet (sOT_as_OT nat_OrderedType)).diff (getAnn an)
      (of_list (sOT_as_OT nat_OrderedType)
        (setAVL_FSet (sOT_as_OT nat_OrderedType)) z)) }

(** val livenessAnalysis :
    (var set ann -> (var set ann -> var set ann * bool) -> var set ann) ->
    stmt -> var set ann **)

let livenessAnalysis first s =
  analysis (fun s0 t0 ->
    if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset s0 t0
    then true
    else false) first
    (sOT_as_OT (setAVL_FSet (sOT_as_OT nat_OrderedType)).fSet_OrderedType)
    set_var_semilattice liveness_analysis s

(** val toILF :
    (stmt -> var set option ann * var list ann) -> stmt -> stmt option **)

let toILF ssa_construction ili =
  let (lv, additional_arguments) = ssa_construction ili in
  if trs_dec_inst [] [] (freeVars0 ili) ili lv additional_arguments
       (annotation_dec_inst ili lv)
       (annotation_dec_inst ili additional_arguments)
  then Some (compile ili additional_arguments)
  else None

(** val fromILF :
    (stmt -> var set -> var set -> __ -> var -> var) -> (var -> var list ->
    var list -> (var list * var list) list option) -> (var set ann -> (var
    set ann -> var set ann * bool) -> var set ann) -> stmt -> stmt option **)

let fromILF allocation_oracle parallel_move first s =
  let s_renamed_apart = rename_apart s in
  let __U03f1_ =
    allocation_oracle (rename_apart s) (freeVars0 s)
      (fst (rename_apart' id (freeVars0 s) s)) __
  in
  let lv = livenessAnalysis first s_renamed_apart in
  if if locally_inj_dec_inst __U03f1_ s_renamed_apart lv
          (annotation_dec_inst s_renamed_apart lv)
     then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).for_all (fun x ->
               if inst_equiv_cm
                    (inst_eq_dec_ordered_type (sOT_as_OT nat_OrderedType))
                    (__U03f1_ x) (id x)
               then true
               else false) (getAnn lv)
          then if (setAVL_FSet (sOT_as_OT nat_OrderedType)).subset
                    (getAnn lv) (freeVars0 s)
               then live_sound_dec_inst [] s_renamed_apart lv
                      (annotation_dec_inst s_renamed_apart lv)
               else false
          else false
     else false
  then let s_allocated = rename __U03f1_ s_renamed_apart in
       (match lower parallel_move [] s_allocated (live_rename __U03f1_ lv) with
        | Some a -> Some a
        | None -> None)
  else None

