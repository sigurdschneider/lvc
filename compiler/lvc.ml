type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)



(** val add : int -> int -> int **)

let rec add = (+)

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

module Nat =
 struct
  
 end

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match l with
    | [] -> default
    | x :: _ -> x)
    (fun m ->
    match l with
    | [] -> default
    | _ :: t -> nth m t default)
    n0

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

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

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO _ -> N0
       | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO _ -> Npos XH
       | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos _ -> false)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos _ -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : positive -> n -> n * n **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> ((Npos XH), N0)
          | _ -> (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos _ -> Lt
       | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val of_nat : int -> z **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      Z0)
      (fun n1 -> Zpos
      (Coq_Pos.of_succ_nat n1))
      n0

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> z * z **)

  let quotrem a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in ((of_N q), (of_N r))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p ->
    (match p with
     | XO _ -> false
     | _ -> true)
  | Zneg p ->
    (match p with
     | XO _ -> false
     | _ -> true)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> false

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
 end

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_le_dec : z -> z -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val z_gt_dec : z -> z -> bool **)

let z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val z_ge_dec : z -> z -> bool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val z_le_gt_dec : z -> z -> bool **)

let z_le_gt_dec x y =
  z_le_dec x y

(** val z_gt_le_dec : z -> z -> bool **)

let z_gt_le_dec x y =
  z_gt_dec x y

(** val z_ge_lt_dec : z -> z -> bool **)

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

type 'a specificOrderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_SpecificOrderedType *)

(** val sOT_cmp : 'a1 specificOrderedType -> 'a1 -> 'a1 -> comparison **)

let sOT_cmp specificOrderedType0 =
  specificOrderedType0

(** val sOT_as_OT : 'a1 specificOrderedType -> 'a1 orderedType **)

let sOT_as_OT h =
  sOT_cmp h

(** val shift_nat : int -> positive -> positive **)

let rec shift_nat n0 z0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    z0)
    (fun n1 -> XO
    (shift_nat n1 z0))
    n0

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : int -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val nat_compare : int -> int -> comparison **)

let rec nat_compare n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      Eq)
      (fun _ ->
      Lt)
      m)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      Gt)
      (fun m0 ->
      nat_compare n1 m0)
      m)
    n0

(** val nat_OrderedType : int specificOrderedType **)

let nat_OrderedType =
  nat_compare

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

(** val inter :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set **)

let inter _ x = x.inter

(** val diff :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set **)

let diff _ x = x.diff

(** val equal : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool **)

let equal _ x = x.equal

(** val subset : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> bool **)

let subset _ x = x.subset

(** val elements : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 list **)

let elements _ x = x.elements

module SetList =
 struct
  type 'a set = 'a list

  (** val fold :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2 **)

  let rec fold comparedec f s i =
    match s with
    | [] -> i
    | x :: l -> fold comparedec f l (f x i)
 end

module SetAVL =
 struct
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * z

  (** val tree_rect :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      z -> 'a2) -> 'a1 tree -> 'a2 **)

  let rec tree_rect h f f0 = function
  | Leaf -> f
  | Node (t0, y, t1, z0) ->
    f0 t0 (tree_rect h f f0 t0) y t1 (tree_rect h f f0 t1) z0

  (** val tree_rec :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      z -> 'a2) -> 'a1 tree -> 'a2 **)

  let rec tree_rec h f f0 = function
  | Leaf -> f
  | Node (t0, y, t1, z0) ->
    f0 t0 (tree_rec h f f0 t0) y t1 (tree_rec h f f0 t1) z0

  (** val height : 'a1 orderedType -> 'a1 tree -> z **)

  let height _ = function
  | Leaf -> Z0
  | Node (_, _, _, h) -> h

  (** val cardinal : 'a1 orderedType -> 'a1 tree -> int **)

  let rec cardinal h = function
  | Leaf -> 0
  | Node (l, _, r, _) -> Pervasives.succ (add (cardinal h l) (cardinal h r))

  (** val empty : 'a1 orderedType -> 'a1 tree **)

  let empty _ =
    Leaf

  (** val is_empty : 'a1 orderedType -> 'a1 tree -> bool **)

  let is_empty _ = function
  | Leaf -> true
  | Node (_, _, _, _) -> false

  (** val mem : 'a1 orderedType -> 'a1 -> 'a1 tree -> bool **)

  let rec mem h x = function
  | Leaf -> false
  | Node (l, y, r, _) ->
    (match compare0 h x y with
     | Eq -> true
     | Lt -> mem h x l
     | Gt -> mem h x r)

  (** val singleton : 'a1 orderedType -> 'a1 -> 'a1 tree **)

  let singleton _ x =
    Node (Leaf, x, Leaf, (Zpos XH))

  (** val create :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create h l x r =
    Node (l, x, r, (Z.add (Z.max (height h l) (height h r)) (Zpos XH)))

  (** val assert_false :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false h =
    create h

  (** val bal : 'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal h l x r =
    let hl = height h l in
    let hr = height h r in
    if z_gt_le_dec hl (Z.add hr (Zpos (XO XH)))
    then (match l with
          | Leaf -> assert_false h l x r
          | Node (ll, lx, lr, _) ->
            if z_ge_lt_dec (height h ll) (height h lr)
            then create h ll lx (create h lr x r)
            else (match lr with
                  | Leaf -> assert_false h l x r
                  | Node (lrl, lrx, lrr, _) ->
                    create h (create h ll lx lrl) lrx (create h lrr x r)))
    else if z_gt_le_dec hr (Z.add hl (Zpos (XO XH)))
         then (match r with
               | Leaf -> assert_false h l x r
               | Node (rl, rx, rr, _) ->
                 if z_ge_lt_dec (height h rr) (height h rl)
                 then create h (create h l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false h l x r
                       | Node (rll, rlx, rlr, _) ->
                         create h (create h l x rll) rlx (create h rlr rx rr)))
         else create h l x r

  (** val add : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add h x = function
  | Leaf -> Node (Leaf, x, Leaf, (Zpos XH))
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
        if z_gt_le_dec lh (Z.add rh (Zpos (XO XH)))
        then bal h ll lx (join h lr x r)
        else if z_gt_le_dec rh (Z.add lh (Zpos (XO XH)))
             then bal h (join_aux rl) rx rr
             else create h l x r
      in join_aux)

  (** val remove_min :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree * 'a1 **)

  let rec remove_min h l x r =
    match l with
    | Leaf -> (r, x)
    | Node (ll, lx, lr, _) ->
      let (l', m) = remove_min h ll lx lr in ((bal h l' x r), m)

  (** val merge : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, _) ->
         let (s2', m) = remove_min h l2 x2 r2 in bal h s1 m s2')

  (** val remove : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec remove h x = function
  | Leaf -> Leaf
  | Node (l, y, r, _) ->
    (match compare0 h x y with
     | Eq -> merge h l r
     | Lt -> bal h (remove h x l) y r
     | Gt -> bal h l y (remove h x r))

  (** val min_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)

  let rec min_elt h = function
  | Leaf -> None
  | Node (l, y, _, _) ->
    (match l with
     | Leaf -> Some y
     | Node (_, _, _, _) -> min_elt h l)

  (** val max_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)

  let rec max_elt h = function
  | Leaf -> None
  | Node (_, y, r, _) ->
    (match r with
     | Leaf -> Some y
     | Node (_, _, _, _) -> max_elt h r)

  (** val choose : 'a1 orderedType -> 'a1 tree -> 'a1 option **)

  let choose h =
    min_elt h

  (** val concat : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, _) ->
         let (s2', m) = remove_min h l2 x2 r2 in join h s1 m s2')

  type 'elt triple = { t_left : 'elt tree; t_in : bool; t_right : 'elt tree }

  (** val t_left : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)

  let t_left _ x = x.t_left

  (** val t_in : 'a1 orderedType -> 'a1 triple -> bool **)

  let t_in _ x = x.t_in

  (** val t_right : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)

  let t_right _ x = x.t_right

  (** val split : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 triple **)

  let rec split h x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (l, y, r, _) ->
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
    | Node (l1, x1, r1, _) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then join h (inter h l1 l2') x1 (inter h r1 r2')
         else concat h (inter h l1 l2') (inter h r1 r2'))

  (** val diff : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let rec diff h s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then concat h (diff h l1 l2') (diff h r1 r2')
         else join h (diff h l1 l2') x1 (diff h r1 r2'))

  (** val union : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let rec union h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (l1, x1, r1, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = _; t_right = r2' } = split h x1 s2 in
         join h (union h l1 l2') x1 (union h r1 r2'))

  (** val elements_aux :
      'a1 orderedType -> 'a1 list -> 'a1 tree -> 'a1 list **)

  let rec elements_aux h acc = function
  | Leaf -> acc
  | Node (l, x, r, _) -> elements_aux h (x :: (elements_aux h acc r)) l

  (** val elements : 'a1 orderedType -> 'a1 tree -> 'a1 list **)

  let elements h =
    elements_aux h []

  (** val filter_acc :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let rec filter_acc h f acc = function
  | Leaf -> acc
  | Node (l, x, r, _) ->
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
  | Node (l, x, r, _) ->
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
  | Node (l, x, r, _) ->
    if if f x then for_all h f l else false then for_all h f r else false

  (** val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool **)

  let rec exists_ h f = function
  | Leaf -> false
  | Node (l, x, r, _) ->
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
    | Node (l, x0, r, _) -> fold h f r (f x0 (fold h f l x))

  (** val subsetl :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)

  let rec subsetl h subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, _) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl h subset_l1 x1 l2
     | Gt -> if mem h x1 r2 then subset_l1 s2 else false)

  (** val subsetr :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)

  let rec subsetr h subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, _) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem h x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr h subset_r1 x1 r2)

  (** val subset : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool **)

  let rec subset h s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (l1, x1, r1, _) ->
      (match s2 with
       | Leaf -> false
       | Node (l2, x2, r2, _) ->
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
  | More (e0, t, e1) -> f0 e0 t e1 (enumeration_rect h f f0 e1)

  (** val enumeration_rec :
      'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
      'a2) -> 'a1 enumeration -> 'a2 **)

  let rec enumeration_rec h f f0 = function
  | End -> f
  | More (e0, t, e1) -> f0 e0 t e1 (enumeration_rec h f f0 e1)

  (** val cons :
      'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons h s e =
    match s with
    | Leaf -> e
    | Node (l, x, r, _) -> cons h l (More (x, r, e))

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
    | Node (l1, x1, r1, _) ->
      compare_cont h l1 (compare_more h x1 (compare_cont h r1 cont)) e2

  (** val compare_end : 'a1 orderedType -> 'a1 enumeration -> comparison **)

  let compare_end _ = function
  | End -> Eq
  | More (_, _, _) -> Lt

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
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
      coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect h x f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_mem_2 (s, l, y, r0, _x, _res, r1) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_mem_rect h x f f0 f1 f2 l _res r1)
  | R_mem_3 (s, l, y, r0, _x, _res, r1) ->
    f2 s l y r0 _x __ __ _res r1 (coq_R_mem_rect h x f f0 f1 f2 r0 _res r1)

  (** val coq_R_mem_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
      coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec h x f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_mem_2 (s, l, y, r0, _x, _res, r1) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_mem_rec h x f f0 f1 f2 l _res r1)
  | R_mem_3 (s, l, y, r0, _x, _res, r1) ->
    f2 s l y r0 _x __ __ _res r1 (coq_R_mem_rec h x f f0 f1 f2 r0 _res r1)

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

  (** val coq_R_bal_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
      'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
      __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) ->
      ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

  let coq_R_bal_rect _ f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ = function
  | R_bal_0 (x, x0, x1) -> f x x0 x1 __ __ __
  | R_bal_1 (x, x0, x1, x2, x3, x4, x5) ->
    f0 x x0 x1 __ __ x2 x3 x4 x5 __ __ __
  | R_bal_2 (x, x0, x1, x2, x3, x4, x5) ->
    f1 x x0 x1 __ __ x2 x3 x4 x5 __ __ __ __
  | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
    f2 x x0 x1 __ __ x2 x3 x4 x5 __ __ __ x6 x7 x8 x9 __
  | R_bal_4 (x, x0, x1) -> f3 x x0 x1 __ __ __ __ __
  | R_bal_5 (x, x0, x1, x2, x3, x4, x5) ->
    f4 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __
  | R_bal_6 (x, x0, x1, x2, x3, x4, x5) ->
    f5 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __ __
  | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
    f6 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __ x6 x7 x8 x9 __
  | R_bal_8 (x, x0, x1) -> f7 x x0 x1 __ __ __ __

  (** val coq_R_bal_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
      'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
      __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) ->
      ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

  let coq_R_bal_rec _ f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ = function
  | R_bal_0 (x, x0, x1) -> f x x0 x1 __ __ __
  | R_bal_1 (x, x0, x1, x2, x3, x4, x5) ->
    f0 x x0 x1 __ __ x2 x3 x4 x5 __ __ __
  | R_bal_2 (x, x0, x1, x2, x3, x4, x5) ->
    f1 x x0 x1 __ __ x2 x3 x4 x5 __ __ __ __
  | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
    f2 x x0 x1 __ __ x2 x3 x4 x5 __ __ __ x6 x7 x8 x9 __
  | R_bal_4 (x, x0, x1) -> f3 x x0 x1 __ __ __ __ __
  | R_bal_5 (x, x0, x1, x2, x3, x4, x5) ->
    f4 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __
  | R_bal_6 (x, x0, x1, x2, x3, x4, x5) ->
    f5 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __ __
  | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
    f6 x x0 x1 __ __ __ __ x2 x3 x4 x5 __ __ __ x6 x7 x8 x9 __
  | R_bal_8 (x, x0, x1) -> f7 x x0 x1 __ __ __ __

  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
      -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect h x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, l, y, r0, h0) -> f0 s l y r0 h0 __ __
  | R_add_2 (s, l, y, r0, h0, _res, r1) ->
    f1 s l y r0 h0 __ __ _res r1 (coq_R_add_rect h x f f0 f1 f2 l _res r1)
  | R_add_3 (s, l, y, r0, h0, _res, r1) ->
    f2 s l y r0 h0 __ __ _res r1 (coq_R_add_rect h x f f0 f1 f2 r0 _res r1)

  (** val coq_R_add_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
      -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec h x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, l, y, r0, h0) -> f0 s l y r0 h0 __ __
  | R_add_2 (s, l, y, r0, h0, _res, r1) ->
    f1 s l y r0 h0 __ __ _res r1 (coq_R_add_rec h x f f0 f1 f2 l _res r1)
  | R_add_3 (s, l, y, r0, h0, _res, r1) ->
    f2 s l y r0 h0 __ __ _res r1 (coq_R_add_rec h x f f0 f1 f2 r0 _res r1)

  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * z * ('elt tree * 'elt) * 'elt coq_R_remove_min * 'elt tree
     * 'elt

  (** val coq_R_remove_min_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 ->
      __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
      coq_R_remove_min -> 'a2 **)

  let rec coq_R_remove_min_rect h f f0 _ _ _ _ = function
  | R_remove_min_0 (l, x, r0) -> f l x r0 __
  | R_remove_min_1 (l, x, r0, ll, lx, lr, _x, _res, r1, l', m) ->
    f0 l x r0 ll lx lr _x __ _res r1
      (coq_R_remove_min_rect h f f0 ll lx lr _res r1) l' m __

  (** val coq_R_remove_min_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 ->
      __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
      coq_R_remove_min -> 'a2 **)

  let rec coq_R_remove_min_rec h f f0 _ _ _ _ = function
  | R_remove_min_0 (l, x, r0) -> f l x r0 __
  | R_remove_min_1 (l, x, r0, ll, lx, lr, _x, _res, r1, l', m) ->
    f0 l x r0 ll lx lr _x __ _res r1
      (coq_R_remove_min_rec h f f0 ll lx lr _res r1) l' m __

  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  (** val coq_R_merge_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

  let coq_R_merge_rect _ f f0 f1 _ _ _ = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __

  (** val coq_R_merge_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

  let coq_R_merge_rec _ f f0 f1 _ _ _ = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
      -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect h x f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_remove_2 (s, l, y, r0, _x, _res, r1) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_remove_rect h x f f0 f1 f2 l _res r1)
  | R_remove_3 (s, l, y, r0, _x, _res, r1) ->
    f2 s l y r0 _x __ __ _res r1
      (coq_R_remove_rect h x f f0 f1 f2 r0 _res r1)

  (** val coq_R_remove_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
      -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec h x f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_remove_2 (s, l, y, r0, _x, _res, r1) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_remove_rec h x f f0 f1 f2 l _res r1)
  | R_remove_3 (s, l, y, r0, _x, _res, r1) ->
    f2 s l y r0 _x __ __ _res r1 (coq_R_remove_rec h x f f0 f1 f2 r0 _res r1)

  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_min_elt

  (** val coq_R_min_elt_rect :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      'a1 option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      option -> 'a1 coq_R_min_elt -> 'a2 **)

  let rec coq_R_min_elt_rect h f f0 f1 _ _ = function
  | R_min_elt_0 s -> f s __
  | R_min_elt_1 (s, l, y, _x, _x0) -> f0 s l y _x _x0 __ __
  | R_min_elt_2 (s, l, y, _x, _x0, _x1, _x2, _x3, _x4, _res, r0) ->
    f1 s l y _x _x0 __ _x1 _x2 _x3 _x4 __ _res r0
      (coq_R_min_elt_rect h f f0 f1 l _res r0)

  (** val coq_R_min_elt_rec :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      'a1 option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      option -> 'a1 coq_R_min_elt -> 'a2 **)

  let rec coq_R_min_elt_rec h f f0 f1 _ _ = function
  | R_min_elt_0 s -> f s __
  | R_min_elt_1 (s, l, y, _x, _x0) -> f0 s l y _x _x0 __ __
  | R_min_elt_2 (s, l, y, _x, _x0, _x1, _x2, _x3, _x4, _res, r0) ->
    f1 s l y _x _x0 __ _x1 _x2 _x3 _x4 __ _res r0
      (coq_R_min_elt_rec h f f0 f1 l _res r0)

  type 'elt coq_R_max_elt =
  | R_max_elt_0 of 'elt tree
  | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_max_elt

  (** val coq_R_max_elt_rect :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      'a1 option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      option -> 'a1 coq_R_max_elt -> 'a2 **)

  let rec coq_R_max_elt_rect h f f0 f1 _ _ = function
  | R_max_elt_0 s -> f s __
  | R_max_elt_1 (s, _x, y, r0, _x0) -> f0 s _x y r0 _x0 __ __
  | R_max_elt_2 (s, _x, y, r0, _x0, _x1, _x2, _x3, _x4, _res, r1) ->
    f1 s _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ _res r1
      (coq_R_max_elt_rect h f f0 f1 r0 _res r1)

  (** val coq_R_max_elt_rec :
      'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
      'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      'a1 option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      option -> 'a1 coq_R_max_elt -> 'a2 **)

  let rec coq_R_max_elt_rec h f f0 f1 _ _ = function
  | R_max_elt_0 s -> f s __
  | R_max_elt_1 (s, _x, y, r0, _x0) -> f0 s _x y r0 _x0 __ __
  | R_max_elt_2 (s, _x, y, r0, _x0, _x1, _x2, _x3, _x4, _res, r1) ->
    f1 s _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ _res r1
      (coq_R_max_elt_rec h f f0 f1 r0 _res r1)

  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt

  (** val coq_R_concat_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2 **)

  let coq_R_concat_rect _ f f0 f1 _ _ _ = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __

  (** val coq_R_concat_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2 **)

  let coq_R_concat_rec _ f f0 f1 _ _ _ = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __

  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree

  (** val coq_R_split_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)

  let rec coq_R_split_rect h x f f0 f1 f2 _ _ = function
  | R_split_0 s -> f s __
  | R_split_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_split_2 (s, l, y, r0, _x, _res, r1, ll, b, rl) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_split_rect h x f f0 f1 f2 l _res r1)
      ll b rl __
  | R_split_3 (s, l, y, r0, _x, _res, r1, rl, b, rr) ->
    f2 s l y r0 _x __ __ _res r1 (coq_R_split_rect h x f f0 f1 f2 r0 _res r1)
      rl b rr __

  (** val coq_R_split_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)

  let rec coq_R_split_rec h x f f0 f1 f2 _ _ = function
  | R_split_0 s -> f s __
  | R_split_1 (s, l, y, r0, _x) -> f0 s l y r0 _x __ __
  | R_split_2 (s, l, y, r0, _x, _res, r1, ll, b, rl) ->
    f1 s l y r0 _x __ __ _res r1 (coq_R_split_rec h x f f0 f1 f2 l _res r1)
      ll b rl __
  | R_split_3 (s, l, y, r0, _x, _res, r1, rl, b, rr) ->
    f2 s l y r0 _x __ __ _res r1 (coq_R_split_rec h x f f0 f1 f2 r0 _res r1)
      rl b rr __

  type 'elt coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter

  (** val coq_R_inter_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter ->
      'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 **)

  let rec coq_R_inter_rect h f f0 f1 f2 _ _ _ = function
  | R_inter_0 (s1, s2) -> f s1 s2 __
  | R_inter_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_inter_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' _res r2)
  | R_inter_3 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               _res0, r0, _res, r2) ->
    f2 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' _res r2)

  (** val coq_R_inter_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter ->
      'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 **)

  let rec coq_R_inter_rec h f f0 f1 f2 _ _ _ = function
  | R_inter_0 (s1, s2) -> f s1 s2 __
  | R_inter_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_inter_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' _res r2)
  | R_inter_3 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               _res0, r0, _res, r2) ->
    f2 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' _res r2)

  type 'elt coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff

  (** val coq_R_diff_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
      'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 **)

  let rec coq_R_diff_rect h f f0 f1 f2 _ _ _ = function
  | R_diff_0 (s1, s2) -> f s1 s2 __
  | R_diff_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_diff_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' _res r2)
  | R_diff_3 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              _res0, r0, _res, r2) ->
    f2 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' _res r2)

  (** val coq_R_diff_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
      'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 **)

  let rec coq_R_diff_rec h f f0 f1 f2 _ _ _ = function
  | R_diff_0 (s1, s2) -> f s1 s2 __
  | R_diff_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_diff_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' _res r2)
  | R_diff_3 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              _res0, r0, _res, r2) ->
    f2 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ _res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' _res0 r0) _res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' _res r2)

  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_union * 'elt tree * 'elt coq_R_union

  (** val coq_R_union_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 **)

  let rec coq_R_union_rect h f f0 f1 _ _ _ = function
  | R_union_0 (s1, s2) -> f s1 s2 __
  | R_union_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_union_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ _res0 r0
      (coq_R_union_rect h f f0 f1 l1 l2' _res0 r0) _res r2
      (coq_R_union_rect h f f0 f1 r1 r2' _res r2)

  (** val coq_R_union_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 **)

  let rec coq_R_union_rec h f f0 f1 _ _ _ = function
  | R_union_0 (s1, s2) -> f s1 s2 __
  | R_union_1 (s1, s2, l1, x1, r1, _x) -> f0 s1 s2 l1 x1 r1 _x __ __
  | R_union_2 (s1, s2, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               _res0, r0, _res, r2) ->
    f1 s1 s2 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ _res0 r0
      (coq_R_union_rec h f f0 f1 l1 l2' _res0 r0) _res r2
      (coq_R_union_rec h f f0 f1 r1 r2' _res r2)

  (** val fold' :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let fold' helt f s =
    SetList.fold helt f (elements helt s)

  (** val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list **)

  let rec flatten_e helt = function
  | End -> []
  | More (x, t, r) -> x :: (app (elements helt t) (flatten_e helt r))
 end

module S = SetAVL

type 'elt set0 =
  'elt S.tree
  (* singleton inductive, whose constructor was Bst *)

(** val this : 'a1 orderedType -> 'a1 set0 -> 'a1 S.tree **)

let this _ s =
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

(** val cardinal0 : 'a1 orderedType -> 'a1 set0 -> int **)

let cardinal0 helt s =
  S.cardinal helt (this helt s)

(** val filter1 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 **)

let filter1 helt f s =
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

(** val set_compare :
    'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> comparison **)

let set_compare h s1 s2 =
  S.compare h (this h s1) (this h s2)

(** val set_OrderedType : 'a1 orderedType -> 'a1 set0 specificOrderedType **)

let set_OrderedType h =
  set_compare h

(** val setAVL_FSet : 'a1 orderedType -> 'a1 fSet **)

let setAVL_FSet helt =
  { empty = (Obj.magic empty0 helt); is_empty = (Obj.magic is_empty0 helt);
    mem = (Obj.magic mem0 helt); add0 = (Obj.magic add1 helt); singleton =
    (Obj.magic singleton0 helt); remove = (Obj.magic remove0 helt); union =
    (Obj.magic union0 helt); inter = (Obj.magic inter0 helt); diff =
    (Obj.magic diff0 helt); equal = (Obj.magic equal0 helt); subset =
    (Obj.magic subset0 helt); fold = (Obj.magic (fun _ -> fold0 helt));
    for_all = (Obj.magic for_all0 helt); exists_ = (Obj.magic exists_0 helt);
    filter0 = (Obj.magic filter1 helt); partition =
    (Obj.magic partition0 helt); cardinal = (Obj.magic cardinal0 helt);
    elements = (Obj.magic elements0 helt); choose = (Obj.magic choose0 helt);
    min_elt = (Obj.magic min_elt0 helt); max_elt = (Obj.magic max_elt0 helt);
    fSet_OrderedType = (Obj.magic set_OrderedType helt) }

(** val of_list : 'a1 orderedType -> 'a1 fSet -> 'a1 list -> 'a1 set **)

let of_list _ f l =
  fold_right f.add0 f.empty l

(** val to_list : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 list **)

let to_list _ f =
  f.elements

type 'a eqDec = 'a -> 'a -> bool

(** val nat_eq_eqdec : int eqDec **)

let nat_eq_eqdec =
  (=)

(** val bool_eqdec : bool eqDec **)

let bool_eqdec =
  bool_dec

type computable = bool

(** val inst_eq_cm : 'a1 eqDec -> 'a1 -> 'a1 -> computable **)

let inst_eq_cm h x y =
  h x y

(** val option_eq_dec : 'a1 eqDec -> 'a1 option -> 'a1 option -> bool **)

let option_eq_dec h x y =
  match x with
  | Some x0 ->
    (match y with
     | Some a0 -> h x0 a0
     | None -> false)
  | None ->
    (match y with
     | Some _ -> false
     | None -> true)

(** val inst_eq_dec_option : 'a1 eqDec -> 'a1 option eqDec **)

let inst_eq_dec_option h =
  option_eq_dec h

(** val equiv_computable : 'a1 orderedType -> 'a1 -> 'a1 -> computable **)

let equiv_computable h x y =
  let c = _cmp h x y in
  (match c with
   | Eq -> true
   | _ -> false)

(** val drop : int -> 'a1 list -> 'a1 list **)

let rec drop n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    xs)
    (fun n1 ->
    drop n1 (tl xs))
    n0

(** val take : int -> 'a1 list -> 'a1 list **)

let rec take n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    [])
    (fun n1 ->
    match l with
    | [] -> []
    | x :: l0 -> x :: (take n1 l0))
    n0

type 'a counted = { counted0 : ('a -> int); incc : ('a -> int -> 'a) }

(** val counted0 : 'a1 counted -> 'a1 -> int **)

let counted0 x = x.counted0

type var = int

(** val inst_eq_dec_var : var eqDec **)

let inst_eq_dec_var =
  nat_eq_eqdec

type lab =
  int
  (* singleton inductive, whose constructor was LabI *)

(** val labN : lab -> int **)

let labN x =
  x

(** val labInc : lab -> int -> lab **)

let labInc l d =
  add d l

(** val inst_counted_lab : lab counted **)

let inst_counted_lab =
  { counted0 = labN; incc = labInc }

(** val zeq : z -> z -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> bool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> bool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false

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

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : int **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_P_mod_two_p : positive -> int -> z **)

  let rec coq_P_mod_two_p p n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      Z0)
      (fun m ->
      match p with
      | XI q -> Z.succ_double (coq_P_mod_two_p q m)
      | XO q -> Z.double (coq_P_mod_two_p q m)
      | XH -> Zpos XH)
      n0

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> coq_P_mod_two_p p wordsize
  | Zneg p ->
    let r = coq_P_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> z **)

  let unsigned n0 =
    intval n0

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : z -> int **)

  let repr x =
    coq_Z_mod_modulus x

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    zeq x y

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    if lt x zero then one else zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    if zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus
    then zero
    else one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    if zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0
    then one
    else zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    if (&&) (lt x zero) (negb (eq (coq_and x (sub (shl one y) one)) zero))
    then one
    else zero

  (** val coq_Zshiftin : bool -> z -> z **)

  let coq_Zshiftin b x =
    if b then Z.succ_double x else Z.double x

  (** val coq_Zzero_ext : z -> z -> z **)

  let coq_Zzero_ext n0 x =
    Z.iter n0 (fun rec0 x0 -> coq_Zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
      (fun _ -> Z0) x

  (** val coq_Zsign_ext : z -> z -> z **)

  let coq_Zsign_ext n0 x =
    Z.iter (Z.pred n0) (fun rec0 x0 ->
      coq_Zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun x0 ->
      if Z.odd x0 then Zneg XH else Z0) x

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (coq_Zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (coq_Zsign_ext n0 (unsigned x))

  (** val coq_Z_one_bits : int -> z -> z -> z list **)

  let rec coq_Z_one_bits n0 x i =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      [])
      (fun m ->
      if Z.odd x
      then i :: (coq_Z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))
      else coq_Z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))
      n0

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (coq_Z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match coq_Z_one_bits wordsize (unsigned x) Z0 with
    | [] -> None
    | i :: l ->
      (match l with
       | [] -> Some (repr i)
       | _ :: _ -> None)

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    if eq x zero then one else zero

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val powerserie : z list -> z **)

  let rec powerserie = function
  | [] -> Z0
  | x :: xs -> Z.add (two_p x) (powerserie xs)

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | [] -> zero
  | a :: b -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (&&)
      ((&&) (proj_sumbool (zlt (Z.add x1 sz1) modulus))
        (proj_sumbool (zlt (Z.add x2 sz2) modulus)))
      ((||) (proj_sumbool (zle (Z.add x1 sz1) x2))
        (proj_sumbool (zle (Z.add x2 sz2) x1)))

  (** val coq_Zsize : z -> z **)

  let coq_Zsize = function
  | Zpos p -> Zpos (Coq_Pos.size p)
  | _ -> Z0

  (** val size : int -> z **)

  let size x =
    coq_Zsize (unsigned x)
 end

module Wordsize_32 =
 struct
  (** val wordsize : int **)

  let wordsize =
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

type val0 = Int.int

(** val val_zero : val0 **)

let val_zero =
  Int.zero

(** val inst_eq_dec_val : val0 eqDec **)

let inst_eq_dec_val x y =
  Int.eq_dec x y

type binop =
| BinOpAdd
| BinOpSub
| BinOpMul
| BinOpDiv
| BinOpEq

type unop =
| UnOpToBool
| UnOpNeg

(** val val2bool : val0 -> bool **)

let val2bool v =
  if inst_eq_cm inst_eq_dec_val v val_zero then false else true

(** val comp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3 **)

let comp f g x =
  g (f x)

type exp =
| Con of val0
| Var of var
| UnOp of unop * exp
| BinOp of binop * exp * exp

(** val freeVars : exp -> var set **)

let rec freeVars = function
| Con _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
| Var v -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton v
| UnOp (_, e0) -> freeVars e0
| BinOp (_, e1, e2) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union (freeVars e1) (freeVars e2)

(** val exp2bool : exp -> bool option **)

let exp2bool = function
| Con c -> Some (val2bool c)
| _ -> None

(** val zip : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec zip f l l' =
  match l with
  | [] -> []
  | x :: l0 ->
    (match l' with
     | [] -> []
     | y :: l'0 -> (f x y) :: (zip f l0 l'0))

(** val mapi_impl : (int -> 'a1 -> 'a2) -> int -> 'a1 list -> 'a2 list **)

let rec mapi_impl f n0 = function
| [] -> []
| x :: l0 -> (f n0 x) :: (mapi_impl f (Pervasives.succ n0) l0)

(** val mapi : (int -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f =
  mapi_impl f 0

type external0 = int

type 'a size0 = 'a -> int

(** val size1 : 'a1 size0 -> 'a1 -> int **)

let size1 size2 =
  size2

(** val size_rec :
    ('a1 -> int) -> 'a1 -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a2 **)

let size_rec f x iS =
  let h = fun n0 x0 ->
    let rec f0 n1 x1 =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        iS x1 (fun _ _ -> assert false (* absurd case *)))
        (fun n2 ->
        iS x1 (fun y _ -> f0 n2 y))
        n1
    in f0 n0 x0
  in
  iS x (fun y _ -> iS y (fun y0 _ -> iS y0 (fun y1 _ -> h (f y1) y1)))

(** val def_size : 'a1 size0 **)

let def_size _ =
  0

(** val size_list : 'a1 size0 -> 'a1 list size0 **)

let rec size_list size_A = function
| [] -> Pervasives.succ (size1 def_size __)
| a :: l -> Pervasives.succ (add (size1 size_A a) (size_list size_A l))

type stmt =
| StmtLet of var * exp * stmt
| StmtIf of exp * stmt * stmt
| StmtApp of lab * exp list
| StmtReturn of exp
| StmtExtern of var * external0 * exp list * stmt
| StmtFun of (var list * stmt) list * stmt

(** val occurVars : stmt -> var set **)

let rec occurVars = function
| StmtLet (x, e, s0) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x (occurVars s0))
    (freeVars e)
| StmtIf (e, s1, s2) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union (occurVars s1)
      (occurVars s2)) (freeVars e)
| StmtApp (_, y) ->
  fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union (map freeVars y)
    (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
| StmtReturn e -> freeVars e
| StmtExtern (x, _, y, s0) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x (occurVars s0))
    (fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
      (map freeVars y) (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
| StmtFun (s0, t) ->
  (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
    (fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
      (map (fun f ->
        (setAVL_FSet (sOT_as_OT nat_OrderedType)).union (occurVars (snd f))
          (of_list (sOT_as_OT nat_OrderedType)
            (setAVL_FSet (sOT_as_OT nat_OrderedType)) (fst f))) s0)
      (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty) (occurVars t)

type 'dom partialOrder = { poLe_dec : ('dom -> 'dom -> computable);
                           poEq_dec : ('dom -> 'dom -> computable) }

(** val poLe_dec : 'a1 partialOrder -> 'a1 -> 'a1 -> computable **)

let poLe_dec x = x.poLe_dec

(** val poEq_dec : 'a1 partialOrder -> 'a1 -> 'a1 -> computable **)

let poEq_dec x = x.poEq_dec

(** val partialOrder_sig : 'a1 partialOrder -> 'a1 partialOrder **)

let partialOrder_sig h =
  { poLe_dec = (fun d d' -> h.poLe_dec d d'); poEq_dec = (fun d d' ->
    h.poEq_dec d d') }

(** val partialOrder_bool : bool partialOrder **)

let partialOrder_bool =
  { poLe_dec = (fun d d' -> if d then if d' then true else false else true);
    poEq_dec = (inst_eq_cm bool_eqdec) }

(** val list_update_at : 'a1 list -> int -> 'a1 -> 'a1 list **)

let rec list_update_at l n0 v =
  match l with
  | [] -> []
  | x :: l0 ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ ->
       v :: l0)
       (fun n1 ->
       x :: (list_update_at l0 n1 v))
       n0)

type 'a ann =
| Ann0 of 'a
| Ann1 of 'a * 'a ann
| Ann2 of 'a * 'a ann * 'a ann
| AnnF of 'a * 'a ann list * 'a ann

(** val ann_size : 'a1 ann size0 **)

let rec ann_size = function
| Ann0 a -> Pervasives.succ (size1 def_size a)
| Ann1 (_, a0) -> Pervasives.succ (ann_size a0)
| Ann2 (_, a2, a3) -> Pervasives.succ (add (ann_size a2) (ann_size a3))
| AnnF (_, sa, a0) ->
  Pervasives.succ (add (size1 (size_list ann_size) sa) (ann_size a0))

(** val getAnn : 'a1 ann -> 'a1 **)

let getAnn = function
| Ann0 a0 -> a0
| Ann1 (a0, _) -> a0
| Ann2 (a0, _, _) -> a0
| AnnF (a0, _, _) -> a0

(** val setTopAnn : 'a1 ann -> 'a1 -> 'a1 ann **)

let setTopAnn s a =
  match s with
  | Ann0 _ -> Ann0 a
  | Ann1 (_, s') -> Ann1 (a, s')
  | Ann2 (_, s1, s2) -> Ann2 (a, s1, s2)
  | AnnF (_, s1, s2) -> AnnF (a, s1, s2)

(** val setAnn : 'a1 -> stmt -> 'a1 ann **)

let rec setAnn a = function
| StmtLet (_, _, s0) -> Ann1 (a, (setAnn a s0))
| StmtIf (_, s1, s2) -> Ann2 (a, (setAnn a s1), (setAnn a s2))
| StmtExtern (_, _, _, s0) -> Ann1 (a, (setAnn a s0))
| StmtFun (s0, s1) -> AnnF (a, (map (comp snd (setAnn a)) s0), (setAnn a s1))
| _ -> Ann0 a

(** val mapAnn : ('a1 -> 'a2) -> 'a1 ann -> 'a2 ann **)

let rec mapAnn f = function
| Ann0 a0 -> Ann0 (f a0)
| Ann1 (a0, an) -> Ann1 ((f a0), (mapAnn f an))
| Ann2 (a0, an1, an2) -> Ann2 ((f a0), (mapAnn f an1), (mapAnn f an2))
| AnnF (a0, an1, an2) -> AnnF ((f a0), (map (mapAnn f) an1), (mapAnn f an2))

(** val indexwise_R_dec' :
    'a1 list -> 'a2 list -> (int -> 'a1 -> 'a2 -> __ -> __ -> computable) ->
    computable **)

let rec indexwise_R_dec' lA lB rdec =
  match lA with
  | [] -> true
  | a :: lA0 ->
    (match lB with
     | [] -> true
     | b :: lB0 ->
       let c = rdec 0 a b __ __ in
       if c
       then indexwise_R_dec' lA0 lB0 (fun n0 a0 b0 _ _ ->
              rdec (Pervasives.succ n0) a0 b0 __ __)
       else false)

(** val ann_R_dec :
    ('a1 -> 'a2 -> computable) -> 'a1 ann -> 'a2 ann -> computable **)

let ann_R_dec h a b =
  size_rec (size1 ann_size) a (fun x x0 _ _ h0 b0 ->
    match x with
    | Ann0 a0 ->
      (match b0 with
       | Ann0 a1 -> h0 a0 a1
       | _ -> false)
    | Ann1 (a0, x1) ->
      (match b0 with
       | Ann1 (a1, b1) ->
         let s = h0 a0 a1 in if s then x0 x1 __ __ __ h0 b1 else false
       | _ -> false)
    | Ann2 (a0, x1, x2) ->
      (match b0 with
       | Ann2 (a1, b1, b2) ->
         let s = h0 a0 a1 in
         if s
         then let c = x0 x1 __ __ __ h0 b1 in
              if c then x0 x2 __ __ __ h0 b2 else false
         else false
       | _ -> false)
    | AnnF (a0, sa, x1) ->
      (match b0 with
       | AnnF (a1, sa0, b1) ->
         let s = h0 a0 a1 in
         if s
         then let s0 = inst_eq_cm inst_eq_dec_var (length sa) (length sa0) in
              if s0
              then let c = x0 x1 __ __ __ h0 b1 in
                   if c
                   then indexwise_R_dec' sa sa0 (fun _ a2 b2 _ _ ->
                          x0 a2 __ __ __ h0 b2)
                   else false
              else false
         else false
       | _ -> false)) __ __ h b

(** val partialOrder_ann : 'a1 partialOrder -> 'a1 ann partialOrder **)

let partialOrder_ann h =
  { poLe_dec = (ann_R_dec h.poLe_dec); poEq_dec = (ann_R_dec h.poEq_dec) }

type 'a status =
| Success of 'a
| Error of char list

(** val option2status : 'a1 option -> char list -> 'a1 status **)

let option2status x h =
  match x with
  | Some a -> Success a
  | None -> Error h

(** val smap : ('a1 -> 'a2 status) -> 'a1 list -> 'a2 list status **)

let rec smap f = function
| [] -> Success []
| x :: l0 ->
  (match f x with
   | Success a ->
     (match smap f l0 with
      | Success a0 -> Success (a :: a0)
      | Error e -> Error e)
   | Error e -> Error e)

(** val filter_by : ('a1 -> bool) -> 'a1 list -> 'a2 list -> 'a2 list **)

let rec filter_by f l l' =
  match l with
  | [] -> []
  | x :: l0 ->
    (match l' with
     | [] -> []
     | y :: l'0 ->
       if f x then y :: (filter_by f l0 l'0) else filter_by f l0 l'0)

(** val countTrue : bool list -> int **)

let rec countTrue = function
| [] -> 0
| b :: xs ->
  if b then add (Pervasives.succ 0) (countTrue xs) else countTrue xs

(** val mapOption : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let mapOption f = function
| Some a -> Some (f a)
| None -> None

(** val oget : 'a1 orderedType -> 'a1 set option -> 'a1 set **)

let oget h = function
| Some s0 -> s0
| None -> (setAVL_FSet h).empty

(** val oto_list : 'a1 orderedType -> 'a1 set option -> 'a1 list **)

let oto_list h = function
| Some s0 -> to_list h (setAVL_FSet h) s0
| None -> []

(** val ounion :
    'a1 orderedType -> 'a1 set option -> 'a1 set option -> 'a1 set option **)

let ounion h s t =
  match s with
  | Some s0 ->
    (match t with
     | Some t0 -> Some ((setAVL_FSet h).union s0 t0)
     | None -> Some s0)
  | None -> t

(** val pos : 'a1 orderedType -> 'a1 list -> 'a1 -> int -> int option **)

let rec pos h l x n0 =
  match l with
  | [] -> None
  | y :: l0 ->
    if equiv_computable h x y
    then Some n0
    else pos h l0 x (Pervasives.succ n0)

type nstmt =
| NstmtLet of var * exp * nstmt
| NstmtIf of exp * nstmt * nstmt
| NstmtApp of var * exp list
| NstmtReturn of exp
| NstmtExtern of var * external0 * exp list * nstmt
| NstmtFun of ((var * var list) * nstmt) list * nstmt

(** val labIndices : var list -> nstmt -> stmt status **)

let rec labIndices symb = function
| NstmtLet (x, e, s0) ->
  (match labIndices symb s0 with
   | Success a -> Success (StmtLet (x, e, a))
   | Error e0 -> Error e0)
| NstmtIf (x, s1, s2) ->
  (match labIndices symb s1 with
   | Success a ->
     (match labIndices symb s2 with
      | Success a0 -> Success (StmtIf (x, a, a0))
      | Error e -> Error e)
   | Error e -> Error e)
| NstmtApp (l, y) ->
  (match option2status (pos (sOT_as_OT nat_OrderedType) symb l 0)
           ('l'::('a'::('b'::('I'::('n'::('d'::('i'::('c'::('e'::('s'::(':'::(' '::('U'::('n'::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))) with
   | Success a -> Success (StmtApp (a, y))
   | Error e -> Error e)
| NstmtReturn x -> Success (StmtReturn x)
| NstmtExtern (x, f, y, s0) ->
  (match labIndices symb s0 with
   | Success a -> Success (StmtExtern (x, f, y, a))
   | Error e -> Error e)
| NstmtFun (f, s2) ->
  let fl = map (comp fst fst) f in
  (match smap (fun fZs ->
           match labIndices (app fl symb) (snd fZs) with
           | Success a -> Success ((snd (fst fZs)), a)
           | Error e -> Error e) f with
   | Success a ->
     (match labIndices (app fl symb) s2 with
      | Success a0 -> Success (StmtFun (a, a0))
      | Error e -> Error e)
   | Error e -> Error e)

type 'a boundedSemiLattice = { bottom : 'a; join0 : ('a -> 'a -> 'a) }

(** val bottom : 'a1 partialOrder -> 'a1 boundedSemiLattice -> 'a1 **)

let bottom _ x = x.bottom

(** val join0 :
    'a1 partialOrder -> 'a1 boundedSemiLattice -> 'a1 -> 'a1 -> 'a1 **)

let join0 _ x = x.join0

(** val bool_boundedsemilattice : bool boundedSemiLattice **)

let bool_boundedsemilattice =
  { bottom = false; join0 = (||) }

(** val sig_R_dec : ('a1 -> 'a1 -> computable) -> 'a1 -> 'a1 -> computable **)

let sig_R_dec h a b =
  h a b

type 'dom analysis = { dom_po : 'dom partialOrder;
                       analysis_step : ('dom -> 'dom); initial_value : 
                       'dom }

(** val dom_po : 'a1 analysis -> 'a1 partialOrder **)

let dom_po x = x.dom_po

(** val analysis_step : 'a1 analysis -> 'a1 -> 'a1 **)

let analysis_step x = x.analysis_step

(** val initial_value : 'a1 analysis -> 'a1 **)

let initial_value x = x.initial_value

(** val safeFirst : 'a1 analysis -> 'a1 -> 'a1 **)

let rec safeFirst analysis0 d =
  let s = analysis0.dom_po.poLe_dec (analysis0.analysis_step d) d in
  if s
  then analysis0.analysis_step d
  else safeFirst analysis0 (analysis0.analysis_step d)

(** val safeFixpoint : 'a1 analysis -> 'a1 **)

let safeFixpoint analysis0 =
  safeFirst analysis0 analysis0.initial_value

type 'a anni =
| Anni0
| Anni1 of 'a
| Anni2 of 'a * 'a
| Anni2opt of 'a option * 'a option

(** val mapAnni : ('a1 -> 'a2) -> 'a1 anni -> 'a2 anni **)

let mapAnni f = function
| Anni0 -> Anni0
| Anni1 a1 -> Anni1 (f a1)
| Anni2 (a1, a2) -> Anni2 ((f a1), (f a2))
| Anni2opt (o1, o2) -> Anni2opt ((mapOption f o1), (mapOption f o2))

(** val getAnni : 'a1 -> 'a1 anni -> 'a1 **)

let getAnni a = function
| Anni1 a0 -> a0
| _ -> a

(** val getAnniLeft : 'a1 -> 'a1 anni -> 'a1 **)

let getAnniLeft a = function
| Anni2 (a0, _) -> a0
| _ -> a

(** val getAnniRight : 'a1 -> 'a1 anni -> 'a1 **)

let getAnniRight a = function
| Anni2 (_, a0) -> a0
| _ -> a

(** val keep : int -> 'a1 list -> 'a1 option list **)

let keep m aP =
  mapi (fun n0 x -> if inst_eq_cm nat_eq_eqdec n0 m then Some x else None) aP

(** val backwardF :
    stmt -> (var list list -> 'a1 list -> stmt -> __ -> 'a1 ann -> 'a1 ann)
    -> var list list -> 'a1 list -> (var list * stmt) list -> 'a1 ann list ->
    'a1 ann list **)

let rec backwardF sT backward0 zL aL f anF =
  match f with
  | [] -> []
  | p :: x ->
    let (_, s) = p in
    (match anF with
     | [] -> []
     | a :: anF' ->
       (backward0 zL aL s __ a) :: (backwardF sT backward0 zL aL x anF'))

(** val backward :
    stmt -> (stmt -> var list list -> 'a1 list -> stmt -> __ -> 'a1 anni ->
    'a1) -> var list list -> 'a1 list -> stmt -> 'a1 ann -> 'a1 ann **)

let rec backward sT btransform zL aL st a =
  match st with
  | StmtLet (_, _, s) ->
    (match a with
     | Ann1 (_, ans) ->
       let ans' = backward sT btransform zL aL s ans in
       let ai = Anni1 (getAnn ans') in
       let d = btransform sT zL aL st __ ai in Ann1 (d, ans')
     | _ -> a)
  | StmtIf (_, s, t) ->
    (match a with
     | Ann2 (_, ans, ant) ->
       let ans' = backward sT btransform zL aL s ans in
       let ant' = backward sT btransform zL aL t ant in
       let ai = Anni2 ((getAnn ans'), (getAnn ant')) in
       let d' = btransform sT zL aL st __ ai in Ann2 (d', ans', ant')
     | _ -> a)
  | StmtApp (_, _) ->
    (match a with
     | Ann0 _ -> Ann0 (btransform sT zL aL st __ Anni0)
     | _ -> a)
  | StmtReturn _ ->
    (match a with
     | Ann0 _ -> Ann0 (btransform sT zL aL st __ Anni0)
     | _ -> a)
  | StmtExtern (_, _, _, s) ->
    (match a with
     | Ann1 (_, ans) ->
       let ans' = backward sT btransform zL aL s ans in
       let ai = Anni1 (getAnn ans') in
       let d' = btransform sT zL aL st __ ai in Ann1 (d', ans')
     | _ -> a)
  | StmtFun (f, t) ->
    (match a with
     | AnnF (_, anF, ant) ->
       let aLinit = app (map getAnn anF) aL in
       let zL' = app (map fst f) zL in
       let anF' =
         backwardF sT (fun x x0 x1 _ -> backward sT btransform x x0 x1) zL'
           aLinit f anF
       in
       let aL' = app (map getAnn anF') aL in
       let ant' = backward sT btransform zL' aL' t ant in
       let ai = Anni1 (getAnn ant') in
       let d' = btransform sT zL' aL' st __ ai in AnnF (d', anF', ant')
     | _ -> a)

(** val makeBackwardAnalysis :
    (stmt -> 'a1 partialOrder) -> (stmt -> 'a1 boundedSemiLattice) -> (stmt
    -> var list list -> 'a1 list -> stmt -> __ -> 'a1 anni -> 'a1) -> stmt ->
    'a1 ann analysis **)

let makeBackwardAnalysis h bSL f s =
  { dom_po = (partialOrder_sig (partialOrder_ann (h s))); analysis_step =
    (fun x -> backward s f [] [] s x); initial_value =
    (setAnn (bSL s).bottom s) }

(** val partialOrder_Subset_Equal_Bounded :
    'a1 orderedType -> 'a1 set -> 'a1 set partialOrder **)

let partialOrder_Subset_Equal_Bounded h _ =
  { poLe_dec = (fun x y ->
    sig_R_dec (fun s t -> if (setAVL_FSet h).subset s t then true else false)
      x y); poEq_dec = (fun x y ->
    sig_R_dec (fun s t -> if (setAVL_FSet h).equal s t then true else false)
      x y) }

(** val set_var_semilattice_bounded :
    var set -> var set boundedSemiLattice **)

let set_var_semilattice_bounded _ =
  { bottom = (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty; join0 =
    (fun x y -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).union x y) }

(** val liveness_transform :
    var list list -> var set list -> stmt -> var set anni -> var set **)

let liveness_transform zL dL st a =
  match st with
  | StmtLet (x, e, _) ->
    (match a with
     | Anni1 d ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff d
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton x))
         (if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x d
          then freeVars e
          else (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtIf (e, _, _) ->
    (match a with
     | Anni2 (ds, dt) ->
       if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some true)
       then ds
       else if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some
                 false)
            then dt
            else (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
                   ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union
                     (freeVars e) ds) dt
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtApp (f, y) ->
    (match a with
     | Anni0 ->
       let lv =
         nth (inst_counted_lab.counted0 f) dL
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
       in
       let z0 = nth (inst_counted_lab.counted0 f) zL [] in
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff lv
           (of_list (sOT_as_OT nat_OrderedType)
             (setAVL_FSet (sOT_as_OT nat_OrderedType)) z0))
         (fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
           (map freeVars
             (filter_by (fun x ->
               (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x lv) z0 y))
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtReturn e ->
    (match a with
     | Anni0 -> freeVars e
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtExtern (x, _, y, _) ->
    (match a with
     | Anni1 d ->
       (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
         ((setAVL_FSet (sOT_as_OT nat_OrderedType)).diff d
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton x))
         (fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
           (map freeVars y) (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  | StmtFun (_, _) ->
    (match a with
     | Anni1 dt -> dt
     | _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)

(** val liveness_transform_dep :
    stmt -> var list list -> var set list -> stmt -> var set anni -> var set **)

let liveness_transform_dep _ zL dL s a =
  liveness_transform zL (map (fun e -> e) dL) s (mapAnni (fun e -> e) a)

(** val liveness_analysis : stmt -> var set ann analysis **)

let liveness_analysis =
  makeBackwardAnalysis (fun sT ->
    partialOrder_Subset_Equal_Bounded (sOT_as_OT nat_OrderedType)
      (occurVars sT)) (fun s -> set_var_semilattice_bounded (occurVars s))
    (fun x x0 x1 x2 _ -> liveness_transform_dep x x0 x1 x2)

(** val livenessAnalysis : stmt -> var set ann **)

let livenessAnalysis s =
  let a = safeFixpoint (liveness_analysis s) in mapAnn (fun e -> e) a

(** val compileF :
    (var list list -> stmt -> var list list ann -> stmt) -> var list list ->
    (var list * stmt) list -> var list list -> var list list -> var list list
    ann list -> (var list * stmt) list **)

let compileF compile2 zL f za za' ans =
  zip (fun zs zaans -> ((app (fst zs) (fst zaans)),
    (compile2 (app za' zL) (snd zs) (snd zaans)))) f
    (zip (fun x x0 -> (x, x0)) za ans)

(** val compile : var list list -> stmt -> var list list ann -> stmt **)

let rec compile zL s an =
  match s with
  | StmtLet (x, e, s0) ->
    (match an with
     | Ann1 (_, an0) -> StmtLet (x, e, (compile zL s0 an0))
     | _ -> s)
  | StmtIf (e, s0, t) ->
    (match an with
     | Ann2 (_, ans, ant) ->
       StmtIf (e, (compile zL s0 ans), (compile zL t ant))
     | _ -> s)
  | StmtApp (f, y) ->
    (match an with
     | Ann0 _ ->
       StmtApp (f,
         (app y
           (map (fun x -> Var x) (nth (inst_counted_lab.counted0 f) zL []))))
     | _ -> s)
  | StmtReturn e ->
    (match an with
     | Ann0 _ -> StmtReturn e
     | _ -> s)
  | StmtExtern (x, f, y, s0) ->
    (match an with
     | Ann1 (_, an0) -> StmtExtern (x, f, y, (compile zL s0 an0))
     | _ -> s)
  | StmtFun (f, t) ->
    (match an with
     | AnnF (za, ans, ant) ->
       StmtFun ((compileF compile zL f za za ans),
         (compile (app za zL) t ant))
     | _ -> s)

(** val addParam : var -> var set list -> var set list -> var set list **)

let addParam x dL aP =
  zip (fun dL0 aP0 ->
    if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x dL0
    then (setAVL_FSet (sOT_as_OT nat_OrderedType)).add0 x aP0
    else aP0) dL aP

(** val addAdd : var set -> var set -> var set option -> var set option **)

let addAdd s dL = function
| Some a ->
  Some
    ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union
      ((setAVL_FSet (sOT_as_OT nat_OrderedType)).inter s dL) a)
| None -> None

(** val computeParameters :
    var set list -> var list list -> var set list -> stmt -> var set ann ->
    var list list ann * var set option list **)

let rec computeParameters dL zL aP s an =
  match s with
  | StmtLet (x, _, s0) ->
    (match an with
     | Ann1 (_, an0) ->
       let (ar, r) = computeParameters dL zL (addParam x dL aP) s0 an0 in
       ((Ann1 ([], ar)), r)
     | _ -> ((Ann0 []), []))
  | StmtIf (_, s0, t) ->
    (match an with
     | Ann2 (_, ans, ant) ->
       let (ars, rs) = computeParameters dL zL aP s0 ans in
       let (art, rt) = computeParameters dL zL aP t ant in
       ((Ann2 ([], ars, art)),
       (zip (ounion (sOT_as_OT nat_OrderedType)) rs rt))
     | _ -> ((Ann0 []), []))
  | StmtApp (f, _) ->
    (match an with
     | Ann0 _ -> ((Ann0 []), (keep (inst_counted_lab.counted0 f) aP))
     | _ -> ((Ann0 []), []))
  | StmtReturn _ ->
    (match an with
     | Ann0 _ -> ((Ann0 []), (map (fun _ -> None) aP))
     | _ -> ((Ann0 []), []))
  | StmtExtern (x, _, _, s0) ->
    (match an with
     | Ann1 (_, an0) ->
       let (ar, r) = computeParameters dL zL (addParam x dL aP) s0 an0 in
       ((Ann1 ([], ar)), r)
     | _ -> ((Ann0 []), []))
  | StmtFun (f, t) ->
    (match an with
     | AnnF (_, ans, ant) ->
       let dL' =
         zip (fun s0 l ->
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).diff s0
             (of_list (sOT_as_OT nat_OrderedType)
               (setAVL_FSet (sOT_as_OT nat_OrderedType)) l)) (map getAnn ans)
           (map fst f)
       in
       let z0 = map fst f in
       let zset =
         fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
           (map
             (comp fst
               (of_list (sOT_as_OT nat_OrderedType)
                 (setAVL_FSet (sOT_as_OT nat_OrderedType)))) f)
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
       in
       let aP' =
         app
           (map (fun _ -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty) f)
           aP
       in
       let ars_rF =
         zip (fun zs a ->
           computeParameters (app dL' dL) (app z0 zL) aP' (snd zs) a) f ans
       in
       let (art, rt) = computeParameters (app dL' dL) (app z0 zL) aP' t ant
       in
       let rFt =
         fold_left (zip (ounion (sOT_as_OT nat_OrderedType)))
           (map snd ars_rF) rt
       in
       let zaF =
         fold_left (setAVL_FSet (sOT_as_OT nat_OrderedType)).union
           (map (oget (sOT_as_OT nat_OrderedType)) (take (length f) rFt))
           (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
       in
       let ur =
         zip
           (addAdd
             ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union zaF zset))
           (app dL' dL) rFt
       in
       ((AnnF
       ((map (oto_list (sOT_as_OT nat_OrderedType)) (take (length f) ur)),
       (map fst ars_rF), art)), (drop (length f) ur))
     | _ -> ((Ann0 []), []))

(** val compileF0 :
    ((bool * var list) list -> stmt -> bool ann -> stmt) -> (bool * var list)
    list -> (var list * stmt) list -> bool ann list -> (var list * stmt) list **)

let rec compileF0 compile2 rZL f ans =
  match f with
  | [] -> []
  | p :: f0 ->
    let (z0, s) = p in
    (match ans with
     | [] -> []
     | a :: ans0 ->
       if getAnn a
       then (z0, (compile2 rZL s a)) :: (compileF0 compile2 rZL f0 ans0)
       else compileF0 compile2 rZL f0 ans0)

(** val compile0 : (bool * var list) list -> stmt -> bool ann -> stmt **)

let rec compile0 rZL s a =
  match s with
  | StmtLet (x, e, s0) ->
    (match a with
     | Ann1 (_, an) -> StmtLet (x, e, (compile0 rZL s0 an))
     | _ -> s)
  | StmtIf (e, s0, t) ->
    (match a with
     | Ann2 (_, ans, ant) ->
       if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some true)
       then compile0 rZL s0 ans
       else if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some
                 false)
            then compile0 rZL t ant
            else StmtIf (e, (compile0 rZL s0 ans), (compile0 rZL t ant))
     | _ -> s)
  | StmtApp (f, y) ->
    (match a with
     | Ann0 _ ->
       StmtApp
         ((countTrue (map fst (take (inst_counted_lab.counted0 f) rZL))), y)
     | _ -> s)
  | StmtReturn x ->
    (match a with
     | Ann0 _ -> StmtReturn x
     | _ -> s)
  | StmtExtern (x, f, e, s0) ->
    (match a with
     | Ann1 (_, an) -> StmtExtern (x, f, e, (compile0 rZL s0 an))
     | _ -> s)
  | StmtFun (f, t) ->
    (match a with
     | AnnF (_, ans, ant) ->
       let lV' =
         app (zip (fun x x0 -> (x, x0)) (map getAnn ans) (map fst f)) rZL
       in
       let f' = compileF0 compile0 lV' f ans in
       (match f' with
        | [] -> compile0 lV' t ant
        | _ :: _ -> StmtFun (f', (compile0 lV' t ant)))
     | _ -> s)

(** val filter2 : var list -> var set -> var list **)

let filter2 z0 lv =
  filter (fun x -> (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x lv) z0

(** val compile1 :
    (var set * var list) list -> stmt -> var set ann -> stmt **)

let rec compile1 lV s a =
  match s with
  | StmtLet (x, e, s0) ->
    (match a with
     | Ann1 (_, an) ->
       if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x (getAnn an)
       then StmtLet (x, e, (compile1 lV s0 an))
       else compile1 lV s0 an
     | _ -> s)
  | StmtIf (e, s0, t) ->
    (match a with
     | Ann2 (_, ans, ant) ->
       if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some true)
       then compile1 lV s0 ans
       else if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some
                 false)
            then compile1 lV t ant
            else StmtIf (e, (compile1 lV s0 ans), (compile1 lV t ant))
     | _ -> s)
  | StmtApp (f, y) ->
    (match a with
     | Ann0 _ ->
       let lvZ =
         nth (inst_counted_lab.counted0 f) lV
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).empty, [])
       in
       StmtApp (f,
       (filter_by (fun y0 ->
         (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem y0 (fst lvZ))
         (snd lvZ) y))
     | _ -> s)
  | StmtReturn x ->
    (match a with
     | Ann0 _ -> StmtReturn x
     | _ -> s)
  | StmtExtern (x, f, e, s0) ->
    (match a with
     | Ann1 (_, an) -> StmtExtern (x, f, e, (compile1 lV s0 an))
     | _ -> s)
  | StmtFun (f, t) ->
    (match a with
     | AnnF (_, ans, ant) ->
       let lV' =
         app (zip (fun x x0 -> (x, x0)) (map getAnn ans) (map fst f)) lV
       in
       StmtFun
       ((zip (fun zs a0 -> ((filter2 (fst zs) (getAnn a0)),
          (compile1 lV' (snd zs) a0))) f ans), (compile1 lV' t ant))
     | _ -> s)

(** val compile_live : stmt -> var set ann -> var set -> var set ann **)

let rec compile_live s a g =
  match s with
  | StmtLet (x, _, s0) ->
    (match a with
     | Ann1 (lv, an) ->
       if (setAVL_FSet (sOT_as_OT nat_OrderedType)).mem x (getAnn an)
       then Ann1 (((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g lv),
              (compile_live s0 an
                ((setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton x)))
       else compile_live s0 an g
     | _ -> a)
  | StmtIf (e, s0, t) ->
    (match a with
     | Ann2 (lv, ans, ant) ->
       if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some true)
       then compile_live s0 ans g
       else if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some
                 false)
            then compile_live t ant g
            else Ann2
                   (((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g lv),
                   (compile_live s0 ans
                     (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty),
                   (compile_live t ant
                     (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty))
     | _ -> a)
  | StmtExtern (x, _, _, s0) ->
    (match a with
     | Ann1 (lv, an) ->
       Ann1 (((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g lv),
         (compile_live s0 an
           ((setAVL_FSet (sOT_as_OT nat_OrderedType)).singleton x)))
     | _ -> a)
  | StmtFun (f, t) ->
    (match a with
     | AnnF (lv, ans, ant) ->
       let ans' =
         zip (fun zs a0 ->
           let a' =
             compile_live (snd zs) a0
               (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty
           in
           setTopAnn a'
             ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union (getAnn a')
               (of_list (sOT_as_OT nat_OrderedType)
                 (setAVL_FSet (sOT_as_OT nat_OrderedType))
                 (filter2 (fst zs) (getAnn a0))))) f ans
       in
       AnnF (((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g lv), ans',
       (compile_live t ant (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty))
     | _ -> a)
  | _ ->
    (match a with
     | Ann0 lv -> Ann0 ((setAVL_FSet (sOT_as_OT nat_OrderedType)).union g lv)
     | _ -> a)

(** val forwardF :
    stmt -> 'a1 partialOrder -> 'a1 boundedSemiLattice -> (var list list ->
    stmt -> __ -> 'a1 ann -> 'a1 ann * 'a1 list) -> var list list -> (var
    list * stmt) list -> 'a1 ann list -> ('a1 ann * 'a1 list) list **)

let rec forwardF sT h h0 forward0 zL f anF =
  match f with
  | [] -> []
  | p :: x ->
    let (_, s) = p in
    (match anF with
     | [] -> []
     | a :: anF' ->
       (forward0 zL s __ a) :: (forwardF sT h h0 forward0 zL x anF'))

(** val forward :
    stmt -> 'a1 partialOrder -> 'a1 boundedSemiLattice -> (stmt -> var list
    list -> stmt -> __ -> 'a1 -> 'a1 anni) -> var list list -> stmt -> 'a1
    ann -> 'a1 ann * 'a1 list **)

let rec forward sT h h0 ftransform zL st a =
  match st with
  | StmtLet (_, _, s) ->
    (match a with
     | Ann1 (d, ans) ->
       let an = ftransform sT zL st __ d in
       let (ans', aL) =
         forward sT h h0 ftransform zL s (setTopAnn ans (getAnni d an))
       in
       ((Ann1 (d, ans')), aL)
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))
  | StmtIf (_, s, t) ->
    (match a with
     | Ann2 (d, ans, ant) ->
       let an = ftransform sT zL st __ d in
       let (ans', aL) =
         forward sT h h0 ftransform zL s (setTopAnn ans (getAnniLeft d an))
       in
       let (ant', aL') =
         forward sT h h0 ftransform zL t (setTopAnn ant (getAnniRight d an))
       in
       ((Ann2 (d, ans', ant')), (zip h0.join0 aL aL'))
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))
  | StmtApp (f, _) ->
    (match a with
     | Ann0 d ->
       let an = ftransform sT zL st __ d in
       ((Ann0 d),
       (list_update_at (map (fun _ -> h0.bottom) zL)
         (inst_counted_lab.counted0 f) (getAnni d an)))
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))
  | StmtReturn _ ->
    (match a with
     | Ann0 d -> ((Ann0 d), (map (fun _ -> h0.bottom) zL))
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))
  | StmtExtern (_, _, _, s) ->
    (match a with
     | Ann1 (d, ans) ->
       let an = ftransform sT zL st __ d in
       let (ans', aL) =
         forward sT h h0 ftransform zL s (setTopAnn ans (getAnni d an))
       in
       ((Ann1 (d, ans')), aL)
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))
  | StmtFun (f, t) ->
    (match a with
     | AnnF (d, anF, ant) ->
       let zL' = app (map fst f) zL in
       let (ant', aLt) = forward sT h h0 ftransform zL' t (setTopAnn ant d)
       in
       let anF' =
         forwardF sT h h0 (fun x x0 _ -> forward sT h h0 ftransform x x0) zL'
           f anF
       in
       let aL' = fold_left (zip h0.join0) (map snd anF') aLt in
       ((AnnF (d, (zip setTopAnn (map fst anF') aL'), ant')),
       (drop (length f) aL'))
     | _ -> (a, (map (fun _ -> h0.bottom) zL)))

(** val makeForwardAnalysis :
    (stmt -> 'a1 partialOrder) -> (stmt -> 'a1 boundedSemiLattice) -> (stmt
    -> var list list -> stmt -> __ -> 'a1 -> 'a1 anni) -> stmt -> 'a1 -> 'a1
    ann analysis **)

let makeForwardAnalysis h bSL f s i =
  { dom_po = (partialOrder_sig (partialOrder_ann (h s))); analysis_step =
    (fun x -> fst (forward s (h s) (bSL s) f [] s (setTopAnn x i)));
    initial_value = (setAnn (bSL s).bottom s) }

(** val unreachable_code_transform :
    stmt -> var list list -> stmt -> bool -> bool anni **)

let unreachable_code_transform _ _ st d =
  match st with
  | StmtIf (e, _, _) ->
    Anni2
      ((if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some
             false)
        then false
        else d),
      (if inst_eq_cm (inst_eq_dec_option bool_eqdec) (exp2bool e) (Some true)
       then false
       else d))
  | _ -> Anni1 d

(** val unreachable_code_analysis : stmt -> bool ann analysis **)

let unreachable_code_analysis s =
  makeForwardAnalysis (fun _ -> partialOrder_bool) (fun _ ->
    bool_boundedsemilattice) (fun x x0 x1 _ ->
    unreachable_code_transform x x0 x1) s true

(** val unreachableCodeAnalysis : stmt -> bool ann **)

let unreachableCodeAnalysis s =
  safeFixpoint (unreachable_code_analysis s)

(** val additionalArguments : stmt -> var set ann -> var list list ann **)

let additionalArguments s lv =
  fst (computeParameters [] [] [] s lv)

(** val toDeBruijn : nstmt -> stmt status **)

let toDeBruijn ilin =
  labIndices [] ilin

(** val toILF : stmt -> stmt **)

let toILF ili =
  let uc = unreachableCodeAnalysis ili in
  let ili_ndc = compile0 [] ili uc in
  let lv = livenessAnalysis ili_ndc in
  let ilid = compile1 [] ili_ndc lv in
  let additional_params =
    additionalArguments ilid
      (compile_live ili_ndc lv
        (setAVL_FSet (sOT_as_OT nat_OrderedType)).empty)
  in
  compile [] ilid additional_params
