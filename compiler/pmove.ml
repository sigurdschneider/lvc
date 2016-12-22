(*

Adapted from:

Rideau, L., Serpette, B.P., Leroy, X.: Tilting at windmills with Coq: formal veriﬁcation
of a compilation algorithm for parallel moves. Journal of Automated Reasoning 40(4),
307–326 (2008)

*)

open String
open Camlcoq

type status = To_move | Being_moved | Moved

let rec zip lst1 lst2 = match lst1,lst2 with
  | [],_ -> []
  | _, []-> []
  | (x::xs),(y::ys) -> (x,y) :: (zip xs ys);;

let print_pair op (src,dst) = string_of_int (Nat.to_int (List.hd src))
			      ^ op
			      ^ (string_of_int (Nat.to_int (List.hd dst)));;


let print_moves srcl dstl =
  concat "\n" (List.map (print_pair " <- ") (List.map (fun (a,b) -> ([a], [b])) (zip srcl dstl))) ^ ";"
;;

let parallel_move (debug:bool) tmp srcl dstl =
  let src = Array.of_list srcl in
  let dst = Array.of_list dstl in
  let _ = if debug then Printf.printf "moves:\n%s\n" (print_moves srcl dstl) else () in
  let n = Array.length src in
  let status = Array.make n To_move in
  let res = ref [] in
  let rec move_one i =
    if not (src.(i) == dst.(i)) then begin
      status.(i) <- Being_moved;
      for j = 0 to n - 1 do
	if src.(j) == dst.(i) then
	  match status.(j) with
	    | To_move ->
		move_one j
	    | Being_moved ->
		 res :=  ([src.(j)], [tmp]) :: !res;
	    src.(j) <- tmp
	    | Moved ->
		()
      done;
      res := ([src.(i)], [dst.(i)]) :: !res;
      status.(i) <- Moved
    end in
  for i = 0 to n - 1 do
    if status.(i) = To_move then move_one i
  done;
  let _ = if debug then Printf.printf "res:\n%s\n" (concat "\n" (List.map (print_pair " = ") !res)) else () in
  (* List.rev *) !res
