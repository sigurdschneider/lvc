
module StringMap = Map.Make (struct type t=string let compare = Pervasives.compare end)
module IntMap = Map.Make (struct type t=int let compare = Pervasives.compare end)

let names : (int StringMap.t) ref = ref StringMap.empty
let ids : (string IntMap.t) ref = ref IntMap.empty

let curr_id = ref 0

let get_next_id () =
let tmp = !curr_id in
  curr_id := tmp + 1; tmp

let register_name s =
  let id = get_next_id () in
  let _ = ids := IntMap.add id s !ids in
  names := StringMap.add s id !names; id

let rec pragma_register_names l =
  match l with
  | [] -> ()
  | x::l -> let _ = register_name x in pragma_register_names l


let calls : (string Stack.t) ref = ref (Stack.create ())

let print_nametable () =
  StringMap.iter (fun s n -> Printf.printf "%d: %s\n" n s) !names
