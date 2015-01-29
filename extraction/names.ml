open Big

module StringMap = Map.Make (struct type t=string let compare = Pervasives.compare end)
module BigMap = Map.Make (struct type t=Big.big_int let compare = Big.compare end)
module IntMap = Map.Make (struct type t=int let compare = Pervasives.compare end)

let names : (int StringMap.t) ref = ref StringMap.empty
let ids : (string IntMap.t) ref = ref IntMap.empty

let curr_id = ref 0

let get_next_id () =
let tmp = !curr_id in
  curr_id := tmp + 1; tmp

let calls : (string Stack.t) ref = ref (Stack.create ())
