open Big

module StringMap = Map.Make (struct type t=string let compare = Pervasives.compare end)
module BigMap = Map.Make (struct type t=Big.big_int let compare = Big.compare end)

let names : (big_int StringMap.t) ref = ref StringMap.empty
let ids : (string BigMap.t) ref = ref BigMap.empty

let curr_id = ref zero

let get_next_id () =
let tmp = !curr_id in
  curr_id := succ tmp; tmp

let calls : (string Stack.t) ref = ref (Stack.create ())
