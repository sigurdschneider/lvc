(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Term
open Declarations
open Pp
open Names
open Tacexpr
open Misctypes
open Hook
open Hints
open Tacintern
open Tacinterp
open Tacticals

DECLARE PLUGIN "smpl"

module StringMap = Map.Make(String)

let smpl_db = ref (StringMap.empty : (Tacexpr.glob_tactic_expr list) StringMap.t)

(* Summary *)

let init    () = smpl_db := StringMap.empty
let freeze   _ = !smpl_db
let unfreeze t = smpl_db := t

let _ = Summary.declare_summary "smpl"
	{ Summary.freeze_function   = freeze;
	  Summary.unfreeze_function = unfreeze;
	  Summary.init_function     = init }

let smpl_create db =
 try let _ = StringMap.find db (!smpl_db) in
     msg_error (str "Smpl Database" ++ str db ++ str "already exists")
 with Not_found -> smpl_db := StringMap.add db [] (!smpl_db)

let smpl_add raw_tac db =
  try let tacexp = glob_tactic raw_tac in
      let db_list = StringMap.find db (!smpl_db) in
      smpl_db := StringMap.add db (db_list@[tacexp]) (!smpl_db)
  with Not_found -> msg_error (str "Unknown Smpl Database" ++ str db)

let smpl_print_entry tac =
  let env =
    try
      let (_, env) = Pfedit.get_current_goal_context () in
      env
    with e when Errors.noncritical e -> Global.env ()
  in let msg = Pptactic.pr_glob_tactic env tac
  in msg_info msg

let smpl_print db =
  try let db_list = StringMap.find db (!smpl_db) in
      let a = msg_info (str "Tactics in Smpl DB " ++ str db ++ str " (in order)") in
      List.iter smpl_print_entry db_list; a
  with Not_found -> msg_error (str "Unknown Smpl Database" ++ str db)

let smpl_tac_entry tac =
  eval_tactic tac

let rec mk_smpl_tac l =
  match l with
  | tac::l -> Tacticals.New.tclORELSE (smpl_tac_entry tac) (mk_smpl_tac l)
  | _ -> Tacticals.New.tclFAIL 0 (str "smpl: no tactic applies")


let smpl_tac db =
  try let db_list = StringMap.find db (!smpl_db) in
      mk_smpl_tac db_list
  with Not_found -> Tacticals.New.tclFAIL 0 (str "smpl: db " ++ str db ++ str " not found")

VERNAC COMMAND EXTEND SmplCreate CLASSIFIED AS SIDEFF
   | [ "Smpl" "Create" preident (db) ] ->
      [ smpl_create db ]
END

VERNAC COMMAND EXTEND SmplAdd CLASSIFIED AS SIDEFF
   | [ "Smpl" "Add" tactic(tac) ":" preident (db) ] ->
      [ smpl_add tac db ]
END

VERNAC COMMAND EXTEND SmplPrint
   | [ "Smpl" "Print" preident(db) ] ->
      [ smpl_print db ]
END

TACTIC EXTEND smpl
| [ "smpl" preident(db) ] -> [ smpl_tac db ]
END
