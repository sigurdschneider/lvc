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
open Errors
open Libobject

DECLARE PLUGIN "smpl"

module StringMap = Map.Make(String)

let smpl_db = ref (StringMap.empty : ((int * Tacexpr.glob_tactic_expr) list) StringMap.t)

(*** Summary ***)

let init    () = smpl_db := StringMap.empty
let freeze   _ = !smpl_db
let unfreeze t = smpl_db := t

let _ = Summary.declare_summary "smpl"
	{ Summary.freeze_function   = freeze;
	  Summary.unfreeze_function = unfreeze;
	  Summary.init_function     = init }

(*** Database actions ***)

let intern_smpl_create db =
 try let _ = StringMap.find db (!smpl_db) in
     errorlabstrm "Smpl" (str "Smpl Database " ++ str db ++ str " already exists.")
 with Not_found -> smpl_db := StringMap.add db [] (!smpl_db)

let rec insert (n,tac) l =
  match l with
  | (n', tac')::l ->
     if n < n' then
       (n,tac)::(n',tac')::l
     else
       (n',tac')::insert (n,tac) l
  | [] -> [(n,tac)]

let intern_smpl_add entry db =
  try let db_list = StringMap.find db (!smpl_db) in
      let db_list' = insert entry db_list in
      smpl_db := StringMap.add db db_list' (!smpl_db)
  with Not_found -> errorlabstrm "Smpl" (str "Unknown Smpl Database " ++ str db ++ str ".")

type smpl_action =
  | CreateDb of string
  | AddTac of string * (int * glob_tactic_expr)

(*** Library interface ***)
(* This code handles loading through Require (Import) *)

let load_smpl_action _ (_, act) =
  match act with
  | CreateDb db -> intern_smpl_create db
  | AddTac (db, entry) -> intern_smpl_add entry db

let cache_smpl_action (kn, act) =
  load_smpl_action 1 (kn, act)

let subst_smpl_action (subst,act) =
  match act with
  | CreateDb db -> act
  | AddTac (db, (pri, tac)) ->
     let tac' = Tacsubst.subst_tactic subst tac in
     if tac==tac' then act else AddTac (db, (pri, tac'))

let classify_smpl_action act = Substitute act

let inSmpl : smpl_action -> obj =
  declare_object {(default_object "SMPL") with
                   cache_function = cache_smpl_action;
		   load_function = load_smpl_action;
		   subst_function = subst_smpl_action;
		   classify_function = classify_smpl_action; }
(*** Interface ***)

let smpl_add n_opt tac db =
  let n = match n_opt with
    | Some n -> n
    | None -> 100 in
  let act = AddTac (db, (n, tac)) in
  Lib.add_anonymous_leaf (inSmpl act)

let smpl_create db =
  let act = CreateDb db in
  Lib.add_anonymous_leaf (inSmpl act)

(*** Printing ***)

let smpl_print_entry (pri,tac) =
  let env =
    try
      let (_, env) = Pfedit.get_current_goal_context () in
      env
    with e when Errors.noncritical e -> Global.env ()
  in let msg = str "Priority " ++ Pp.int pri ++ str ": " ++ Pptactic.pr_glob_tactic env tac
  in msg_info msg

let smpl_print db =
  try let db_list = StringMap.find db (!smpl_db) in
      let a = msg_info (str "Tactics in Smpl DB " ++ str db ++ str " (in order):") in
      List.iter smpl_print_entry db_list; a
  with Not_found -> errorlabstrm "Smpl" (str "Unknown Smpl Database " ++ str db ++ str ".")

let smpl_print_dbs () =
  let _ = msg_info (str "Smpl DBs:") in
  StringMap.iter (fun key entry -> msg_info (str key)) (!smpl_db)

(*** Appling the tactic ***)

let smpl_tac_entry (_, tac) =
  eval_tactic tac

let rec mk_smpl_tac db l =
  match l with
  | tac::l -> Tacticals.New.tclORELSE (smpl_tac_entry tac) (mk_smpl_tac db l)
  | _ -> Tacticals.New.tclFAIL 0 (str "smpl " ++ str db ++ str ": no tactic applies")

let smpl_tac db =
  try let db_list = StringMap.find db (!smpl_db) in
      mk_smpl_tac db db_list
  with Not_found -> Tacticals.New.tclFAIL 0 (str "smpl: db " ++ str db ++ str " not found")

(*** Syntax Extensions ***)

VERNAC COMMAND EXTEND SmplCreate CLASSIFIED AS SIDEFF
   | [ "Smpl" "Create" preident (db) ] ->
      [ smpl_create db ]
END

VERNAC COMMAND EXTEND SmplAdd CLASSIFIED AS SIDEFF
   | [ "Smpl" "Add" natural_opt(n) tactic(tac) ":" preident (db) ] ->
      [ smpl_add n (glob_tactic tac) db ]
END

VERNAC COMMAND EXTEND SmplPrint
   | [ "Smpl" "Print" preident(db) ] ->
      [ smpl_print db ]
END

VERNAC COMMAND EXTEND SmplPrintAll
   | [ "Smpl" "Databases" ] ->
      [ smpl_print_dbs () ]
END

TACTIC EXTEND smpl
| [ "smpl" preident(db) ] -> [ smpl_tac db ]
END
