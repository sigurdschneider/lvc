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

let smpl_db = ref ([] : Tacexpr.glob_tactic_expr list)

(* Summary *)

let init    () = smpl_db := []
let freeze   _ = !smpl_db
let unfreeze t = smpl_db := t

let _ = Summary.declare_summary "smpl"
	{ Summary.freeze_function   = freeze;
	  Summary.unfreeze_function = unfreeze;
	  Summary.init_function     = init }


let smpl_add raw_tac =
  let tacexp = glob_tactic raw_tac in
  smpl_db := (!smpl_db)@[tacexp]

let smpl_add_list lc =
  List.iter (smpl_add) lc

let smpl_print_entry tac =
  let env =
    try
      let (_, env) = Pfedit.get_current_goal_context () in
      env
    with e when Errors.noncritical e -> Global.env ()
  in let msg = Pptactic.pr_glob_tactic env tac
  in msg_info msg

let smpl_print () =
  List.iter smpl_print_entry (!smpl_db)

let smpl_tac_entry tac =
  eval_tactic tac

let rec mk_smpl_tac l =
  match l with
  | tac::l -> Tacticals.New.tclORELSE (smpl_tac_entry tac) (mk_smpl_tac l)
  | _ -> Tacticals.New.tclFAIL 0 (str "no tactic applies")





VERNAC COMMAND EXTEND SmplAdd CLASSIFIED AS SIDEFF
   | [ "Smpl" tactic(tac) ] ->
      [ smpl_add tac ]
END


VERNAC COMMAND EXTEND SmplPrint
   | [ "Print" "Smpl" ] ->
      [ smpl_print () ]
END

TACTIC EXTEND smpl
| [ "smpl" ] -> [ mk_smpl_tac (!smpl_db) ]
END
