(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Term
open Declarations
open Pp

DECLARE PLUGIN "lvc_plugin"

let num_params ind =
      let (mind, ibody) = Global.lookup_inductive ind in
      mind.mind_nparams

let rec is_param c n =
      match kind_of_term c with
      | Ind (ind, _) -> n < num_params ind
      | App (c, args) -> is_param c (n + Array.length args)
      | _ -> false

TACTIC EXTEND is_param
  | [ "is_param" constr(c) natural(n) ] ->
     [
       if is_param c n
       then Proofview.tclUNIT ()
       else Tacticals.New.tclFAIL 0 (str "not a parameter")
     ]
END
