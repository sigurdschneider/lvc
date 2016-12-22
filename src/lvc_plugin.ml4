(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Term
open Declarations
open Pp
open Constrarg
open Extraargs

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

let rec is_constructor_app c =
      match kind_of_term c with
      | Construct _ -> true
      | App (c, args) -> is_constructor_app c
      | _ -> false

TACTIC EXTEND is_constructor_app
  | [ "is_constructor_app" constr(c) ] ->
     [
       if is_constructor_app c
       then Proofview.tclUNIT ()
       else Tacticals.New.tclFAIL 0 (str "not a constructor app")
     ]
END

open Stdarg
open Proofview

(* Time Warning *)

let tclTIME_CB t pr_time =
  let rec aux n t =
    let open Proof in
    Proofview.tclBIND (Proofview.tclUNIT ()) (fun () ->
    let tstart = System.get_time() in
    Proofview.tclBIND (Proofview.tclCASE t) (let open Logic_monad in function
    | Fail (e, info) ->
      begin
        let tend = System.get_time() in
        pr_time tstart tend n "failure";
        Proofview.tclZERO ~info e
      end
    | Next (x,k) ->
        let tend = System.get_time() in
        pr_time tstart tend n "success";
        tclOR (Proofview.tclUNIT x) (fun e -> aux (n+1) (k e))))
  in aux 0 t

let print_time (timeout:float) s tstart tend n msg =
  if (System.time_difference tstart tend) >= timeout then
    Feedback.msg_info(str "Time Warning" ++ pr_opt str s ++ str " exceeded " ++
			str (string_of_float timeout) ++ str "s. Tactic ran " ++
			System.fmt_time_difference tstart tend ++ str " with " ++
		     int n ++ str " backtracking (" ++ str msg ++ str ").")
  else
    ()

TACTIC EXTEND warntime
  | [ "warntime" natural(n) string_opt(s) tactic(tac) ] ->
     [
	tclTIME_CB (Tacinterp.tactic_of_value ist tac)
		   (print_time ((float_of_int n) /. 1000.0) s)
     ]
END
