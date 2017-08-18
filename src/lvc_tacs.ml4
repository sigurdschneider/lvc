(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Term
open Declarations
open Pp
open Stdarg
open Ltac_plugin
open Tacarg
open Extraargs


DECLARE PLUGIN "lvc_plugin"

let num_params ind =
      let (mind, ibody) = Global.lookup_inductive ind in
      mind.mind_nparams

let rec is_param sigma c n =
      match EConstr.kind sigma c with
      | Ind (ind, _) -> n < num_params ind
      | App (c, args) -> is_param sigma c (n + Array.length args)
      | _ -> false

TACTIC EXTEND is_param
  | [ "is_param" constr(c) natural(n) ] ->
     [
       Proofview.Goal.enter begin fun gl ->
				  if is_param (Proofview.Goal.sigma gl) c n
				  then Proofview.tclUNIT ()
				  else Tacticals.New.tclFAIL 0 (str "not a parameter")
			    end
     ]
END

let rec is_inductive sigma c =
      match EConstr.kind sigma c with
      | Ind _ -> true
      | App (c, args) -> is_inductive sigma c
      | _ -> false

TACTIC EXTEND is_inductive
  | [ "is_inductive" constr(c) ] ->
     [
        Proofview.Goal.enter begin fun gl ->
				   if is_inductive (Proofview.Goal.sigma gl) c
				   then Proofview.tclUNIT ()
				   else Tacticals.New.tclFAIL 0 (str "not an inductive")
			     end
     ]
END

let rec is_constructor_app sigma c =
      match EConstr.kind sigma c with
      | Construct _ -> true
      | App (c, args) -> is_constructor_app sigma c
      | _ -> false

TACTIC EXTEND is_constructor_app
  | [ "is_constructor_app" constr(c) ] ->
     [
       Proofview.Goal.enter begin fun gl ->
				  if is_constructor_app (Proofview.Goal.sigma gl) c
				  then Proofview.tclUNIT ()
				  else Tacticals.New.tclFAIL 0 (str "not a constructor app")
			    end
     ]
END

open Stdarg
open Proofview

(* Time Warning *)

let tclTIME_CB t pr_time =
  let open Proof in
  Proofview.tclBIND (Proofview.tclUNIT ())
		    (fun () ->
		     let tstart = System.get_time() in
		     Proofview.tclBIND t (fun () ->
					  let tend = System.get_time() in
					  pr_time tstart tend;
					  Proofview.tclUNIT ()
					 ))


let print_time (timeout:float) s tstart tend =
  if (System.time_difference tstart tend) >= timeout then
    Feedback.msg_info(str "Time Warning" ++ pr_opt str s ++ str " exceeded " ++
			str (string_of_float timeout) ++ str "s. Tactic ran " ++
			System.fmt_time_difference tstart tend ++ str ".")
  else
    ()

TACTIC EXTEND warntime
  | [ "warntime" natural(n) string_opt(s) tactic(tac) ] ->
     [
	tclTIME_CB (Tacinterp.tactic_of_value ist tac)
		   (print_time ((float_of_int n) /. 1000.0) s)
     ]
END


let print_goal_as_lemma () =
  Proofview.Goal.nf_enter
    begin fun gl ->
	  let sigma = Tacmach.New.project gl in
	  let concl = Tacmach.New.pf_concl gl in
	  let hyps  = Tacmach.New.pf_hyps_types gl in
	  let _ = Feedback.msg_info (str "Lemma unnamed ") in
	  let phyps = List.map
			(fun (id, ty) ->
			 Feedback.msg_info @@
			   str "(" ++
			     (Names.Id.print id) ++ str ":" ++
			     (Termops.print_constr ty) ++ str ")")
			(List.rev hyps) in
	  let _ = Feedback.msg_info ( str " : " ++ Termops.print_constr concl) in
	  tclUNIT ()
    end

TACTIC EXTEND goal_as_lemma
  | [ "goal_as_lemma" ] ->
     [
	print_goal_as_lemma ()
     ]
END
