open Format
open Term
open Coqlib
(* open Tacmach *)
(* open Tacticals *)
(* open Tactics *)
open Pp

let print_array f sep fin fmt a =
  Array.iter (fun i -> fprintf fmt "%a%s" f i sep) a;
  fprintf fmt "%s@." fin

let string_of_name name =
  match name with
    | Names.Anonymous -> "anonymous"
    | Names.Name n -> Names.string_of_id n

let print_kn fmt kn =
  fprintf fmt "%s" (Names.string_of_con (Names.constant_of_kn kn))

let rec print_constr fmt c =
  let f = print_constr in
  match kind_of_term c with
  | _ when c = build_coq_False () -> fprintf fmt "False"
  | _ when c = build_coq_True () -> fprintf fmt "True"
  | _ when c = build_coq_not () -> fprintf fmt "Not"
  | _ when c = build_coq_or () -> fprintf fmt "Or"
  | _ when c = build_coq_and () -> fprintf fmt "And"
  | Rel i -> fprintf fmt "rel %d" i
  | Var id -> fprintf fmt ("var %s") (Names.string_of_id id)
  | Meta _ -> fprintf fmt "meta"
  | Evar (i, constr_array) ->
      fprintf fmt "Evar : %d %a" (Evar.repr i) (print_array f " " "") constr_array
  | Sort s ->
      (match s with
	 | Prop Null -> fprintf fmt "sort(prop)"
	 | Prop Pos -> fprintf fmt "sort(set)"
	 | Type _ -> fprintf fmt "sort(type)")
  | Cast (term, _, typ) ->
      fprintf fmt "cast du term %a avec le type %a" f term f typ
  | Prod (name, typ, typ') ->
      fprintf fmt "Prod (%s * %a * {%a})" (string_of_name name) f typ f typ'
  | Lambda (name, typ, constr) ->
      fprintf fmt "Lambda (%s : %a=%a)"
	(string_of_name name) f typ f constr
  | LetIn (name, constr,typ, constr') ->
      fprintf fmt "Let %s : %a = %a in %a@."
	(string_of_name name) f typ f constr f constr'
  | App (constr, constr_array) ->
      fprintf fmt "%a @ (%a)" f constr (print_array f ", " "") constr_array
  | Const (const, _) ->
      fprintf fmt "constante %s" (Names.string_of_con const)
  | Ind((mult_ind, i), _) ->
      fprintf fmt "Ind (%a, %d)" print_kn (Names.user_mind mult_ind) i
  | Construct (((mult_ind, i), i'), _) ->
      fprintf fmt "Constructor ((%a, %d), %d)"
	print_kn (Names.user_mind mult_ind) i i'
  | Case (case_info, constr, constr', constr_array) ->
      fprintf fmt "match %a as %a with @.%a end" f constr f constr'
	(print_array f "\n" "") constr_array
  | Fix ((int_array, int),(name_a, type_a, constr_a)) ->
      fprintf fmt "fix %d, %d\n %a\n %a\n %a@."
	(Array.length int_array) int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a
  | CoFix (int, (name_a, type_a, constr_a)) ->
      fprintf fmt "cofix %d\n %a\n %a\n %a@."
	int
	(print_array (fun fmt s ->
			fprintf fmt "%s" (string_of_name s)) ", " "")
	name_a
	(print_array f ", " "") type_a
	(print_array f ", " "") constr_a
  | Proj (p, c) -> fprintf fmt "Proj (%s, %a)" 
    (Names.string_of_con (Names.Projection.constant p)) f c

let print_ast constr_expr =
  let constr, _ =
    Constrintern.interp_constr (Global.env ()) Evd.empty constr_expr in
    fprintf std_formatter "%a" print_constr constr
