open Parser
open Lexer
open List
open Util
open Lvcutil
open Names
open Pmove
open Camlcoq
open Status
open DCVE
open Liveness
open Compiler
open Parmov

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

let main () =
  (* Give identifiert i, n the lowest indexes, do force
     heuristic to pick them. *)
  let _ = register_name "i" in
  let _ = register_name "n" in
  let debug = false in
  let infile = ref "" in
  let outfile = ref "a.s" in
  let do_addParams = ref false in
  let toILI = ref false in
  let set_addParams b = do_addParams := b in
  let set_toILI b = toILI := b in
  let set_infile s = infile:=s in
  let speclist = [
    ("-o", Arg.Set_string outfile, "<file> Place the output into <file>");
    (*    ("-1", Arg.Bool set_DCE, "<bool> DCE on IL/I input (default is true)"); *)
    ("-c", Arg.Bool set_addParams, "<bool> Translate to IL/F (default is false)");
    (*    ("-3", Arg.Bool set_toILI, "<bool> Enable IL/F to IL/I phase (default is false)") *)
  ] in
  (*let print_string a s = Printf.eprintf "%s" (camlstring_of_coqstring s); a in
  let toString_nstmt s = explode (print_nstmt !ids 0 s) in
  let toString_stmt s = explode (print_stmt !ids 0 s) in
  let toString_ann s p a = explode (print_ann (fun s -> implode (p s)) 0 a) in
  let toString_set s = explode (print_set !ids s) in
  let toString_list s = explode (print_list (fun x -> print_var !ids x) "," s) in *)
    Arg.parse speclist set_infile ("usage: lvcc [options]");
    try
      (* Printf.printf "Compiling"; *)
      let file_chan = open_in !infile in
      let lexbuf = Lexing.from_channel  file_chan in
      let ilin = Parser.program Lexer.token lexbuf in
      let _ =  Printf.printf "Input (functions named):\n";
	       print_nstmt stdout false !ids 0 ilin;
               Printf.printf "\n\n" in
      let ili = (match Compiler.toDeBruijn ilin with
		 | Success ili -> ili
		 | Error e -> raise (Compiler_error "Converting to de bruijn failed (did you define all functions?)"))
		 in
      let s_dce =
	(match fromILF ili with
	 | Success x -> Printf.printf "after reg alloc (functions de-bruijn, regs lowercase, slots uppercase):\n";
			print_stmt stdout true !ids 0 x;
			Printf.printf "\n\n";
	   x
	 | Error e -> raise (Compiler_error "reg alloc failed")
	)
      in
      let ilf =
(*	if !do_addParams then
	  let x = Compiler.addParams s_dce lv_dce in
	  Printf.printf "as IL/F program (functions de-bruijn):\n%s\n\n" (print_stmt !ids 0 x);
	  x
	else *)
	  (Printf.printf "to IL/F program translation disabled, enable with argument -c true\n";
	  s_dce)
(*      in
      let sopt =
	if !optimize then
	  (match Lvc.optimize generic_first ilf with
	   | Lvc.Success sopt ->
	      Printf.printf "\noptimized compilate:\n%s\n\n" (print_stmt !ids 0 sopt);
	      sopt
	   | Lvc.Error e -> raise (Compiler_error (implode e))
	   )
	else
	ilf
      in
      let res =
	 if !toILI then
          (match Compiler.fromILF parallel_move generic_first sopt with
	   | Lvc.Success ili ->
	      Printf.printf "\nto IL/I compilate (functions are de-bruijn now):\n%s\n\n" (print_stmt !ids 0 ili);
	      ili
	   | Lvc.Error e -> raise (Compiler_error (implode e))
	  )
	else
	sopt*)
      in ()
    with Parsing.Parse_error -> Printf.eprintf "A parsing error occured \n"
      | Sys_error s-> Printf.eprintf "%s\n" s
      | Compiler_error e -> Printf.eprintf "\nCompilation failed:\n%s\n" e
      | Range_error e -> Printf.eprintf "The integer %s is not in range\n" e;;

main ();
