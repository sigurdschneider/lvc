open Parser
open Lexer
open List
open Util
open Names
open Big
open Pmove

let main () =
  let infile = ref "" in
  let outfile = ref "a.s" in
  let toILF = ref false in
  let optimize = ref false in
  let toILI = ref false in
  let set_toILF b = toILF := b in
  let set_optimize b = optimize := b in
  let set_toILI b = toILI := b in
  let set_infile s = infile:=s in
  let speclist = [
    ("-o",Arg.Set_string outfile, "<file> Place the output into <file>");
    ("-1", Arg.Bool set_toILF, "<bool> Enable IL/I to IL/F phase (default is false)");
    ("-2", Arg.Bool set_optimize, "<bool> Enable optimization (default is false)");
    ("-3", Arg.Bool set_toILI, "<bool> Enable IL/F to IL/I phase (default is false)")
  ] in
  let print_string a s = Printf.eprintf "%s" (implode s); a in
  let toString_nstmt s = explode (print_nstmt !ids 0 s) in
  let toString_stmt s = explode (print_stmt !ids 0 s) in
  let toString_ann s p a = explode (print_ann (fun s -> implode (p s)) 0 a) in
  let toString_set s = explode (print_set !ids s) in
  let toString_list s = explode (print_list (fun x -> print_var !ids x) "," s) in
    Arg.parse speclist set_infile ("usage: lvc [options]");
    try
      if (not !toILF) && (not !optimize) && (not !toILI) then
	raise (Compiler_error "No translation phase selected, try --help.")
      else
      (* Printf.printf "Compiling"; *)
      let file_chan = open_in !infile in
      let lexbuf = Lexing.from_channel  file_chan in
      let ilin = Parser.program Lexer.token lexbuf in
      let _ =  Printf.printf "Input:\n%s\n\n" (print_nstmt !ids 0 ilin) in
      let ili = (match Lvc.toDeBruijn ilin with
		 | Lvc.Success ili -> ili
		 | Lvc.Error e -> raise (Compiler_error "Converting to de bruijn failed (did you define all functions?)"))
		 in
      let ilf =
	if !toILF then
	  (match Lvc.toILF generic_first
			   (* print_string toString_nstmt toString_stmt toString_ann toString_set toString_list *) ili (* 0 *) with
	   | Lvc.Success ilf ->
 	      Printf.printf "\nto IL/F compilate:\n%s\n\n" (print_stmt !ids 0 ilf);
	      ilf

	   | Lvc.Error e -> raise (Compiler_error (implode e))
	  )
	else
	  ili in
      let sopt =
	if !optimize then
	  (match Lvc.optimize generic_first ilf with
	   | Lvc.Success sopt ->
	      Printf.printf "\noptimized compilate:\n%s\n\n" (print_stmt !ids 0 sopt);
	      sopt
	   | Lvc.Error e -> raise (Compiler_error (implode e))
	   )
	else ilf
      in
      let res =
	if !toILI then
          (match Lvc.fromILF parallel_move generic_first sopt with
	   | Lvc.Success ili ->
	      Printf.printf "\nto IL/I compilate:\n%s\n\n" (print_stmt !ids 0 ili);
	      ili
	   | Lvc.Error e -> raise (Compiler_error (implode e))
	  )
	else
	  sopt in ()
    with Parsing.Parse_error -> Printf.eprintf "A parsing error occured \n"
      | Sys_error s-> Printf.eprintf "%s\n" s
      | Compiler_error e -> Printf.eprintf "\nCompilation failed:\n%s\n" e
      | Range_error e -> Printf.eprintf "The integer %s is not in range\n" e;;

main ();
