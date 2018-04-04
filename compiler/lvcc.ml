open Parser
open Lexer
open List
open Util
open Lvcutil
open Names
open Pmove
open Camlcoq
open Status
open DCE
open Liveness
open Compiler
open Parmov
open Str

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;;

let rec find_def x l =
  match l with
  | (y,z)::l' -> if x = y then z else find_def x l'
  | nil -> BinNums.Coq_xH

exception NotLinearizableException

let main () =
  (* Give identifiert i, n the lowest indexes, do force
     heuristic to pick them. *)
  let debug = true in
  let _ = Clflags.option_g := debug in
  let _ = Clflags.option_v := true in
  let verbose = ref false in
  let num_registers = ref 2 in
  let only_to_linear = ref false in
  let infile = ref "" in
  let outfile = ref "a.s" in
  let set_infile s = infile:=s in
  let speclist = [
    ("-o", Arg.Set_string outfile, "<file> Place the output into <file>");
    (*    ("-1", Arg.Bool set_DCE, "<bool> DCE on IL/I input (default is true)"); *)
    ("-v", Arg.Set verbose, "Print compilation phases (default is false)");
    ("-r", Arg.Set_int num_registers, "Set the number of registers for the translation to Linear (default is 2)");
    ("-s", Arg.Set only_to_linear, "Don't modify IL program and translate directly to CompCert (default is false)");
    (*    ("-3", Arg.Bool set_toILI, "<bool> Enable IL/F to IL/I phase (default is false)") *)
  ] in
  (*let print_string a s = Printf.eprintf "%s" (camlstring_of_coqstring s); a in
  let toString_nstmt s = explode (print_nstmt !ids 0 s) in
  let toString_stmt s = explode (print_stmt !ids 0 s) in
  let toString_ann s p a = explode (print_ann (fun s -> implode (p s)) 0 a) in
  let toString_set s = explode (print_set !ids s) in
  let toString_list s = explode (print_list (fun x -> print_var !ids x) "," s) in *)
  Arg.parse speclist set_infile ("usage: lvcc [options]");
  let filename = Str.replace_first (Str.regexp "^.*[\\/]") "" !infile in
  let basename = Str.replace_first (Str.regexp "(\\.[^.]*)$") "" filename in
  let asmname = basename ^ ".s" in
  let machname = basename ^ ".mach" in
  let dump_oc suffix =
    let name = (basename ^ "." ^ suffix ^ ".im") in
    if !verbose then Printf.printf ">>> phase %s\n" name else ();
    open_out name in
  let dump suffix prg =
    let oc = dump_oc suffix in
    print_stmt oc true !ids 0 prg;
    Printf.fprintf oc "\n";
    if !verbose then (print_stmt stdout true !ids 0 prg; Printf.printf "\n") else ();
    close_out oc in
  let dumpn suffix prg =
    let oc = dump_oc suffix in
    print_nstmt oc true !ids 0 prg;
    Printf.fprintf oc "\n";
    if !verbose then (print_nstmt stdout true !ids 0 prg; Printf.printf "\n") else ();
    close_out oc in
  let file_chan = open_in !infile in
  let lexbuf = Lexing.from_channel  file_chan in
  try
    (* Printf.printf "Compiling"; *)
    let (map, ilin) = Parser.program Lexer.token lexbuf in
    let _ = print_nametable () in
    let readout = (dump_oc "read") in
    let _ =  print_nstmt readout false !ids 0 ilin in
    let _ = close_out readout in
    let _ = dumpn "0_in" ilin in
    let ili = (match Compiler.toDeBruijn ilin with
	       | Success ili -> ili
	       | Error e -> raise (Compiler_error "Converting to de bruijn failed (did you define all functions?)"))
    in
    let s_fromILF =
      if not !only_to_linear then
	let _ = dump "1_in_db" ili in
	let s_toILF = toILF ili in
	let _ = dump "10_toILF" s_toILF in
	let s_opt = optimize s_toILF in
	let _ = dump "20_opt" s_opt in
	let spo_c = ref 0 in
	let o = fun x -> find_def x map
	in
	let spo = fun (n:Datatypes.nat) (s:BinNums.positive SetInterface.set) ->
	  (
	    let _ = spo_c := !spo_c + 1 in
	    let _ = Printf.printf "Spillrequest #%d for %d " !spo_c (Nat.to_int n) in
	    let _ = print_set stdout true !ids s in
	    let _ = Printf.printf " -> " in
	    let kill = if !spo_c = 1
		       then set_from_list [P.of_int 1; P.of_int 5]
		       else if !spo_c = 2
		       then set_from_list [P.of_int 1]
		       else if !spo_c = 6
		       then set_from_list [P.of_int 21]
		       else if !spo_c = 11
		       then set_from_list [P.of_int 5]
		       else if !spo_c = 12
		       then set_from_list [P.of_int 3]
		       else emptyset in
	    let _ = print_set stdout true !ids kill in
	    let _ = Printf.printf "\n" in
	    kill) in
	let (s_prespill, s_prealloc, s_fromILF) =
	  (match fromILF s_opt o spo with
	   | ((presp, ren), Success x) -> (presp, ren, x)
	   | (_, Error e) -> raise (Compiler_error "reg alloc failed")
	  )
	in
	let _ = dump "23_prespill" s_prespill in
	let _ = dump "25_prealloc" s_prealloc in
	let _ = dump "30_fromILF" s_fromILF in
	s_fromILF
      else
	ili
    in
    let _ =
      match IsLinearizable.toLinearPreconditions ToLinear.max_reg s_fromILF with
      | Success _ -> ()
      | Error msg -> raise (Compiler_error (implode msg))
    in
    let function_id = Camlcoq.intern_string "LVC" in
    let linear = ToLinear.coq_ILItoLinear function_id s_fromILF in
    PrintMach.destination := Some machname;
    let asm =
      match Compiler0.apply_partial
	      (LinearToAsm.transf_linear_program linear)
	      Asmexpand.expand_program with
      | Errors.OK asm ->
         asm
      | Errors.Error msg ->
         Printf.eprintf "%s: %a" filename Driveraux.print_error msg;
         exit 2 in
    (* Print Asm in text form *)
    let oc = open_out asmname in
    PrintAsm.print_program oc asm;
    close_out oc
  with Sys_error s-> Printf.eprintf "%s\n" s
     | Compiler_error e -> Printf.eprintf "\nCompilation failed:\n%s\n" e
     | Range_error e -> Printf.eprintf "The integer %s is not in range\n" e
     (*| Lexer.Error msg ->
	 Printf.fprintf stderr "%s%!" msg*)
     | Parser.Error ->
 	let pos = lexbuf.Lexing.lex_curr_p in
	let tok = Lexing.lexeme lexbuf in
	let open Lexing in
	let line = pos.pos_lnum in
	let col = pos.pos_cnum - pos.pos_bol in
	Printf.fprintf stderr "At line %d:%d: syntax error: %s\n%!"
		       line col tok
;;


  main ();
