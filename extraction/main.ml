open Parser
open Lexer
open List
open Util
open Names
open Big
open Pmove

let main () =
  let infile = ref "" in
  let outfile = ref "a.out" in
  let optimize = ref true in
  let set_optimize b = optimize := b in
  let set_infile s = infile:=s in
  let speclist = [
    ("-o",Arg.Set_string outfile, "Place the output into <file>");
    ("-O", Arg.Bool set_optimize, "Enable optimization (default is on)")
  ] in
    Arg.parse speclist set_infile ("usage: lvc [options]");
    try
      let file_chan = open_in !infile in
      let lexbuf = Lexing.from_channel  file_chan in
      let result = Parser.expr Lexer.token lexbuf in
      let _ = Printf.printf "Normalized Input:\n%s\n\n" (print_nexpr 0 result !ids) in
      match (Lyn.labIndices result []) with
        | None -> let _ = Printf.printf "Ill-formed program (probably undeclared
          function)" in ()
        | Some ili -> 
          let lv = Lyn.livenessAnalysis generic_first ili in
          let _ = Printf.printf "Liveness\n%s\n\n" (print_ann (print_set !ids) 0 lv) in
          let aa = Lyn.additionalArguments ili lv in
          let _ = Printf.printf "AdditionalArguments\n%s\n\n" 
	    (print_ann (print_list (fun s -> "[" ^ (print_list (fun x -> print_var x !ids) ", " s) ^ "]") " ") 0 aa) in
          let v = Lyn.toILF ili lv in
          let _ = match v with 
	    | Lyn.Success ilf -> Printf.printf "Compilate:\n%s\n\n" (print_expr 0 ilf !ids);
	      let ren = Lyn.rename_apart ilf in
              let _ = Printf.printf "Renamed apart\n%s\n\n" (print_expr 0 ren (BigMap.empty)) in
	      let lv2 = Lyn.livenessAnalysis generic_first ren in
              let _ = Printf.printf "Liveness\n%s\n\n" (print_ann (print_set BigMap.empty) 0 lv2) in
	      (match (Lyn.linear_scan ren lv2 (fun x -> x)) with
		| Lyn.Success renaming -> 
		  let alloc = Lyn.rename renaming ren in
		  let _ = Printf.printf "Allocated\n%s\n\n" (print_expr 0 alloc (BigMap.empty)) in
		  let lv3 = Lyn.live_rename renaming lv2 in
		  let _ = Printf.printf "Liveness\n%s\n\n" (print_ann (print_set (BigMap.empty)) 0 lv3) in
		  
		  (let v = Lyn.fromILF Lyn.linear_scan parallel_move generic_first ilf in
		   match v with
		     | Lyn.Success s -> Printf.printf "Compilate:\n%s\n\n" 
		       (print_expr 0 s (BigMap.empty));
                     | Lyn.Error e -> Printf.printf "Compilation failed:%s\n\n" (implode e) )
                | Lyn.Error e -> Printf.printf "Compilation failed:\n%s" (implode e))
            | Lyn.Error e -> Printf.printf "Compilation failed:\n%s" (implode e) in
          ()
    with Parsing.Parse_error ->
        Printf.eprintf "A parsing error occured \n"
      | Sys_error s-> Printf.eprintf "%s\n" s
      | Compiler_error -> Printf.eprintf "The compilation failed\n\n"
      | Range_error e -> Printf.eprintf "The integer %s is not in range\n" e;;

main ();

