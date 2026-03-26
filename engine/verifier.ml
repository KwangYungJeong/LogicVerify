open Utils 
open Program 

(* Implement a partial correctness verifier *)
let verify : Args.t -> Syntax.pgm -> bool 
=fun args pgm -> 
  
  print_endline ("Input File: " ^ args.inputFile);
  
  print_endline "\n[Methods to Verify]";
  List.iter (fun (mthd: Syntax.mthd) ->
    print_endline ("  - " ^ mthd.id)
  ) pgm.mthds;


  print_endline "===============================";
  true

