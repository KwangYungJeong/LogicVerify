open Utils 
open Program 
open Engine 

exception Error of string

let position : Lexing.lexbuf -> string
= fun lexbuf -> begin
  let pos = lexbuf.lex_curr_p in
  pos.pos_fname ^ ":" ^ 
  (pos.pos_lnum |> string_of_int) ^ ":" ^ 
  ((pos.pos_cnum - pos.pos_bol + 1) |> string_of_int)
end

let read_args : unit -> Args.t
=fun () -> 
  let _ = Args.create() in 
  let args = Args.read () in
    if args.printArg then print_endline (Args.to_string ()) else ();
    args 

let read_pgm : string -> Syntax.pgm 
=fun filename -> 
  let in_c = Stdlib.open_in filename in
  let lexbuf = Lexing.from_channel in_c in
  try
    let res = Parser.start Lexer.next_token lexbuf in
      close_in in_c; 
      res
  with
  | Lexer.LexingError msg -> (
    close_in in_c;
    Error ("read: " ^ msg ^ "[" ^ (position lexbuf) ^ "]") |> Stdlib.raise)
  | Parser.Error -> (
    close_in in_c;
    Error ("read: syntax error [" ^ (position lexbuf) ^ "]") |> Stdlib.raise)

let main : unit -> unit
=fun () -> 
  let _ = 
    let _ = Z3.set_global_param "sat.random_seed" "0" in
    let _ = Z3.set_global_param "nlsat.seed" "0" in
    let _ = Z3.set_global_param "sls.random_seed" "0" in
    let _ = Z3.set_global_param "fp.spacer.random_seed" "0" in
    let _ = Z3.set_global_param "smt.random_seed" "51" in
    ()
  in
  let _ = Random.self_init () in 
  let args = read_args () in 
  let pgm = read_pgm args.inputFile |> Desugar.perform in 
  let _ = Typechecker.check_pgm pgm in 
  let _ = if args.printAdt then prerr_endline ("Input Program.\n" ^ (pgm |> Pp.string_of_pgm ~indent:1)) else () in 
  let _ = pgm |> Verifier.verify args in 
    () 

let _ = main()
