open Utils 
open Program

(* Method verify status structure and it's arrayi *)
type method_verify_status = {
  method_id : string;
  checked : bool;
  verified : bool;
}

(* Implement a partial correctness verifier *)
let verify : Args.t -> Syntax.pgm -> bool 
=fun args pgm -> 
  
  print_endline ("Input File: " ^ args.inputFile);
  
  print_endline "\n[Methods to Verify]";
  List.iter (fun (mthd: Syntax.mthd) ->
    print_endline ("  - " ^ mthd.id)
  ) pgm.mthds;
  print_endline "===============================";

  print_endline "\n[Verifying Methods]";
  let (temp_mv_list: method_verify_status list ref) =  ref [] in 
  List.iter (fun (mthd: Syntax.mthd) ->
    print_endline ("  - " ^ mthd.id);
    let (new_mv_item: method_verify_status) = {
      method_id = mthd.id;
      checked   = false;
      verified  = false
    } in
    temp_mv_list := new_mv_item::!temp_mv_list
  ) pgm.mthds;
  print_endline "===============================";

  (* find max id length for print alignment *)
  let max_id_len =
    List.fold_left (fun cur_max (m: method_verify_status) ->
      max cur_max (String.length m.method_id)
    ) 0 ! temp_mv_list
  in

  print_endline "\n[Verify Summary]";
  List.iter (fun (mv_status: method_verify_status) ->
    let status_msg = 
      if mv_status.checked then
        "checked: true, verified: "^ string_of_bool mv_status.verified
      else
        "checked: false"
    in
    (* '*' means 1st arguments, '%s' means string, '-' menas left align *)
    let aligned_id = Printf.sprintf "%-*s" max_id_len mv_status.method_id in
    print_endline("  - " ^ aligned_id ^ " -> " ^ status_msg)
  ) (List.rev !temp_mv_list);
  print_endline "===============================";

  print_endline "\n[Verify Statistics]";
  let total_count    = List.length !temp_mv_list in
  let checked_count  = List.length (List.filter(fun (m: method_verify_status) -> m.checked) !temp_mv_list) in
  let verified_count = List.length (List.filter(fun (m: method_verify_status) -> m.verified) ! temp_mv_list) in
  print_endline( "  - " ^ string_of_int checked_count  ^ " / " ^ string_of_int total_count   ^ " (checked/total)");
  print_endline( "  - " ^ string_of_int verified_count ^ " / " ^ string_of_int checked_count ^ " (verified/checked)");
  print_endline "===============================\n";

  true
