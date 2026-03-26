open Syntax
open Graph
open Utils.Lib 
open Printf

exception SemanticError of string 

module Value = struct
  type t = V_int of int | V_bool of bool | V_arr of int * (int list)
  let max_int = 50
  let random typ = 
    let random_int max_int = Random.int max_int - max_int / 2 in 
    let random_nat max_int = Random.int max_int / 2 in 
      match typ with 
      | T_int -> V_int (random_int max_int)
      | T_bool -> V_bool (Random.bool())
      | T_arr typ' -> 
        begin 
          match typ' with 
          | T_int -> 
            let sz = random_nat 20 in
            V_arr (sz, List.map (fun _ -> random_int max_int) (range sz))        
          | _ -> raise (Failure "Value: only integer array is allowed")
          end 
      | _ -> failwith "Value.random: not supported type"

  let new_array size = V_arr (size, make_list size 0)

  let nth_array (sz, elems) idx = 
    if 0 <= idx && idx < sz then 
      List.nth elems idx 
    else 
      failwith "Value.nth_array"

  let modify_array (sz, elems) idx value = 
    if 0 <= idx && idx < sz then 
      (sz, replace_list_elem elems idx value)
    else 
      failwith "Value.modify_array"

  let to_string v = 
    match v with 
    | V_int n -> string_of_int n 
    | V_bool b -> string_of_bool b 
    | V_arr (_, elems) -> string_of_list string_of_int elems 
end 

module Memory = struct
  type t = (id, Value.t) BatMap.t 
  let empty = BatMap.empty 
  let bind = BatMap.add 
  let lookup x m = 
    try BatMap.find x m
    with _ -> raise (SemanticError ("Memory: " ^ x ^ " is not found")) 
  let fold = BatMap.foldi 
  let to_string : t -> string 
  =fun m -> 
    if m = empty then "{}" 
    else 
      "{" ^ BatMap.foldi (fun x v s -> 
        s ^ " " ^ x ^ " |-> " ^ (Value.to_string v)
      ) m "" ^ "}" 
end

module CollectingSemantics = struct
  type t = (Node.t, Memory.t BatSet.t) BatMap.t 
  let empty = BatMap.empty 
  let lookup n t = try BatMap.find n t with _ -> BatSet.empty 
  let add n m t = BatMap.add n (BatSet.add m (lookup n t)) t 
  let to_string t = 
    if t = empty then "{}"
    else 
      "{\n" ^ BatMap.foldi (fun node mems s -> 
        s ^ sprintf "%s |-> %s\n" (Node.to_string node) (string_of_set Memory.to_string mems) 
      ) t "" ^ "}\n" 
end

open Value

let rec eval_call pgm fid actuals mem = 
  match find_method fid pgm.mthds, find_function fid pgm.funcs, find_predicate fid pgm.preds with 
  | None, Some func, None -> eval_function_call pgm func actuals mem 
  | None, None, None -> raise (SemanticError (sprintf "eval_call: %s not found" fid)) 
  | _ -> raise (SemanticError "eval_call: not implemented")

and eval_function_call : pgm -> func -> exp list -> Memory.t -> Value.t 
=fun pgm func actuals mem -> 
  if List.length actuals <> List.length func.args then 
    raise (SemanticError (sprintf "eval_call: # of actual and formual arguments do not match (%s)" func.fid))
  else 
    let mem = list_fold (fun ((_, formal, _), actual) -> 
                Memory.bind formal (eval pgm actual mem)
              ) (zip func.args actuals) mem in 
      eval pgm func.body mem 

and eval_binary pgm op e1 e2 mem = 
  match eval pgm e1 mem, eval pgm e2 mem with 
  | V_int n1, V_int n2 -> V_int (op n1 n2)
  | _ -> raise (SemanticError "eval_binary: type error")

and eval : pgm -> exp -> Memory.t -> Value.t 
=fun pgm e mem -> 
  match e with 
  | E_int n -> V_int n 
  | E_bool b -> V_bool b 
  | E_lv (V_var x) -> Memory.lookup x mem 
  | E_lv (V_arr (x, e)) -> 
    begin 
      match Memory.lookup x mem, eval pgm e mem with 
      | V_arr (size, elems), V_int idx -> 
        if idx >= size || idx < 0 
        then 
          begin 
            raise (SemanticError "array index out of bounds") 
          end 
        else V_int (List.nth elems idx)
      | _ -> raise (SemanticError "eval: array is expected")
    end 
  | E_add (e1, e2) -> eval_binary pgm (+) e1 e2 mem 
  | E_sub (e1, e2) -> eval_binary pgm (-) e1 e2 mem 
  | E_mul (e1, e2) -> eval_binary pgm ( * ) e1 e2 mem 
  | E_div (e1, e2) -> eval_binary pgm (/) e1 e2 mem 
  | E_mod (e1, e2) -> eval_binary pgm (mod) e1 e2 mem
  | E_and (e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_bool b1, V_bool b2 -> V_bool (b1 && b2)
      | _ -> raise (SemanticError "type error in e1 and e2")
    end  
  | E_or (e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_bool b1, V_bool b2 -> V_bool (b1 || b2)
      | _ -> raise (SemanticError "type error in e1 and e2")
    end  
  | E_neg e -> 
    begin 
      match eval pgm e mem with 
      | V_int n -> V_int (-n)
      | _ -> raise (SemanticError "E_neg: type error")
    end 
  | E_len x -> 
    begin 
      match Memory.lookup x mem with 
      | V_arr (size, _) -> V_int size 
      | _ -> raise (SemanticError "E_len: type error")
    end 
  | E_not e -> 
    begin 
      match eval pgm e mem with 
      | V_bool b -> V_bool (not b)
      | _ -> raise (SemanticError "E_not: type error")
    end 
  | E_cmp (Eq, e1, e2)  -> V_bool (eval pgm e1 mem = eval pgm e2 mem)
  | E_cmp (Neq, e1, e2) -> V_bool (eval pgm e1 mem <> eval pgm e2 mem)
  | E_cmp (Lt, e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_int n1, V_int n2 -> V_bool (n1 < n2)
      | _ -> raise (SemanticError "E_lt: type error")
    end 
  | E_cmp (Gt, e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_int n1, V_int n2 -> V_bool (n1 > n2)
      | _ -> raise (SemanticError "E_gt: type error")
    end 
  | E_cmp (Le, e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_int n1, V_int n2 -> V_bool (n1 <= n2)
      | _ -> raise (SemanticError "E_le: type error")
    end 
  | E_cmp (Ge, e1, e2) -> 
    begin 
      match eval pgm e1 mem, eval pgm e2 mem with 
      | V_int n1, V_int n2 -> V_bool (n1 >= n2) 
      | _ -> raise (SemanticError "E_ge: type error")
    end 
  | E_arr_update _ -> raise (Failure "E_arr: must not occur")
  | E_call (f, args) -> eval_call pgm f args mem
  | E_new _ -> raise (Failure "E_new: not yet implemented")
  | E_if (e1, e2, e3) -> 
    begin 
      match eval pgm e1 mem with 
      | V_bool true -> eval pgm e2 mem 
      | V_bool false -> eval pgm e3 mem 
      | _ -> raise (SemanticError "eval: type error in E_if (condition is not bool)")
    end

let run_node : pgm -> mthd -> Node.t -> Memory.t -> Memory.t option 
=fun pgm mthd node mem -> 
  match Node.get_instr node with 
  | I_skip | I_break | I_if_entry | I_if_exit | I_loop_entry | I_loop_exit 
  | I_function_entry | I_function_exit -> Some mem 
  | I_assign (V_var x, exp) -> Some (Memory.bind x (eval pgm exp mem) mem)
  | I_assign (V_arr (x, e), exp) -> 
    let (sz, elems) = 
      match Memory.lookup x mem with 
      | V_arr (sz, elems) -> (sz, elems)
      | _ -> raise (SemanticError ("run_node : " ^ (Node.to_string node) ^ " : array value is expected")) in 
    let pos = 
      match eval pgm e mem with 
      | V_int n -> n 
      | _ -> raise (SemanticError ("run_node : " ^ (Node.to_string node) ^ " : pos is not int")) in 
    let new_elem = 
     match eval pgm exp mem with 
     | V_int n -> n 
     | _ -> raise (SemanticError ("run_node: array elem must be integer")) in 
    let new_arr_val = V_arr (sz, replace_list_elem elems pos new_elem) in 
      Some (Memory.bind x new_arr_val mem)
  | I_assume e -> 
    begin 
      match eval pgm e mem with 
      | V_bool false -> None 
      | V_bool true -> Some mem 
      | _ -> raise (SemanticError "run_node : I_assume : type error")
    end 
  | I_return exps -> 
    begin 
      assert (List.length mthd.rvars = List.length exps); 
      let rvals = List.map (fun e -> eval pgm e mem) exps in 
        Some (list_fold (fun ((_, rv, _), rval) -> 
          Memory.bind rv rval 
        ) (zip mthd.rvars rvals) mem)
    end
  | I_new (x, exp) -> 
    begin 
      match eval pgm exp mem with 
      | V_int size -> Some (Memory.bind x (Value.new_array size) mem)
      | _ -> raise (SemanticError "run_node: I_new: type error")
    end     
  (* TODO *)
  | I_call _ -> raise (Failure "run_node: call is not yet implemented")

let run : pgm -> mthd -> Cfg.t -> Memory.t -> Memory.t * CollectingSemantics.t 
=fun pgm mthd cfg input_mem -> 
  let init_workset = [(Cfg.get_entry cfg, input_mem)] in 
  let rec iter workset cs = 
    match workset with 
    | [] -> raise (Failure "Interpreter.run: empty workset")
    | (node, mem)::workset' -> 
      let cs' = CollectingSemantics.add node mem cs in 
        if Cfg.is_exit node cfg then (mem, cs') 
        else 
          begin 
            match run_node pgm mthd node mem with 
            | None -> iter workset' cs' 
            | Some mem' -> 
              let next =  List.map (fun s -> (s, mem')) (NodeSet.elements (Cfg.succs node cfg)) in 
              iter (next@workset') cs' 
          end in 
  let output, cs = iter init_workset CollectingSemantics.empty  in 
    (output, cs)