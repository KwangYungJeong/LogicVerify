open Syntax 
open Utils.Lib 
open Printf 

let rec string_of_typ : typ -> string 
=fun t ->  
  match t with
  | T_int     -> "Int"
  | T_bool    -> "Bool"
  | T_arr t1  -> (string_of_typ t1) ^ "[]"
  | T_func (_, _) -> "Func" (* TODO *)
  | T_pred _ -> "Pred" (* TODO *)
  | T_mthd _ -> "Mthd" (* TODO *)
  | T_tuple _ -> "Tuple" (* TODO *)

and string_of_exp : exp -> string
=fun e -> 
  match e with
  | E_int   n1          -> (string_of_int n1)
  | E_bool  b1          -> (if b1 then "true" else "false")
  | E_lv    v1          -> (string_of_lv v1)
  | E_arr_update   (x1, e2, e3) -> x1 ^ "<" ^ string_of_exp e2 ^ ":" ^ string_of_exp e3 ^ ">"
  | E_add   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " + " ^ (string_of_exp e2) ^ ")"
  | E_sub   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " - " ^ (string_of_exp e2) ^ ")"
  | E_mul   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " * " ^ (string_of_exp e2) ^ ")"
  | E_div   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " / " ^ (string_of_exp e2) ^ ")"
  | E_mod   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " % " ^ (string_of_exp e2) ^ ")"
  | E_and   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " && " ^ (string_of_exp e2) ^ ")"
  | E_or   (e1, e2)    -> "(" ^ (string_of_exp e1) ^ " || " ^ (string_of_exp e2) ^ ")"
  | E_neg   e1          -> "-" ^ (string_of_exp e1)
  | E_len   id1         -> "|" ^ id1 ^ "|"
  | E_not   e1          -> "!" ^ (string_of_exp e1)
  | E_cmp  (Eq, e1, e2) -> "(" ^ (string_of_exp e1) ^ " == " ^ (string_of_exp e2) ^ ")"
  | E_cmp  (Neq, e1, e2) -> "(" ^ (string_of_exp e1) ^ " != " ^ (string_of_exp e2) ^ ")"
  | E_cmp  (Le, e1, e2) -> "(" ^ (string_of_exp e1) ^ " <= " ^ (string_of_exp e2) ^ ")"
  | E_cmp  (Lt, e1, e2) -> "(" ^ (string_of_exp e1) ^ " < " ^ (string_of_exp e2) ^ ")"
  | E_cmp  (Ge, e1, e2) -> "(" ^ (string_of_exp e1) ^ " >= " ^ (string_of_exp e2) ^ ")"
  | E_cmp  (Gt, e1, e2) -> "(" ^ (string_of_exp e1) ^ " > " ^ (string_of_exp e2) ^ ")"
  | E_call  (fid, exps) -> fid ^ string_of_list string_of_exp exps 
  | E_new e -> sprintf "new [%s]" (string_of_exp e)
  | E_if (e1, e2, e3) -> sprintf "if %s then %s else %s" (string_of_exp e1) (string_of_exp e2) (string_of_exp e3)

and string_of_lv : lv -> string
=fun v -> 
  match v with
  | V_var id1       -> id1
  | V_arr (id1, e2)  -> id1 ^ "[" ^ (string_of_exp e2) ^ "]"

let rec string_of_fmla : fmla -> string
=let ts = string_of_fmla in 
  fun f -> 
  match f with
  | F_exp     e1        -> (e1 |> string_of_exp)
  | F_order   (es1, es2) -> "(" ^ string_of_list string_of_exp es1 ^ " < " ^ string_of_list string_of_exp es2 ^ ")"
  | F_not     f1        -> "~(" ^ (f1 |> ts) ^ ")"
  | F_and     fl1       -> "(" ^ (fl1 |> List.map ts |> String.concat " && ") ^ ")"
  | F_or      fl1       -> "(" ^ (fl1 |> List.map ts |> String.concat " || ") ^ ")"
  | F_imply   (f1, f2)  -> "(" ^ (f1 |> ts) ^ " -> "  ^ (f2 |> ts) ^ ")"
  | F_iff     (f1, f2)  -> "(" ^ (f1 |> ts) ^ " <-> " ^ (f2 |> ts) ^ ")"
  | F_forall  (x1, Some t1, f2)  -> "(forall " ^ (x1) ^ ":" ^ string_of_typ t1 ^ " :: " ^ (f2 |> ts) ^ ")"
  | F_exists  (x1, Some t1, f2)  -> "(exists " ^ (x1) ^ ":" ^ string_of_typ t1 ^ " :: " ^ (f2 |> ts) ^ ")"
  | F_forall  (x1, None, f2)  -> "(forall " ^ (x1) ^ " :: " ^ (f2 |> ts) ^ ")"
  | F_exists  (x1, None, f2)  -> "(exists " ^ (x1) ^ " :: " ^ (f2 |> ts) ^ ")"

let string_of_inv : inv -> string 
=fun f -> string_of_fmla f 

let string_of_rank : rank -> string
=fun r -> "#rank: " ^ string_of_list string_of_exp r 

let string_of_stmt : ?indent:int -> stmt -> string
=fun ?(indent=0) s -> 
  let rec inner_to_string : ?depth:int -> stmt -> string 
  =fun ?(depth=indent+1) s -> begin
    let its = inner_to_string ~depth in 
    let its_deep = inner_to_string ~depth:(depth + 1) in 
    let tb = char_of_int 9 in (* \t *)
    let idt = String.make depth tb in (* \t * depth *)
    match s with
    | S_seq     sl1               -> sl1 |> List.map its |> String.concat "\n"
    | S_skip                      -> idt ^ "skip;"
    | S_assign  (v1, e2)          -> idt ^ (v1 |> List.map string_of_lv |> String.concat ", ") ^ " := " ^ (e2 |> List.map string_of_exp |> String.concat ", ") ^ ";"
    | S_if      (e1, s2, s3)      -> idt ^ "if (" ^ (e1 |> string_of_exp) ^ ") {\n" ^
                                        (s2 |> its_deep) ^ "\n" ^
                                      idt ^ "} {\n" ^
                                        (s3 |> its_deep) ^ "\n" ^
                                      idt ^ "}"
    | S_while   (i1, r2, e3, s4)  -> idt ^ "while " ^ (e3 |> string_of_exp) ^ "\n" ^

                                     list_fold (fun inv acc -> 
                                      acc ^ idt ^ "invariant " ^ string_of_inv inv ^ "\n"
                                     ) i1 "" ^
                                      (if (r2 |> Option.is_some) then (idt ^ "\t" ^ (r2 |> Option.value ~default:[] |> string_of_rank) ^ "\n") else "") ^
                                      idt ^ "{\n" ^
                                        (s4 |> its_deep) ^ "\n" ^
                                      idt ^ "}"
    | S_return exps -> idt ^ "return " ^ (exps |> List.map string_of_exp |> String.concat ", ") ^ ";"
    | S_break                     -> idt ^ "break;"
    (* inner_to_string function end *)
  end in
  inner_to_string s
  (* to_string function end *)  

let string_of_decl (t1, id1, expopt) = 
  match expopt with 
  | Some exp -> sprintf "%s %s := %s;" (t1 |> string_of_typ) id1 (string_of_exp exp)
  | None -> sprintf "%s %s;" (t1 |> string_of_typ) id1 

let string_of_mthd : ?indent:int -> mthd -> string
=fun ?(indent=0) { pre; post; rank; rvars; id; args; locals; stmt } -> 
  let tb = char_of_int 9 in (* \t *)
  let idt = String.make indent tb in (* \t * depth *)
  list_fold (fun pre acc -> 
    acc ^ idt ^ "requires " ^ (pre |> string_of_fmla) ^ "\n" 
  ) pre "" ^ 
  list_fold (fun post acc -> 
    acc ^ idt ^ "ensures " ^ (post |> string_of_fmla) ^ "\n" 
  ) post "" ^ 
  idt ^ (if (rank |> Option.is_some) then ((rank |> Option.value ~default:[] |> string_of_rank) ^ "\n") else "") ^
  idt ^ " " ^ id ^ " (" ^ (args |> List.map string_of_decl |> String.concat ", ") ^ ")" ^ 
    "returns (" ^ (rvars |> List.map string_of_decl |> String.concat ", ") ^ ") {\n" ^
  idt ^ "\t// locals: (" ^ (locals |> List.map string_of_decl |> String.concat ", ") ^ ")\n" ^
  (stmt |> string_of_stmt ~indent:(indent+1)) ^ "\n" ^
  idt ^ "}\n\n"

let string_of_pred : ?indent:int -> pred -> string 
=fun ?(indent=0) { name; args; fmla } ->
  ignore indent; 
  sprintf "predicate %s (%s)\n" name (string_of_list string_of_decl args) ^
  sprintf "{" ^ 
  sprintf "    %s" (string_of_fmla fmla) ^
  sprintf "}\n\n"

let string_of_func : ?indent:int -> func -> string 
=fun ?(indent=0) { fid; args; ret_ty; body } ->
  ignore indent; 
  sprintf "function %s (%s) : %s\n" fid (string_of_list string_of_decl args) (string_of_typ ret_ty) ^
  sprintf "{" ^ 
  sprintf "    %s" (string_of_exp body) ^
  sprintf "}\n\n"
  

let string_of_pgm ?(indent=0) { preds; mthds; funcs; } = 
  string_of_list (string_of_pred ~indent:indent) preds ~sep:"" ~first:"" ~last:"" ^ 
  string_of_list (string_of_mthd ~indent:indent) mthds ~sep:"" ~first:"" ~last:"" ^
  string_of_list (string_of_func ~indent:indent) funcs ~sep:"" ~first:"" ~last:""