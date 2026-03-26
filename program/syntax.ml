open Utils.Lib 

type id = string

type typ = 
  | T_int 
  | T_bool 
  | T_arr of typ 
  | T_func of typ list * typ 
  | T_pred of typ list 
  | T_mthd of typ list * typ list (* argument types, result types *)
  | T_tuple of typ list 
  
type exp = 
  | E_int of int 
  | E_bool of bool 
  | E_lv of lv 
  | E_arr_update of id * exp * exp (* single point variation of array *)
  | E_add of exp * exp 
  | E_sub of exp * exp 
  | E_mul of exp * exp 
  | E_div of exp * exp 
  | E_mod of exp * exp
  | E_and of exp * exp 
  | E_or of exp * exp 
  | E_neg of exp 
  | E_len of id 
  | E_not of exp 
  | E_cmp of cmpop * exp * exp 
  | E_call of id * exp list 
  | E_new of exp 
  | E_if of exp * exp * exp 

and cmpop = Eq | Neq | Le | Ge | Lt | Gt 
  
and lv = V_var of id | V_arr of id * exp 

type fmla = 
  | F_exp of exp 
  | F_order of exp list * exp list 
  | F_not of fmla 
  | F_and of fmla list 
  | F_or of fmla list 
  | F_imply of fmla * fmla 
  | F_iff of fmla * fmla 
  | F_forall of id * typ option * fmla 
  | F_exists of id * typ option * fmla 

type inv = fmla 
type rank = exp list 

type stmt = 
  | S_seq of stmt list 
  | S_skip 
  | S_assign of lv list * exp list
  | S_if of exp * stmt * stmt 
  | S_while of inv list * rank option * exp * stmt 
  | S_return of exp list 
  | S_break 

type decl = typ * id * exp option 

type mthd = {
  pre: fmla list; 
  post: fmla list; 
  rank: rank option; 
  id: id;    (* function name *)
  args: decl list; 
  rvars : decl list; (* return variables *)
  locals: decl list; 
  stmt: stmt; 
}

type pred = {
  name : id; 
  args : decl list; 
  fmla : fmla; 
}

type func = {
  fid : id; 
  args : decl list; 
  ret_ty : typ; 
  body : exp; 
}

type global = Mthd of mthd | Pred of pred | Func of func

type pgm = {
  preds : pred list; 
  mthds : mthd list; 
  funcs : func list; 
}

(******************************)

let add_initializers : decl list -> stmt list 
=fun decls -> 
  list_fold (fun (_, x, expopt) acc -> 
    match expopt with 
    | Some exp -> acc@[S_assign ([V_var x], [exp])]
    | None -> acc
  ) decls [] 

let create_method body pre post rank rvars id args locals = {
  pre = pre; 
  post = post; 
  rank = rank; 
  rvars = rvars; 
  id = id; 
  args = args; 
  locals = locals; 
  stmt = S_seq ((add_initializers locals) @ [body])
}

let create_predicate name args fmla = { name = name; args = args; fmla = fmla; }

let create_function name args ret_ty body = { fid = name; args = args; ret_ty = ret_ty; body = body}

let create_program globals = 
   ([], [], [])
  |> list_fold (fun global (preds, mthds, funcs) -> 
      match global with 
      | Mthd m -> (preds, m::mthds, funcs)
      | Pred p -> (p::preds, mthds, funcs)
      | Func f -> (preds, mthds, f::funcs)
    ) globals 
  |> fun (preds, mthds, funcs) -> { preds = preds; mthds = mthds; funcs = funcs }

let _var_id = ref 0 
let new_var() = _var_id := !_var_id + 1; "x" ^ string_of_int (!_var_id)

let find_function : id -> func list -> func option 
=fun x funcs -> 
  try Some (List.find (fun func -> func.fid = x) funcs)
  with _ -> None 

let find_predicate : id -> pred list -> pred option 
=fun x preds -> 
  try Some (List.find (fun pred -> pred.name = x) preds)
  with _ -> None 

let find_method : id -> mthd list -> mthd option 
=fun x mthds -> 
  try Some (List.find (fun mthd -> mthd.id = x) mthds)
  with _ -> None 
  
let is_all_vars lvs = List.for_all (fun lv -> match lv with V_var _ -> true | _ -> false) lvs

let is_method fid pgm = 
  match List.find_opt (fun mthd -> mthd.id = fid) pgm.mthds with 
  | Some _ -> true 
  | None -> false 

let rec replace_exp : id -> exp -> exp -> exp 
=fun x e exp -> 
  match exp with 
  | E_int n -> E_int n 
  | E_bool b -> E_bool b 
  | E_lv (V_var y) -> if x = y then e else exp 
  | E_lv (V_arr (y, e1)) -> 
    if x = y then 
      match e with 
      | E_lv (V_var z) -> E_lv (V_arr (z, replace_exp x e e1))
      | _ -> raise (Failure "Syntax.replace_exp: cannot replace array name by an expression")
    else E_lv (V_arr (y, replace_exp x e e1))
  | E_arr_update (y, e1, e2) -> 
    if x = y then 
      match e with 
      | E_lv (V_var z) -> E_arr_update (z, replace_exp x e e1, replace_exp x e e2)
      | _ -> raise (Failure "Syntax.replace_exp: cannot replace array name by an expression")
    else E_arr_update (y, replace_exp x e e1, replace_exp x e e2)
  | E_add (e1, e2) -> E_add (replace_exp x e e1, replace_exp x e e2)
  | E_sub (e1, e2) -> E_sub (replace_exp x e e1, replace_exp x e e2)
  | E_mul (e1, e2) -> E_mul (replace_exp x e e1, replace_exp x e e2)
  | E_div (e1, e2) -> E_div (replace_exp x e e1, replace_exp x e e2)
  | E_mod (e1, e2) -> E_mod (replace_exp x e e1, replace_exp x e e2)
  | E_and (e1, e2) -> E_and (replace_exp x e e1, replace_exp x e e2)
  | E_or (e1, e2) -> E_or (replace_exp x e e1, replace_exp x e e2)
  | E_neg e1 -> E_neg (replace_exp x e e1)
  | E_len y -> 
    if x = y then 
      match e with 
      | E_lv (V_var z) -> E_len z 
      | _ -> raise (Failure "Syntax.replace_exp: cannot replace length name by an expression")
    else E_len y 
  | E_not e1 -> E_not (replace_exp x e e1)
  | E_cmp (op, e1, e2) -> E_cmp (op, replace_exp x e e1, replace_exp x e e2)
  | E_call (fid, exps) -> E_call (fid, List.map (replace_exp x e) exps)
  | E_new exp -> E_new (replace_exp x e exp)
  | E_if (e1, e2, e3) -> E_if (replace_exp x e e1, replace_exp x e e2, replace_exp x e e3)

and replace_fmla : id -> exp -> fmla -> fmla 
=fun x e f -> 
  match f with 
  | F_exp exp -> F_exp (replace_exp x e exp)
  | F_order (es1, es2) -> F_order (List.map (replace_exp x e) es1, List.map (replace_exp x e) es2)
  | F_not f1 -> F_not (replace_fmla x e f1)
  | F_and fs -> F_and (List.map (replace_fmla x e) fs)
  | F_or fs -> F_or (List.map (replace_fmla x e) fs)
  | F_imply (f1, f2) -> F_imply (replace_fmla x e f1, replace_fmla x e f2)
  | F_iff (f1, f2) -> F_iff (replace_fmla x e f1, replace_fmla x e f2)
  | F_forall (y, typ, f1) -> 
    let fresh_var = new_var() in 
      let body = rename_fmla y fresh_var f1 (* avoid variable capture *) in 
        F_forall (fresh_var, typ, replace_fmla x e body)
  | F_exists (y, typ, f1) -> 
    let fresh_var = new_var() in 
      let body = rename_fmla y fresh_var f1 (* avoid variable capture *) in 
        F_exists (fresh_var, typ, replace_fmla x e body)

and rename_exp : id -> id -> exp -> exp 
=fun x x' e -> replace_exp x (E_lv (V_var x')) e 

and rename_fmla : id -> id -> fmla -> fmla 
=fun x x' f -> replace_fmla x (E_lv (V_var x')) f 

module Prenex = struct
  type quantifier = FORALL of id | EXISTS of id 
  type t = quantifier list * fmla 

  let rec no_quantifiers : fmla -> bool 
  =fun f -> 
    match f with 
    | F_exp _ -> true 
    | F_order _ -> true 
    | F_not f1 -> no_quantifiers f1 
    | F_and fs  
    | F_or fs -> List.for_all no_quantifiers fs
    | F_imply (f1, f2)
    | F_iff (f1, f2) -> no_quantifiers f1 && no_quantifiers f2 
    | F_forall _ 
    | F_exists _ -> false 

  let rec is_prenex : fmla -> bool 
  =fun f -> 
    match f with 
    | F_forall (_, _, body) -> is_prenex body 
    | F_exists (_, _, body) -> is_prenex body 
    | _ -> no_quantifiers f 

  let rec from_fmla : fmla -> t 
  =fun f ->
    assert (is_prenex f); 
    match f with 
    | F_forall (x, _, f1) -> 
      let (qs, body) = from_fmla f1 in 
        (FORALL x::qs, body)
    | F_exists (x, _, f1) -> 
      let (qs, body) = from_fmla f1 in 
        (EXISTS x::qs, body)
    | _ -> ([], f) 
  
  let body_of : t -> fmla 
  =fun (_, body) -> body 

  let quantifiers_of : t -> quantifier list 
  =fun (qs, _) -> qs 

  let quantified_vars_of : t -> id list 
  =fun (qs, _) -> 
    let xs = 
      List.map (fun q -> 
        match q with 
        | FORALL x -> x 
        | EXISTS x -> x) qs in 
      prerr_endline (string_of_list (fun x -> x) xs); 
      xs 

  let make : quantifier list -> fmla -> t 
  =fun qs f -> (qs, f)
  
  let prenex2fmla : t -> fmla 
  =fun (qs, body) -> 
    List.fold_right (fun q f -> 
      match q with 
      | FORALL x -> F_forall (x, Some T_int, f)
      | EXISTS x -> F_exists (x, Some T_int, f)
    ) qs body 
end 