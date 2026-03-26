open Syntax
open Pp 
open Utils.Lib
open Printf 

let type_of_exp : exp -> typ 
=fun _ -> Syntax.T_int  

module TyEnv = struct
  type t = (id, typ) BatMap.t 
  let empty = BatMap.empty 
  let add = BatMap.add 
  let find = BatMap.find 
  let to_string m = 
    BatMap.foldi (fun x ty str -> 
      str ^ sprintf "%s |-> %s\n" x (string_of_typ ty)
    ) m ""
end 

let typeof_pred (pred : pred) = T_pred (List.map fst3 pred.args)
let typeof_mthd (mthd : mthd) = T_mthd (List.map fst3 mthd.args, List.map fst3 mthd.rvars)
let typeof_func (func : func) = T_func (List.map fst3 func.args, func.ret_ty)

let rec check_arg_types tyenv declared_args_types args = 
  let args_types = args |> List.map (check_types_exp tyenv) in 
    List.for_all (fun (dat, at) -> 
      match at with 
      | Some dat' -> dat = dat'
      | _ -> false 
    ) (zip declared_args_types args_types) 

and is_int_type_exp : TyEnv.t -> exp -> bool 
=fun tyenv e -> 
  match check_types_exp tyenv e with 
  | Some T_int -> true 
  | _ -> false 

and is_int_type_exps : TyEnv.t -> exp list -> bool 
=fun tyenv exps -> List.for_all (is_int_type_exp tyenv) exps

and is_bool_type_exp : TyEnv.t -> exp -> bool 
=fun tyenv e -> 
  match check_types_exp tyenv e with 
  | Some T_bool -> true 
  | _ -> false   

and is_bool_type_exps : TyEnv.t -> exp list -> bool 
=fun tyenv exps -> List.for_all (is_bool_type_exp tyenv) exps
  
and is_arr_type_exp : TyEnv.t -> exp -> bool 
=fun tyenv e -> 
  match check_types_exp tyenv e with 
  | Some (T_arr _) -> true 
  | _ -> false   
  
and check_types_exp : TyEnv.t -> exp -> typ option 
=fun tyenv exp -> 
  match exp with 
  | E_int _ -> Some T_int 
  | E_bool _ -> Some T_bool 
  | E_lv (V_var x) -> begin try Some (TyEnv.find x tyenv) with _ -> None end 
  | E_lv (V_arr (a, idx)) -> begin 
      match TyEnv.find a tyenv, check_types_exp tyenv idx with 
      | T_arr elem_ty, Some T_int -> Some elem_ty
      | _ -> None 
    end 
  | E_add (e1, e2)
  | E_sub (e1, e2)
  | E_mul (e1, e2)
  | E_div (e1, e2)
  | E_mod (e1, e2) -> if is_int_type_exps tyenv [e1; e2] then Some T_int else None
  | E_and (e1, e2) 
  | E_or (e1, e2) -> if is_bool_type_exps tyenv [e1; e2] then Some T_bool else None
  | E_neg e1 -> if is_int_type_exp tyenv e1 then Some T_int else None 
  | E_len x -> if is_arr_type_exp tyenv (E_lv (V_var x)) then Some T_int else None 
  | E_not e1 -> if is_bool_type_exp tyenv e1 then Some T_bool else None 
  | E_cmp (Eq, e1, e2) 
  | E_cmp (Neq, e1, e2) -> 
    begin 
      match check_types_exp tyenv e1, check_types_exp tyenv e2 with 
      | Some ty1, Some ty2 when ty1 = ty2 -> Some T_bool 
      | _ -> None 
    end 
  | E_cmp (Lt, e1, e2)
  | E_cmp (Le, e1, e2)
  | E_cmp (Gt, e1, e2)
  | E_cmp (Ge, e1, e2) -> if is_int_type_exps tyenv [e1; e2] then Some T_bool else None 
  | E_call (fid, args) -> begin 
      match TyEnv.find fid tyenv with 
      | T_pred declared_args_types -> 
        if check_arg_types tyenv declared_args_types args then Some T_bool 
        else None
      | T_func (declared_args_types, typ) -> 
        if check_arg_types tyenv declared_args_types args then Some typ
        else None
      | T_mthd (declared_args_types, ret_types) -> 
        if check_arg_types tyenv declared_args_types args then Some (T_tuple ret_types)
        else None 
      | _ -> None 
    end 
  | E_new e1 -> if is_int_type_exp tyenv e1 then Some (T_arr T_int) else None 
  | E_if (e1, e2, e3) -> 
    if is_bool_type_exp tyenv e1 then 
      match check_types_exp tyenv e2, check_types_exp tyenv e3 with 
      | Some ty1, Some ty2 when ty1 = ty2 -> Some ty1 
      | _ -> None 
    else None 
  | E_arr_update _ -> failwith ("Typechecker: arr_update must not occur")

let rec check_types_fmla : TyEnv.t -> fmla -> typ option 
=fun tyenv fmla -> 
  match fmla with 
  | F_exp exp -> check_types_exp tyenv exp 
  | F_order (exps1, exps2) -> begin 
      if List.length exps1 = List.length exps2 && 
         List.for_all (is_int_type_exp tyenv) exps1 && 
         List.for_all (is_int_type_exp tyenv) exps2 
      then Some T_bool 
      else None 
    end 
  | F_not fmla -> if is_well_typed_fmla tyenv fmla then Some T_bool else None 
  | F_and fmlas 
  | F_or fmlas -> if is_well_typed_fmlas tyenv fmlas then Some T_bool else None 
  | F_imply (f1, f2) 
  | F_iff (f1, f2) -> if is_well_typed_fmlas tyenv [f1; f2] then Some T_bool else None 
  | F_forall (i, _, fmla) -> (* assumption: all quantified vars are int *)
    if is_well_typed_fmla (TyEnv.add i T_int tyenv) fmla then Some T_bool else None 
  | F_exists (i, _, fmla) -> 
    if is_well_typed_fmla (TyEnv.add i T_int tyenv) fmla then Some T_bool else None 

and is_well_typed_fmla tyenv fmla = 
  match check_types_fmla tyenv fmla with 
  | Some T_bool -> true 
  | _ -> false 

and is_well_typed_fmlas tyenv fmlas = List.for_all (is_well_typed_fmla tyenv) fmlas

let check_types_pred : TyEnv.t -> pred -> bool
=fun tyenv pred -> 
  prerr_endline (sprintf "Predicate %s" pred.name); 
  tyenv
  |> list_fold (fun (typ, arg, _) -> TyEnv.add arg typ) pred.args 
  |> (fun tyenv -> check_types_fmla tyenv pred.fmla <> None)

let rec check_types_mthd : pgm -> TyEnv.t -> mthd -> bool
=fun pgm tyenv mthd -> 
  prerr_endline (sprintf "Method %s" mthd.id);   
  check_types_mthd_pre tyenv mthd && 
  check_types_mthd_post tyenv mthd && 
  check_types_mthd_rank tyenv mthd && 
  check_types_mthd_body pgm tyenv mthd 

and check_types_mthd_pre tyenv mthd = 
  let tyenv = tyenv |> list_fold (fun (ty, arg, _) -> TyEnv.add arg ty) mthd.args in 
    List.for_all (fun f -> 
      prerr_endline (sprintf "  - pre: %s" (string_of_fmla f));
      is_well_typed_fmla tyenv f
    ) mthd.pre 

and check_types_mthd_post tyenv mthd = 
  let tyenv = tyenv |> list_fold (fun (ty, arg, _) -> TyEnv.add arg ty) (mthd.args @ mthd.rvars) in 
    List.for_all (fun f -> 
      prerr_endline (sprintf "  - post: %s" (string_of_fmla f));
      is_well_typed_fmla tyenv f
    ) mthd.post

and check_types_mthd_rank tyenv mthd = 
  let tyenv = tyenv |> list_fold (fun (ty, arg, _) -> TyEnv.add arg ty) (mthd.args @ mthd.rvars) in 
    match mthd.rank with 
    | Some exps -> 
      prerr_endline (sprintf "  - rank: %s" (string_of_rank exps));
      List.for_all (is_int_type_exp tyenv) exps 
    | None -> true 

and check_types_mthd_body pgm tyenv mthd = 
  let tyenv = tyenv |> list_fold (fun (ty, arg, _) -> TyEnv.add arg ty) (mthd.args @ mthd.rvars @ mthd.locals) in 
    (prerr_endline (sprintf "  - body: well-formedness"); check_mthd_body_well_formed pgm mthd.stmt) && 
    (prerr_endline (sprintf "  - body: well-typedness");  check_types_stmt pgm tyenv mthd.stmt)

and check_mthd_body_well_formed pgm body = 
  (* 
    1. method call must be of the form "x, y, ... := M()", i.e., no method calls inside expressions 
    2. "new" must be of the form "x := new [...]"
  *)
  match body with 
  | S_skip -> true 
  | S_seq stmts -> check_mthd_body_well_formed_list pgm stmts 
  | S_assign (lvs, [E_call(fid, args)]) when is_method fid pgm && is_all_vars lvs -> no_mthd_calls_and_new_list pgm args
  | S_assign ([V_var _], [E_new size]) -> no_mthd_calls_and_new pgm size 
  | S_assign (_, exps) -> no_mthd_calls_and_new_list pgm exps 
  | S_if (e, s1, s2) -> no_mthd_calls_and_new pgm e && check_mthd_body_well_formed_list pgm [s1; s2]
  | S_while (_, _, e, s) -> no_mthd_calls_and_new pgm e && check_mthd_body_well_formed pgm s
  | S_return exps -> no_mthd_calls_and_new_list pgm exps 
  | S_break -> true 

and check_mthd_body_well_formed_list pgm stmts = List.for_all (check_mthd_body_well_formed pgm) stmts 

and no_mthd_calls_and_new pgm exp = 
  match exp with 
  | E_int _ | E_bool _ | E_lv _ | E_len _ -> true 
  | E_arr_update (_, e1, e2) -> no_mthd_calls_and_new_list pgm [e1; e2]
  | E_add (e1, e2) | E_sub (e1, e2) | E_mul (e1, e2) | E_div (e1, e2) 
  | E_mod (e1, e2) | E_and (e1, e2) | E_or (e1, e2) 
  | E_cmp (_, e1, e2) -> no_mthd_calls_and_new_list pgm [e1; e2] 
  | E_neg e1 | E_not e1 -> no_mthd_calls_and_new pgm e1 
  | E_if (e1, e2, e3) -> no_mthd_calls_and_new_list pgm [e1; e2; e3]
  | E_call (fid, exps) -> not (is_method fid pgm) && no_mthd_calls_and_new_list pgm exps 
  | E_new _ -> false 

and no_mthd_calls_and_new_list pgm exps = List.for_all (no_mthd_calls_and_new pgm) exps 
   
and check_types_stmt : pgm -> TyEnv.t -> stmt -> bool 
=fun pgm tyenv stmt ->  
  match stmt with 
  | S_skip -> true 
  | S_seq stmts -> List.for_all (check_types_stmt pgm tyenv) stmts 
  | S_assign (lvs, [E_call(fid, args)]) when is_method fid pgm && is_all_vars lvs -> 
    begin 
      try 
        let actual_arg_types = 
          args 
          |> List.map (check_types_exp tyenv)
          |> List.map option2elem in 
        let lvs_types = 
          lvs 
          |> List.map (fun lv -> E_lv lv)
          |> List.map (check_types_exp tyenv)
          |> List.map option2elem in 
          begin 
            match find_method fid pgm.mthds with 
            | Some mthd -> 
              begin 
                match typeof_mthd mthd with 
                | T_mthd (formal_arg_types, res_types) -> formal_arg_types = actual_arg_types && lvs_types = res_types 
                | _ -> failwith "check_types_stmt: must not occur"
              end 
            | None -> failwith "check_types_stmt: must not occur" 
          end 
      with _ -> (prerr_endline "      * type error: assign1"; false)
    end 
  | S_assign (lvs, exps) -> 
    begin 
      try 
        let lvs_types = lvs |> List.map (fun lv -> check_types_exp tyenv (E_lv lv)) |> List.map option2elem in 
        let exps_types = exps |> List.map (check_types_exp tyenv) |> List.map option2elem in 
          lvs_types = exps_types 
      with _ -> (prerr_endline "      * type error: assign2"; false) 
    end 
  | S_if (e, s1, s2) -> 
    begin 
      match check_types_exp tyenv e with 
      | Some _ -> check_types_stmt pgm tyenv s1 && check_types_stmt pgm tyenv s2 
      | _ -> (prerr_endline "      * type error: if"; false) 
    end 
  | S_while (invs, _, e, s) -> 
    List.for_all (fun inv -> 
      match check_types_fmla tyenv inv with 
      | Some _ -> true 
      | _ -> (prerr_endline "    * type error: while loop invaraint"; false)
    ) invs 
    &&   
    begin 
      match check_types_exp tyenv e with 
      | Some _ -> check_types_stmt pgm tyenv s
      | _ -> (prerr_endline "      * type error: while"; false) 
    end 
  | S_return exps -> 
    begin 
      try 
        exps 
        |> List.map (check_types_exp tyenv) 
        |> List.map option2elem
        |> fun _ -> true
      with _ -> (prerr_endline "      * type error: return"; false) 
    end 
  | S_break -> true 

let check_types_func : TyEnv.t -> func -> bool
=fun tyenv func -> 
  prerr_endline (sprintf "Function %s" func.fid); 
  ignore (tyenv, func); true 

let check_types : pgm -> bool 
=fun pgm -> 
  let tyenv = 
    TyEnv.empty 
    |> list_fold (fun pred -> TyEnv.add pred.name (typeof_pred pred)) pgm.preds 
    |> list_fold (fun mthd -> TyEnv.add mthd.id (typeof_mthd mthd)) pgm.mthds 
    |> list_fold (fun func -> TyEnv.add func.fid (typeof_func func)) pgm.funcs in 
    List.for_all (check_types_pred tyenv) pgm.preds && 
    List.for_all (check_types_mthd pgm tyenv) pgm.mthds && 
    List.for_all (check_types_func tyenv) pgm.funcs 

let no_global_name_conflicts : pgm -> bool 
=fun pgm -> 
  let pred_names = List.map (fun pred -> pred.name) pgm.preds in 
  let mthd_names = List.map (fun mthd -> mthd.id) pgm.mthds in 
  let func_names = List.map (fun func -> func.fid) pgm.funcs in 
  let all_names = pred_names @ mthd_names @ func_names in 
  let count_map = 
    list_fold (fun name map -> 
      let count = try BatMap.find name map with _ -> 0 in 
        BatMap.add name (count + 1) map 
    ) all_names BatMap.empty in 
  let conflicts = 
    BatMap.foldi (fun name count acc -> 
      if count > 1 then name::acc else acc 
    ) count_map [] in 
    if conflicts <> [] then 
      (prerr_endline (sprintf "Type Error: global name conflicts (%s)" (string_of_list id conflicts ~first:"" ~last:"" ~sep:", ")); 
      false)
    else true 

let check_pgm : pgm -> bool  
=fun pgm -> 
  prerr_endline ""; 
  prerr_endline "-- Typechecker begins --\n"; 
  if no_global_name_conflicts pgm && 
     check_types pgm 
  then true
  else failwith "Typechecker failed"