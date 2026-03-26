open Syntax
open Utils.Lib

let lvs_are_vars lvs = List.for_all (fun lv -> match lv with V_var _ -> true | _ -> false) lvs

let is_method fid pgm = 
  match List.find_opt (fun mthd -> mthd.id = fid) pgm.mthds with 
  | Some _ -> true 
  | None -> false 

let make_tmp_vars : typ list -> decl list 
=fun types -> List.map (fun ty -> (ty, new_var(), None)) types

let rec multi_assign_stmt : pgm -> mthd -> stmt -> stmt * decl list 
=fun pgm mthd stmt -> 
  match stmt with 
  | S_assign (lvs, [E_call(fid, _)]) when is_method fid pgm && lvs_are_vars lvs -> stmt, []
  | S_assign ([lv], [e]) -> S_assign ([lv], [e]), []
  | S_assign (lvs, exps) when List.length lvs = List.length exps -> 
    let tmp_vars = make_tmp_vars (List.map Typechecker.type_of_exp exps) in 
    let exps2tmps = List.map (fun ((_, x, _), e) -> S_assign ([V_var x], [e])) (zip tmp_vars exps) in 
    let tmps2lvs = List.map (fun (lv, (_, x, _)) -> S_assign ([lv], [E_lv (V_var x)])) (zip lvs tmp_vars) in 
      (S_seq (exps2tmps @ tmps2lvs), tmp_vars)
  | S_assign _ -> failwith "Desugar.multi_assign_mthd: S_assign"
  | S_seq stmts -> 
      List.map (fun stmt -> multi_assign_stmt pgm mthd stmt) stmts
      |> (fun res -> S_seq (List.map fst res), 
                     List.map snd res |> List.fold_left List.append [])
  | S_skip -> S_skip, []
  | S_if (e, s1, s2) -> 
    let s1, tmp_vars1 = multi_assign_stmt pgm mthd s1 in 
    let s2, tmp_vars2 = multi_assign_stmt pgm mthd s2 in 
      S_if (e, s1, s2), tmp_vars1 @ tmp_vars2
  | S_while (invs, rank, exp, stmt) -> 
    let stmt, tmp_vars = multi_assign_stmt pgm mthd stmt in 
      S_while (invs, rank, exp, stmt), tmp_vars
  | S_return exps -> S_return exps, []
  | S_break -> S_break, [] 

let multi_assign_mthd : pgm -> mthd -> mthd
=fun pgm mthd -> 
  let s, tmp_vars = multi_assign_stmt pgm mthd mthd.stmt in 
  { 
    mthd with 
      stmt = s; 
      locals = mthd.locals @ tmp_vars 
  }

let rec is_comparison_chain : exp -> bool 
=fun exp -> 
  match exp with 
  | E_cmp (_, e1, e2) when is_not_comparison_chain e1 && is_not_comparison_chain e2 -> true 
  | E_cmp (_, e1, e2) -> is_comparison_chain e1 && is_not_comparison_chain e2 
  | _ -> false 

and is_not_comparison_chain : exp -> bool 
=fun exp -> 
  match exp with 
  | E_cmp _ -> false 
  | _ -> true 

let rec chain2tree : exp -> exp * exp 
=fun exp -> 
  match exp with 
  | E_cmp (cmpop, e1, e2) when is_comparison_chain e1 -> 
    let left, rhs = chain2tree e1 in 
      (E_and (left, E_cmp (cmpop, rhs, e2)), e2)
  | E_cmp (_, _, e2) -> (exp, e2)
  | _ -> (exp, exp)

let rec comparison_chain_exp : pgm -> exp -> exp 
=fun pgm exp -> 
  if is_comparison_chain exp then fst (chain2tree exp)
  else 
    match exp with 
    | E_int _ | E_bool _ | E_lv _ | E_arr_update _ | E_len _ -> exp 
    | E_add (e1, e2) -> E_add (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_sub (e1, e2) -> E_sub (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_mul (e1, e2) -> E_mul (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_div (e1, e2) -> E_div (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_mod (e1, e2) -> E_mod (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_and (e1, e2) -> E_and (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_or  (e1, e2) -> E_or  (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_neg e -> E_neg (comparison_chain_exp pgm e)
    | E_not e -> E_not (comparison_chain_exp pgm e)
    | E_cmp (cmpop, e1, e2) -> E_cmp (cmpop, comparison_chain_exp pgm e1, comparison_chain_exp pgm e2)
    | E_call (x, exps) -> E_call (x, comparison_chain_exps pgm exps)
    | E_new e -> E_new (comparison_chain_exp pgm e)
    | E_if (e1, e2, e3) -> E_if (comparison_chain_exp pgm e1, comparison_chain_exp pgm e2, comparison_chain_exp pgm e3)

and comparison_chain_exps : pgm -> exp list -> exp list
=fun pgm exps -> List.map (comparison_chain_exp pgm) exps 

and comparison_chain_fmla : pgm -> fmla -> fmla 
=fun pgm fmla -> 
  match fmla with 
  | F_exp e -> F_exp (comparison_chain_exp pgm e)
  | F_order (es1, es2) -> F_order (comparison_chain_exps pgm es1, comparison_chain_exps pgm es2)
  | F_not f -> F_not (comparison_chain_fmla pgm f)
  | F_and fmlas -> F_and (List.map (comparison_chain_fmla pgm) fmlas)
  | F_or fmlas -> F_or (List.map (comparison_chain_fmla pgm) fmlas)
  | F_imply (f1, f2) -> F_imply (comparison_chain_fmla pgm f1, comparison_chain_fmla pgm f2)
  | F_iff (f1, f2) -> F_iff (comparison_chain_fmla pgm f1, comparison_chain_fmla pgm f2)
  | F_forall (x, tyopt, f) -> F_forall (x, tyopt, comparison_chain_fmla pgm f)
  | F_exists (x, tyopt, f) -> F_exists (x, tyopt, comparison_chain_fmla pgm f)

and comparison_chain_fmlas : pgm -> fmla list -> fmla list 
=fun pgm fmlas -> List.map (comparison_chain_fmla pgm) fmlas
  
and comparison_chain_stmt : pgm -> stmt -> stmt
=fun pgm stmt -> 
  match stmt with 
  | S_skip -> S_skip
  | S_seq stmts -> S_seq (List.map (comparison_chain_stmt pgm) stmts)
  | S_assign (lvs, exps) -> S_assign (lvs, comparison_chain_exps pgm exps)
  | S_if (e, s1, s2) -> S_if (comparison_chain_exp pgm e, comparison_chain_stmt pgm s1, comparison_chain_stmt pgm s2)
  | S_while (invs, Some rank, e, s) -> S_while (comparison_chain_fmlas pgm invs, Some (comparison_chain_exps pgm rank), comparison_chain_exp pgm e, comparison_chain_stmt pgm s)
  | S_while (invs, None, e, s) -> S_while (comparison_chain_fmlas pgm invs, None, comparison_chain_exp pgm e, comparison_chain_stmt pgm s)
  | S_return exps -> S_return (comparison_chain_exps pgm exps)
  | S_break -> S_break 

let comparison_chain_mthd : pgm -> mthd -> mthd
=fun pgm mthd -> 
  { 
    mthd with 
      stmt = comparison_chain_stmt pgm mthd.stmt; 
      pre = comparison_chain_fmlas pgm mthd.pre; 
      post = comparison_chain_fmlas pgm mthd.post
  }  

let comparison_chain_pred : pgm -> pred -> pred
=fun pgm pred -> 
  { 
    pred with 
      fmla = comparison_chain_fmla pgm pred.fmla
  }

let multi_assign : pgm -> pgm 
=fun pgm -> { pgm with mthds = List.map (multi_assign_mthd pgm) pgm.mthds }

let comparison_chain : pgm -> pgm 
=fun pgm -> 
  { pgm with 
    mthds = List.map (comparison_chain_mthd pgm) pgm.mthds;
    preds = List.map (comparison_chain_pred pgm) pgm.preds
  }

let perform : pgm -> pgm 
=fun pgm -> 
  pgm 
  |> multi_assign 
  |> comparison_chain