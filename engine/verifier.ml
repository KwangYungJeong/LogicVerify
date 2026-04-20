open Utils 
open Program
open Smt
open Syntax

(* Global debug toggle *)
let debug_enabled = ref false

let debug_log msg =
  if !debug_enabled then print_endline ("   [DEBUG] " ^ msg)



(* Gradual Step 3: Handle E_call (Predicate Names) in Expressions *)
let rec subst_exp (subst: (id * exp) list) (e: exp) : exp =
  match e with
  | E_int _ | E_bool _ -> e
  | E_lv (V_var id) -> (match List.assoc_opt id subst with Some e' -> e' | None -> e)
  | E_lv (V_arr (id, idx)) -> 
      let idx' = subst_exp subst idx in
      (match List.assoc_opt id subst with 
       | Some (E_lv (V_var id')) -> E_lv (V_arr (id', idx'))
       | _ -> E_lv (V_arr (id, idx')))
  | E_add (e1, e2) -> E_add (subst_exp subst e1, subst_exp subst e2)
  | E_sub (e1, e2) -> E_sub (subst_exp subst e1, subst_exp subst e2)
  | E_mul (e1, e2) -> E_mul (subst_exp subst e1, subst_exp subst e2)
  | E_div (e1, e2) -> E_div (subst_exp subst e1, subst_exp subst e2)
  | E_mod (e1, e2) -> E_mod (subst_exp subst e1, subst_exp subst e2)
  | E_and (e1, e2) -> E_and (subst_exp subst e1, subst_exp subst e2)
  | E_or (e1, e2) -> E_or (subst_exp subst e1, subst_exp subst e2)
  | E_neg e1 -> E_neg (subst_exp subst e1)
  | E_len id -> 
      (match List.assoc_opt id subst with
       | Some (E_lv (V_var id')) -> E_len id'
       | _ -> E_len id)
  | E_not e1 -> E_not (subst_exp subst e1)
  | E_cmp (op, e1, e2) -> E_cmp (op, subst_exp subst e1, subst_exp subst e2)
  | E_call (id, args) -> E_call (id, List.map (subst_exp subst) args)
  | E_if (e1, e2, e3) -> E_if (subst_exp subst e1, subst_exp subst e2, subst_exp subst e3)
  | _ -> e

let bound_var_counter = ref 0

let rec subst_fmla (subst: (id * exp) list) (f: fmla) : fmla =
  match f with
  | F_exp e -> F_exp (subst_exp subst e)
  | F_not f1 -> F_not (subst_fmla subst f1)
  | F_and fs -> F_and (List.map (subst_fmla subst) fs)
  | F_or fs -> F_or (List.map (subst_fmla subst) fs)
  | F_imply (f1, f2) -> F_imply (subst_fmla subst f1, subst_fmla subst f2)
  | F_iff (f1, f2) -> F_iff (subst_fmla subst f1, subst_fmla subst f2)
  | F_forall (id, t, f1) -> 
      if subst = [] then F_forall (id, t, f1)
      else (
        incr bound_var_counter;
        let new_id = id ^ "_b" ^ string_of_int !bound_var_counter in
        let subst' = (id, E_lv (V_var new_id)) :: List.filter (fun (x,_) -> x <> id) subst in
        F_forall (new_id, t, subst_fmla subst' f1)
      )
  | F_exists (id, t, f1) -> 
      if subst = [] then F_exists (id, t, f1)
      else (
        incr bound_var_counter;
        let new_id = id ^ "_b" ^ string_of_int !bound_var_counter in
        let subst' = (id, E_lv (V_var new_id)) :: List.filter (fun (x,_) -> x <> id) subst in
        F_exists (new_id, t, subst_fmla subst' f1)
      )
  | _ -> f

let rec subst_array_id_exp (arr_id: id) (new_id: id) (e: exp) : exp =
  match e with
  | E_int _ | E_bool _ -> e
  | E_lv (V_var id) -> if id = arr_id then E_lv (V_var new_id) else e
  | E_lv (V_arr (id, e_k)) ->
      let e_k' = subst_array_id_exp arr_id new_id e_k in
      if id = arr_id then E_lv (V_arr (new_id, e_k'))
      else E_lv (V_arr (id, e_k'))
  | E_add (e1, e2) -> E_add (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_sub (e1, e2) -> E_sub (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_mul (e1, e2) -> E_mul (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_div (e1, e2) -> E_div (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_mod (e1, e2) -> E_mod (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_and (e1, e2) -> E_and (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_or (e1, e2) -> E_or (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_neg e1 -> E_neg (subst_array_id_exp arr_id new_id e1)
  | E_len id -> if id = arr_id then E_len new_id else E_len id
  | E_not e1 -> E_not (subst_array_id_exp arr_id new_id e1)
  | E_cmp (op, e1, e2) -> E_cmp (op, subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2)
  | E_call (id, args) -> E_call (id, List.map (subst_array_id_exp arr_id new_id) args)
  | E_if (e1, e2, e3) -> E_if (subst_array_id_exp arr_id new_id e1, subst_array_id_exp arr_id new_id e2, subst_array_id_exp arr_id new_id e3)
  | _ -> e

let rec subst_array_id_fmla (arr_id: id) (new_id: id) (f: fmla) : fmla =
  match f with
  | F_exp e -> F_exp (subst_array_id_exp arr_id new_id e)
  | F_not f1 -> F_not (subst_array_id_fmla arr_id new_id f1)
  | F_and fs -> F_and (List.map (subst_array_id_fmla arr_id new_id) fs)
  | F_or fs -> F_or (List.map (subst_array_id_fmla arr_id new_id) fs)
  | F_imply (f1, f2) -> F_imply (subst_array_id_fmla arr_id new_id f1, subst_array_id_fmla arr_id new_id f2)
  | F_iff (f1, f2) -> F_iff (subst_array_id_fmla arr_id new_id f1, subst_array_id_fmla arr_id new_id f2)
  | F_forall (id, t, f1) -> F_forall (id, t, subst_array_id_fmla arr_id new_id f1)
  | F_exists (id, t, f1) -> F_exists (id, t, subst_array_id_fmla arr_id new_id f1)
  | _ -> f


let rec subst_len_exp (arr_id: id) (size_exp: exp) (e: exp) : exp =
  match e with
  | E_int _ | E_bool _ -> e
  | E_lv (V_var _) -> e
  | E_lv (V_arr (id, e_k)) -> E_lv (V_arr (id, subst_len_exp arr_id size_exp e_k))
  | E_add (e1, e2) -> E_add (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_sub (e1, e2) -> E_sub (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_mul (e1, e2) -> E_mul (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_div (e1, e2) -> E_div (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_mod (e1, e2) -> E_mod (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_and (e1, e2) -> E_and (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_or (e1, e2) -> E_or (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_neg e1 -> E_neg (subst_len_exp arr_id size_exp e1)
  | E_len id -> if id = arr_id then size_exp else E_len id
  | E_not e1 -> E_not (subst_len_exp arr_id size_exp e1)
  | E_cmp (op, e1, e2) -> E_cmp (op, subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2)
  | E_call (id, args) -> E_call (id, List.map (subst_len_exp arr_id size_exp) args)
  | E_if (e1, e2, e3) -> E_if (subst_len_exp arr_id size_exp e1, subst_len_exp arr_id size_exp e2, subst_len_exp arr_id size_exp e3)
  | _ -> e

let rec subst_len_fmla (arr_id: id) (size_exp: exp) (f: fmla) : fmla =
  match f with
  | F_exp e -> F_exp (subst_len_exp arr_id size_exp e)
  | F_not f1 -> F_not (subst_len_fmla arr_id size_exp f1)
  | F_and fs -> F_and (List.map (subst_len_fmla arr_id size_exp) fs)
  | F_or fs -> F_or (List.map (subst_len_fmla arr_id size_exp) fs)
  | F_imply (f1, f2) -> F_imply (subst_len_fmla arr_id size_exp f1, subst_len_fmla arr_id size_exp f2)
  | F_iff (f1, f2) -> F_iff (subst_len_fmla arr_id size_exp f1, subst_len_fmla arr_id size_exp f2)
  | F_forall (id, t, f1) -> F_forall (id, t, subst_len_fmla arr_id size_exp f1)
  | F_exists (id, t, f1) -> F_exists (id, t, subst_len_fmla arr_id size_exp f1)
  | _ -> f


let rec translate_exp (pgm : Syntax.pgm) (tyenv : Typechecker.TyEnv.t) (ast_exp : Syntax.exp) : Smt.Expr.t =
  match ast_exp with
  | E_call ("Dist", [x_exp; y_exp]) -> 
      debug_log "Inlining Dist(x, y)";
      let x = translate_exp pgm tyenv x_exp in
      let y = translate_exp pgm tyenv y_exp in
      Smt.Expr.create_ite (Smt.Expr.create_lt x y) ~t:(Smt.Expr.create_sub y x) ~f:(Smt.Expr.create_sub x y)
  | E_call ("random", [l_exp; _u_exp]) -> 
      debug_log "Inlining random(l, u) -> l";
      translate_exp pgm tyenv l_exp
  | E_call ("beq", [a_exp; b_exp; k1_exp; k2_exp]) ->
      debug_log "Inlining beq(a, b, k1, k2)";
      let a = translate_exp pgm tyenv a_exp in
      let b = translate_exp pgm tyenv b_exp in
      let k1 = translate_exp pgm tyenv k1_exp in
      let k2 = translate_exp pgm tyenv k2_exp in
      let i = Smt.Expr.create_var (Smt.Expr.sort_of_int ()) ~name:"bi" in
      let cond = Smt.Fmla.create_and [Smt.Expr.create_le k1 i; Smt.Expr.create_le i k2] in
      let body = Smt.Expr.create_eq (Smt.Expr.read_arr a ~idx:i) (Smt.Expr.read_arr b ~idx:i) in
      Smt.Fmla.create_forall i (Smt.Fmla.create_or [Smt.Fmla.create_not cond; body])
  | E_call (id, args) -> 
      (match List.find_opt (fun (p: Syntax.pred) -> p.name = id) pgm.preds with
      | Some p ->
          debug_log ("Inlining predicate: " ^ id);
          let subst = List.map2 (fun (_, x, _) arg -> (x, arg)) p.args args in
          translate_fmla pgm tyenv (subst_fmla subst p.fmla)
      | None ->
          match List.find_opt (fun (f: Syntax.func) -> f.fid = id) pgm.funcs with
          | Some f ->
              debug_log ("Inlining function: " ^ id);
              let subst = List.map2 (fun (_, x, _) arg -> (x, arg)) f.args args in
              translate_exp pgm tyenv (subst_exp subst f.body)
          | None ->
              debug_log ("Found unknown E_call (returning 0): " ^ id);
              Smt.Expr.of_int 0)
  | E_and (e1, e2) -> 
      debug_log "Found E_and (logic)";
      Fmla.create_and [translate_exp pgm tyenv e1; translate_exp pgm tyenv e2]
  | E_or (e1, e2) -> 
      debug_log "Found E_or (logic)";
      Fmla.create_or [translate_exp pgm tyenv e1; translate_exp pgm tyenv e2]
  | E_not e1 ->
      debug_log "Found E_not (logic)";
      Fmla.create_not (translate_exp pgm tyenv e1)
  | E_neg e -> 
      debug_log "Found E_neg (arith)";
      Smt.Expr.create_neg (translate_exp pgm tyenv e)
  | E_int n -> 
      debug_log ("Found E_int: " ^ string_of_int n);
      Smt.Expr.of_int n
  | E_bool b -> 
      debug_log ("Found E_bool: " ^ string_of_bool b);
      if b then Smt.Expr.true_ () else Smt.Expr.false_ ()
  | E_if (e1, e2, e3) ->
      debug_log "Found E_if";
      Smt.Expr.create_ite (translate_exp pgm tyenv e1) ~t:(translate_exp pgm tyenv e2) ~f:(translate_exp pgm tyenv e3)
  | E_lv (V_var id) -> 
      debug_log ("Found E_lv (var): " ^ id);
      let t = Typechecker.TyEnv.find id tyenv in
      let sort = match t with
        | T_int -> Smt.Expr.sort_of_int ()
        | T_bool -> Smt.Expr.sort_of_bool ()
        | T_arr val_t -> 
            let val_sort = match val_t with
              | T_int -> Smt.Expr.sort_of_int ()
              | T_bool -> Smt.Expr.sort_of_bool ()
              | _ -> Smt.Expr.sort_of_int () (* Default *)
            in Smt.Expr.sort_of_arr val_sort
        | _ -> Smt.Expr.sort_of_int ()
      in
      Smt.Expr.create_var sort ~name:id
  | E_lv (V_arr (id, idx_exp)) -> 
      debug_log ("Found E_lv (arr): " ^ id);
      let t = Typechecker.TyEnv.find id tyenv in
      let sort = match t with
        | T_arr val_t -> 
            let val_sort = match val_t with
              | T_int -> Smt.Expr.sort_of_int ()
              | T_bool -> Smt.Expr.sort_of_bool ()
              | _ -> Smt.Expr.sort_of_int ()
            in Smt.Expr.sort_of_arr val_sort
        | _ -> Smt.Expr.sort_of_int ()
      in
      let arr_expr = Smt.Expr.create_var sort ~name:id in
      let idx_expr = translate_exp pgm tyenv idx_exp in
      Smt.Expr.read_arr arr_expr ~idx:idx_expr
  | E_cmp (op, e1, e2) -> 
      debug_log "Found E_cmp";
      let v1 = translate_exp pgm tyenv e1 in
      let v2 = translate_exp pgm tyenv e2 in
      (match op with
      | Le -> Smt.Expr.create_le v1 v2
      | Lt -> Smt.Expr.create_lt v1 v2
      | Ge -> Smt.Expr.create_ge v1 v2
      | Gt -> Smt.Expr.create_gt v1 v2
      | Eq -> Smt.Expr.create_eq v1 v2
      | Neq -> Smt.Expr.create_neq v1 v2)
  | E_add (e1, e2) -> 
      debug_log "Found E_add";
      Smt.Expr.create_add (translate_exp pgm tyenv e1) (translate_exp pgm tyenv e2)
  | E_sub (e1, e2) -> 
      debug_log "Found E_sub";
      Smt.Expr.create_sub (translate_exp pgm tyenv e1) (translate_exp pgm tyenv e2)
  | E_mul (e1, e2) -> 
      debug_log "Found E_mul";
      Smt.Expr.create_mul (translate_exp pgm tyenv e1) (translate_exp pgm tyenv e2)
  | E_div (e1, e2) -> 
      debug_log "Found E_div";
      Smt.Expr.create_div (translate_exp pgm tyenv e1) (translate_exp pgm tyenv e2)
  | E_mod (e1, e2) -> 
      debug_log "Found E_mod";
      Smt.Expr.create_mod (translate_exp pgm tyenv e1) (translate_exp pgm tyenv e2)
  | E_len id -> 
      debug_log ("Found E_len: " ^ id);
      Smt.Expr.create_var (Smt.Expr.sort_of_int ()) ~name:("|" ^ id ^ "|")
  | _ -> 
      debug_log ("Found other E_xxx (returning 0): " ^ Pp.string_of_exp ast_exp);
      Smt.Expr.of_int 0


(* Gradual Step 2: Handle F_and & F_exp Detection (with Explicit Types) *)
and translate_fmla (pgm : Syntax.pgm) (tyenv : Typechecker.TyEnv.t) (ast_fmla : Syntax.fmla) : Smt.Fmla.t =
  match ast_fmla with
  | F_and fs -> 
      debug_log "Found F_and";
      Fmla.create_and (List.map (translate_fmla pgm tyenv) fs)
  | F_or fs -> 
      debug_log "Found F_or";
      Fmla.create_or (List.map (translate_fmla pgm tyenv) fs)
  | F_not f1 -> 
      debug_log "Found F_not";
      Fmla.create_not (translate_fmla pgm tyenv f1)
  | F_imply (f1, f2) -> 
      debug_log "Found F_imply";
      Fmla.create_imply (translate_fmla pgm tyenv f1) (translate_fmla pgm tyenv f2)
  | F_forall (id, t_opt, f1) -> 
      debug_log ("Found F_forall: " ^ id);
      let t = match t_opt with Some t -> t | None -> T_int in
      let sort = match t with
        | T_int -> Smt.Expr.sort_of_int ()
        | T_bool -> Smt.Expr.sort_of_bool ()
        | _ -> Smt.Expr.sort_of_int ()
      in
      let var = Smt.Expr.create_var sort ~name:id in
      let tyenv' = Typechecker.TyEnv.add id t tyenv in
      Smt.Fmla.create_forall var (translate_fmla pgm tyenv' f1)
  | F_exists (id, t_opt, f1) -> 
      debug_log ("Found F_exists: " ^ id);
      let t = match t_opt with Some t -> t | None -> T_int in
      let sort = match t with
        | T_int -> Smt.Expr.sort_of_int ()
        | T_bool -> Smt.Expr.sort_of_bool ()
        | _ -> Smt.Expr.sort_of_int ()
      in
      let var = Smt.Expr.create_var sort ~name:id in
      let tyenv' = Typechecker.TyEnv.add id t tyenv in
      Smt.Fmla.create_exists var (translate_fmla pgm tyenv' f1)
  | F_iff (f1, f2) -> 
      debug_log "Found F_iff";
      Fmla.create_iff (translate_fmla pgm tyenv f1) (translate_fmla pgm tyenv f2)
  | F_exp e -> 
      debug_log "Found F_exp";
      translate_exp pgm tyenv e
  | _ -> 
      debug_log ("Found other F_xxx: " ^ Pp.string_of_fmla ast_fmla);
      Fmla.false_ ()

let wp_arr_counter = ref 0

let wp_node (mthd: Syntax.mthd) (node: Graph.Node.t) (post: fmla) : fmla =
  match Graph.Node.get_instr node with
  | I_assign (V_var id, e) ->
      debug_log ("WP: I_assign (var) " ^ id);
      subst_fmla [(id, e)] post
  | I_assign (V_arr (arr_id, idx_exp), e) ->
      debug_log ("WP: I_assign (arr) " ^ arr_id);
      incr wp_arr_counter;
      let new_arr_id = arr_id ^ "_wp" ^ string_of_int !wp_arr_counter in
      let post' = subst_array_id_fmla arr_id new_arr_id post in
      let k_id = "k_wp" ^ string_of_int !wp_arr_counter in
      let k_exp = E_lv (V_var k_id) in
      let bounds = E_and (E_cmp (Le, E_int 0, k_exp), E_cmp (Lt, k_exp, E_len arr_id)) in
      let ite_val = E_if (E_cmp (Eq, k_exp, idx_exp), e, E_lv (V_arr (arr_id, k_exp))) in
      let eq_cond = E_cmp (Eq, E_lv (V_arr (new_arr_id, k_exp)), ite_val) in
      let arr_constraint = F_forall (k_id, Some T_int, F_imply (F_exp bounds, F_exp eq_cond)) in
      let len_constraint = F_exp (E_cmp (Eq, E_len new_arr_id, E_len arr_id)) in
      let imply_fmla = F_imply (F_and [arr_constraint; len_constraint], post') in
      F_forall (new_arr_id, Some (T_arr T_int), imply_fmla)
  | I_new (arr_id, size_exp) ->
      debug_log ("WP: I_new " ^ arr_id);
      subst_len_fmla arr_id size_exp post
  | I_assume e ->
      debug_log "WP: I_assume";
      F_imply (F_exp e, post)
  | I_return exps ->
      debug_log "WP: I_return";
      let subst_list = List.map2 (fun (_, r_id, _) exp -> (r_id, exp)) mthd.rvars exps in
      subst_fmla subst_list post
  | I_skip | I_break | I_if_entry | I_if_exit
  | I_loop_entry | I_loop_exit
  | I_function_entry | I_function_exit ->
      post
  | _ ->
      post (* For unhandled instructions, just pass the postcondition up *)

let wp (mthd: Syntax.mthd) (nodes: Graph.Node.t list) (post: fmla) : fmla =
  print_endline "\n  [WP Generation Process]";
  print_endline ("    Init WP (Post): " ^ Pp.string_of_inv post);
  List.fold_right (fun node acc_post -> 
    let new_wp = wp_node mthd node acc_post in
    print_endline ("    <- [Node] " ^ Graph.Node.to_string node);
    print_endline ("       [WP]   " ^ Pp.string_of_inv new_wp);
    new_wp
  ) nodes post


(* Method verify status structure and it's arrayi *)
type method_verify_status = {
  method_id : string;
  mutable checked : bool;
  mutable verified : bool;
}

(* Implement a partial correctness verifier *)
let verify : Args.t -> Syntax.pgm -> bool 
=fun args pgm -> 

  print_endline "\n[Verifier has started]";
  print_endline ("Input File: " ^ args.inputFile);
  print_endline "===============================";
    
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
      verified  = true; (* Start as true, become false if any BP fails *)
    } in
    temp_mv_list := new_mv_item::!temp_mv_list;

    (* Generate CFG *)
    let cfg = Graph.mthd2cfg pgm mthd in
    (* Generate Basic Paths *)
    let bps = Graph.get_basic_paths cfg in

    (* 
      BasicPath.t structure for reference:
      type t = { 
        pre : Syntax.inv;           (* Pre-condition (Condition) *)
        nodes : Node.t list;        (* Statements (Sentence) *)
        post : Syntax.inv;          (* Post-condition (Condition) *)
      }
      note: I removed rank_pre and rank_post elements, which is used for completness check that is out of class scope.
    *)

    (* Create TyEnv for this method *)
    let tyenv = 
      List.fold_left (fun acc (ty, x, _) -> Typechecker.TyEnv.add x ty acc) Typechecker.TyEnv.empty mthd.args in
    let tyenv = 
      List.fold_left (fun acc (ty, x, _) -> Typechecker.TyEnv.add x ty acc) tyenv mthd.locals in
    let tyenv = 
      List.fold_left (fun acc (ty, x, _) -> Typechecker.TyEnv.add x ty acc) tyenv mthd.rvars in

    (* Print Basic Paths *)
    let path_count = ref 0 in
    print_endline ("    * # of basic paths: " ^ string_of_int (BatSet.cardinal bps));
    BatSet.iter (fun (bp: Graph.BasicPath.t) ->
      incr path_count;
      debug_log ("--BP start (Path #" ^ string_of_int !path_count ^ ") ----------------");
      
      print_endline "bp.pre:";
      print_endline ("  " ^ Pp.string_of_inv bp.pre);
      let translated_pre = translate_fmla pgm tyenv bp.pre in
      debug_log ("translated_pre: " ^ Fmla.to_string translated_pre);
      
      debug_log "bp.nodes:";
      List.iter (fun (node: Graph.Node.t) -> 
        print_endline ("  " ^ Graph.Node.to_string node)
      ) bp.nodes;
      
      print_endline "bp.post:";
      print_endline ("  " ^ Pp.string_of_inv bp.post);
      
      (* Step X: Calculate Weakest Precondition *)
      debug_log "Calculating Weakest Precondition (WP)";
      let actual_post = wp mthd bp.nodes bp.post in
      debug_log ("WP: " ^ Pp.string_of_inv actual_post);

      let translated_post = translate_fmla pgm tyenv actual_post in
      debug_log ("translated_post (WP): " ^ Fmla.to_string translated_post);

      (* Step 12-B: Check Validity (pre -> wp) *)
      debug_log "Check Validity";
      let implication = Fmla.create_imply translated_pre translated_post in
      debug_log ("Implication: " ^ Fmla.to_string implication);
      
      let (res, _model_opt) = Smt.Solver.check_validity [implication] in
      debug_log ("Result: " ^ Smt.Solver.string_of_validity res);

      new_mv_item.checked <- true;
      if not (Smt.Solver.is_valid res) then (
        print_endline ("\n      [BP-FAIL] Path #" ^ string_of_int !path_count ^ " failed verification!\n");
        (match _model_opt with
         | Some m -> print_endline ("Model:\n" ^ Z3.Model.to_string m)
         | None -> print_endline "No model available.");
        new_mv_item.verified <- false;
      ) else (
        print_endline ("\n      [BP-SUCC] Path #" ^ string_of_int !path_count ^ " verified.\n");
      );
    ) bps;
    print_endline ("---BP End------------------------------------------------");
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
    let is_correct = String.ends_with ~suffix:"_Correct" mv_status.method_id in
    let is_incorrect = String.ends_with ~suffix:"_Incorrect" mv_status.method_id in
    
    let skull = 
      if mv_status.checked then
        if (is_correct && not mv_status.verified) || (is_incorrect && mv_status.verified) then " ☠️"
        else ""
      else ""
    in

    let status_msg = 
      if mv_status.checked then
        "checked: true, verified: "^ string_of_bool mv_status.verified ^ skull
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
