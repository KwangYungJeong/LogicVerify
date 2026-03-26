open Syntax 
open Utils.Lib
open Pp 

module type Node = sig
  type instr = 
  | I_assign of lv * exp 
  | I_new of id * exp 
  | I_assume of exp 
  | I_skip
  | I_break 
  | I_if_entry 
  | I_if_exit 
  | I_loop_entry 
  | I_loop_exit 
  | I_function_entry 
  | I_function_exit 
  | I_return of exp list
  | I_call of id list * id * exp list 
  type t 
  val dummy : t 
  val create_assign : lv -> exp -> t 
  val create_new : id -> exp -> t 
  val create_assume : exp -> t 
  val create_skip : unit -> t 
  val create_return : exp list -> t
  val create_break : unit -> t 
  val create_if_entry : unit -> t 
  val create_if_exit : unit -> t
  val create_loop_entry : unit -> t 
  val create_loop_exit : unit -> t
  val create_function_entry : unit -> t 
  val create_function_exit : unit -> t
  val create_call : id list -> id -> exp list -> t 
  val is_callnode : t -> bool 
  val get_nodeid : t -> int 
  val get_instr : t -> instr 
  val to_string : t -> string
  val to_string_simple : t -> string
  val compare : t -> t -> int   
end

module Node : Node = struct
  type instr = 
  | I_assign of lv * exp 
  | I_new of id * exp 
  | I_assume of exp 
  | I_skip
  | I_break 
  | I_if_entry 
  | I_if_exit 
  | I_loop_entry 
  | I_loop_exit 
  | I_function_entry 
  | I_function_exit 
  | I_return of exp list
  | I_call of id list * id * exp list 
  type t = int * instr
  let new_id : unit -> int =
    let id =  ref 0 in 
      fun _ -> (id := !id + 1; !id)
  let dummy = (-1, I_skip)
  let create_assign x a = (new_id(), I_assign (x, a))
  let create_new x exp = (new_id(), I_new (x, exp))
  let create_assume b = (new_id(), I_assume b)
  let create_skip () = (new_id(), I_skip)
  let create_break () = (new_id(), I_break)
  let create_if_entry () = (new_id(), I_if_entry) 
  let create_if_exit () = (new_id(), I_if_exit)
  let create_loop_entry () = (new_id(), I_loop_entry)
  let create_loop_exit () = (new_id(), I_loop_exit)
  let create_function_entry () = (new_id(), I_function_entry)
  let create_function_exit () = (new_id(), I_function_exit)
  let create_return exps = (new_id(), I_return exps)
  let create_call xs fid args = (new_id(), I_call(xs, fid, args))
  let get_nodeid (id, _) = id
  let get_instr (_, instr) = instr
  let is_callnode n = 
    match get_instr n with 
    | I_call _ -> true 
    | _ -> false 
  let compare = Stdlib.compare
  let to_string n = 
    match n with
    | (id, I_assign (x, a)) -> string_of_int id ^ ": " ^ " " ^ string_of_lv x ^ " := " ^ string_of_exp a
    | (id, I_new (x, a)) -> string_of_int id ^ ": " ^ " " ^ x ^ " := new " ^ "[" ^ string_of_exp a ^ "]"
    | (id, I_assume b) -> string_of_int id ^ ": " ^ "assume"  ^ " " ^ string_of_exp b
    | (id, I_skip) -> string_of_int id ^ ": " ^ "skip"
    | (id, I_break) -> string_of_int id ^ ": " ^ "break"
    | (id, I_if_entry) -> string_of_int id ^ ": " ^ "if entry"
    | (id, I_if_exit) -> string_of_int id ^ ": " ^ "if exit"
    | (id, I_loop_entry) -> string_of_int id ^ ": " ^ "loop entry"
    | (id, I_loop_exit) -> string_of_int id ^ ": " ^ "loop exit"
    | (id, I_function_entry) -> string_of_int id ^ ": " ^ "function entry"
    | (id, I_function_exit) -> string_of_int id ^ ": " ^ "function exit"
    | (id, I_return exps) -> string_of_int id ^ ": " ^ "return " ^ (string_of_list string_of_exp exps)
    | (id, I_call (xs, fid, args)) -> string_of_int id ^ ": " ^ (xs |> String.concat ", ") ^ " := " ^ 
                                        fid ^ "(" ^ string_of_list string_of_exp args ^ ")"

  let to_string_simple n = 
    match n with
    | (_, I_assign _) -> "assign"
    | (_, I_new _) -> "new"
    | (_, I_assume _) -> "assume"
    | (_, I_skip) -> "skip"
    | (_, I_break) -> "break"
    | (_, I_if_entry) -> "if entry"
    | (_, I_if_exit) -> "if exit"
    | (_, I_loop_entry) -> "loop entry"
    | (_, I_loop_exit) -> "loop exit"
    | (_, I_function_entry) -> "function entry"
    | (_, I_function_exit) -> "function exit"
    | (_, I_return _) -> "return"
    | (_, I_call _) -> "call"
end

module VarMap = Map.Make(String)
module NodeSet = Set.Make(Node)
module NodeMap = Map.Make(Node)

module type Cfg = sig 
  type t 
  val empty : t 
  val nodesof : t -> Node.t list 
  val succs : Node.t -> t -> NodeSet.t
  val preds : Node.t -> t -> NodeSet.t
  val entries : t -> NodeSet.t 
  val set_fid : string -> t -> t 
  val add_entry : Node.t -> t -> t 
  val add_exit : Node.t -> t -> t 
  val add_locals : decl list -> t -> t
  val add_args : decl list -> t -> t
  val add_rvars : decl list -> t -> t 
  val get_fid : t -> string
  val get_entry : t -> Node.t 
  val get_exit : t -> Node.t 
  val get_locals : t -> decl list 
  val get_args : t -> decl list 
  val get_rvars : t -> decl list
  val add_node : Node.t -> t -> t
  val add_nodes : Node.t list -> t -> t
  val remove_succs : Node.t -> t -> t 
  val add_loophead : Node.t -> t -> t 
  val is_loophead : Node.t -> t -> bool 
  val is_entry : Node.t -> t -> bool 
  val is_exit : Node.t -> t -> bool 
  val get_loopheads : t -> Node.t list 
  val add_invariant : Node.t -> inv -> t -> t 
  val add_rank : Node.t -> rank -> t -> t 
  val get_invariant : Node.t -> t -> inv option 
  val get_rank : Node.t -> t -> rank option 
  val get_callnodes : t -> Node.t list 
  val add_edge : Node.t -> Node.t -> t -> t
  val remove_node : Node.t -> t -> t 
  val remove_edge : Node.t -> Node.t -> t -> t 
  val remove_orphans : t -> t
  val remove_skips : t -> t
  val print : t -> unit 
  val dot : t -> unit
end 

module Cfg : Cfg = struct
  type t = { 
    fid : string; 
    entry : Node.t; 
    exit : Node.t;
    locals : decl list;  
    args : decl list; 
    nodes : NodeSet.t; 
    succs : NodeSet.t NodeMap.t; 
    preds : NodeSet.t NodeMap.t; 
    loopheads : NodeSet.t; 
    invariants : inv NodeMap.t; 
    ranks : rank NodeMap.t; 
    ret_vars : decl list; 
  }
  
  let empty = { 
    fid = ""; 
    entry = Node.dummy; 
    exit = Node.dummy; 
    locals = []; 
    args = []; 
    nodes = NodeSet.empty; 
    succs = NodeMap.empty; 
    preds = NodeMap.empty; 
    loopheads = NodeSet.empty; 
    invariants = NodeMap.empty; 
    ranks = NodeMap.empty; 
    ret_vars = [];
  }

  let nodesof : t -> Node.t list 
  =fun t -> NodeSet.elements t.nodes

  let succs : Node.t -> t -> NodeSet.t
  =fun n g -> try NodeMap.find n g.succs with _ -> NodeSet.empty

  let preds : Node.t -> t -> NodeSet.t
  =fun n g -> try NodeMap.find n g.preds with _ -> NodeSet.empty

  let set_fid : string -> t -> t 
  =fun fid g -> { g with fid = fid }

  let add_entry : Node.t -> t -> t 
  =fun n g -> { g with entry = n }

  let add_exit : Node.t -> t -> t
  =fun n g -> { g with exit = n }

  let add_locals : decl list -> t -> t 
  =fun locals g -> { g with locals = locals }

  let add_args : decl list -> t -> t 
  =fun args g -> { g with args = args }

  let add_rvars : decl list -> t -> t 
  =fun rvars g -> { g with ret_vars = rvars }

  let get_fid : t -> string 
  =fun g -> g.fid 

  let get_entry : t -> Node.t 
  =fun g -> g.entry 

  let get_exit : t -> Node.t 
  =fun g -> g.exit 

  let get_locals : t -> decl list 
  =fun g -> g.locals

  let get_args : t -> decl list 
  =fun g -> g.args 

  let get_rvars : t -> decl list 
  =fun g -> g.ret_vars

  let entries : t -> NodeSet.t 
  =fun t -> NodeSet.filter (fun n -> NodeSet.is_empty (preds n t)) t.nodes

  let add_node : Node.t -> t -> t
  =fun n g -> { g with nodes = NodeSet.add n g.nodes }

  let add_nodes : Node.t list -> t -> t
  =fun ns g -> g |> (List.fold_right add_node ns)

  let add_loophead : Node.t -> t -> t 
  =fun n g -> { g with loopheads = NodeSet.add n g.loopheads }

  let is_loophead : Node.t -> t -> bool 
  =fun n g -> NodeSet.mem n g.loopheads 

  let is_entry : Node.t -> t -> bool 
  =fun n g -> n = g.entry 

  let is_exit : Node.t -> t -> bool 
  =fun n g -> n = g.exit 

  let get_loopheads : t -> Node.t list 
  =fun g -> List.filter (fun n -> is_loophead n g) (nodesof g)

  let add_invariant : Node.t -> inv -> t -> t 
  =fun n inv g -> { g with invariants = NodeMap.add n inv g.invariants }

  let get_invariant : Node.t -> t -> inv option 
  =fun n g -> 
    try 
      Some (NodeMap.find n g.invariants)
    with _ -> None

  let add_rank : Node.t -> rank -> t -> t 
  =fun n r g -> { g with ranks = NodeMap.add n r g.ranks }

  let get_callnodes : t -> Node.t list 
  =fun g -> List.filter Node.is_callnode (NodeSet.elements g.nodes)

  let get_rank : Node.t -> t -> rank option 
  =fun n g -> 
    try 
      Some (NodeMap.find n g.ranks)
    with _ -> None

  let add_edge : Node.t -> Node.t -> t -> t
  =fun n1 n2 g -> 
    g 
    |> add_nodes [n1;n2] 
    |> (fun g -> { g with succs = NodeMap.add n1 (NodeSet.add n2 (succs n1 g)) g.succs }) 
    |> (fun g -> { g with preds = NodeMap.add n2 (NodeSet.add n1 (preds n2 g)) g.preds }) 

  let remove_edge : Node.t -> Node.t -> t -> t 
  =fun n1 n2 g -> 
    g 
    |> (fun g -> { g with succs = NodeMap.add n1 (NodeSet.remove n2 (succs n1 g)) g.succs }) 
    |> (fun g -> { g with preds = NodeMap.add n2 (NodeSet.remove n1 (preds n2 g)) g.preds }) 

  let remove_succs : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> NodeSet.fold (remove_edge n) (succs n g)

  let remove_preds : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> NodeSet.fold (fun p -> remove_edge p n) (preds n g)

  let remove_node : Node.t -> t -> t 
  =fun n g -> 
    g 
    |> remove_succs n 
    |> remove_preds n 
    |> (fun g -> { g with nodes = NodeSet.remove n g.nodes })
  
  let rec remove_orphans : t -> t 
  =fun g -> 
    let orphans = NodeSet.filter (fun n -> g.entry <> n) (entries g) in 
      if NodeSet.is_empty orphans then g 
      else remove_orphans (NodeSet.fold remove_node orphans g)
    
  let remove_skips : t -> t 
  =fun g -> 
    let rec iter g = 
      let g' = 
        list_fold (fun n g -> 
          match Node.get_instr n with 
          | I_skip -> 
            if NodeSet.cardinal (preds n g) = 1 && 
                NodeSet.cardinal (succs n g) = 1 then 
              let pred = NodeSet.choose (preds n g) in 
              let succ = NodeSet.choose (succs n g) in 
                remove_node n g 
                |> remove_edge pred n 
                |> remove_edge n succ
                |> add_edge pred succ 
            else g
          | _ -> g) (nodesof g) g in 
        if g = g' then g 
        else iter g' in 
    iter g 
    
  let print g = 
    print_endline "** Nodes **";
    NodeSet.iter (fun n -> 
      print_endline (Node.to_string n)
    ) g.nodes;
    print_endline "";
    print_endline "** Edges **";
    NodeMap.iter (fun n succs -> 
      NodeSet.iter (fun s ->
        print_endline (string_of_int (Node.get_nodeid n) ^ " -> " ^ string_of_int (Node.get_nodeid s))
      ) succs
    ) g.succs

  let string_of_annotation n g = 
    match get_invariant n g, get_rank n g with 
    | Some inv, Some rank -> string_of_inv inv ^ " " ^ string_of_rank rank 
    | Some inv, None -> string_of_inv inv 
    | _, Some rank -> string_of_rank rank 
    | _ -> ""

  let dot g = 
    print_endline "digraph G {";
    NodeSet.iter (fun n -> 
      print_string (string_of_int (Node.get_nodeid n) ^ " ");
      print_string ("[label=\"" ^ string_of_annotation n g ^ "   " ^ Node.to_string n ^ " " ^ "\"]");
      print_endline ""
    ) g.nodes;
    NodeMap.iter (fun n succs -> 
      NodeSet.iter (fun s ->
        print_endline (string_of_int (Node.get_nodeid n) ^ " -> " ^ string_of_int (Node.get_nodeid s))
      ) succs
    ) g.succs;
    print_endline "}"
end

type ctx = {
  loop_entry : Node.t option; 
  loop_exit : Node.t option; 
}

let ctx0 = {
  loop_entry = None; 
  loop_exit = None; 
}

let mthd2cfg : pgm -> mthd -> Cfg.t 
=fun pgm mthd -> 
  let function_entry = Node.create_function_entry() in 
  let function_exit = Node.create_function_exit() in 
  let id = fun x -> x in 
  let rec helper : ctx -> stmt -> Cfg.t -> Node.t * Cfg.t * (Node.t option)
  =fun ctx cmd cfg -> 
    match cmd with
    | S_break -> 
      let n = Node.create_break() in 
      begin 
        match ctx.loop_exit with 
        | Some loop_exit -> (n, Cfg.add_node n cfg |> Cfg.add_edge n loop_exit, None)
        | None -> raise (Failure "Cfg.mthd2cfg: break cannot find loop exit")
      end 
    | S_skip -> 
      let n = Node.create_skip() in
        (n, Cfg.add_node n cfg, Some n)
    | S_assign (lvs, [E_call(fid, args)]) when is_method fid pgm && is_all_vars lvs -> 
      let xs = List.map (fun lv -> match lv with V_var x -> x | _ -> failwith "S_assign: must not occur") lvs in 
      let n = Node.create_call xs fid args in
        (n, Cfg.add_node n cfg, Some n) 
    | S_assign ([V_var x], [E_new size]) -> 
      let n = Node.create_new x size in 
        (n, Cfg.add_node n cfg, Some n)
    | S_assign ([lv], [a]) -> 
      let n = Node.create_assign lv a in
        (n, Cfg.add_node n cfg, Some n)
    | S_assign _ -> 
      (* TODO : 
        1. multiple assignments (e.g., x, y = y, x) 
        2. lv assignment by function call (e.g., a[i] = f(1)) *)
      failwith (Printf.sprintf "%s: not supported assignment form" (string_of_stmt cmd))
    | S_return e -> 
      let n = Node.create_return e in 
      let cfg = 
        cfg 
        |> Cfg.add_edge n function_exit in 
        (n, Cfg.add_node n cfg, None)
    | S_if (b,c1,c2) ->
      let entry = Node.create_if_entry () in
      let exit = Node.create_if_exit () in
      let n_true = Node.create_assume b in
      let n_false = Node.create_assume (E_not b) in
      let (e1, cfg, x1_opt) = helper ctx c1 cfg in
      let (e2, cfg, x2_opt) = helper ctx c2 cfg in
      let cfg = 
        cfg 
        |> Cfg.add_edge entry n_true
        |> Cfg.add_edge entry n_false
        |> Cfg.add_edge n_true e1 
        |> Cfg.add_edge n_false e2 
        |> begin match x1_opt with 
           | Some x1 -> Cfg.add_edge x1 exit 
           | None -> id end
        |> begin match x2_opt with 
           | Some x2 -> Cfg.add_edge x2 exit 
           | None -> id end in
        (entry, cfg, Some exit)
    | S_while (invs, rankopt, b, c) -> 
      let entry = Node.create_loop_entry () in
      let exit = Node.create_loop_exit () in 
      let n_true = Node.create_assume b in 
      let n_false = Node.create_assume (E_not b) in
      let ctx = {loop_entry = Some entry; loop_exit = Some exit} in 
      let (e, cfg, x_opt) = helper ctx c cfg in 
      let cfg = 
        cfg 
        |> Cfg.add_edge entry n_true 
        |> Cfg.add_edge entry n_false 
        |> Cfg.add_edge n_true e 
        |> begin match x_opt with 
           | Some x -> Cfg.add_edge x entry 
           | None -> id end 
        |> Cfg.add_edge n_false exit
        |> Cfg.add_loophead entry 
        |> Cfg.add_invariant entry (F_and invs) 
        |> begin 
              match rankopt with 
              | Some rank -> Cfg.add_rank entry rank 
              | None -> (fun x -> x)
           end in
        (entry, cfg, Some exit)
    | S_seq cmds -> 
      let entry = Node.create_skip () in
      let exit = Node.create_skip () in
      let (cfg, prev_x_opt) = 
        List.fold_left (fun (cfg, prev_x_opt) cmd -> 
          let (e', cfg', x_opt') = helper ctx cmd cfg in
            match prev_x_opt with 
            | Some prev_x -> (Cfg.add_edge prev_x e' cfg', x_opt')
            | None -> (cfg', x_opt')
        ) (cfg, Some entry) cmds in 
        begin 
          match prev_x_opt with 
          | Some prev_x -> (entry, Cfg.add_edge prev_x exit cfg, Some exit)
          | None -> (entry, cfg, Some exit) 
        end in
  let (entry, cfg, exit_opt) = helper ctx0 mthd.stmt Cfg.empty in
    cfg
    |> Cfg.set_fid mthd.id 
    |> Cfg.add_locals mthd.locals 
    |> Cfg.add_args mthd.args 
    |> Cfg.add_rvars mthd.rvars 
    |> Cfg.add_edge function_entry entry 
    |> begin match exit_opt with 
       | Some exit -> Cfg.add_edge exit function_exit 
       | None -> id end 
    |> Cfg.add_invariant function_entry (F_and mthd.pre)
    |> Cfg.add_invariant function_exit (F_and mthd.post)
    |> begin 
          match mthd.rank with 
          | Some rank -> Cfg.add_rank function_entry rank 
          | None -> id 
       end
    |> Cfg.add_entry function_entry 
    |> Cfg.add_exit function_exit 
    (* |> Cfg.add_call_precondition  *)
    |> Cfg.remove_orphans 
    |> Cfg.remove_skips

module CfgMap = struct 
  type t = (id, Cfg.t) BatMap.t
  let empty = BatMap.empty 
  let find = BatMap.find 
  let add = BatMap.add 
  let fold = BatMap.foldi 
  let map = BatMap.map 
end 

let replace_inv : decl -> exp -> inv -> inv 
=fun (_, x, _) e fmla -> Syntax.replace_fmla x e fmla

let funpre2callpre : inv -> decl list -> exp list -> inv 
=fun inv formals actuals -> 
  list_fold (fun (formal, actual) inv ->
    replace_inv formal actual inv  
  ) (zip formals actuals) inv 

let funrank2callrank : rank -> decl list -> exp list -> rank 
=fun rank formals actuals -> 
  List.map (fun e -> 
    list_fold (fun ((_, formal, _), actual) ->
      Syntax.replace_exp formal actual
    ) (zip formals actuals) e
  ) rank 
  
let add_call_precondition : CfgMap.t -> Cfg.t -> Cfg.t
=fun cfgmap g -> 
  list_fold (fun n g -> 
    match Node.get_instr n with 
    | Node.I_call (_, fid, args) -> 
      let callee_cfg = CfgMap.find fid cfgmap in 
      let pre_opt = Cfg.get_invariant (Cfg.get_entry callee_cfg) callee_cfg in 
      let rank_opt = Cfg.get_rank (Cfg.get_entry callee_cfg) callee_cfg in 
        begin 
          match pre_opt, rank_opt with 
          | Some pre, Some funrank -> 
            let inv = funpre2callpre pre (Cfg.get_args callee_cfg) args in 
            let rank = funrank2callrank funrank (Cfg.get_args callee_cfg) args in 
              g |> Cfg.add_invariant n inv |> Cfg.add_rank n rank 
          | Some pre, None -> 
            let inv = funpre2callpre pre (Cfg.get_args callee_cfg) args in 
              g |> Cfg.add_invariant n inv 
          | _ -> raise (Failure "Cfg.add_call_precondition: should never occur")
        end
    | _ -> g
  ) (Cfg.nodesof g) g

let pgm2cfgmap : pgm -> CfgMap.t 
=fun pgm -> 
  let cfgmap = list_fold (fun m -> CfgMap.add m.id (mthd2cfg pgm m)) pgm.mthds CfgMap.empty in 
    CfgMap.fold (fun mid cfg -> 
        CfgMap.add mid (add_call_precondition cfgmap cfg)
    ) cfgmap CfgMap.empty  

module BasicPath = struct
  type t = { 
    pre : Syntax.inv; 
    rank_pre : Syntax.rank option; 
    nodes : Node.t list; 
    post : Syntax.inv; 
    rank_post : Syntax.rank option; 
  }
  let create pre rank_pre nodes post rank_post = { 
    pre = pre; 
    rank_pre = rank_pre; 
    nodes = nodes; 
    post = post; 
    rank_post = rank_post; 
  }

  let first bp = List.hd bp.nodes
  let last bp = last_of_list bp.nodes 

  let nodes_of bp = bp.nodes 
  let pre_of bp = bp.pre 
  let post_of bp = bp.post 
  
  let post2list bp = 
    match post_of bp with 
    | F_and posts -> posts 
    | _ -> failwith "BasicPath.post2list"

  let to_string bp = 
    string_of_inv bp.pre ^ "\n" ^ 
    (match bp.rank_pre with Some rank -> string_of_rank rank ^ "\n " | None -> "") ^
    string_of_list Node.to_string bp.nodes ~sep:"\n" ~first:"" ~last:"" ^ "\n" ^
    string_of_inv bp.post ^
    (match bp.rank_post with Some rank -> "\n" ^ string_of_rank rank ^ "\n " | None -> "")

  let to_string_simple bp = 
    let nodes = List.filter (fun node -> 
      match Node.get_instr node with 
      | I_if_entry 
      | I_if_exit
      | I_loop_entry 
      | I_loop_exit 
      | I_function_entry 
      | I_function_exit 
      | I_call _ -> true 
      | _ -> false    
    ) bp.nodes in 
    string_of_list Node.to_string_simple nodes ~sep:" -> " ~first:"" ~last:"" 
end

let rec fix f s = 
  let s' = f s in 
    if BatSet.subset s' s then s' 
    else fix f s' 

let search : Node.t -> Cfg.t -> BasicPath.t BatSet.t
=fun n cfg -> 
  let init = BatSet.singleton [n] in 
  let update : (Node.t list) BatSet.t -> (Node.t list) BatSet.t
  =fun paths -> 
    BatSet.fold (fun path paths -> 
      match path with 
      | hd::tl -> 
        if tl <> [] && (Cfg.is_loophead hd cfg || Cfg.is_exit hd cfg) then paths 
        else
          let succs = Cfg.succs hd cfg in 
            NodeSet.fold (fun succ paths -> 
              BatSet.add (succ::hd::tl) paths
            ) succs paths 
      | [] -> raise (Failure "search.update")
    ) paths paths in 
  let paths = BatSet.map (fun path -> List.rev path) (fix update init) in 
  let first path = List.nth path 0 in 
  let last path = List.nth path (List.length path - 1) in 
  let is_basic_path path = 
      (Cfg.is_entry (first path) cfg || Cfg.is_loophead (first path) cfg) && 
      (Cfg.is_loophead (last path) cfg || Cfg.is_exit (last path) cfg) in 
  let basic_paths = 
    BatSet.map (fun path -> 
      let pre = 
        match Cfg.get_invariant (first path) cfg with 
        | Some pre -> pre 
        | None -> raise (Failure "Should not occur") in 
      let post = 
        match Cfg.get_invariant (last path) cfg with 
        | Some post -> post 
        | None -> raise (Failure "Should not occur") in 
      let rank_pre = Cfg.get_rank (first path) cfg in 
      let rank_post = Cfg.get_rank (last path) cfg in  
      BasicPath.create pre rank_pre path post rank_post 
    ) (BatSet.filter (fun p -> List.length p > 1 && is_basic_path p) paths) in 
    basic_paths

let gen_bps_call_precondition : Cfg.t -> BasicPath.t BatSet.t -> BasicPath.t BatSet.t
=fun cfg bps -> 
  BatSet.fold (fun (bp: BasicPath.t) -> 
    list_fold (fun (idx, n) -> 
      if Node.is_callnode n then 
        let nodes' = list_prefix bp.nodes (idx - 1) in 
        let bp' = { bp with 
            nodes = nodes'; 
            post = 
              (match Cfg.get_invariant n cfg with 
              | Some inv -> inv 
              | None -> raise (Failure "gen_bps_call_precondition: should never occur")); 
            rank_post = Cfg.get_rank n cfg 
          } in 
        BatSet.add bp' 
      else id 
    ) (enumerate bp.nodes)
  ) bps bps
    
let get_basic_paths : Cfg.t -> BasicPath.t BatSet.t
=fun cfg -> 
  let entry = Cfg.get_entry cfg in 
  let exit = Cfg.get_exit cfg in 
  let loopheads = Cfg.get_loopheads cfg in 
  (* let _ = assert (List.for_all (fun lh -> Cfg.get_invariant lh cfg <> None) loopheads) in  *)
  let to_search = [entry; exit] @ loopheads in 
    list_fold (fun n -> BatSet.union (search n cfg)) to_search BatSet.empty
    |> gen_bps_call_precondition cfg 