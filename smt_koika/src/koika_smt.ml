open Eff_monad
(* open Sexplib *)
open Syntax
open Z3
open Query

open Core
let sprintf = Printf.sprintf

(* ========== GLOBALS ============== *)
let g_z3_ctx_cfg =
  let base_cfg = [ ("model", "true") (* Generate model *)
                 ; ("proof", "false") (* Disable proof generation *)
                 ; ("auto_config", "false")
                 ] in
  base_cfg

let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver              = Solver.mk_solver g_ctx g_z3_solver_logic_opt

let assert_with assertion error_msg =
  if assertion then ()
  else failwith error_msg

let option_get_or_fail vopt error_msg =
  match vopt with
  | Some v -> v
  | None -> failwith error_msg
(* =========== Types ================ *)
type option_field =
  | Option_IsSome
  | Option_Value
[@@deriving show,sexp]

let boolean_sort = Boolean.mk_sort g_ctx
let mk_bv_s = BitVector.mk_const_s g_ctx

let mk_ite = Boolean.mk_ite g_ctx
let mk_true = Boolean.mk_true g_ctx
let mk_false = Boolean.mk_false g_ctx
let mk_or = Boolean.mk_or g_ctx
let mk_and = Boolean.mk_and g_ctx
let mk_not = Boolean.mk_not g_ctx
let mk_eq = Boolean.mk_eq g_ctx
let mk_implies = Boolean.mk_implies g_ctx

let get_bv_size (expr: Expr.expr) =
  BitVector.get_size (Expr.get_sort expr)

let bexpr_to_bv_expr (expr: Expr.expr) : Expr.expr =
  mk_ite expr (BitVector.mk_numeral g_ctx "1" 1)
              (BitVector.mk_numeral g_ctx "0" 1)


module UnitSort = struct
  open Z3.Datatype

  let mk_sort =
    mk_sort_s g_ctx "Unit"
      [ mk_constructor_s g_ctx "unit"
                         (Symbol.mk_string g_ctx "isUnit")
                         [] [] []
      ]

  let mk_unit =
    let constructors = get_constructors mk_sort in
    Expr.mk_app g_ctx (option_get_or_fail (List.hd constructors) "UnitSort: constructor not found") []
end

let mk_bv_or_unit str sz =
  if sz = 0 then UnitSort.mk_unit
  else mk_bv_s str sz

let mk_bv_or_unit_sort sz =
  if sz = 0 then UnitSort.mk_sort
  else BitVector.mk_sort g_ctx sz

let mk_bv1_to_bool expr =
  mk_eq expr (BitVector.mk_numeral g_ctx "1" 1)

let get_annot_ty (annots: annot_t list): int =
  let annot = List.find_exn annots ~f:(
                fun annot -> match annot with
                             | Annot_ty _ -> true
                             | _ -> false) in
  match annot with
  | Annot_ty sz -> sz
  | _ -> failwith "No annot_ty"

let get_annot_id (annots: annot_t list): int =
  let annot = List.find_exn annots ~f:(
                fun annot -> match annot with
                             | Annot_id _ -> true
                             | _ -> false) in
  match annot with
  | Annot_id id -> id
  | _ -> failwith "No annot_id"

let z_of_blist (blist: bool list) =
  Z.of_string ("0b" ^ (String.concat ~sep:"" (List.map ~f:(fun b -> if b then "1" else "0") (List.rev blist))))

let rec replace_first ~equal:(equal: 'a -> 'a -> bool)
                      ~key:(key: 'a) ~new_value:(new_value:'b)
                      (xs: ('a * 'b) list) : ('a * 'b) list =
  match xs with
  | [] -> failwith ("Key not found")
  | (a,b)::xs ->
      if equal key a then
        (key,new_value)::xs
      else (a,b) :: (replace_first ~equal:equal ~key:key ~new_value:new_value xs)

module Z3Option = struct

  type t =
    { is_some: Expr.expr;
      value : Expr.expr
    }

  let mk_initial str (value_fn: string -> Expr.expr) =
    { is_some = Boolean.mk_const_s g_ctx (str ^ "#option.is_some");
      value = value_fn (str ^ "#option.value")
    }

  let mk_empty str (value_fn: string -> Expr.expr) =
    { is_some = Boolean.mk_false g_ctx;
      value = value_fn (str ^ "#option.dummy_value")
    }

  let get (v: t) (ty: option_field) =
    match ty with
    | Option_IsSome -> v.is_some
    | Option_Value -> v.value

  let update (v: t) (ty: option_field) (expr: Expr.expr) =
    match ty with
    | Option_IsSome -> {v with is_some = expr}
    | Option_Value -> {v with value = expr}
end

  (* ========== Debug ========== *)

let dprintf = Printf.printf

let g_debug_level = 4
let smt_debug_print level str =
  if g_debug_level >= level then
    print_endline str


(* === pretty printing === *)

let string_of_dbg_id dbg_id  = show_debug_id_ty dbg_id
let string_of_machine_id machine_id =
  show_machine_id_t machine_id

let string_of_reg_list (regs: (debug_id_ty reg_t * int) list) =
  (String.concat ~sep:"; "
    (List.map ~f:(fun (id, ty) ->  sprintf "(%s: %n)" (string_of_dbg_id id) ty)  regs))

let string_of_scheduler schedule =
    (String.concat ~sep:";"
             (List.map ~f:(fun (name, a) ->
               sprintf "%s: %s" name (show_aaction pp_debug_id_ty a)) schedule))

let string_of_file (file: file_t) : string = show_file_t file

let debug_id_ty_compare ((_,n1): debug_id_ty) ((_,n2): debug_id_ty) : int =
  compare n1 n2

let debug_id_ty_equal ((_,n1): debug_id_ty) ((_,n2): debug_id_ty) : bool =
  Int.equal n1 n2

type schedule_t = (string * debug_id_ty aaction) list
type symb_schedule_t =
  | ConcreteSchedule of schedule_t
  | AbstractSchedule

module IdMap = Core.Map.Make (struct
  type t = debug_id_ty
  let compare : t -> t -> int = debug_id_ty_compare

  let sexp_of_t t : Sexp.t = sexp_of_debug_id_ty t

  let t_of_sexp t = debug_id_ty_of_sexp t
end)

module IntMap = Map.Make (Int)
module MachineIdMap = Map.Make (struct
  type t = machine_id_t
  let compare : t -> t -> int = Stdlib.compare

  let sexp_of_t t : Sexp.t = sexp_of_machine_id_t t

  let t_of_sexp t = machine_id_t_of_sexp t

end)

type log_taint =
  { lread0 : Expr.expr;
    lread1 : Expr.expr;
    lwrite0 : Expr.expr;
    lwrite1 : Expr.expr;
  }

let conflicts_with_read0 (t: log_taint) : Expr.expr =
  mk_or [t.lwrite0; t.lwrite1]
let conflicts_with_read1 (t: log_taint) : Expr.expr =
  t.lwrite1
let conflicts_with_write0 (t: log_taint) : Expr.expr =
  mk_or [t.lwrite0; t.lread1; t.lwrite1]
let conflicts_with_write1 (t: log_taint) : Expr.expr =
  t.lwrite1

let empty_log_taint  =
  { lread0 = mk_false;
    lread1 = mk_false;
    lwrite0 = mk_false;
    lwrite1 = mk_false;
  }

let init_symbolic_log_taint (s: string -> string) =
  { lread0 = Boolean.mk_const_s g_ctx (s "read0");
    lread1 = Boolean.mk_const_s g_ctx (s "read1");
    lwrite0 = Boolean.mk_const_s g_ctx (s "write0");
    lwrite1 = Boolean.mk_const_s g_ctx (s "write1");
  }

type log_entry_field =
  | LE_Read0
  | LE_Read1
  | LE_Write0
  | LE_Write1
type z3_expr = Expr.expr
type reg_map_t = z3_expr IdMap.t
type taint_log_t = log_taint IdMap.t
type ext_log_t = Z3Option.t IdMap.t
type ext_func_decl_map_t = FuncDecl.func_decl IdMap.t
type machine_reg_map_t = reg_map_t MachineIdMap.t
type ext_log_map_t = ext_log_t MachineIdMap.t
type ext_fun_map_t = ext_func_decl_map_t MachineIdMap.t


let get_reg_map (map: machine_reg_map_t)
                (machine_id: machine_id_t)
                (reg: debug_id_ty)
                : Expr.expr =
  Map.find_exn (Map.find_exn map machine_id) reg

let get_ext_log_map (map: ext_log_map_t)
                    (machine_id: machine_id_t)
                    (ext_fn: debug_id_ty)
                    : Z3Option.t =
  Map.find_exn (Map.find_exn map machine_id) ext_fn

let string_of_expr_id_map (map: z3_expr IdMap.t) : string =
  String.concat ~sep:"; " (List.map ~f:(fun (id, expr) ->
      sprintf "(%s, %s)" (string_of_dbg_id id) (Expr.to_string expr))
    (Map.to_alist ~key_order:`Increasing map))

(* Id and typing *)
module AnnotateAction = struct
  type state_ty = {
    id_gen: int;
  }

  include EffMonad (struct type state = state_ty end)

  let mk_initial
      : state =
    { id_gen = 0;
    }

  let get_fresh_id : int eff =
    get >>= fun st ->
    put { id_gen = st.id_gen + 1 } >>
    return st.id_gen

  let rec do_action (rl_name: string)
                    ((AnnotAction(action, annots)) : debug_id_ty aaction)
                    : (debug_id_ty aaction) eff =
    let do_action = do_action rl_name in
    get_fresh_id >>= fun id ->
    (match action with
     | Fail sz -> return (Fail sz)
     | Var var ->
         return (Var var)
     | Const cst ->
         return (Const cst)
     | Assign (var,action) ->
         do_action action >>= fun (action) ->
         return (Assign(var,action))
     | Seq (a1,a2) ->
         do_action a1 >>= fun (a1) ->
         do_action a2 >>= fun (a2) ->
         return (Seq(a1,a2))
     | If (a1,a2,a3) ->
         do_action a1 >>= fun (a1) ->
         do_action a2 >>= fun (a2) ->
         do_action a3 >>= fun (a3) ->
         return (If(a1,a2,a3))
     | Bind (var, a1, a2) ->
         do_action a1 >>= fun (a1) ->
         do_action a2 >>= fun (a2) ->
         return (Bind (var, a1, a2))
     | Read (port,reg) ->
         return (Read(port, reg))
     | Write(port, reg, action) ->
         do_action action >>= fun action ->
         return (Write(port,reg,action))
     | Zop fn -> return (Zop fn)
     | Unop (fn,action) ->
         do_action action >>= fun action ->
         return (Unop (fn,action))
     | Binop (fn2,a1,a2) ->
         do_action a1 >>= fun a1 ->
         do_action a2 >>= fun a2 ->
         return (Binop (fn2, a1, a2))
     | InternalCall _ ->
          failwith "Assume all InternalCalls are inlined"
     | ExternalCall (fn,a) ->
         do_action a >>= fun a ->
         return (ExternalCall (fn,a))
    ) >>= fun (action) ->
    return (AnnotAction (action, (Annot_id id::annots)))

  let do_schedule (schedule: (string * debug_id_ty aaction) list)
                  : (string * debug_id_ty aaction) list eff =
    mapM (fun (name, action) ->
        do_action name action >>= fun (action) ->
        return (name,action)) schedule

end

let bits1_expr (bitsfn: bits1) (a1: Expr.expr) : Expr.expr =
  match bitsfn with
  | Not ->
      BitVector.mk_not g_ctx a1
  | Slice (offset, width) ->
      assert_with (width > 0) ("bits1_expr: width of length 0");
      BitVector.mk_extract g_ctx (offset + width - 1) (offset) a1
  | SExt width ->
      let arg_width = get_bv_size a1 in
      assert_with (width >= arg_width) "SExt: width >= arg_width";
      BitVector.mk_sign_ext g_ctx (width - arg_width) a1
  | ZExtL width ->
      let arg_width = get_bv_size a1 in
      assert_with (width >= arg_width) "SExt: width >= arg_width";
      BitVector.mk_zero_ext g_ctx (width - arg_width) a1

let bits2_expr (bitsfn: bits2) (a1: Expr.expr) (a2: Expr.expr) : Expr.expr =
  match bitsfn with
  | And -> BitVector.mk_and g_ctx a1 a2
  | Or -> BitVector.mk_or g_ctx a1 a2
  | Xor -> BitVector.mk_xor g_ctx a1 a2
  | Lsl ->
      assert (get_bv_size a1 >= get_bv_size a2);
      let aligned_shift = BitVector.mk_zero_ext g_ctx (get_bv_size a1 - get_bv_size a2) a2 in
      BitVector.mk_shl g_ctx a1 aligned_shift
  | Lsr ->
      assert (get_bv_size a1 >= get_bv_size a2);
      let aligned_shift = BitVector.mk_zero_ext g_ctx (get_bv_size a1 - get_bv_size a2) a2 in
      BitVector.mk_lshr g_ctx a1 aligned_shift
  | Asr ->
      assert (get_bv_size a1 >= get_bv_size a2);
      let aligned_shift = BitVector.mk_zero_ext g_ctx (get_bv_size a1 - get_bv_size a2) a2 in
      BitVector.mk_ashr g_ctx a1 aligned_shift
  | Concat -> BitVector.mk_concat g_ctx a1 a2
  | Sel ->
      assert (get_bv_size a1 >= get_bv_size a2);
      let aligned_shift = BitVector.mk_zero_ext g_ctx (get_bv_size a1 - get_bv_size a2) a2 in
      BitVector.mk_extract g_ctx 0 0 (BitVector.mk_lshr g_ctx a1 aligned_shift)
  | Plus ->  BitVector.mk_add g_ctx a1 a2
  | Minus -> BitVector.mk_sub g_ctx a1 a2
  | EqBits b -> bexpr_to_bv_expr
                  (if b
                   then mk_not (mk_eq a1 a2)
                   else mk_eq a1 a2)
  | Compare (signed, cmp) ->
      bexpr_to_bv_expr (
      begin match (signed, cmp) with
      | (true, CLt) -> BitVector.mk_slt g_ctx a1 a2
      | (true, CGt) -> BitVector.mk_sgt g_ctx a1 a2
      | (true, CLe) -> BitVector.mk_sle g_ctx a1 a2
      | (true, CGe) -> BitVector.mk_sge g_ctx a1 a2
      | (false, CLt) -> BitVector.mk_ult g_ctx a1 a2
      | (false, CGt) -> BitVector.mk_ugt g_ctx a1 a2
      | (false, CLe) -> BitVector.mk_ule g_ctx a1 a2
      | (false, CGe) ->  BitVector.mk_uge g_ctx a1 a2
      end)
  | IndexedSlice width ->
      assert_with (width > 0) "Indexed slice: width must be > zero";
      assert (get_bv_size a1 >= get_bv_size a2);
      let aligned_offset = BitVector.mk_zero_ext g_ctx (get_bv_size a1 - get_bv_size a2 ) a2 in
      BitVector.mk_extract g_ctx (width-1) 0 (BitVector.mk_lshr g_ctx a1 aligned_offset)

type 'id_ty struct_env_t = 'id_ty struct_t list

let rec get_dstruct_field' (acc: int) (flds: (debug_id_ty dstruct_field_t * int) list)
                          (fname: debug_id_ty)
                         : int * int =
  match flds with
  | [] -> failwith "get_dstruct_field: field not found"
  | (field,sz)::flds ->
      if debug_id_ty_equal field fname then
        (acc, sz)
      else get_dstruct_field' (acc + sz) flds fname

let get_dstruct_field_range (def: debug_id_ty struct_t) (fname: debug_id_ty) : int * int =
  let (index, sz) = get_dstruct_field' 0 def.dstruct_fields (* TODO *)  fname in
  (index, index+sz)

let mk_reg_expr (machine_id: machine_id_t)
                (rule_id: int)
                (reg: debug_id_ty)
                (sz: int)
                : Expr.expr =
  mk_bv_s (sprintf "__init{%s}[%s]@R%d" (string_of_machine_id machine_id) (string_of_dbg_id reg) rule_id) sz

module SmtAction = struct
  type state_ty = {
    machine_id: machine_id_t;
    rule_name: string;
    rule_idx: int;
    rule_body: debug_id_ty aaction;
    init_reg_map: reg_map_t;
    cur_reg_map: reg_map_t;
    sched_taint: taint_log_t;
    action_taint: taint_log_t;
    ext_log : ext_log_t;
    ext_func_decls: FuncDecl.func_decl IdMap.t;
    struct_defs: debug_id_ty struct_env_t;

    gamma : (string * Expr.expr) list;
    guards : Expr.expr list;
    (* assertions : Expr.expr list; *)
    fail_conds: Expr.expr list;
  }

  include EffMonad (struct type state = state_ty end)

  let mk_empty_action_log (registers: (debug_id_ty reg_t) list)
    : taint_log_t =
    List.fold_left ~f:(fun acc reg ->
        Map.add_exn
          ~key:reg
          ~data:(empty_log_taint) acc)
          ~init:IdMap.empty registers

  let mk_initial_state (machine_id: machine_id_t)
                       (registers: (debug_id_ty reg_t * int) list)
                       (rule_name: string)
                       (rule_idx: int)
                       (rule_body: debug_id_ty aaction)
                       (init_reg_map: reg_map_t)
                       (sched_taint: taint_log_t)
                       (ext_log: ext_log_t)
                       (* (ext_calls: (Expr.expr list) IdMap.t) *)
                       (ext_func_decls: FuncDecl.func_decl IdMap.t)
                       (struct_defs: debug_id_ty struct_env_t)
                       : state_ty =
    { machine_id = machine_id;
      rule_name = rule_name;
      rule_idx = rule_idx;
      rule_body = rule_body;
      init_reg_map = init_reg_map;
      cur_reg_map = init_reg_map;
      sched_taint = sched_taint;
      action_taint = mk_empty_action_log (List.map ~f:fst registers);
      ext_log = ext_log;
      (* ext_calls = ext_calls; *)
      ext_func_decls = ext_func_decls;
      struct_defs = struct_defs;

      gamma = [];
      guards = [];
      (* assertions = []; *)
      fail_conds = [];
    }

  let apply_ext_func_decl (fn: debug_id_ty) (expr: Expr.expr)
                       : Expr.expr eff =
    get >>= fun st ->
    let decl = Map.find_exn st.ext_func_decls fn in
    return (FuncDecl.apply decl [expr])

  let get_id_string (id: int) : string eff =
    get >>= fun st ->
    return (sprintf "[%s]__Action__%s:%d:%d__"
              (string_of_machine_id st.machine_id) st.rule_name st.rule_idx id)

  let lookup_reg (reg: debug_id_ty) : z3_expr eff =
    get >>= fun st ->
    return (Map.find_exn st.init_reg_map reg)

  let lookup_cur_reg (reg: debug_id_ty) : z3_expr eff =
    get >>= fun st ->
    return (Map.find_exn st.cur_reg_map reg)


  let get_fail_conds : Expr.expr list eff =
    get >>= fun st ->
    return st.fail_conds

  let get_cur_reg_map : reg_map_t eff =
    get >>= fun st ->
    return st.cur_reg_map

  let get_sched_taint : taint_log_t eff =
    get >>= fun st ->
    return st.sched_taint

  let lookup_sched_taint (idx: debug_id_ty) : log_taint eff =
    get >>= fun st ->
    return (Map.find_exn st.sched_taint idx)

  let lookup_action_taint (idx: debug_id_ty) : log_taint eff =
    get >>= fun st ->
    return (Map.find_exn st.action_taint idx)

  let get_action_taint : taint_log_t eff =
    get >>= fun st ->
    return st.action_taint

  let set_action_taint (idx: debug_id_ty) (fld: log_entry_field) (expr: Expr.expr): unit eff =
    get >>= fun st ->
    put {st with action_taint =
      Map.update st.action_taint idx
            ~f:(fun opt_taint ->
              match opt_taint with
              | Some taint ->
                  begin match fld with
                  | LE_Read0 -> {taint with lread0 = expr}
                  | LE_Read1 -> {taint with lread1 = expr}
                  | LE_Write0 -> {taint with lwrite0 = expr}
                  | LE_Write1 -> {taint with lwrite1 = expr}
                  end
              | None -> failwith "taint not found"
            )}

  let get_ext_log : ext_log_t eff =
    get >>= fun st ->
    return st.ext_log

  (*
  let get_ext_calls : ((Expr.expr list) IdMap.t )eff =
    get >>= fun st ->
    return st.ext_calls
  *)

  let put_fail_conds (conds: Expr.expr list) : unit eff =
    get >>= fun st ->
    put {st with fail_conds = conds}

  let add_fail_cond (cond: Expr.expr) : unit eff =
    get_fail_conds >>= fun conds ->
    put_fail_conds (cond::conds)
(*
  let get_assertions : Expr.expr list eff =
    get >>= fun st ->
    return st.assertions
*)
  let get_guards: Expr.expr list eff =
    get >>= fun st ->
    return st.guards

  let add_guard (guard: Expr.expr ): unit eff =
    get >>= fun st ->
    put { st with guards = guard::st.guards}

  let remove_guard : unit eff =
    get >>= fun st ->
    match st.guards with
    | [] -> failwith "No guards to remove"
    | _::guards ->
        put { st with guards = guards }

  let get_guard_expr: Expr.expr eff =
    get_guards >>= fun guards ->
    return (mk_and guards)

  let get_gamma: (string * Expr.expr) list eff =
    get >>= fun st -> return st.gamma

  let lookup_var (var: string): Expr.expr eff =
    get_gamma >>= fun gamma ->
    return (List.Assoc.find_exn ~equal:String.equal gamma var)

  let assign_var (var: string) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with gamma =
        replace_first ~equal:String.equal ~key:var ~new_value:expr
                      st.gamma}
  let bind_var (var: string) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put { st with gamma = (var,expr)::st.gamma }

  let unbind_var (var:string): unit eff =
    get >>= fun st ->
    match st.gamma with
    | [] -> failwith "Empty gamma"
    | (hd,_)::gamma ->
        if String.equal hd var then
          put { st with gamma = gamma }
        else failwith "Unexpected gamma head"

  let do_guarded_write ~guard:(guard: Expr.expr)
                      (reg: debug_id_ty) (new_v: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with cur_reg_map =
            Map.update st.cur_reg_map reg
                        ~f:(fun opt_v -> match opt_v with
                                         | Some v -> mk_ite guard new_v v
                                         | None -> failwith "reg not found"
                        )}

  let conflicts_with_ext_call (ext_fn: debug_id_ty) : Expr.expr eff =
    get_ext_log >>= fun ext_log ->
    let opt = Map.find_exn ext_log ext_fn in
    return opt.is_some

  let do_guarded_ext_call
    ~guard:(guard: Expr.expr)
    (ext_fn: debug_id_ty) (new_v: Expr.expr) : Expr.expr eff =
    get >>= fun st ->
    put {st with ext_log =
            Map.update st.ext_log ext_fn
                        ~f:(fun opt_v ->
                          match opt_v with
                          | Some v ->
                              { is_some = mk_or [guard; v.is_some];
                                value = mk_ite guard new_v v.value
                              }
                          | None -> failwith "ext fn not found"
                         )
        } >>
    apply_ext_func_decl ext_fn new_v

  let get_struct (sname: debug_id_ty): (debug_id_ty struct_t) eff  =
    get >>= fun st ->
    return (List.find_exn st.struct_defs ~f:(
      fun def -> debug_id_ty_equal sname def.dstruct_name))

  let smt_zop (fn: debug_id_ty fn0) : Expr.expr eff =
    match fn with
    | StructInit sname ->
        get_struct sname >>= fun def ->
        return (BitVector.mk_numeral g_ctx "0" (struct_sz def))

  let get_dstruct_field_range (sname: debug_id_ty) (fname: debug_id_ty)
                             : (int * int) eff =
    get_struct sname >>= fun def ->
    return (get_dstruct_field_range def fname)

  let smt_unop (fn: debug_id_ty fn1) (a1: Expr.expr): Expr.expr eff =
    match fn with
    | Bits1 fn1 ->
        return (bits1_expr fn1 a1)
    | Struct1 fn1 ->
        begin match fn1 with
        | GetField (sname,sfield) ->
            get_dstruct_field_range sname sfield >>= fun (low, high) ->
            return (BitVector.mk_extract g_ctx (high-1) low a1)
        end
    | Ignore ->
        return (UnitSort.mk_unit)


  let smt_binop (fn: debug_id_ty fn2) (a1: Expr.expr) (a2: Expr.expr): Expr.expr eff =
    match fn with
    | Bits2 bitsfn ->
        return (bits2_expr bitsfn a1 a2)
    | Struct2 (SubstField (name,field)) ->
        get_struct name >>= fun def ->
        get_dstruct_field_range name field >>= fun (low,high) ->
        let sz = struct_sz def in
        (*
        printf "sname sz: %s %d\n" (string_of_dbg_id name) sz;
        printf "low/high: %s %d %d\n" (string_of_dbg_id field) low high;
        *)
        assert (high > low);
        assert (high <= struct_sz def);
        let ret = a2 in
        let ret = if high < sz then
                    BitVector.mk_concat g_ctx (BitVector.mk_extract g_ctx (sz-1) high a1) ret
                  else
                    ret in
        let ret = if low > 0 then
                    BitVector.mk_concat g_ctx ret (BitVector.mk_extract g_ctx (low-1) 0 a1) else ret in
        return ret

  let rec smt_action (AnnotAction(action, annots) : debug_id_ty aaction)
                 : Expr.expr eff =
    let id = get_annot_id annots in
    (* let sz = get_annot_ty annots in *)
    get_id_string id >>= fun expr_string ->
    match action with
    | Fail ty ->
        get_guard_expr >>= fun guard ->
        add_fail_cond guard >>
        return (mk_bv_or_unit (expr_string ^ "Fail") ty)
    | Var var ->
        lookup_var var
    | Const cst ->
        if (List.length cst = 0) then
          return UnitSort.mk_unit
        else return (BitVector.mk_numeral g_ctx (Z.to_string (z_of_blist cst)) (List.length cst))
    | Assign (var,a)->
        smt_action a >>= fun a_expr ->
        get_guard_expr >>= fun guard ->
        lookup_var var >>= fun old_var ->
        let new_value = mk_ite guard a_expr old_var in
        assign_var var new_value >>
        return (UnitSort.mk_unit)
    | Seq (a1,a2) ->
        smt_action a1 >>= fun _ ->
        smt_action a2
    | If (cond,tbranch,fbranch) ->
        smt_action cond >>= fun cond ->
        let guard_true = mk_bv1_to_bool cond in
        let guard_false = mk_not (mk_bv1_to_bool cond) in
        add_guard guard_true >>
        smt_action tbranch >>= fun tbranch ->
        remove_guard >>
        add_guard guard_false >>
        smt_action fbranch >>= fun fbranch ->
        remove_guard >>
        return (mk_ite guard_true tbranch fbranch)
    | Bind (var, a1,a2) ->
        smt_action a1 >>= fun a1 ->
        bind_var var a1 >>
        smt_action a2 >>= fun a2 ->
        unbind_var var >>
        return a2
    | Read (port, reg) ->
        lookup_sched_taint reg >>= fun sched_taint ->
        get_guard_expr >>= fun guard ->
        begin match port with
        | P0 ->
          add_fail_cond (mk_and [guard;conflicts_with_read0 sched_taint]) >>
          set_action_taint reg LE_Read0 guard >>
          lookup_reg reg
        | P1 ->
          add_fail_cond (mk_and [guard;conflicts_with_read1 sched_taint]) >>
          set_action_taint reg LE_Read1 guard >>
          lookup_cur_reg reg
        end
    | Write (port, reg, action) ->
        smt_action action >>= fun action ->
        get_guard_expr >>= fun guard ->
        do_guarded_write ~guard:guard reg action >>
        lookup_sched_taint reg >>= fun sched_taint ->
        lookup_action_taint reg >>= fun action_taint ->
        begin match port with
        | P0 ->
          add_fail_cond (mk_and [guard;conflicts_with_write0 sched_taint]) >>
          add_fail_cond (mk_and [guard;conflicts_with_write0 action_taint]) >>
          set_action_taint reg LE_Write0 guard
        | P1 ->
          add_fail_cond (mk_and [guard;conflicts_with_write1 sched_taint]) >>
          add_fail_cond (mk_and [guard;conflicts_with_write1 action_taint]) >>
          set_action_taint reg LE_Write1 guard
        end >>
        return (UnitSort.mk_unit)
    | Zop fn ->
        smt_zop fn
    | Unop (fn,action) ->
        smt_action action >>= fun action ->
        smt_unop fn action
    | Binop (fn,a1,a2) ->
        smt_action a1 >>= fun a1 ->
        smt_action a2 >>= fun a2 ->
        smt_binop fn a1 a2
    | InternalCall (_,_) ->
        failwith "InternalCalls should be already inlined"
    | ExternalCall (fn,action) ->
        smt_action action >>= fun action ->
        get_guard_expr >>= fun guard ->
        conflicts_with_ext_call fn >>= fun conflicts_expr ->
        add_fail_cond (mk_and [guard; conflicts_expr]) >>
        do_guarded_ext_call ~guard:guard fn action

  let do_rule : (reg_map_t * ext_log_t * taint_log_t * Expr.expr) eff =
    get >>= fun st ->
    smt_action st.rule_body >>= fun _ ->
    get_fail_conds >>= fun fail_conds ->
    get_cur_reg_map >>= fun cur_reg_map ->
    get_ext_log >>= fun ext_log ->
    get_action_taint >>= fun action_taint ->
    (*get_ext_calls >>= fun ext_calls -> *)
    (* get_assertions >>= fun assertions -> *)
    return (cur_reg_map, ext_log, action_taint, mk_or fail_conds)

end
let rec foldi_helper i max f acc =
  if i = max then acc
  else foldi_helper (i+1) max f (f i acc)

let foldi max f acc =
  foldi_helper 0 max f acc


module SmtAbstractMachine = struct
  type state_ty =
    { machine_id: machine_id_t;
      machine: machine_t;
      reg_init: reg_map_t;
      reg_mid : reg_map_t;
      reg_final: reg_map_t;
      mid_ext_log: ext_log_t;
      ext_log: ext_log_t
    }

  let mk_init_ext_log
    (machine_id: machine_id_t)
    (ext_sigma: (debug_id_ty ext_fn_t * (int * int)) list)
    (id: int)
    : ext_log_t =
    List.fold_left ~f:(fun acc (fn,(in_sz,_)) ->
        Map.add_exn
          ~key:fn
~data:(Z3Option.mk_initial (sprintf "__ExtLog{%s}[%s]@[%d]" (string_of_machine_id machine_id) (string_of_dbg_id fn) id)
                  (fun name -> mk_bv_s name in_sz)
                ) acc)
          ~init:IdMap.empty ext_sigma

  let mk_initial_reg_map (machine_id: machine_id_t)
                         (rule_id: int)
                         (* (num_rules: int) *)
                         (registers: (debug_id_ty reg_t * int) list)
                         : reg_map_t =
    List.fold_left ~f:(fun acc (reg,sz) ->
        Map.add_exn
          ~key:reg
          ~data:(mk_reg_expr machine_id rule_id reg sz)
          acc) ~init:IdMap.empty registers

  let mk_initial_state (machine_id: machine_id_t)
                       (machine: machine_t)
                       : state_ty =
    { machine_id = machine_id;
      machine = machine;
      reg_init = mk_initial_reg_map machine_id 0 machine.file_registers;
      reg_mid =  mk_initial_reg_map machine_id 1 machine.file_registers;
      reg_final = mk_initial_reg_map machine_id 2 machine.file_registers;
      mid_ext_log = mk_init_ext_log machine_id machine.file_ext_sigma 0;
      ext_log = mk_init_ext_log machine_id machine.file_ext_sigma 1;
    }
end

module SmtMachine = struct
  type state_ty =
    { machine_id: machine_id_t;
      machine: machine_t;
      reg_map: reg_map_t IntMap.t;
      sched_taint: taint_log_t IntMap.t;
      ext_log: ext_log_t IntMap.t;
      (* ext_calls: (Expr.expr list) IdMap.t; *)

      ext_func_decls: FuncDecl.func_decl IdMap.t;
      fail_vars: Expr.expr IntMap.t;
      (* assertions: Expr.expr list; *)

      schedule: ((string * debug_id_ty aaction) list);
    }

  include EffMonad (struct type state = state_ty end)

  let mk_initial_reg_map (machine_id: machine_id_t)
                         (num_rules: int)
                         (registers: (debug_id_ty reg_t * int) list)
                         : reg_map_t IntMap.t =
    foldi (num_rules + 1) (fun rule acc ->
      let new_map = List.fold_left ~f:(fun acc (reg,sz) ->
        Map.add_exn
          ~key:reg
          ~data:(mk_reg_expr machine_id rule reg sz)
            acc) ~init:IdMap.empty registers in
      Map.add_exn ~key:rule ~data:new_map acc) IntMap.empty

  let mk_initial_ext_log (machine_id: machine_id_t)
                         (num_rules: int)
                         (ext_sigma: (debug_id_ty ext_fn_t * (int * int)) list)
                         : ext_log_t IntMap.t =
    foldi (num_rules + 1) (fun rule acc ->
      let new_map = List.fold_left ~f:(fun acc (fn,(in_sz,_)) ->
        Map.add_exn
          ~key:fn
          ~data:(Z3Option.mk_initial (sprintf "__ExtLog{%s}[%s]@R%d" (string_of_machine_id machine_id) (string_of_dbg_id fn) rule)
                  (fun name -> mk_bv_s name in_sz)
                ) acc)
          ~init:IdMap.empty ext_sigma in
      Map.add_exn ~key:rule ~data:new_map acc ) IntMap.empty

  let mk_initial_sched_taint (machine_id: machine_id_t)
                         (num_rules: int)
                         (registers: (debug_id_ty reg_t * int) list)
                         : taint_log_t IntMap.t =
    foldi (num_rules + 1) (fun rule acc ->
      let new_map = List.fold_left ~f:(fun acc (reg,_) ->
        Map.add_exn
          ~key:reg
          ~data:(init_symbolic_log_taint
                  (fun le ->
                (sprintf "__SchedLog{%s}[%s]@R%d.%s" (string_of_machine_id machine_id) (string_of_dbg_id reg) rule le)))
            acc) ~init:IdMap.empty registers in
      Map.add_exn ~key:rule ~data:new_map acc) IntMap.empty

  let mk_fail_vars (machine_id: machine_id_t)
                   (rule_names: string list)
                   : Expr.expr IntMap.t =
    fst (List.fold_left ~f:(fun (acc,ctr) name ->
      (Map.add_exn ~key:ctr
                      ~data:(Boolean.mk_const_s g_ctx (sprintf "__FAIL{%s}:%s.%d#fail" (string_of_machine_id machine_id) name ctr)) acc, ctr+1)
    ) ~init:(IntMap.empty, 0) rule_names)

  let mk_ext_func_decls
    (machine_id: machine_id_t)
    (sigmas: (debug_id_ty ext_fn_t * (int * int)) list)
    : FuncDecl.func_decl IdMap.t =
    List.fold_left ~f:(fun acc (id, (in_sz, out_sz)) ->
      Map.add_exn ~key:id
        ~data:(FuncDecl.mk_func_decl_s g_ctx
                 (sprintf "__EXTFN{%s}[%s]"
                  (string_of_machine_id machine_id)
                  (string_of_dbg_id id)
                 )
                 [mk_bv_or_unit_sort in_sz]
                 (mk_bv_or_unit_sort out_sz)
              )
        acc
    ) ~init:IdMap.empty sigmas

  let mk_initial_state (machine_id: machine_id_t)
                       (machine: machine_t)
                       (schedule: schedule_t)
                       : state_ty =
    let num_rules = List.length schedule in
    let init_ext_log = mk_initial_ext_log machine_id num_rules machine.file_ext_sigma in
    { machine_id = machine_id;
      machine = machine;

      reg_map = mk_initial_reg_map machine_id num_rules machine.file_registers;
      sched_taint = mk_initial_sched_taint machine_id num_rules machine.file_registers;
      ext_log = init_ext_log;
      (* ext_calls = mk_initial_ext_calls machine.file_ext_sigma; *)

      ext_func_decls = mk_ext_func_decls machine_id machine.file_ext_sigma;
      fail_vars = mk_fail_vars machine_id (List.map ~f:fst schedule);
      schedule = schedule;
    }

  let get_reg_map (rl_idx: int) : reg_map_t eff =
    get >>= fun st ->
    return (Map.find_exn st.reg_map rl_idx)

  let add_reg_map (rl_idx: int) (map: reg_map_t) : unit eff =
    get >>= fun st ->
    put {st with reg_map = Map.add_exn ~key:rl_idx ~data:(map) st.reg_map}

  let get_ext_log (rl_idx: int): ext_log_t eff =
    get >>= fun st ->
    return (Map.find_exn st.ext_log rl_idx)

  let get_sched_taint (rl_idx: int): taint_log_t eff =
    get >>= fun st ->
    return (Map.find_exn st.sched_taint rl_idx)

  let get_schedule : (string * debug_id_ty aaction) list eff =
    get >>= fun st ->
    return st.schedule

  let get_machine: machine_t eff =
    get >>= fun st ->
    return st.machine

  let put_schedule
      (schedule: ((string * debug_id_ty aaction) list))
      : unit eff =
    get >>= fun st ->
    put {st with schedule = schedule}

  let get_fail_var (rl_num: int) : Expr.expr eff =
    get >>= fun st ->
    return (Map.find_exn st.fail_vars rl_num)

  let mk_eq_reg_maps (fail_expr: Expr.expr)
                     ~init:(init_reg_map: reg_map_t)
                     ~rule:(rule_reg_map: reg_map_t)
                     ~final:(final_reg_map: reg_map_t)
                     : Expr.expr list =
    Map.fold2 init_reg_map final_reg_map ~init:[]
      ~f:(fun ~key:key ~data:data acc ->
          match data with
          | `Both (v_init,v_final) ->
              let v_rule = Map.find_exn rule_reg_map key in
              (mk_eq v_final (mk_ite fail_expr v_init v_rule))::acc
          | _ -> failwith "Domain not equal"
          )

  (* final = guarded log_app of init and rule *)
  let mk_eq_log_app_taints (fail_expr: Expr.expr)
                           ~init:(init_taint: taint_log_t)
                           ~rule:(rule_taint: taint_log_t)
                           ~final:(final_taint: taint_log_t)
                           : Expr.expr list =
    Map.fold2 init_taint final_taint ~init:[]
      ~f:(fun ~key:key ~data:data acc ->
            match data with
            | `Both (v_init, v_final) ->
                let v_rule = Map.find_exn rule_taint key in
                (mk_eq v_final.lread0
                  (mk_ite fail_expr v_init.lread0 (mk_or [v_init.lread0;v_rule.lread0])))
                ::(mk_eq v_final.lread1
                  (mk_ite fail_expr v_init.lread1 (mk_or [v_init.lread1;v_rule.lread1])))
                ::(mk_eq v_final.lwrite0
                  (mk_ite fail_expr v_init.lwrite0 (mk_or [v_init.lwrite0;v_rule.lwrite0])))
                ::(mk_eq v_final.lwrite1
                  (mk_ite fail_expr v_init.lwrite1 (mk_or [v_init.lwrite1;v_rule.lwrite1])))
                :: acc
            | _ -> failwith "Domain not equal"
         )


  let mk_eq_ext_maps (fail_expr: Expr.expr)
                     ~init:(init_ext_log: ext_log_t)
                     ~rule:(rule_ext_log: ext_log_t)
                     ~final:(final_ext_log: ext_log_t)
                     : Expr.expr list =
    Map.fold2 init_ext_log final_ext_log ~init:[]
      ~f:(fun ~key:key ~data:data acc ->
            match data with
            | `Both (v_init, v_final) ->
                let v_rule = Map.find_exn rule_ext_log key in
                (mk_eq v_final.value (mk_ite fail_expr v_init.value v_rule.value))::(mk_eq v_final.is_some (mk_ite fail_expr v_init.is_some v_rule.is_some))::acc
            | _ -> failwith "Domain not equal"
          )


  let do_smt_rule (rl_num: int)
                  (rule_name: string)
                  (rule_body: debug_id_ty aaction)
                  : unit eff =
    get >>= fun st ->
    get_reg_map rl_num >>= fun initial_regs ->
    get_ext_log rl_num >>= fun ext_log ->
    get_sched_taint rl_num >>= fun sched_taint ->
    let initial_state =
        SmtAction.mk_initial_state st.machine_id st.machine.file_registers
                                   rule_name rl_num rule_body
                                   initial_regs sched_taint ext_log
                                   st.ext_func_decls
                                   st.machine.file_struct_defs in
    let ((cur_reg_map, cur_ext_log, rule_taint, smt_fail), _) =
        SmtAction.run initial_state (SmtAction.do_rule) in
    (* TODO *)
    printf "------BEGIN %d %s-----\n" rl_num rule_name;
    get_fail_var rl_num >>= fun fail_var ->
    let fail_expr = Expr.simplify (mk_eq fail_var smt_fail) None in
    (* printf "FAIL: %s\n" (Expr.to_string fail_expr); *)

    get_reg_map (rl_num+1) >>= fun final_regs ->
    get_ext_log (rl_num+1) >>= fun final_ext_log ->
    get_sched_taint (rl_num+1) >>= fun final_sched_taint ->
    let reg_eqs = mk_eq_reg_maps fail_var
                    ~init:initial_regs
                    ~rule: cur_reg_map
                    ~final: final_regs in
    let ext_fn_eqs = mk_eq_ext_maps fail_var
                    ~init:ext_log
                    ~rule:cur_ext_log
                    ~final:final_ext_log in
    let taint_log_eqs = mk_eq_log_app_taints fail_var
                    ~init:sched_taint
                    ~rule:rule_taint
                    ~final:final_sched_taint in
    (* TODO: ext log *)
    Solver.add g_solver [fail_expr];
    Solver.add g_solver (List.map ~f:(fun e -> Expr.simplify e None) reg_eqs);
    Solver.add g_solver (List.map ~f:(fun e -> Expr.simplify e None) ext_fn_eqs);
    Solver.add g_solver (List.map ~f:(fun e -> Expr.simplify e None) taint_log_eqs);

    (* Solver.add g_solver smt_asserts; *)
    (* printf "Solver: %s\n" (Solver.to_string g_solver); *)
    (* Equate fail log *)
    return ()

  let do_annots : unit eff =
    get_schedule >>= fun schedule ->
    let initial_state =
        AnnotateAction.mk_initial  in
    let (annotated_schedule, _) =
      AnnotateAction.run initial_state
        (AnnotateAction.do_schedule schedule) in
    smt_debug_print 7 "Done AnnoteAction phase";
    put_schedule annotated_schedule

  let do_smt : unit eff =
    get_schedule >>= fun schedule ->
    (*printf "Smt schedule\n";
    printf "%s" (string_of_scheduler schedule); *)
    mapMi_ (fun rl_num (rl_name, rl) ->
      do_smt_rule rl_num rl_name rl
    ) schedule >>
    (smt_debug_print 7 "Done SmtAction phase";
     return ())

  let extract_final_state : (reg_map_t * reg_map_t * ext_log_t * ext_log_t * taint_log_t * FuncDecl.func_decl IdMap.t) eff =
    get >>= fun st ->
    get_reg_map 0 >>= fun initial_regs ->
    get_ext_log 0 >>= fun init_ext_log ->
    get_sched_taint 0 >>= fun init_sched_taint ->
    get_reg_map (List.length st.schedule) >>= fun final_regs ->
    get_ext_log (List.length st.schedule) >>= fun ext_log ->
    return (initial_regs, final_regs, init_ext_log, ext_log, init_sched_taint, st.ext_func_decls)
end

let initialise_solver (solver: Solver.solver) =
  smt_debug_print 5 "Initialising solver.";
  let params = Params.mk_params g_ctx in
  Solver.set_parameters solver params

let run_solver print_model =
    match Solver.check g_solver [] with
    | SATISFIABLE ->
        smt_debug_print 1 "SAT :(";
        begin match Solver.get_model g_solver with
              | Some model ->
                  (if print_model then
                    begin
                      print_endline "SOLVER";
                      print_endline (Solver.to_string g_solver);
                      print_endline "BINDING MODEL";
                      print_endline (Model.to_string model)
                    end);
                  Some model
              | None ->
                  failwith "Model not found"
              end
    | UNSATISFIABLE ->
        smt_debug_print 1 "UNSAT :)";
        None
    | UNKNOWN ->
        failwith
          (sprintf "ERROR: status unknown. Reason: %s"
                   (Solver.get_reason_unknown g_solver))

let eval_assertions model assertions oc =
  Printf.fprintf oc "EVALUATING ASSERTIONS\n";
  begin match model with
  | Some model ->
      List.iter ~f:(fun expr ->
        match Model.eval model expr true with
        | Some v -> Printf.fprintf oc "%s: %s\n" (Expr.to_string v) (Expr.to_string expr)
        | None -> Printf.fprintf oc "None: %s\n" (Expr.to_string expr)
      ) assertions
  | None -> ()
  end

let get_machine_from_file (file_machines: file_type) (machine_id: machine_id_t)
    : machine_t =
    match file_machines with
    | Single (machine, _) ->
        assert (Stdlib.compare machine_id MachineImpl = 0);
        machine
    | Product (impl,spec, _, _) ->
        begin match machine_id with
        | MachineImpl -> impl
        | MachineSpec -> spec
        end
    | AbstractSingle (machine) ->
        assert (Stdlib.compare machine_id MachineImpl = 0);
        machine
    | AbstractProduct(impl,spec) ->
        begin match machine_id with
        | MachineImpl -> impl
        | MachineSpec -> spec
        end

module SmtFile = struct
  type state_ty =
    { file: file_t;
      init_reg_maps: machine_reg_map_t;
      mid_reg_maps: machine_reg_map_t;
      final_reg_maps: machine_reg_map_t;
      init_ext_log_maps: ext_log_map_t;
      mid_ext_log_maps: ext_log_map_t;
      ext_log_maps: ext_log_map_t;
      ext_func_decls: ext_fun_map_t;
    }

  let mk_initial_state (file: file_t) : state_ty =
    { file = file ;
      init_reg_maps = MachineIdMap.empty;
      mid_reg_maps = MachineIdMap.empty;
      final_reg_maps = MachineIdMap.empty;
      init_ext_log_maps = MachineIdMap.empty;
      mid_ext_log_maps= MachineIdMap.empty;
      ext_log_maps = MachineIdMap.empty;
      ext_func_decls = MachineIdMap.empty;
    }

  include EffMonad (struct type state = state_ty end)

  let get_machine (machine_id: machine_id_t)
                  : machine_t eff =
    get >>= fun st ->
    return (get_machine_from_file st.file.file_machines machine_id)

        (*
    return (snd (List.find_exn ~f:(fun (id, _) -> Stdlib.compare machine_id id = 0) st.file.file_machines)) *)

  let get_struct (machine_id: machine_id_t) (sname: debug_id_ty)
                 : (debug_id_ty struct_t) eff  =
    get_machine machine_id >>= fun machine ->
    return (List.find_exn machine.file_struct_defs ~f:(
      fun def -> debug_id_ty_equal sname def.dstruct_name))

  let get_dstruct_field_range
      (machine_id: machine_id_t)
      (sname: debug_id_ty)
      (fname: debug_id_ty)
      : (int * int) eff =
    get_struct machine_id sname >>= fun def ->
    return (get_dstruct_field_range def fname)


  let add_init_reg_map (machine_id: machine_id_t)
                       (map: reg_map_t)
                       : unit eff =
    get >>= fun st ->
    put { st with init_reg_maps =
            Map.add_exn ~key:machine_id
                                 ~data:map st.init_reg_maps }

  let add_mid_reg_map (machine_id: machine_id_t)
                       (map: reg_map_t)
                       : unit eff =
    get >>= fun st ->
    put { st with mid_reg_maps =
            Map.add_exn ~key:machine_id
                                 ~data:map st.mid_reg_maps}

  let add_final_reg_map (machine_id: machine_id_t)
                        (map: reg_map_t)
                       : unit eff =
    get >>= fun st ->
    put { st with final_reg_maps =
            Map.add_exn ~key:machine_id
                                 ~data:map st.final_reg_maps}

  let add_init_ext_log (machine_id: machine_id_t)
                       (ext_log: ext_log_t)
                       : unit eff =
    get >>= fun st ->
    put { st with init_ext_log_maps =
            Map.add_exn ~key:machine_id
                                 ~data:ext_log st.init_ext_log_maps}

  let add_mid_ext_log (machine_id: machine_id_t)
                      (ext_log: ext_log_t)
                      : unit eff =
    get >>= fun st ->
    put { st with mid_ext_log_maps =
            Map.add_exn ~key:machine_id
                                 ~data:ext_log st.mid_ext_log_maps}


  let add_ext_log (machine_id: machine_id_t)
                  (ext_log: ext_log_t)
                  : unit eff =
    get >>= fun st ->
    put { st with ext_log_maps =
            Map.add_exn ~key:machine_id
                                 ~data:ext_log st.ext_log_maps}

  let add_ext_func_decls (machine_id: machine_id_t)
                         (ext_func_decls: ext_func_decl_map_t)
                  : unit eff =
    get >>= fun st ->
    put { st with ext_func_decls =
            Map.add_exn ~key:machine_id
                                 ~data:ext_func_decls  st.ext_func_decls}


  let get_init_reg (machine_id: machine_id_t) (reg: debug_id_ty)
                   : Expr.expr eff =
    get >>= fun st ->
    return (get_reg_map st.init_reg_maps machine_id reg)

  let get_mid_reg (machine_id: machine_id_t) (reg: debug_id_ty)
                   : Expr.expr eff =
    get >>= fun st ->
    return (get_reg_map st.mid_reg_maps machine_id reg)

  let get_final_reg (machine_id: machine_id_t) (reg: debug_id_ty)
                   : Expr.expr eff =
    get >>= fun st ->
    return (get_reg_map st.final_reg_maps machine_id reg)

  let get_init_ext (machine_id: machine_id_t) (fn: debug_id_ty)
                   : Z3Option.t eff =
    get >>= fun st ->
    return (get_ext_log_map st.init_ext_log_maps machine_id fn)

  let get_mid_ext (machine_id: machine_id_t) (fn: debug_id_ty)
                  : Z3Option.t eff =
    get >>= fun st ->
    return (get_ext_log_map st.mid_ext_log_maps machine_id fn)

  let get_final_ext (machine_id: machine_id_t) (fn: debug_id_ty)
                    : Z3Option.t eff =
    get >>= fun st ->
    return (get_ext_log_map st.ext_log_maps machine_id fn)

  let get_func_decl (machine: machine_id_t)
                    (fn: debug_id_ty)
                    : FuncDecl.func_decl eff =
    get >>= fun st ->
    return (Map.find_exn (Map.find_exn st.ext_func_decls machine) fn)

  let rec sval_to_expr
      (bound_vars: ((string* Expr.expr) list))
      (sv: sval) : Expr.expr eff =
    let sval_to_expr = sval_to_expr bound_vars in
    match sv with
    | SConst cst ->
        return (BitVector.mk_numeral g_ctx (Z.to_string (z_of_blist cst)) (List.length cst))
    | SInitReg (machine_id,reg) ->
      get_init_reg machine_id reg
    | SMidReg (machine_id, reg) ->
      get_mid_reg machine_id reg
    | SFinalReg (machine_id,reg) ->
      get_final_reg machine_id reg
    | SMidExtLog (machine_id, ext_fn) ->
      get_mid_ext machine_id ext_fn >>= fun ext ->
      let sz = get_bv_size ext.value in
      return (mk_ite ext.is_some ext.value (BitVector.mk_numeral g_ctx "0" sz))
    | SFinalExtLog (machine_id, ext_fn) ->
      get_final_ext machine_id ext_fn >>= fun ext ->
      let sz = get_bv_size ext.value in
      return (mk_ite ext.is_some ext.value (BitVector.mk_numeral g_ctx "0" sz))
    | SCommittedExtLog (machine_id, ext_fn) ->
        get_mid_ext machine_id ext_fn >>= fun mid_ext ->
        get_final_ext machine_id ext_fn >>= fun final_ext ->
        let sz = get_bv_size mid_ext.value in
        let v_mid =
          (mk_ite mid_ext.is_some mid_ext.value (BitVector.mk_numeral g_ctx "0" sz)) in
        let v_final =
          (mk_ite final_ext.is_some final_ext.value (BitVector.mk_numeral g_ctx "0" sz)) in
        return (BitVector.mk_or g_ctx v_final v_mid)
    | SBits1 (bits1, v1) ->
        sval_to_expr v1 >>= fun v1 ->
        return (bits1_expr bits1 v1)
    | SBits2 (bits2, v1, v2) ->
        sval_to_expr v1 >>= fun v1 ->
        sval_to_expr v2 >>= fun v2 ->
        return (bits2_expr bits2 v1 v2)
    | SGetField (machine, sname, fname, v) ->
        sval_to_expr v >>= fun v ->
        get_dstruct_field_range machine sname fname >>= fun (low,high) ->
        return (BitVector.mk_extract g_ctx (high-1) low v)
        (*
    | SymbExtCallArg arg ->
        begin match opt_ext_args with
        | Some ext_arg_map ->
            return (List.Assoc.find_exn ~equal:(fun arg1 arg2 -> Stdlib.compare arg1 arg2 = 0) ext_arg_map arg )
        | None -> failwith "TODO SymbExtCallArg"
        end *)
    | SExtCallApp (mid,extfn,v) ->
        sval_to_expr v >>= fun v ->
        get_func_decl mid extfn >>= fun decl ->
        return (FuncDecl.apply decl [v])
    | SBound arg ->
        return (List.Assoc.find_exn ~equal:(fun arg1 arg2 -> Stdlib.compare arg1 arg2 = 0) bound_vars arg)

  let rec spred_to_expr (bound_vars: (string * Expr.expr) list)
                        (pred: spred)
                        : Expr.expr eff =
    let spred_to_expr' = spred_to_expr bound_vars in
    let sval_to_expr = sval_to_expr bound_vars in
    match pred with
    | PConst b -> return (if b then mk_true else mk_false)
    | PAnd (p1,p2) ->
        spred_to_expr' p1 >>= fun p1 ->
        spred_to_expr' p2 >>= fun p2 ->
        return (mk_and [p1;p2])
    | POr (p1,p2)->
        spred_to_expr' p1 >>= fun p1 ->
        spred_to_expr' p2 >>= fun p2 ->
        return (mk_or [p1;p2])
    | PNot sp ->
        spred_to_expr' sp >>= fun sp ->
        return (mk_not sp)
    | PImpl (sp1,sp2)  ->
        spred_to_expr' sp1 >>= fun sp1 ->
        spred_to_expr' sp2 >>= fun sp2 ->
        return (mk_implies sp1 sp2)
    | PEq (sv1, sv2) ->
        sval_to_expr sv1 >>= fun sv1 ->
        sval_to_expr sv2 >>= fun sv2 ->
        return (mk_eq sv1 sv2)
    | PNEq (sv1, sv2) ->
        sval_to_expr sv1 >>= fun sv1 ->
        sval_to_expr sv2 >>= fun sv2 ->
        return (mk_not (mk_eq sv1 sv2))
    | PForallArg1 ((arg,ty),body) ->
        (* TODO: we ensure no nested quantifiers for now*)
        begin match bound_vars with
        | [] ->
          let arg_sort = mk_bv_or_unit_sort ty in
          let bound_var = Quantifier.mk_bound g_ctx 0 arg_sort in
          spred_to_expr [arg, bound_var] body >>= fun body ->
          return (Quantifier.expr_of_quantifier
            (Quantifier.mk_forall g_ctx
              [mk_bv_or_unit_sort ty]
              [Symbol.mk_string g_ctx "__ARG__"]
              body
              None [] [] None None))
        | _ -> failwith "TODO: PForallArg1 nested quantifiers"
        end
    | PForallArg2 ((arg1,ty1),(arg2,ty2),body) ->
        begin match bound_vars with
        | [] ->
          let arg_sort1 = mk_bv_or_unit_sort ty1 in
          let arg_sort2 = mk_bv_or_unit_sort ty2 in
          let bound_var1 = Quantifier.mk_bound g_ctx 0 arg_sort1 in
          let bound_var2 = Quantifier.mk_bound g_ctx 1 arg_sort2 in
          spred_to_expr [(arg2,bound_var2);(arg1, bound_var1)] body >>= fun body ->
          return (Quantifier.expr_of_quantifier
            (Quantifier.mk_forall g_ctx
              [arg_sort2; arg_sort1]
              [Symbol.mk_string g_ctx "__ARG2__";
               Symbol.mk_string g_ctx "__ARG1__"
              ]
              body
              None [] [] None None))
        | _ -> failwith "TODO: PForallArg2 nested quantifiers"
        end
    | PExtFnEq (fn)->
       get_func_decl MachineImpl fn >>= fun impl_decl ->
       get_func_decl MachineSpec fn >>= fun spec_decl ->
       begin match FuncDecl.get_domain impl_decl with
       | [arg_sort] ->
         return (Quantifier.expr_of_quantifier
                  (Quantifier.mk_forall g_ctx
                   [arg_sort]
                   [Symbol.mk_string g_ctx "__arg__"]
  (mk_eq (FuncDecl.apply impl_decl [Quantifier.mk_bound g_ctx 0 arg_sort ]) (FuncDecl.apply spec_decl [Quantifier.mk_bound g_ctx 0 arg_sort]))
                  None [] [] None None))
        | _ -> failwith "Error: PExtFnEq"
        end
    | PFancy _ -> failwith "PFancy"

  let add_assume_init_ext_log_empty (ext_log: ext_log_t): unit eff =
    let asserts = Map.data (Map.map ~f:(fun v -> mk_eq v.is_some mk_false) ext_log) in
    Solver.add g_solver asserts;
    return ()

  let add_assume_init_sched_taint_empty (sched_taint: taint_log_t): unit eff =
    let asserts = Map.data (Map.map ~f:(fun v ->
      mk_and [mk_eq v.lread0 mk_false
             ;mk_eq v.lread1 mk_false
             ;mk_eq v.lwrite0 mk_false
             ;mk_eq v.lwrite1 mk_false
             ]) sched_taint) in
    Solver.add g_solver asserts;
    return ()


  let get_assumptions : (Expr.expr list) eff =
    get >>= fun st ->
    mapM (spred_to_expr []) st.file.file_assumptions

  let get_assertions : (Expr.expr list) eff =
    get >>= fun st ->
    mapM (spred_to_expr []) st.file.file_assertions

    (*
  let add_assertions () : (Expr.expr list) eff =
    get >>= fun st ->
    mapM (spred_to_expr []) st.file.file_assertions >>= fun assertions ->
    Solver.assert_and_track
      g_solver
      (Expr.simplify (mk_not (mk_and assertions)) None)
      (Expr.mk_fresh_const g_ctx "negated_vcs" boolean_sort);
    smt_debug_print 4 (sprintf "ASSERTIONS %s" (Expr.to_string (Expr.simplify (mk_not (mk_and assertions)) None)));
    return assertions
    *)

  let do_abstract_schedule (machine_id: machine_id_t)
                           (machine: machine_t)
                           : unit eff =
    let initial_state : SmtAbstractMachine.state_ty =
        SmtAbstractMachine.mk_initial_state machine_id machine in
    let init_regs = initial_state.reg_init in
    let mid_regs = initial_state.reg_mid in
    let final_regs = initial_state.reg_final in
    let mid_ext_log = initial_state.mid_ext_log in
    let ext_log = initial_state.ext_log in
    add_assume_init_ext_log_empty ext_log >>
    add_init_reg_map machine_id init_regs >>
    add_mid_reg_map machine_id mid_regs >>
    add_final_reg_map machine_id final_regs >>
    add_init_ext_log machine_id ext_log >>
    add_mid_ext_log machine_id mid_ext_log >>
    add_ext_log machine_id ext_log


  let do_concrete_schedule (machine_id: machine_id_t)
                           (machine: machine_t)
                           (schedule: schedule_t) : unit eff =
      let initial_state : SmtMachine.state =
        SmtMachine.mk_initial_state machine_id machine schedule in
      let (>>) = SmtMachine.(>>) in
      let do_stuff =
        SmtMachine.do_annots >>
        SmtMachine.do_smt >>
        SmtMachine.extract_final_state in
      let ((init_regs, final_regs, init_ext_log, ext_log, init_sched_taint, ext_func_decls), _) = SmtMachine.run initial_state do_stuff in
      let (>>=) = bind in
      let (>>) m m' = m >>= fun _ -> m' in

      add_assume_init_ext_log_empty init_ext_log >>
      add_assume_init_sched_taint_empty init_sched_taint >>
      add_init_reg_map machine_id init_regs >>
      add_final_reg_map machine_id final_regs >>
      add_init_ext_log machine_id init_ext_log >>
      add_ext_log machine_id ext_log >>
      add_ext_func_decls machine_id ext_func_decls

  (*
  let do_generic_concrete_schedule (machine_id: machine_id_t)
                           (machine: machine_t)
                           (schedule: schedule_t) : unit eff =
      let initial_state : SmtMachine.state =
        SmtMachine.mk_initial_state machine_id machine schedule in
      let (>>) = SmtMachine.(>>) in
      let do_stuff =
        SmtMachine.do_annots >>
        SmtMachine.do_generic_smt >>
        SmtMachine.extract_final_state in
      let ((init_regs, final_regs, init_ext_log, ext_log, ext_func_decls), _) = SmtMachine.run initial_state do_stuff in
      let (>>=) = bind in
      let (>>) m m' = m >>= fun _ -> m' in

      add_assume_init_ext_log_empty init_ext_log >>
      add_init_reg_map machine_id init_regs >>
      add_final_reg_map machine_id final_regs >>
      add_init_ext_log machine_id init_ext_log >>
      add_ext_log machine_id ext_log >>
      add_ext_func_decls machine_id ext_func_decls
  *)

  let do_machine (machine_id: machine_id_t)
                 (machine: machine_t)
                 (schedule: symb_schedule_t): unit eff =
    begin match schedule with
    | ConcreteSchedule sched ->
          do_concrete_schedule machine_id machine sched
          (* do_generic_concrete_schedule machine_id machine sched *)
    | AbstractSchedule -> do_abstract_schedule machine_id machine
    end


  let smt_file : (Expr.expr list * Expr.expr list) eff =
    get >>= fun st ->
    begin match st.file.file_machines with
     | Single (machine, schedule) ->
          do_machine MachineImpl machine (ConcreteSchedule schedule)
     | Product (impl,spec, impl_sched, spec_sched) ->
         (do_machine MachineImpl impl (ConcreteSchedule impl_sched)
         >> do_machine MachineSpec spec (ConcreteSchedule spec_sched))
     | AbstractSingle machine ->
          do_machine MachineImpl machine (AbstractSchedule)
     | AbstractProduct (impl, spec) ->
        (    do_machine MachineImpl impl AbstractSchedule
         >> do_machine MachineSpec spec AbstractSchedule)
    end >>
    get_assumptions >>= fun assumptions ->
    get_assertions >>= fun assertions ->
    return (assumptions, assertions)
end

    (* stupid side effects *)


    (*
    add_assumptions ()

    begin match Solver.check g_solver [] with
             | SATISFIABLE ->
                smt_debug_print 1 "Checkpoint passed: assumes are SAT";
                smt_debug_print 1 "HERE";
                smt_debug_print 1 (Solver.to_string g_solver);
                begin match Solver.check g_solver [] with
                | SATISFIABLE -> failwith "HI"
                | UNSATISFIABLE -> failwith "BYE"
                | UNKNOWN -> failwith "BOO"
                end;
                failwith "DONE";
                return None
             | UNSATISFIABLE ->
                 let _ = Solver.get_unsat_core g_solver in
                 smt_debug_print 1 "Assumes are false";
                 failwith "Assumes are false"
             | UNKNOWN ->
                 let error_msg = sprintf "ERROR: status unknown. Reason %s"
                                  (Solver.get_reason_unknown g_solver) in
                 return (Some (`Unknown error_msg))
     end >>= fun error_opt ->
    if is_some (error_opt  ) then
      failwith "Assumptions don't hold" (* TODO *)
    else begin
      smt_debug_print 1 "BEGIN ADD ASSERTIONS";
      add_assertions () >>= fun assertions  ->
      smt_debug_print 1 "END ADD ASSERTIONS";

      let model = run_solver false in
      return (model, assertions)
    end
    *)

let machine_lookup_reg_from_id (machine: machine_t) (id: int)
  : debug_id_ty * int =
  List.find_exn machine.file_registers
    ~f:(fun ((_, rid),_) ->
          Int.equal rid id
       )

let lookup_reg_from_id (file: file_t) (mid: machine_id_t) (id: int)
                       : debug_id_ty * int =
  machine_lookup_reg_from_id (get_machine_from_file file.file_machines mid ) id

module DoQueries = struct
  open Query_ast

  let parse (s: string) : expr option =
    let lexbuf = Lexing.from_string s in
    Option.try_with (fun _ -> Query_parser.cmd Query_lexer.read lexbuf)

  let query_model_e model e : string =
    match Model.get_const_interp_e model e with
    | Some expr -> (Expr.to_string expr)
    | None -> "No interp"

  let rec query file model  =
    smt_debug_print 1 "Enter query or STOP: ";
    let s = Core.read_line () in
    let parsed = parse s in
    begin match parsed with
    | Some parsed ->
      begin match parsed with
      | Stop -> smt_debug_print 1 "DONE!"
      | Query (mid, RegRange(start_reg, end_reg), rule_num) ->
          let mid' = begin match mid with
                     | Impl -> MachineImpl
                     | Spec -> MachineSpec
                     end in
          let regs = List.init (max 0 (end_reg - start_reg)) (fun i -> start_reg + i) in
          let resp = String.concat ~sep:"\n" (List.map ~f:(fun reg ->
            let (reg_id, sz) = lookup_reg_from_id file mid' reg in
            let expr = mk_reg_expr mid' rule_num reg_id sz in
            let resp = query_model_e model expr in
            sprintf "%s:%s" (string_of_dbg_id reg_id) resp) regs) in
          print_endline resp;
          query file model

      | Query (mid, RegList regs, rule_num) ->
          let mid' = begin match mid with
                     | Impl -> MachineImpl
                     | Spec -> MachineSpec
                     end in
          let resp = String.concat ~sep:"\n" (List.map ~f:(fun reg ->
            let (reg_id, sz) = lookup_reg_from_id file mid' reg in
            let expr = mk_reg_expr mid' rule_num reg_id sz in
            let resp = query_model_e model expr in
            sprintf "%s:%s" (string_of_dbg_id reg_id) resp) regs) in
          print_endline resp;
          query file model
      end
    | None -> smt_debug_print 1 "ERROR: try again or STOP" ;
              query file model
    end

  let user_query_model file (model) : unit =
    begin match model with
    | Some model -> query file model
    | None -> smt_debug_print 1 "No model to query"
  end
end

let smt_file (file: file_t) (query_model: bool) (print_solver: bool) model_outfile =
  let initial_state : SmtFile.state =
    SmtFile.mk_initial_state file in
  initialise_solver g_solver;
  let do_stuff = SmtFile.smt_file in
  smt_debug_print 1 "SMT_FILE";
  let ((assumptions, assertions), _) = SmtFile.run initial_state do_stuff in
  smt_debug_print 1 "ADDING_ASSUMPTIONS";
  Solver.add g_solver assumptions;
  begin match Solver.check g_solver [] with
  | SATISFIABLE ->
      smt_debug_print 1 "Checkpoint passed: assumes are SAT"
     (*  smt_debug_print 1 (Solver.to_string g_solver) *)
  | UNSATISFIABLE ->
    (* let exprs = Solver.get_unsat_core g_solver in *)
    (*
    smt_debug_print 1 "UNSAT CORE";
    List.iter ~f:(fun expr -> smt_debug_print 1 (Expr.to_string expr))
              exprs;
    smt_debug_print 1 (sprintf "%d" (List.length exprs));
    *)
    smt_debug_print 1 (Solver.to_string g_solver);
    failwith "Assumes are false"
  | UNKNOWN ->
    let error_msg = sprintf "ERROR: status unknown. Reason %s"
                                  (Solver.get_reason_unknown g_solver) in
    failwith error_msg
  end;
  smt_debug_print 1 "ADDING_ASSERTIONS";
  Solver.assert_and_track
      g_solver
      (Expr.simplify (mk_not (mk_and assertions)) None)
      (Expr.mk_fresh_const g_ctx "negated_vcs" boolean_sort);
   let model = run_solver false in
  (* smt_debug_print 4 (sprintf "ASSERTIONS %s" (Expr.to_string (Expr.simplify (mk_not (mk_and assertions)) None))); *)
  begin match model, model_outfile with
        | Some model, Some file ->
            let oc = Core.open_out file in
            Printf.fprintf oc "%s\n" (Model.to_string model);
            (if print_solver then
              Printf.fprintf oc "SOLVER: \n %s\n" (Solver.to_string g_solver));
            eval_assertions (Some model) assertions (oc);
            Core.close_out oc
        | _, _ -> ()
  end;
  begin if query_model then
    DoQueries.user_query_model file model
  end;
  (* smt_debug_print 8 (sprintf "Solver: %s\n" (Solver.to_string g_solver)); *)
  ()


let do_file file query_model print_solver model_outfile =
  smt_file file query_model print_solver model_outfile

