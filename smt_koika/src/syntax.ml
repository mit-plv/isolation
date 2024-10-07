open Core

type debug_id_ty = [%import:Extracted.debug_id_ty] [@@deriving show,sexp]
type annot_t = [%import:Extracted.annot_t] [@@deriving show,sexp]
type port = [%import:Extracted.port] [@@deriving show,sexp]
type 'id_ty reg_t = [%import:'id_ty Extracted.reg_t] [@@deriving show,sexp]
type var_t = [%import:Extracted.var_t] [@@deriving show,sexp]
type 'id_ty fn_name_t = [%import:'id_ty Extracted.fn_name_t] [@@deriving show,sexp]
type 'id_ty fn_name_t0 = [%import:'id_ty Extracted.fn_name_t0] [@@deriving show,sexp]
type 'id_ty ext_fn_t = [%import:'id_ty Extracted.ext_fn_t] [@@deriving show,sexp]
type 'id_ty ext_fn_t0 = [%import:'id_ty Extracted.ext_fn_t0] [@@deriving show,sexp]
type 'id_ty dstruct_name_t = [%import:'id_ty Extracted.dstruct_name_t] [@@deriving show,sexp]
type 'id_ty dstruct_field_t = [%import:'id_ty Extracted.dstruct_field_t] [@@deriving show,sexp]
type 'id_ty struct_t = [%import:'id_ty Extracted.struct_t] [@@deriving show,sexp]
type bits1 = [%import:Extracted.bits1] [@@deriving show,sexp]
type 'id_ty struct1 = [%import:'id_ty Extracted.struct1] [@@deriving show,sexp]
type bits_comparison = [%import:Extracted.bits_comparison] [@@deriving show,sexp]
type bits2 = [%import:Extracted.bits2] [@@deriving show,sexp]
type 'id_ty fn0 = [%import:'id_ty Extracted.fn0] [@@deriving show,sexp]
type 'id_ty fn1 = [%import:'id_ty Extracted.fn1] [@@deriving show,sexp]
type 'id_ty struct2 = [%import:'id_ty Extracted.struct2] [@@deriving show,sexp]
type 'id_ty fn2 = [%import:'id_ty Extracted.fn2] [@@deriving show,sexp]
type 'id_ty aaction' = [%import:'id_ty Extracted.aaction'] [@@deriving show,sexp]
  and 'id_ty aaction = [%import:'id_ty Extracted.aaction] [@@deriving show,sexp]
type vect_t = [%import:Extracted.vect_t] [@@deriving show,sexp]
type 'id_ty struct_env_t = [%import:'id_ty Extracted.struct_env_t] [@@deriving show,sexp]
type machine_id_t = [%import:Extracted.machine_id_t] [@@deriving show,sexp]
(* type ext_call_arg = [%import:Extracted.ext_call_arg] [@@deriving show,sexp] *)
type sval = [%import:Extracted.sval] [@@deriving show,sexp]
type spred = [%import:Extracted.spred] [@@deriving show,sexp]
  and fancy_spred = [%import:Extracted.fancy_spred] [@@deriving show, sexp]
(* type quantified_spred = [%import:Extracted.quantified_spred] [@@deriving show,sexp] *)
type machine_t = [%import:Extracted.machine_t] [@@deriving show,sexp]
type file_type = [%import:Extracted.file_type] [@@deriving show,sexp]
type file_t = [%import:Extracted.file_t] [@@deriving show,sexp]

let struct_sz = Extracted.struct_sz

