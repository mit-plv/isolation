Require Import koika.Common.
Require Import koika.Syntax.
Require Import koika.Parsing.
Require Import koika.Utils.
Require Import koika.Environments.
Require Import koika.SyntaxUtils.
Require Import koika.SyntaxMacros.

Section Maybe.
  Context (id: debug_id_ty).
  Context (data_sz: nat).

  Definition FIELD_maybe_valid := _StructField "valid" 0%N.
  Definition FIELD_maybe_data := _StructField "data" 1%N.

  Definition STRUCT_maybe_fields :=
    [(FIELD_maybe_valid, 1)
    ;(FIELD_maybe_data, data_sz)
    ].

  Definition STRUCT_maybe :=
    {| dstruct_name := id;
       dstruct_fields := STRUCT_maybe_fields
    |}.

  Definition invalid : action :=
    {{ struct id {FIELD_maybe_valid := Ob~0 }
    }}.

  Definition valid (v: action): action :=
    {{ struct id {FIELD_maybe_valid := Ob~1;
                  FIELD_maybe_data := `v`
                 }
    }}.

End Maybe.

Section RegWrite.
  Context (id: debug_id_ty).
  Context (reg_sz: nat).
  Context (data_sz: nat).

  Definition FIELD_regwrite_reg := (_StructField "reg" 0%N).
  Definition FIELD_regwrite_data := (_StructField "data" 1%N).

  Definition STRUCT_regwrite_fields :=
    [(FIELD_regwrite_reg, reg_sz)
    ;(FIELD_regwrite_data, data_sz)
    ].

  Definition STRUCT_regwrite :=
    {| dstruct_name := id;
       dstruct_fields := STRUCT_regwrite_fields
    |}.

  Definition mk_reg_write (reg: action) (data: action) : action :=
    {{ struct id {FIELD_regwrite_reg := (`reg`);
                  FIELD_regwrite_data := (`data`)
                 }
    }}.

End RegWrite.

(*! Generated from OCaml script *)
Module Type Fifo_sig.
  Parameter data_sz : nat.
  Parameter reg_base : N.
  Parameter int_fn_base : N.
End Fifo_sig.

Module Fifo1 (F: Fifo_sig).
  Definition REG_data0 : debug_id_ty := _Reg "Fifo1__data0" (F.reg_base + 0)%N.
  Definition REG_valid0 : debug_id_ty := _Reg "Fifo1__valid0" (F.reg_base + 1)%N.
  Definition reg_list : list (reg_t * nat) :=  [
      (REG_data0, F.data_sz);
      (REG_valid0, 1)
    ].

  Lemma reg_list_sorted : sorted (map fst (id_transform_reg_types snd reg_list)) = true. Proof. solve_is_sorted. Qed.
  Definition reg_type_env := SortedRegEnv.from_list (id_transform_reg_types snd reg_list) reg_list_sorted.
  (* Definition reg_types : reg_types_t := SortedRegEnv.opt_get reg_type_env. *)

  Definition ext_fn_tys : @ext_fn_types_t debug_id_ty := [].
  Definition struct_defs : @struct_env_t debug_id_ty := [].

  Definition FN_can_enq_id : N := (F.int_fn_base + 0)%N.
  Definition FN_enq_id : N := (F.int_fn_base + 1)%N.
  Definition FN_can_deq_id : N := (F.int_fn_base + 2)%N.
  Definition FN_deq_id : N := (F.int_fn_base + 3)%N.
  Definition FN_reset_id : N := (F.int_fn_base + 4)%N.
  Definition FN_peek_id : N := (F.int_fn_base + 5)%N.

  Definition mk_int_fn_spec := mk_int_fn_spec reg_list ext_fn_tys struct_defs.


  Definition FN_can_enq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/can_enq" FN_can_enq_id) (0) (1)
     {{ !read1(REG_valid0) }} .
  Definition FN_enq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/enq" FN_enq_id) (F.data_sz) (0)
    {{
         guard(intcall (FN_can_enq.(fid)) (Ob));
         write1(REG_data0, var "_ARG_");
         write1(REG_valid0, Ob~1)
    }}.
  Definition FN_can_deq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/can_deq" FN_can_deq_id) (0) (1)
    {{ read0(REG_valid0) }}.
  Definition FN_deq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/deq" FN_deq_id) (0) (F.data_sz)
    {{
          guard(intcall (FN_can_deq.(fid)) (Ob));
          write0(REG_valid0, Ob~0);
          read0(REG_data0)
     }}.
  Definition FN_reset : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/reset" FN_reset_id) (0) (0)
    {{
          write0(REG_valid0, Ob~0);
          write0(REG_data0, ` (Const (Bits.zeroes F.data_sz))`)
     }}.
  Definition FN_peek : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1/peek" FN_peek_id) (0) (F.data_sz)
    {{
          guard(intcall (FN_can_deq.(fid)) (Ob));
          read0(REG_data0)
     }}.
  Definition int_fns : list int_fn_spec_t :=  [FN_can_enq;FN_enq;FN_can_deq;FN_deq;FN_reset;FN_peek].
End Fifo1.

Module Fifo1Bypass (F: Fifo_sig).


  Definition REG_data0 : debug_id_ty := _Reg "Fifo1__data0" (F.reg_base + 0)%N.
  Definition REG_valid0 : debug_id_ty := _Reg "Fifo1__valid0" (F.reg_base + 1)%N.
  Definition reg_list : list (reg_t * nat) :=  [
      (REG_data0, F.data_sz);
      (REG_valid0, 1)
    ].

  Lemma reg_list_sorted : sorted (map fst (id_transform_reg_types snd reg_list)) = true. Proof. solve_is_sorted. Qed.
  Definition reg_type_env := SortedRegEnv.from_list (id_transform_reg_types snd reg_list) reg_list_sorted.
  Definition ext_fn_tys : @ext_fn_types_t debug_id_ty := [].
  Definition struct_defs : @struct_env_t debug_id_ty := [].


  Definition FN_can_enq_id : N := (F.int_fn_base + 0)%N.
  Definition FN_enq_id : N := (F.int_fn_base + 1)%N.
  Definition FN_can_deq_id : N := (F.int_fn_base + 2)%N.
  Definition FN_deq_id : N := (F.int_fn_base + 3)%N.
  Definition FN_reset_id : N := (F.int_fn_base + 4)%N.
  Definition FN_peek_id : N := (F.int_fn_base + 5)%N.

  Definition mk_int_fn_spec := mk_int_fn_spec reg_list ext_fn_tys struct_defs.


  Definition FN_can_enq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/can_enq" FN_can_enq_id) (0) (1)
     {{ !read0(REG_valid0) }} .
  Definition FN_enq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/enq" FN_enq_id) (F.data_sz) (0)
    {{
         guard(intcall (FN_can_enq.(fid)) (Ob));
         write0(REG_data0, var "_ARG_");
         write0(REG_valid0, Ob~1)
    }}.
  Definition FN_can_deq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/can_deq" FN_can_deq_id) (0) (1)
    {{ read1(REG_valid0) }}.
  Definition FN_deq : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/deq" FN_deq_id) (0) (F.data_sz)
    {{
          guard(intcall (FN_can_deq.(fid)) (Ob));
          write1(REG_valid0, Ob~0);
          read1(REG_data0)
     }}.
  Definition FN_reset : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/reset" FN_reset_id) (0) (0)
    {{
          write1(REG_valid0, Ob~0);
          write1(REG_data0, ` (Const (Bits.zeroes F.data_sz))`)
     }}.
  Definition FN_peek : int_fn_spec_t := mk_int_fn_spec (_Fn "Fifo1Bypass/peek" FN_peek_id) (0) (F.data_sz)
    {{
          guard(intcall (FN_can_deq.(fid)) (Ob));
          read1(REG_data0)
     }}.
  Definition int_fns : list int_fn_spec_t :=  [FN_can_enq;FN_enq;FN_can_deq;FN_deq;FN_reset;FN_peek].
End Fifo1Bypass.
