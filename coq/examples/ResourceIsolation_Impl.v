(*! Resource isolation implementation *)

Require Import Koika.Frontend.
Require Import Koika.examples.ResourceIsolation_Util.
Require Coq.NArith.NArith.

Module Impl.

  Ltac solve_is_sorted :=
    cbv - [Nat.add Nat.ltb];
    PeanoNat.Nat.nzsimpl;
    repeat rewrite nat_ltb_succ;
    reflexivity.

  Notation sid := struct_name.
  Notation fid := fn_name.

  Section TypeDefs.

    Definition sz := 32.
    Definition ctr_sz := 8.

    Definition ENUM_stage_sz := 2.
    Definition ENUM_stage__None := Ob~0~0.
    Definition ENUM_stage__INIT := Ob~0~1.
    Definition ENUM_stage__F := Ob~1~0.
    Definition ENUM_stage__G := Ob~1~1.

    Definition ENUM_stage := [ENUM_stage__None; ENUM_stage__INIT; ENUM_stage__F; ENUM_stage__G].
    Goal forallb (fun e => Nat.eqb (List.length e) ENUM_stage_sz) ENUM_stage = true. Proof. reflexivity. Qed.

    Definition S_job_req_id := 0.
    Definition FLD_job_req_n := 0.
    Definition FLD_job_req_m := 1.
    Definition FLD_job_req_x := 2.

    Definition S_job_req :=
      {| struct_name := _Struct "job_req" S_job_req_id;
         struct_fields := [(_StructField "n" FLD_job_req_n, ctr_sz)
                          ;(_StructField "m" FLD_job_req_m, ctr_sz)
                          ;(_StructField "x" FLD_job_req_x, sz)
                          ]
      |}.

    Definition S_maybe_job_req_id := 1.
    Definition S_maybe_job_req :=
      STRUCT_maybe (_Struct "maybe_job_req" S_maybe_job_req_id) (struct_sz S_job_req).

    Definition S_maybe_1_id := 2.
    Definition S_maybe_1 :=
      STRUCT_maybe (_Struct "maybe_1" S_maybe_1_id) 1.

    Definition S_maybe_sz_id := 3.
    Definition S_maybe_sz :=
      STRUCT_maybe (_Struct "maybe_sz" S_maybe_sz_id) sz.

    Definition S_job_t_id := 4.
    Definition FLD_job_t_stage := 0.
    Definition FLD_job_t_job_info := 1.

    Definition S_job_t :=
      {| struct_name := _Struct "job_t" S_job_t_id;
         struct_fields := [(_StructField "stage" FLD_job_t_stage, ENUM_stage_sz)
                          ;(_StructField "job_info" FLD_job_t_job_info, struct_sz S_job_req)
                          ]
      |}.

    Definition S_box_req_id := 5.
    Definition FLD_box_req_num_iters := 0.
    Definition FLD_box_req_x := 1.
    Definition S_box_req_t :=
      {| struct_name := _Struct "box_req" S_box_req_id;
         struct_fields := [(_StructField "num_iters" FLD_box_req_num_iters, ctr_sz)
                          ;(_StructField "x" FLD_box_req_x, sz)
                          ]
      |}.


    Definition struct_env : struct_env_t :=
      [S_job_req; S_maybe_job_req; S_maybe_1; S_maybe_sz; S_job_t; S_box_req_t].

    (* Checks *)
    Goal (sorted (map struct_name struct_env) = true). Proof. reflexivity. Qed.
    Goal (forallb (fun s => sorted (map fst s.(struct_fields))) struct_env = true). Proof. reflexivity. Qed.

  End TypeDefs.

  Section ExtFnDefs.
    Definition EXTFN_F0 := _ExtFn "F0" 0.
    Definition EXTFN_F1 := _ExtFn "F1" 1.
    Definition EXTFN_G0 := _ExtFn "G0" 2.
    Definition EXTFN_G1 := _ExtFn "G1" 3.
    Definition EXTFN_GetJob := _ExtFn "GetJob" 4.
    Definition EXTFN_ReadReadyForJob := _ExtFn "ReadReadyForJob" 5.
    Definition EXTFN_ReadOutputReg := _ExtFn "ReadOutputReg" 6.

    Definition ext_fn_types_list : list (ext_fn_t * (nat * nat)) :=
      [(EXTFN_F0, (sz,sz))
      ;(EXTFN_F1, (sz,sz))
      ;(EXTFN_G0, (sz,sz))
      ;(EXTFN_G1, (sz,sz))
      ;(EXTFN_GetJob, (1, struct_sz S_maybe_job_req))
      ;(EXTFN_ReadReadyForJob, (struct_sz S_maybe_1, 0))
      ;(EXTFN_ReadOutputReg, (struct_sz S_maybe_sz, 0))
      ].

    Definition ext_fn_types := lookup_ext_fn ext_fn_types_list : ext_fn_types_t.

  End ExtFnDefs.

  Module Type IterBox_sig.
    Parameter name : string.
    Parameter reg_base : nat.
    Parameter ext_fn : ext_fn_t.
    Parameter int_fn_base : nat.
  End IterBox_sig.

  Module IterBox (sig: IterBox_sig).

    Definition REG_valid0 := _Reg (sig.name ++ "_valid0") sig.reg_base.
    Definition REG_acc := _Reg (sig.name ++ "acc") (sig.reg_base + 1).
    Definition REG_ctr := _Reg (sig.name ++ "ctr") (sig.reg_base + 2).

    Definition reg_tys_list : list (reg_t * nat) :=
      [(REG_valid0, 1)
      ;(REG_acc, sz)
      ;(REG_ctr, ctr_sz)
      ].

    Definition reg_tys : reg_types_t :=
      lookup_reg_type reg_tys_list.

    Goal (sorted (map fst reg_tys_list) = true).
    Proof. solve_is_sorted. Qed.
    Definition ext_fn_tys_list :=
      [(sig.ext_fn, (sz,sz))].

    Definition ext_fn_tys : ext_fn_types_t :=
      lookup_ext_fn ext_fn_tys_list.

    Definition FN_step_id := sig.int_fn_base.
    Definition FN_can_send_req_id := sig.int_fn_base + 1.
    Definition FN_send_req_id := sig.int_fn_base + 2.
    Definition FN_can_receive_resp_id := sig.int_fn_base + 3.
    Definition FN_receive_resp_id := sig.int_fn_base + 4.

    Definition struct_env : struct_env_t :=
      [S_box_req_t; S_maybe_sz].

    Definition FN_step : int_fn_spec_t :=
      {| fn_name := _Fn "IterBox/step" FN_step_id;
         fn_reg_tys := reg_tys;
         fn_ext_fn_tys := ext_fn_tys;
         fn_struct_defs := struct_env;
         fn_arg_ty := 0;
         fn_arg_name := "_ARG_";
         fn_ret_ty := 0;
         fn_body :=
           {{ let "n" := read0(REG_ctr) in
              if (read0(REG_valid0) && (var "n" != `Const (Bits.zeroes ctr_sz)`)) then
                write0(REG_acc, extcall sig.ext_fn (read0(REG_acc)));
                write0(REG_ctr, var "n" - `Const (Bits.of_nat ctr_sz 1)`)
               else pass
          }}
      |}.

    Definition FN_can_send_req: int_fn_spec_t :=
      {| fn_name := _Fn "IterBox/can_send_req" FN_can_send_req_id;
         fn_reg_tys := reg_tys;
         fn_ext_fn_tys := ext_fn_tys;
         fn_struct_defs := struct_env;
         fn_arg_ty := 0;
         fn_arg_name := "_ARG_";
         fn_ret_ty := 1;
         fn_body :=
           {{ !read1(REG_valid0)
           }}
      |}.

    Definition FN_send_req: int_fn_spec_t :=
      {| fn_name := _Fn "IterBox/send_req" FN_send_req_id;
         fn_reg_tys := reg_tys;
         fn_ext_fn_tys := ext_fn_tys;
         fn_struct_defs := struct_env;
         fn_arg_ty := struct_sz S_box_req_t;
         fn_arg_name := "_ARG_";
         fn_ret_ty := 0;
         fn_body :=
           {{ guard(intcall (FN_can_send_req.(fid)) (Ob));
              write1(REG_acc, get_field(S_box_req_t.(sid), var "_ARG_", FLD_box_req_x));
              write1(REG_ctr, get_field(S_box_req_t.(sid), var "_ARG_", FLD_box_req_num_iters));
              write1(REG_valid0, Ob~1)
           }}
      |}.

    Definition FN_can_receive_resp: int_fn_spec_t :=
      {| fn_name := _Fn "IterBox/can_receive_resp" FN_can_receive_resp_id;
         fn_reg_tys := reg_tys;
         fn_ext_fn_tys := ext_fn_tys;
         fn_struct_defs := struct_env;
         fn_arg_ty := 0;
         fn_arg_name := "_ARG_";
         fn_ret_ty := 1;
         fn_body :=
           {{ (read1(REG_valid0) && (read1(REG_ctr) == `Const (Bits.zeroes ctr_sz)`))
           }}
      |}.

    Definition FN_receive_resp: int_fn_spec_t :=
      {| fn_name := _Fn "IterBox/receive_resp" FN_receive_resp_id;
         fn_reg_tys := reg_tys;
         fn_ext_fn_tys := ext_fn_tys;
         fn_struct_defs := struct_env;
         fn_arg_ty := 0;
         fn_arg_name := "_ARG_";
         fn_ret_ty := struct_sz (S_maybe_sz);
         fn_body :=
           {{ guard(intcall (FN_can_receive_resp.(fid)) (Ob));
              write1(REG_valid0, Ob~0);
              `valid S_maybe_sz.(sid) {{read1(REG_acc)}}`
           }}
      |}.

    Definition int_fns : int_fn_env_t :=
      [FN_step; FN_can_send_req; FN_send_req; FN_can_receive_resp; FN_receive_resp].

    Goal (sorted (map fn_name int_fns) = true).
    Proof. solve_is_sorted. Qed.
  End IterBox.

  Definition F0_reg_base := 0.
  Definition F0_fn_base := 0.

  Module F0_sig <: IterBox_sig.
    Definition name := "IterBox/F0".
    Definition reg_base := F0_reg_base.
    Definition ext_fn := EXTFN_F0.
    Definition ext_fn_ty := (sz,sz).
    Definition int_fn_base := F0_fn_base.
  End F0_sig.
  Module F0Box := IterBox F0_sig.

  Definition F1_reg_base := F0_reg_base + List.length (F0Box.reg_tys_list).
  Definition F1_fn_base := F0_fn_base + List.length (F0Box.int_fns).

  Module F1_sig <: IterBox_sig.
    Definition name := "IterBox/F1".
    Definition reg_base := F1_reg_base.
    Definition ext_fn := EXTFN_F1.
    Definition ext_fn_ty := (sz,sz).
    Definition int_fn_base := F1_fn_base.
  End F1_sig.
  Module F1Box := IterBox F1_sig.

  Definition G0_reg_base := F1_reg_base + List.length (F1Box.reg_tys_list).
  Definition G0_fn_base := F1_fn_base + List.length (F1Box.int_fns).

  Module G0_sig <: IterBox_sig.
    Definition name := "IterBox/G0".
    Definition reg_base := G0_reg_base.
    Definition ext_fn := EXTFN_G0.
    Definition ext_fn_ty := (sz,sz).
    Definition int_fn_base := G0_fn_base.
  End G0_sig.
  Module G0Box := IterBox G0_sig.

  Definition G1_reg_base := G0_reg_base + List.length (G0Box.reg_tys_list).
  Definition G1_fn_base := G0_fn_base + List.length (G0Box.int_fns).

  Module G1_sig <: IterBox_sig.
    Definition name := "IterBox/G1".
    Definition reg_base := G1_reg_base.
    Definition ext_fn := EXTFN_G1.
    Definition ext_fn_ty := (sz,sz).
    Definition int_fn_base := G1_fn_base.
  End G1_sig.
  Module G1Box := IterBox G1_sig.

  Definition _reg_base := G1_reg_base + List.length (G1Box.reg_tys_list).
  Definition _fn_base := G1_fn_base + List.length (G1Box.int_fns).

  Section RegDefs.
    Definition REG_job0 := _Reg "job0" _reg_base.
    Definition REG_job1 := _Reg "job1" _reg_base+1.
    Definition REG_clk := _Reg "clk" _reg_base+2.
    Definition REG_ext_ready_for_job := _Reg "ext_ready_for_job" _reg_base+3.
    Definition REG_ext_output_reg := _Reg "ext_output_reg" _reg_base+4.
    Definition REG_ext_output_reg0 :=_Reg "ext_output_reg0" _reg_base+5.
    Definition REG_ext_output_reg1 :=_Reg "ext_output_reg1" _reg_base+6.
    Definition REG_job0' := _Reg "job0'" _reg_base+7.
    Definition REG_job1' := _Reg "job1'" _reg_base+8.

    Definition reg_types_list : list (reg_t * nat) :=
      F0Box.reg_tys_list ++ F1Box.reg_tys_list ++ G0Box.reg_tys_list ++ G1Box.reg_tys_list ++
      [(REG_job0, struct_sz S_job_t)
      ;(REG_job1, struct_sz S_job_t)
      ;(REG_clk, 1)
      ;(REG_ext_ready_for_job, struct_sz S_maybe_1)
      ;(REG_ext_output_reg, struct_sz S_maybe_sz)
      ;(REG_ext_output_reg0, struct_sz S_maybe_sz)
      ;(REG_ext_output_reg1, struct_sz S_maybe_sz)
      ;(REG_job0', struct_sz S_job_t)
      ;(REG_job1', struct_sz S_job_t)
      ].

    Lemma reg_types_sorted : (sorted (map fst reg_types_list) = true). Proof. reflexivity. Qed.

    Definition reg_tys := SortedRegEnv.from_list reg_types_list reg_types_sorted.

    Definition reg_types : reg_types_t :=
      SortedRegEnv.opt_get reg_tys.

  End RegDefs.

  Section IntFnDefs.
    Definition int_fn_env : int_fn_env_t :=
      (F0Box.int_fns ++ F1Box.int_fns ++ G0Box.int_fns ++ G1Box.int_fns)%list.
  End IntFnDefs.

  Section Rules.
    Definition interact_with_world : action :=
      {{ extcall EXTFN_ReadReadyForJob (read0(REG_ext_ready_for_job));
         extcall EXTFN_ReadOutputReg (read0(REG_ext_output_reg))
      }}.

    Definition do_input : action :=
      {{ let "rdy" := read0(REG_ext_ready_for_job) in
         if (get_field(S_maybe_1.(sid), var "rdy", FIELD_maybe_valid)) then
           let "job_id" := get_field (S_maybe_1.(sid), var "rdy", FIELD_maybe_data) in
           let "maybe_input" := extcall EXTFN_GetJob (var "job_id") in
           if (get_field (S_maybe_job_req.(sid), var "maybe_input", FIELD_maybe_valid)) then
             if var "job_id" == Ob~0 then
               write0(REG_job0, struct (S_job_t.(sid))
                                       { FLD_job_t_stage := (const ENUM_stage__INIT);
                                         FLD_job_t_job_info :=
                                           get_field(S_maybe_job_req.(sid),
                                                      var "maybe_input", FIELD_maybe_data)})
             else (* job_id == Ob~1 *)
               write0(REG_job1, struct (S_job_t.(sid))
                                       { FLD_job_t_stage := (const ENUM_stage__INIT);
                                         FLD_job_t_job_info :=
                                           get_field(S_maybe_job_req.(sid),
                                                      var "maybe_input", FIELD_maybe_data)})
           else pass
         else
           pass
      }}.

    Definition step_boxes : action :=
      {{ intcall (F0Box.FN_step.(fid)) (Ob);
         intcall (F1Box.FN_step.(fid)) (Ob);
         intcall (G0Box.FN_step.(fid)) (Ob);
         intcall (G1Box.FN_step.(fid)) (Ob)
      }}.

    Definition do_step0 : action :=
      {{ let "job0_st" := read1(REG_job0) in
         let "job_info" := get_field(S_job_t.(sid), var "job0_st", FLD_job_t_job_info) in
         let "stage" := get_field(S_job_t.(sid), var "job0_st", FLD_job_t_stage) in
         let "output_info" := `invalid S_maybe_sz.(sid)` in
         let "job0_st'" := var "job0_st" in
         (if (var "stage" == const ENUM_stage__None) then
            pass
          else if (var "stage" == const ENUM_stage__INIT) then
            if intcall (F0Box.FN_can_send_req.(fid)) (Ob) then
              intcall (F0Box.FN_send_req.(fid))
                        (struct (S_box_req_t.(sid))
                               { FLD_box_req_num_iters := get_field(S_job_req.(sid), var "job_info",
                                                                    FLD_job_req_n);
                                 FLD_box_req_x := get_field(S_job_req.(sid), var "job_info",
                                                            FLD_job_req_x)});
              set "job0_st'" := (struct (S_job_t.(sid))
                                      { FLD_job_t_stage := (const ENUM_stage__F);
                                        FLD_job_t_job_info := var "job_info"
                                       })
            else
              pass
          else if (var "stage" == const ENUM_stage__F) then
            if intcall (G0Box.FN_can_send_req.(fid)) (Ob) &&
               intcall (F0Box.FN_can_receive_resp.(fid)) (Ob) then
              let "resp" := intcall (F0Box.FN_receive_resp.(fid)) (Ob) in
              (* if (get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_valid)) then *)
                intcall (G0Box.FN_send_req.(fid))
                        (struct (S_box_req_t.(sid))
                                { FLD_box_req_num_iters := get_field(S_job_req.(sid), var "job_info",
                                                                     FLD_job_req_m);
                                  FLD_box_req_x := get_field(S_maybe_sz.(sid), var "resp",
                                                             FIELD_maybe_data)});
                set "job0_st'" := (struct (S_job_t.(sid))
                                      { FLD_job_t_stage := (const ENUM_stage__G);
                                        FLD_job_t_job_info := var "job_info"
                                       })
              (* else *)
              (*   pass *)
            else
              pass
          else (* stage == STAGE_G *)
            if read0(REG_clk) == Ob~0 &&
               intcall (G0Box.FN_can_receive_resp.(fid)) (Ob) then
              let "resp" := intcall (G0Box.FN_receive_resp.(fid)) (Ob) in
              (* if (get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_valid)) then *)
                set "job0_st'" := (struct (S_job_t.(sid)) { FLD_job_t_stage := const ENUM_stage__None });
                set "output_info" :=
                  `valid S_maybe_sz.(sid) {{ get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_data)}}`
              (* else *)
              (*   pass *)
            else
              pass
         );
         write0(REG_ext_output_reg0, var "output_info");
         write1(REG_job0, var "job0_st'");
         write0(REG_job0', var "job0_st'")
         (* if (read0(REG_clk) == Ob~0) then *)
         (*   write1(REG_ext_output_reg, "output_info") *)
         (* else *)
         (*   pass *)
      }}.

    Definition do_step1 : action :=
      {{ let "job1_st" := read1(REG_job1) in
         let "job_info" := get_field(S_job_t.(sid), var "job1_st", FLD_job_t_job_info) in
         let "stage" := get_field(S_job_t.(sid), var "job1_st", FLD_job_t_stage) in
         let "output_info" := `invalid S_maybe_sz.(sid)` in
         let "job1_st'" := var "job1_st" in
         (if (var "stage" == const ENUM_stage__None) then
            pass
          else if (var "stage" == const ENUM_stage__INIT) then
            if intcall (F1Box.FN_can_send_req.(fid)) (Ob) then
              intcall (F1Box.FN_send_req.(fid))
                        (struct (S_box_req_t.(sid))
                               { FLD_box_req_num_iters := get_field(S_job_req.(sid), var "job_info",
                                                                    FLD_job_req_n);
                                 FLD_box_req_x := get_field(S_job_req.(sid), var "job_info",
                                                            FLD_job_req_x)});
              set "job1_st'" := (struct (S_job_t.(sid))
                                      { FLD_job_t_stage := (const ENUM_stage__F);
                                        FLD_job_t_job_info := var "job_info"
                                       })
            else
              pass
          else if (var "stage" == const ENUM_stage__F) then
            if intcall (G1Box.FN_can_send_req.(fid)) (Ob) &&
               intcall (F1Box.FN_can_receive_resp.(fid)) (Ob) then
              let "resp" := intcall (F1Box.FN_receive_resp.(fid)) (Ob) in
              (* if (get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_valid)) then *)
                intcall (G1Box.FN_send_req.(fid))
                        (struct (S_box_req_t.(sid))
                                { FLD_box_req_num_iters := get_field(S_job_req.(sid), var "job_info",
                                                                     FLD_job_req_m);
                                  FLD_box_req_x := get_field(S_maybe_sz.(sid), var "resp",
                                                             FIELD_maybe_data)});
                set "job1_st'" := (struct (S_job_t.(sid))
                                      { FLD_job_t_stage := (const ENUM_stage__G);
                                        FLD_job_t_job_info := var "job_info"
                                       })
              (* else pass *)
            else
              pass
          else (* stage == STAGE_G *)
            if read0(REG_clk) == Ob~1 &&
               intcall (G1Box.FN_can_receive_resp.(fid)) (Ob) then
              let "resp" := intcall (G1Box.FN_receive_resp.(fid)) (Ob) in
              (* if (get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_valid)) then *)
                set "job1_st'" := (struct (S_job_t.(sid)) { FLD_job_t_stage := const ENUM_stage__None });
                set "output_info" :=
                  `valid S_maybe_sz.(sid) {{ get_field(S_maybe_sz.(sid), var "resp", FIELD_maybe_data)}}`
              (* else pass *)
            else
              pass
         );
         write0(REG_ext_output_reg1, var "output_info");
         write1(REG_job1, var "job1_st'");
         write0(REG_job1', var "job1_st'")
         (* if (read0(REG_clk) == Ob~0) then *)
         (*   write1(REG_ext_output_reg, "output_info") *)
         (* else *)
         (*   pass *)
      }}.

    Definition update_ready : action :=
      {{ let "job0_st" := read1(REG_job0') in
         let "job1_st" := read1(REG_job1') in
         let "rdy" := `invalid S_maybe_1.(struct_name)` in
         if (get_field(S_job_t.(struct_name), var "job0_st", FLD_job_t_stage)
               == const ENUM_stage__None) then
           set "rdy" := `valid S_maybe_1.(struct_name) {{ Ob~0}}`
         else if (get_field(S_job_t.(struct_name), var "job1_st", FLD_job_t_stage)
               == const ENUM_stage__None) then
           set "rdy" := `valid S_maybe_1.(struct_name) {{ Ob~1}}`
         else
           pass;
         write0(REG_ext_ready_for_job, var "rdy");
         (if (read0(REG_clk) == Ob~0) then
           write1(REG_ext_output_reg, read1(REG_ext_output_reg0))
         else
           write1(REG_ext_output_reg, read1(REG_ext_output_reg1)));
         write0(REG_clk, read0(REG_clk) + Ob~1)
      }}.

    (* Definition do_clk : action := *)
    (*   {{ write0(REG_clk, read0(REG_clk) + Ob~1) }}. *)

  End Rules.

  Section Schedule.

    Inductive rule_name_t :=
    | InteractWithWorld
    | DoInput
    | StepBoxes
    | DoStep0
    | DoStep1
    | UpdateReady.
    (* | DoClk. *)

    Definition schedule : @scheduler rule_name_t :=
      InteractWithWorld |> DoInput |> StepBoxes |> DoStep0 |> DoStep1 |> UpdateReady |> (* DoClk |>  *)Done.

    Definition rules : rule_name_t -> action :=
      fun rl => match rl with
             | InteractWithWorld => interact_with_world
             | DoInput => do_input
             | StepBoxes => step_boxes
             | DoStep0 => do_step0
             | DoStep1 => do_step1
             | UpdateReady => update_ready
             (* | DoClk => do_clk *)
             end.

  End Schedule.

  Section Typecheck.
    Notation typecheck := (typecheck_rule reg_types ext_fn_types int_fn_env struct_env).
    Notation typecheck_schedule := (typecheck_schedule reg_types ext_fn_types int_fn_env struct_env).
    Notation typecheck_int_fns := (fun int_fn_env => typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env).

    Lemma typecheck_schedule_Success : typecheck_schedule schedule rules = Success tt.
    Proof. reflexivity. Qed.

    Lemma typecheck_int_fns_Success : typecheck_int_fns int_fn_env = Success tt.
    Proof. reflexivity. Qed.

    Lemma oraat_schedule_does_not_conflict:
      schedule_does_not_conflict Impl.int_fn_env Impl.rules schedule = Success true .
    Proof. reflexivity. Qed.

  End Typecheck.

  Section StateMachine.
    Import Common.

    Definition initial_state : state_t :=
      SortedRegEnv.map (fun r sz => if Nat.eqb r REG_ext_ready_for_job
                                    then (option_to_maybe' 1 (Some Ob~0))
                                    else Bits.zeroes sz) reg_tys.

    Definition get_observations (st: state_t) :=
      {| obs_ready_for_job := unsafe_get_reg st REG_ext_ready_for_job;
         obs_output_reg := unsafe_get_reg st REG_ext_output_reg
      |}.

    Notation "st .[ idx ]" := (unsafe_get_reg st idx) (at level 1, format "st .[ idx ]").

    Definition get_job_accepted (st: state_t) (input: input_t) : option (Tag * list bool) :=
      match input with
      | Some req =>
        match st.[REG_ext_ready_for_job] with
        | [valid;job_id] =>
          if valid then
            let tag := (if job_id then Tag1 else Tag0) in
            Some (tag, req)
          else None
        | _ => None
        end
      | None => None
      end.

    Definition koika_step' (sigma: input_t -> ext_sigma_t)
                           (st: state_t) (input: input_t)
                           : result state_t unit :=
      interp_cycle (sigma input) int_fn_env struct_env st rules schedule.

    Definition koika_step (sigma: input_t -> ext_sigma_t)
                          (st: state_t) (input: input_t)
                          : result (state_t * output_t) unit :=
      let/res st' := koika_step' sigma st input in
      let output := {| output_observations := get_observations st;
                       output_job_accepted := get_job_accepted st input
                    |} in
      Success (st', output).

    Definition mk_GetJob (input: input_t) : list bool :=
      match input with
      | Some req => option_to_maybe' (struct_sz S_job_req) (Some (firstn_fill false (struct_sz S_job_req) req))
      | None => [false] ++ (Bits.zeroes (struct_sz S_job_req))
      end.

  (* Technically for functional correctness, also want F0=F1 and G0=G1 *)
    Record wf_sigma (sigma: input_t -> ext_sigma_t) : Prop :=
      { wf: forall input, WF_ext_sigma ext_fn_types (sigma input);
        wf_GetJob: forall input job_id, sigma input EXTFN_GetJob job_id = Success (mk_GetJob input);
        wf_Constants: forall input1 input2 fn, if Nat.eqb fn EXTFN_GetJob
                                          then True
                                          else sigma input1 fn = sigma input2 fn
      }.

    Section WithExternalWorld.
      Context (sigma: input_t -> ext_sigma_t).
      Context {external_world_state_t : Type}.
      Context (input_machine: @i_machine_t external_world_state_t output_t input_t).


      Definition step (st: state_t) (input_st: external_world_state_t)
                      : result (state_t * external_world_state_t * output_t) unit :=
        step (koika_step sigma) input_machine st input_st.

      Definition step_n' (n: nat) (st: state_t) (input_st: external_world_state_t)
                 : result (state_t * external_world_state_t * list output_t) unit :=
        step_n' (koika_step sigma) input_machine n st input_st .

      Definition step_n (n: nat) : result (list output_t) unit :=
        step_n initial_state (koika_step sigma)
               input_machine n.

     End WithExternalWorld.

  End StateMachine.

End Impl.

(*
Module Tests.
  Import Impl.
  Import Common.
  Import Coq.NArith.NArith.

  Definition sigma__fns (input: input_t) : list (ext_fn_t * (vect_t -> result vect_t unit)) :=
    [(EXTFN_F0, (fun v => plus v (one sz)))
    ;(EXTFN_F1, (fun v => plus v (one sz)))
    ;(EXTFN_G0, (fun v => plus v (firstn_fill false sz (of_N 2%N))))
    ;(EXTFN_G1, (fun v => plus v (firstn_fill false sz (of_N 2%N))))
    ;(EXTFN_GetJob, (fun _ => option_to_maybe (S_maybe_job_req.(struct_fields)) input))
    ;(EXTFN_ReadReadyForJob, (fun _ => Success Ob))
    ;(EXTFN_ReadOutputReg, (fun _ => Success Ob))
    ].

  Definition sigma (input: input_t) : ext_sigma_t :=
    fun ext_fn =>
      match find (fun '(fn, _) => Nat.eqb ext_fn fn) (sigma__fns input) with
      | Some (_, res) => fun v => res v
      | None => fun _ => Failure (__debug__ ("fn not found", ext_fn) tt)
      end.

  Record external_world_state_t : Type :=
    { clk : bool;
      jobs: list vect_t;
      outstanding0: option (vect_t);
      outstanding1: option (vect_t);
      outputs: list (option vect_t * vect_t)
    }.

  (* At each cycle: observe ext_ready_for_job and ext_output_reg *)

  Definition initial_job_list := [(0,5,1);(5,0,1);(2,3,1);(1,1,5)].
  Definition initial_jobs : list vect_t :=
    map (fun '(n,m,x) =>
           let bits_n := (of_nat ctr_sz n) in
           let bits_m := (of_nat ctr_sz m) in
           let bits_x := (of_nat sz x) in
           (bits_n ++ bits_m ++ bits_x)%list
        ) initial_job_list.

  (* Definition foo := *)
  (*   map (fun value => *)
  (*          let n := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_n value) in *)
  (*          let m := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_m value) in *)
  (*          let x := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_x value) in *)
  (*          (n,m,x) *)
  (*       ) initial_jobs. *)

  (* Eval compute in foo. *)

  Definition input_machine :@i_machine_t external_world_state_t output_t input_t :=
    {| i_initial_state := {| clk := false;
                             jobs := initial_jobs;
                             outstanding0 := None;
                             outstanding1 := None;
                             outputs := []
                          |};
       i_get_output := fun st => List.hd_error st.(jobs);
       i_step := fun st obs =>
                   let st:= match obs.(output_observations).(obs_output_reg) with
                            | true::job => if st.(clk) then (* do job0 *)
                                            {| clk := st.(clk);
                                               jobs := st.(jobs);
                                               outstanding0 := None;
                                               outstanding1 := st.(outstanding1);
                                               outputs := (st.(outstanding0), job)::st.(outputs)
                                            |}
                                         else
                                            {| clk := st.(clk);
                                               jobs := st.(jobs);
                                               outstanding0 := st.(outstanding0);
                                               outstanding1 := None;
                                               outputs := (st.(outstanding1), job)::st.(outputs)
                                            |}
                            | _ => st
                            end in
                   match obs.(output_job_accepted) with
                   | Some (tag, req) =>  {| clk := negb st.(clk);
                                            jobs := List.tl st.(jobs);
                                            outstanding0 := match tag with
                                                            | Tag0 => Some req
                                                            | Tag1 => st.(outstanding0)
                                                            end;
                                            outstanding1 := match tag with
                                                            | Tag0 => st.(outstanding1)
                                                            | Tag1 => Some req
                                                            end;
                                            outputs := st.(outputs)
                                         |}
                   | None => {| clk := negb st.(clk);
                               jobs := st.(jobs);
                               outstanding0 := st.(outstanding0);
                               outstanding1 := st.(outstanding1);
                               outputs := st.(outputs)
                            |}
                   end
    |}.


  Lemma wf_initial_state: WF_state reg_types Impl.initial_state.
  Proof.
    unfold Impl.initial_state, WF_state; intros. destruct_match; auto.
    unfold get_reg, Impl.reg_types in *. rewrite SortedRegEnv.opt_get_map.
    destruct_match; simplify; auto.
    destruct_match; simplify; auto.
    + compute in Heqo0. simplify. auto.
    + rewrite zeroes_length. reflexivity.
  Qed.

  Lemma wf_int_fn_env : WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env.
  Proof.
    unfold WF_int_fn_env. reflexivity.
  Qed.

  Definition compute_n (n: nat) :=
    match ResourceIsolation_Util.step_n' (koika_step sigma) input_machine n initial_state
        (i_initial_state input_machine) with
    | Success (st, imachine, obs) =>
      map (fun '(input, output) =>
             (match input with
              | Some value =>
                let n := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_n value) in
                let m := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_m value) in
                let x := to_nat (unsafe_get_field (S_job_req.(struct_fields)) FLD_job_req_x value) in
                Some (n,m,x)
              | None => None
              end, to_nat output)) imachine.(outputs)
    | _ => []
    end.

  Eval vm_compute in (compute_n 14).
  (* x + n + 2m *)
End Tests.
*)
