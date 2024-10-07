Require Import koika.Common
               koika.Syntax
               koika.Environments
               koika.AnnotatedSyntax.

Inductive machine_id_t :=
| MachineImpl
| MachineSpec.

Inductive sval :=
| SConst (cst: list bool)
| SInitReg (machine_id: machine_id_t) (reg: debug_id_ty)
| SMidReg (machine_id: machine_id_t) (reg: debug_id_ty) (* for implications in assumptions only *)
| SFinalReg (machine_id: machine_id_t) (reg: debug_id_ty)
| SMidExtLog (machine_id: machine_id_t) (extfn: debug_id_ty)
| SFinalExtLog (machine_id: machine_id_t) (extfn: debug_id_ty)
| SCommittedExtLog (machine_id: machine_id_t) (extfn: debug_id_ty)
| SBits1 (op: bits1) (v1 : sval)
| SBits2 (op: bits2) (v1 v2: sval)
| SGetField (machine_id: machine_id_t) (sname field: debug_id_ty) (v: sval)
| SExtCallApp (machine_id: machine_id_t) (extfn: debug_id_ty) (v: sval)
| SBound (arg: string)
.

Inductive spred :=
| PConst (b: bool)
| PAnd (p1 p2: spred)
| POr (p1 p2: spred)
| PNot (pred: spred)
| PImpl (p1 p2: spred)
| PEq (v1 v2: sval)
| PNEq (v1 v2: sval)
| PForallArg1 (arg: string * nat) (body: spred)
| PForallArg2 (arg1 arg2: (string * nat)) (body: spred)
| PExtFnEq (fn: debug_id_ty)
| PFancy: fancy_spred -> spred
with fancy_spred :=
| PBase: spred -> fancy_spred
| PForallRegs: (debug_id_ty -> fancy_spred) -> list debug_id_ty -> fancy_spred
| PForallRegs2: (debug_id_ty * debug_id_ty -> fancy_spred) -> list (debug_id_ty * debug_id_ty) -> fancy_spred
.

Scheme spred_mut := Induction for spred Sort Prop
with fancy_spred_mut := Induction for fancy_spred Sort Prop.




Record machine_t :=
  { file_registers: list (@reg_t debug_id_ty * nat)
  ; file_ext_sigma: list (@ext_fn_t debug_id_ty * (nat * nat))
  ; file_struct_defs: @struct_env_t debug_id_ty
  }.

Inductive file_type :=
| Single (impl: machine_t) (impl_sched: list (string * @aaction debug_id_ty))
| Product (impl spec: machine_t) (impl_sched spec_sched: list (string * @aaction debug_id_ty))
| AbstractSingle (impl: machine_t)
| AbstractProduct (impl spec: machine_t).



Record file_t :=
{ file_machines: file_type;
  file_assumptions: list spred;
  file_assertions: list spred
}.

Record fancy_file_t :=
{ fancy_file_machines: file_type;
  fancy_file_assumptions: list (string * fancy_spred);
  fancy_file_assertions: list (string * fancy_spred)
}.
