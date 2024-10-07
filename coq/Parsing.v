Require Import Koika.Common.
Require Import Koika.Syntax.
Require Import Koika.SyntaxMacros.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import List.ListNotations.
Open Scope string_scope.


Declare Custom Entry koika.
Declare Custom Entry koika_var.
Declare Custom Entry koika_args.
Declare Custom Entry koika_consts.
Declare Custom Entry koika_reg.

(* Koika_consts *)

Notation "'0'" := ([false]) (in custom koika_consts at level 0).

Notation "'1'" := ([true]) (in custom koika_consts at level 0).
Notation "bs '~' '0'" := (cons false bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (cons true bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '1'").
Notation "'Ob' '~' number" :=
  (Const number)
    (in custom koika at level 7, number custom koika_consts at level 99, format "'Ob' '~' number").

Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").
Notation "'fail' '(' t ')'" :=
  (Fail t) (in custom koika, t constr at level 0, format "'fail' '(' t ')'").
Notation "'pass'" := (Const nil) (in custom koika at level 0).

Notation "'Ob'" := (Const nil) (in custom koika at level 0).


Notation "'let' a ':=' b 'in' c" := (Bind a b c) (in custom koika at level 91, a custom koika_var at level 1, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a" := (a%string) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'").
Notation "a" := (a%string) (in custom koika_reg at level 0, a constr at level 0, format "'[' a ']'").
Notation "a ';' b" := (Seq a b) (in custom koika at level 90, format "'[v' a ';' '/' b ']'" ).
Notation "'(' a ')'" := (a) (in custom koika at level 1, a custom koika, format "'[v' '(' a ')' ']'").
Notation "'set' a ':=' b" := (Assign a b) (in custom koika at level 89, a custom koika_var at level 1, format "'set'  a  ':='  b").
Notation "'read0' '(' reg ')' " := (Read P0 reg) (in custom koika, reg custom koika_reg, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " := (Read P1 reg) (in custom koika, reg custom koika_reg, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (Write P0 reg value)
    (in custom koika, reg custom koika_reg at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (Write P1 reg value)
    (in custom koika, reg custom koika_reg at level 13, format "'write1' '(' reg ',' value ')'").


Notation "'var' a" := (Var (a%string)) (in custom koika at level 1, a constr at level 0).


Notation "'if' a 'then' t 'else' f" := (If a t f) (in custom koika at level 86, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'guard' '(' a ')' " := (If (Unop (Bits1 Not) a) (Fail 0) ((Const []))) (in custom koika at level 86, right associativity, format "'guard' '(' a ')'").
(* Notation "'when' a 'do' t " := (If a t (Const [])) (in custom koika at level 91, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'"). *)
Notation "a '&&' b" :=  (Binop (Bits2 And) a b) (in custom koika at level 80,  right associativity, format "a  '&&'  b").
Notation "'!' a" := (Unop (Bits1 Not) a) (in custom koika at level 75, format "'!' a").
Notation "a '||' b" :=  (Binop (Bits2 Or) a b) (in custom koika at level 85, format "a  '||'  b").
Notation "a  '^'  b" :=  (Binop (Bits2 Xor) a b) (in custom koika at level 85).
Notation "a  '+'  b" :=  (Binop (Bits2 Plus) a b) (in custom koika at level 85).
Notation "a  '-'  b" :=  (Binop (Bits2 Minus) a b) (in custom koika at level 85).
Notation "a  '!='  b" := (Binop (Bits2 (EqBits true)) a b) (in custom koika at level 79).
Notation "a  '=='  b" :=  (Binop (Bits2 (EqBits false)) a b) (in custom koika at level 79).
(* Notation "a  '>>'  b" :=  (Binop (Bits2 ULsr) a b) (in custom koika at level 79). *)
(* Notation "a  '>>>'  b" :=  (Binop (Bits2 UAsr) a b) (in custom koika at level 79). *)
(* Notation "a  '<<'  b" :=  (Binop (Bits2 ULsl) a b) (in custom koika at level 79). *)
Notation "a  '<'  b" := (Binop (Bits2 (Compare false cLt)) a b) (in custom koika at level 79).
Notation "a  '<s'  b" := (Binop (Bits2 (Compare true cLt)) a b) (in custom koika at level 79).
Notation "a  '<='  b" := (Binop (Bits2 (Compare false cLe)) a b) (in custom koika at level 79).
Notation "a  '<s='  b" := (Binop (Bits2 (Compare true cLe)) a b) (in custom koika at level 79).
Notation "a  '>'  b" := (Binop (Bits2 (Compare false cGt)) a b) (in custom koika at level 79).
Notation "a  '>s'  b" := (Binop (Bits2 (Compare true cGt)) a b) (in custom koika at level 79).
Notation "a  '>='  b" := (Binop (Bits2 (Compare false cGe)) a b) (in custom koika at level 79).
Notation "a  '>s='  b" := (Binop (Bits2 (Compare true cGe)) a b) (in custom koika at level 79).
Notation "a '++' b" :=  (Binop (Bits2 Concat) a b) (in custom koika at level 80,  right associativity, format "a  '++'  b").
Notation "a '[' b ']'" := (Binop (Bits2 Sel) a b) (in custom koika at level 75, format "'[' a [ b ] ']'").
(* Notation "a '[' b ':' c ']'" := (UBinop (Bits2 (UIndexedSlice c)) a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'"). *)
(* Notation "a '[' b ':+' c ']'" := (UBinop (UBits2 (UIndexedSlice c)) a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'"). *)
(* Notation "'`' a '`'" := ( a) (in custom koika at level 99, a constr at level 99). *)

Notation "'extcall' method '(' arg ')'" :=
  (ExternalCall method arg)
    (in custom koika at level 98, method constr at level 0, arg custom koika).

Notation "'`' a '`'" := (a) (in custom koika at level 99, a constr at level 99).
Notation "'const' a" := (Const a) (in custom koika at level 99, a constr at level 99).


Notation "'get_field' '(' t ',' v ',' f ')'" :=
  (Unop (Struct1 (GetField t f)) v)
    (in custom koika, t constr at level 11, v custom koika at level 13,
        f custom koika_var at level 0,
        format "'get_field' '(' t ','  v ','  f ')'").
Notation "'subst' '(' t ',' v ',' f ',' a ')'" :=
  (Binop (Struct2 (SubstField t f)) v a)
    (in custom koika, t constr at level 11, v custom koika at level 13,
        a custom koika at level 13, f custom koika_var at level 0,
        format "'subst' '(' t ','  v ','  f ',' a ')'").

Declare Custom Entry koika_structs_init.
Notation "f ':=' expr" := (List.cons (f,expr) nil) (in custom koika_structs_init at level 20, f custom koika_var at level 0, expr custom koika at level 88).
Notation "a ';' b" := (List.app a b) (in custom koika_structs_init at level 91, a custom koika_structs_init).
Notation "'struct' structtype '{' fields '}'" :=
  (action_struct_init structtype fields) (in custom koika, structtype constr at level 0, fields custom koika_structs_init at level 92).
Notation "'struct' structtype '{' '}'" :=
  (Zop (StructInit structtype)) (in custom koika, structtype constr at level 0).

(* Koika_args *)
Declare Custom Entry koika_middle_args.
Notation "x" := [x] (in custom koika_middle_args at level 0, x custom koika at level 99).
Notation "x ',' y" := (app x y) (in custom koika_middle_args at level 1, x custom koika_middle_args, y custom koika_middle_args, right associativity).

(* Notation "'()'"  := nil (in custom koika_args). *)
(* Notation "'(' x ')'"  := x (in custom koika_args, x custom koika_middle_args). *)
Notation "'intcall' method '(' arg ')' " :=
  (InternalCall method arg)
    (in custom koika at level 98, method constr at level 0, arg custom koika).


Module Tests.
    Definition Reg0 := _Reg "reg0" 0.
    Definition Reg1 := _Reg "reg1" 1.
    Definition Reg2 := _Reg "reg2" 2.
    Definition Reg3 := _Reg "reg2" 3.
    Definition ExtMethod := _ExtFn "ExtMethod" 0.
    Definition IntFn := _Fn "IntCall" 0.
    Definition Struct_Maybe_1 :=
      {| struct_name := _Struct "Maybe_1" 0;
         struct_fields := [(_StructField "valid" 0, 1);
                           (_StructField "data" 1, 1)
                          ]
      |}.

    Definition test_fail := {{ fail(2)}}. (* Print test_fail. *)
    Definition test_pass := {{ pass }}. (* Print test_pass. *)
    Definition test_const1 := {{ Ob~1 }}. (* Print test_const1. *)
    Definition test_const0 := {{ Ob~0 }}. (* Print test_const0. *)
    Definition test_const := {{ Ob~1~0 }}. (* Print test_const. (* Note: reversed *) *)
    Definition test_let := {{ let "v" := Ob~1~0 in pass }}. (* Print test_let. *)
    Definition test_let2 := {{ let "v" := Ob~1~0 in var "v" }}. (* Print test_let2. *)
    Definition test_seq := {{ Ob~1~0; let "v" := Ob~1 in pass }}. (* Print test_seq. *)
    Definition test_set__fail := {{ set "a" := Ob~1 }}. (* Print test_set__fail. *)
    Definition test_read0 := {{ read0(Reg0) }}. (* Print test_read0. *)
    Definition test_read1 := {{ read1(Reg1) }}. (* Print test_read1. *)
    Definition test_write0 := {{ write0(Reg2, Ob~0~1) }}. (* Print test_write0. *)
    Definition test_write1 := {{ write1(Reg3, Ob~1~0~0) }}. (* Print test_write1. *)
    Definition test_write1__fail := {{ write1(Reg3, Ob~1~0) }}. (* Print test_write1. *)
    Definition test_bits2_and := {{ write1(Reg3, Ob~1~1 && Ob~1~0) }}. (* Print test_bits2_and. *)
    Definition test_extcall := {{ extcall ExtMethod (Ob~1~0) }}. (* Print test_extcall. *)

    Definition test_intcall__nil := {{intcall IntFn (Ob)}}. (* Print test_intcall__nil. *)
    Definition test_intcall__one := {{intcall IntFn (Ob~1) }}. (* Print test_intcall__one. *)
    Definition test_struct : action := {{ let "v" := struct (Struct_Maybe_1.(struct_name)) {} in
                                          let "x" := get_field(Struct_Maybe_1.(struct_name), var "v", 1) in
                                          let "y" := subst(Struct_Maybe_1.(struct_name), var "v", 0, Ob~0) in
                                          let "z" := struct (Struct_Maybe_1.(struct_name))
                                                            { 0 := Ob~1;
                                                              1 := Ob~1 } in
                                          pass
                                       }}.

End Tests.
