Require Import koika.Common.
Require Import koika.Symbolic.
Require Import koika.Syntax.

Declare Custom Entry symb.
Declare Custom Entry symb_mid.
Declare Custom Entry symb_list.
Declare Custom Entry symb_middle_args.
Declare Custom Entry symb_val.
Declare Custom Entry symb_consts.
Declare Custom Entry symb_reg.
(* Notation "0" := (0) (in custom symb_mid at level 0). *)
(* Notation "1" := (1) (in custom symb_mid at level 0). *)

Notation "a" := (a%string) (in custom symb_reg at level 0, a constr at level 0, format "'[' a ']'").

Notation "'True'" := (PBase (PConst true)) (in custom symb at level 0).
Notation "'False'" := (PBase (PConst false)) (in custom symb at level 0).
Notation "'{{{' e '}}}'" := (e) (e custom symb at level 200, format "'{{{' '[v' '/' e '/' ']' '}}}'").

Notation "x" := [x] (in custom symb_middle_args at level 0, x custom symb at level 99).
Notation "x ',' y" := (app x y) (in custom symb_middle_args at level 1, x custom symb_middle_args, y custom symb_middle_args, right associativity).


Notation "'()'"  := nil (in custom symb_list).
Notation "'(' x ')'"  := x (in custom symb_list, x custom symb_middle_args).

Notation " A '/\' B "  := (PBase (PAnd (PFancy A)  (PFancy B ))) (in custom symb at level 80, right associativity).
Notation "A '\/' B "  := (PBase (POr (PFancy A) (PFancy B))) (in custom symb at level 80, right associativity).
Notation "'¬' p"  := (PBase (PNot (PFancy p))) (in custom symb at level 75, p custom symb).
Notation "p1 '->' p2"  := (PBase (PImpl (PFancy p1) (PFancy p2))) (in custom symb at level 86, p1 custom symb, p2 custom symb, right associativity).

Notation "'(' a ')'" := (a) (in custom symb_val at level 1, a custom symb_val, format "'[v' '(' a ')' ']'").
Notation "'{' a '}'" := (a) (in custom symb at level 1, a custom symb, format "'[v' '{' a '}' ']'").
Notation "v1 '=' v2"  := (PBase (PEq v1 v2)) (in custom symb at level 86, v1 custom symb_val, v2 custom symb_val).
Notation "v1 '<>' v2"  := (PBase (PNEq v1 v2)) (in custom symb at level 86, v1 custom symb_val, v2 custom symb_val).


Notation "'0'" := ([false]) (in custom symb_consts at level 0).

Notation "'1'" := ([true]) (in custom symb_consts at level 0).
Notation "bs '~' '0'" := (cons false bs) (in custom symb_consts at level 7, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (cons true bs) (in custom symb_consts at level 7, left associativity, format "bs '~' '1'").

Notation "'#' s" := ((SConst s)) (in custom symb_val at level 98, s constr at level 0, only parsing).
Notation "'Ob' '~' number" :=
  (SConst number)
    (in custom symb_val at level 7, number custom symb_consts at level 99, format "'Ob' '~' number").


Notation "'impl0.[' reg ']'" := (SInitReg MachineImpl reg) (in custom symb_val, reg  constr).
Notation "'impl1.[' reg ']'" := (SFinalReg MachineImpl reg) (in custom symb_val, reg  constr).
Notation "'spec0.[' reg ']'" := (SInitReg MachineSpec reg) (in custom symb_val, reg  constr).
Notation "'spec1.[' reg ']'" := (SFinalReg MachineSpec reg) (in custom symb_val, reg  constr).

(* Notation "'impl_ext0.[' fn ']'" := (SInitExtLog MachineImpl fn) (in custom symb_val, fn constr). *)
Notation "'impl_ext1.[' fn ']'" := (SFinalExtLog MachineImpl fn) (in custom symb_val, fn constr).
(* Notation "'spec_ext0.[' fn ']'" := (SInitExtLog MachineSpec fn) (in custom symb_val, fn constr). *)
Notation "'spec_ext1.[' fn ']'" := (SFinalExtLog MachineSpec fn) (in custom symb_val, fn constr).

Notation "'!' v" := (SBits1 Not v) (in custom symb_val at level 75, format "'!' v").
Notation "'zeroExtend(' a ',' b ')'" :=  (SBits1 (ZExtL b) a) (in custom symb_val, b constr at level 0, format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'" :=  (SBits1 (SExt b) a) (in custom symb_val, b constr at level 0, format "'sext(' a ',' b ')'").


Notation "a '&&' b" :=  (SBits2 (And) a b) (in custom symb_val at level 80,  right associativity, a custom symb_val, b custom symb_val, format "a  '&&'  b").
Notation "a '||' b" :=  (SBits2 (Or) a b) (in custom symb_val at level 80,  right associativity, a custom symb_val, b custom symb_val, format "a  '||'  b").
Notation "a '++' b" :=  (SBits2 (Concat) a b) (in custom symb_val at level 80,  right associativity, a custom symb_val, b custom symb_val, format "a  '++'  b").

Notation "a '==' b" :=  (SBits2 (EqBits true) a b) (in custom symb_val at level 80,  right associativity, a custom symb_val, b custom symb_val, format "a  '=='  b").
Notation "a '!=' b" :=  (SBits2 (EqBits false) a b) (in custom symb_val at level 80,  right associativity, a custom symb_val, b custom symb_val, format "a  '!='  b").

Notation "a '^' b" :=  (SBits2 (Xor) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '^'  b").
Notation "a '+' b" :=  (SBits2 (Plus) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '+'  b").
Notation "a '-' b" :=  (SBits2 (Minus) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '-'  b").

Notation "a '[[' b ']]'" :=  (SBits2 (Sel) a b) (in custom symb_val at level 75,  a custom symb_val, b custom symb_val, format "'[' a  [[ b ]] ']'").
Notation "a '<<' b" :=  (SBits2 (Lsl) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '<<'  b").
Notation "a '>>' b" :=  (SBits2 (Lsr) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>>'  b").
Notation "a '>>>' b" :=  (SBits2 (Asr) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>>>'  b").
Notation "a '<' b" :=  (SBits2 (Compare false cLt) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '<'  b").
Notation "a '<s' b" :=  (SBits2 (Compare true cLt) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '<s'  b").
Notation "a '<=' b" :=  (SBits2 (Compare false cLe) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '<='  b").
Notation "a '<s=' b" :=  (SBits2 (Compare true cLe) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '<s='  b").
Notation "a '>' b" :=  (SBits2 (Compare false cGt) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>'  b").
Notation "a '>s' b" :=  (SBits2 (Compare true cGt) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>s'  b").
Notation "a '>=' b" :=  (SBits2 (Compare false cGe) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>='  b").
Notation "a '>s=' b" :=  (SBits2 (Compare true cGe) a b) (in custom symb_val at level 80,  a custom symb_val, b custom symb_val, format "a  '>s='  b").
Notation "a '[' b ':+' c ']'" := (SBits2 (IndexedSlice c) a b) (in custom symb_val at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'").
Notation "a '[' b ':' c ']'" := (SBits1 (Slice b c) a) (in custom symb_val at level 75, a custom symb_val, b constr at level 0, c constr at level 0, format "'[' a [ b ':' c ] ']'").

Notation "'forall' x 'in' B ',' C " :=
    (PForallRegs (fun x => C) B) (in custom symb at level 100, x ident, B constr at level 100) .

Notation "'forall' '(' x ',' y ')' 'in2' B ',' C " :=
    (PForallRegs2 (fun '(x,y) => C) B) (in custom symb at level 100, x ident, y ident, B constr at level 100) .

Notation "'forall1'  x 'of' n  ',' B " :=
    (PBase (PForallArg1 (x,n) (PFancy B))) (in custom symb at level 100, x constr at level 100, n constr at level 69) .
Notation "'forall2'  x 'of' n1 'and' y 'of' n2  ',' B " :=
    (PBase (PForallArg2 (x, n1) (y,n2) (PFancy B))) (in custom symb at level 100, x constr at level 100, y constr at level 100, n1 constr at level 100, n2 constr at level 100) .



Notation "'`' a '`'" := (a) (in custom symb_val at level 99, a constr at level 99).
Notation "'``' a '``'" := (a) (in custom symb at level 99, a constr at level 99).

Goal {{{ forall (x, y) in2 [(("",0%N),("",1%N))] , `SBound "hello"` = `SBound "hello"`}}} = (PBase (PForallArg1 ("hello",2) (PFancy (PBase (PEq (SBound "hello") (SBound "hello")))))). Abort.


Goal {{{ forall1 "hello" of 2 , `SBound "hello"` = `SBound "hello"`}}} = (PBase (PForallArg1 ("hello",2) (PFancy (PBase (PEq (SBound "hello") (SBound "hello")))))).  reflexivity. Qed.
Goal {{{ forall2 "hello" of 2 and "bye" of 3, `SBound "hello"` = `SBound "hello"`}}} = (PBase (PForallArg2 ("hello",2) ("bye", 3) (PFancy (PBase (PEq (SBound "hello") (SBound "hello")))))).  reflexivity. Qed.

(* Notation "'forall' x 'not_in' B ',' C " := *)
(*     (PNegForallRegs (fun x => C) B) (in custom symb at level 100, x ident, B constr at level 100) . *)



Definition reg_clk : reg_t := ("clk", 0%N).
Definition fn_tick : fn_name_t := ("tick", 0%N).

Goal {{{ True }}} = (PBase (PConst true)). reflexivity. Qed.
Goal {{{ False }}} = (PBase (PConst false)). reflexivity. Qed.
Goal {{{ True /\ False }}} = (PBase (PAnd (PFancy (PBase (PConst true))) (PFancy (PBase (PConst false))))). reflexivity. Qed.
Goal {{{ True /\ { False \/ True } }}}= (PBase (PAnd (PFancy (PBase (PConst true)))
                                          (PFancy (PBase (POr (PFancy (PBase (PConst false))) (PFancy (PBase (PConst true)))))))).  reflexivity. Qed.
Goal {{{ ¬ True }}} = (PBase (PNot (PFancy (PBase (PConst true))))). reflexivity. Qed.


(* Goal {{{ {True} -> False -> True }}} = (PBase PImpl (PConst true) (PImpl (PConst false) (PConst true)). *)
(*   reflexivity. Qed. *)
(* Goal {{{ Ob~1~0[[ Ob~0 ]] = Ob~0 }}} = PEq (SBits2 Sel (SConst [false;true]) (SConst [false])) (SConst [false]). reflexivity. Qed. *)
(* Goal {{{ Ob~1~0 = Ob~1~1 }}} = PEq (SConst [false;true]) (SConst [true;true]). reflexivity. Qed. *)
(* Goal {{{ sext(impl0.[reg_clk], 1) = Ob~1~1 }}} = PEq (SBits1 (SExt 1) (SInitReg MachineImpl reg_clk)) (SConst [true;true]). reflexivity. Qed. *)
(* Goal {{{ zeroExtend(spec1.[reg_clk],2) = Ob~1~1 }}} = PEq (SBits1 (ZExtL 2) (SFinalReg MachineSpec reg_clk)) (SConst [true;true]). reflexivity. Qed. *)
(* Goal {{{ spec1.[reg_clk][2:3] = Ob~1~1 }}} = PEq (SBits1 (Slice 2 3) (SFinalReg MachineSpec reg_clk)) (SConst [true;true]). reflexivity. Qed. *)
(* Goal {{{ (Ob~0~0 == Ob~1~1) = (Ob~0 != Ob~0) }}} = PEq (SBits2 (EqBits true) (SConst [false;false]) (SConst [true;true])) (SBits2 (EqBits false) (SConst [false]) (SConst [false])). reflexivity. Qed. *)
(* Goal {{{ `SInitReg (MachineImpl) reg_clk` = Ob~1~1 ^ Ob~1~0 }}} = PEq (SInitReg (MachineImpl) reg_clk) *)
(*      (SBits2 Xor (SConst [true;true]) (SConst [false;true])). reflexivity. Qed. *)

(* Goal {{{ !spec_ext1.[fn_tick] = Ob~1~1 || Ob~1~0 }}} = PEq (SBits1 Not (SFinalExtLog MachineSpec fn_tick)) (SBits2 Or (SConst [true;true]) (SConst [false;true])). reflexivity. Qed. *)

(* Goal {{{ !spec_ext1.[fn_tick] = Ob~1~1 ++ Ob~1~0 }}} = PEq (SBits1 Not (SFinalExtLog MachineSpec fn_tick)) (SBits2 Concat (SConst [true;true]) (SConst [false;true])). reflexivity. Qed. *)

(* Goal {{{ !spec_ext1.[fn_tick] = Ob~1~1 && Ob~1~0 }}} = PEq (SBits1 Not (SFinalExtLog MachineSpec fn_tick)) (SBits2 And (SConst [true;true]) (SConst [false;true])). reflexivity. Qed. *)

(* Goal {{{ (Ob~1~1 >> Ob~1~0) << (Ob~0~0 >>> Ob~0~1) =  Ob~0~0 }}} = PEq (SBits2 Lsl (SBits2 Lsr (SConst [true;true]) (SConst [false;true])) (SBits2 Asr (SConst [false;false]) (SConst [true;false]))) (SConst [false;false]). reflexivity. Qed. *)

(* Definition foo := [true]. *)
(* Goal {{{ #(foo) = Ob~1 }}} = PEq (SConst [true]) (SConst [true]). reflexivity. Qed. *)
