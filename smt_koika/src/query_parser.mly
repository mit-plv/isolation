%{
  open Query_ast

%}

%token <int> INT
%token STOP
%token AT_SIGN
%token EOF
%token MID_IMPL
%token MID_SPEC
%token REG_IMPL
%token REG_SPEC
%token REGS_IMPL
%token REGS_SPEC
%token LEFT_BRACK
%token RIGHT_BRACK
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA

%start <Query_ast.expr> cmd
%%

cmd:
  | e = expr; EOF { e }
  ;

reglist:
  | LEFT_BRACK; regs = list_fields; RIGHT_BRACK { RegList regs}
  | LEFT_PAREN; id1 = INT; COMMA; id2 = INT; RIGHT_PAREN { RegRange (id1,id2) }


list_fields: 
  vl = separated_list(COMMA, INT) { vl }

expr:
| REG_IMPL; id = INT; AT_SIGN; rule_num = INT {Query (Impl, RegList [id],rule_num)}
| REG_SPEC; id = INT; AT_SIGN; rule_num = INT {Query (Spec, RegList [id],rule_num)}
| REGS_IMPL; regs = reglist ; AT_SIGN; rule_num = INT {Query(Impl, regs ,rule_num)}
| REGS_SPEC; regs = reglist ; AT_SIGN; rule_num = INT {Query(Spec, regs ,rule_num)}
| STOP { Stop }
; 
