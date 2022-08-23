tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int>  SYM_CHARACTER<char>
tokens SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
tokens SYM_INT SYM_CHAR SYM_VOID
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ 
non-terminals S INSTR INSTRS LINSTRS ELSE EXPR FACTOR ID_OR_CALL
non-terminals LPARAMS REST_PARAMS CALLPARAMS REST_CALL_PARAMS
non-terminals IDENTIFIER INTEGER TYPE CHARACTER
non-terminals FUNDEF FUNDEFS FUNCALL ASSIGN_OR_CALL ASSIGN_OR_DECL DEF_OR_NOTDEF
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals BOOL_EXPR
non-terminals CMP_EXPR
non-terminals EQ_EXPR
axiom S
{

  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils

   (* TODO *)
  let rec resolve_associativity term other = 
    match other with
    |Node(tree_arg, tree2::[]) -> (Node(tree_arg, term::tree2::[]))
    |Node(tree_arg, tree2::rest::[]) -> resolve_associativity (Node(tree_arg, [term; tree2])) rest
    | _ -> term

  let rec resolve_associativity_v2 (term : tree) (other : (tag*tree)list) : tree = 
    match other with
   |[] -> term
   |(tag, tree) :: rest -> resolve_associativity_v2 (Node(tag, term::tree::[])) rest

}



rules
S -> FUNDEF FUNDEFS SYM_EOF {(Node(Tlistglobdef, $1::$2))
}

TYPE -> SYM_INT  {TypeLeaf(Tint)}
TYPE -> SYM_CHAR {TypeLeaf(Tchar)}
TYPE -> SYM_VOID {TypeLeaf(Tvoid)}

FUNDEFS -> FUNDEF FUNDEFS { $1::$2}
FUNDEFS -> { [] }

FUNDEF -> TYPE IDENTIFIER SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS DEF_OR_NOTDEF {Node (Tfundef, [Node(Tfuntype, [$1]);Node(Tfunname,[$2]);$4]@($6))}

DEF_OR_NOTDEF -> SYM_LBRACE LINSTRS SYM_RBRACE {[Node(Tfunbody, [$2])]}
DEF_OR_NOTDEF -> SYM_SEMICOLON {[]}



LPARAMS -> TYPE IDENTIFIER REST_PARAMS { Node(Tfunargs, Node(Targ, [Node(Tvartype,[$1]);$2])::$3)}
LPARAMS -> {NullLeaf}

REST_PARAMS -> SYM_COMMA TYPE IDENTIFIER REST_PARAMS 
{Node(Targ, [Node(Tvartype, [$2]);$3])::$4}
REST_PARAMS -> {[]}

LINSTRS -> INSTR INSTRS{match $2 with |[] -> $1 |_ -> Node(Tblock, $1::$2)}
LINSTRS ->  {NullLeaf}

INSTRS -> INSTR INSTRS {$1::$2}
INSTRS -> {[]}

INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_LBRACE LINSTRS SYM_RBRACE ELSE 
{Node (Tif, $3::$6::$8)}
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON {Node(Treturn, [$2])}
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_LBRACE LINSTRS SYM_RBRACE {Node(Twhile, [$3; $6])}
INSTR -> TYPE IDENTIFIER ASSIGN_OR_DECL {$3 [Node(Tvartype, [$1]); $2]}
INSTR -> IDENTIFIER ASSIGN_OR_CALL {$2 $1}

ASSIGN_OR_CALL -> SYM_ASSIGN EXPR SYM_SEMICOLON {fun x -> Node(Tassign, Node(Tassignvar,[x; $2])::[])}
ASSIGN_OR_CALL -> FUNCALL SYM_SEMICOLON {$1}

ASSIGN_OR_DECL -> SYM_ASSIGN EXPR SYM_SEMICOLON {fun x -> Node(Tassign, Node(Tassignvar,x@[$2])::[])}
ASSIGN_OR_DECL -> SYM_SEMICOLON {fun x -> Node(Tdecl, x)}

FUNCALL -> SYM_LPARENTHESIS CALLPARAMS SYM_RPARENTHESIS {fun x -> Node(Tcall, x::[$2])}

CALLPARAMS -> EXPR REST_CALL_PARAMS { Node(Targs, $1::$2)}
CALLPARAMS -> {NullLeaf}

REST_CALL_PARAMS -> SYM_COMMA EXPR REST_CALL_PARAMS 
{$2::$3}
REST_CALL_PARAMS -> {[]}


ELSE -> SYM_ELSE SYM_LBRACE LINSTRS SYM_RBRACE {if ($3=NullLeaf) then [] else Node(Telse,[$3])::[]}
ELSE -> {[]}

EXPR -> ADD_EXPRS BOOL_EXPR {resolve_associativity_v2 $1 $2}

BOOL_EXPR -> CMP_EXPR {$1}
BOOL_EXPR -> EQ_EXPR {$1}
BOOL_EXPR -> {[]}


ADD_EXPRS -> MUL_EXPRS ADD_EXPR {resolve_associativity_v2 $1 $2}

ADD_EXPR -> SYM_PLUS MUL_EXPRS ADD_EXPR {(Tadd,$2)::$3}
ADD_EXPR -> SYM_MINUS MUL_EXPRS ADD_EXPR {(Tsub,$2)::$3}
ADD_EXPR -> {[]}



MUL_EXPRS -> FACTOR MUL_EXPR{resolve_associativity_v2 $1 $2}

MUL_EXPR -> SYM_ASTERISK FACTOR MUL_EXPR {(Tmul,$2)::$3}
MUL_EXPR -> SYM_DIV FACTOR MUL_EXPR {(Tdiv,$2)::$3}
MUL_EXPR -> SYM_MOD FACTOR MUL_EXPR {(Tmod,$2)::$3}
MUL_EXPR -> {[]}


CMP_EXPR -> SYM_LT ADD_EXPRS BOOL_EXPR {(Tclt, $2)::$3}
CMP_EXPR -> SYM_LEQ ADD_EXPRS BOOL_EXPR {(Tcle, $2)::$3}
CMP_EXPR -> SYM_GT ADD_EXPRS BOOL_EXPR {(Tcgt, $2)::$3}
CMP_EXPR -> SYM_GEQ ADD_EXPRS BOOL_EXPR {(Tcge, $2)::$3}

EQ_EXPR -> SYM_EQUALITY ADD_EXPRS BOOL_EXPR {(Tceq, $2)::$3}
EQ_EXPR -> SYM_NOTEQ ADD_EXPRS BOOL_EXPR{(Tne, $2)::$3}

FACTOR -> SYM_MINUS FACTOR {Node(Tneg, [$2])}
FACTOR -> IDENTIFIER ID_OR_CALL {$2 $1}
FACTOR -> INTEGER {$1}
FACTOR -> CHARACTER {$1}
FACTOR -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS {$2}

ID_OR_CALL -> {fun x -> x}
ID_OR_CALL -> FUNCALL {$1}


IDENTIFIER -> SYM_IDENTIFIER {StringLeaf ($1)}

INTEGER -> SYM_INTEGER {IntLeaf ($1)}

CHARACTER -> SYM_CHARACTER {CharLeaf ($1)}

