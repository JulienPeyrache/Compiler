tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA SYM_PRINT
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
non-terminals S INSTR INSTRS LINSTRS ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS
non-terminals IDENTIFIER INTEGER
non-terminals FUNDEF
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals BOOL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
axiom S
{

  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils

   (* TODO *)
  
  let rec renverser_peigne_binaire (peigne : tree) : tree ->
  match peigne with
  |Node(t1, tree1::tree2::[]) -> match tree2 with
    |Node(t2, tree3::tree4::[]) -> let peigne2 = Node(t2, [Node(t1, [tree1;tree3]) ; tree4]) in renverser_peigne_binaire peigne2
    |_ -> peigne
  | _ -> peigne

  let resolve_associativity tree_tag term other =
      (* TODO *)
    match other with 
    | Node(t, tree1::[]) -> Node(tree_tag, [Node(t, [term; tree1])]) 
    | _ -> Node(tree_tag, [term; other])


  
  
  
  
  (tree_tag : tag) (tree1 : tree) (tree2 : tree) : tree = 
  match tree2 with
 | Node(tag2, t::q) -> 
 | StringLeaf of string -> Node(tree_tag, [tree1; tree2])
 | IntLeaf of int -> Node(tree_tag, [tree1; tree2])
 | NullLeaf -> tree1
 | CharLeaf(c) -> Node(tree_tag, [tree1; tree2])


}



rules
S -> FUNDEF SYM_EOF {  Node (Tlistglobdef, [$1]) }

FUNDEF -> IDENTIFIER SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS LINSTRS {
      let fargs = $3 in
      let instr = $5 in
      Node (Tfundef, [$1; Node (Tfunargs, fargs) ; instr ])
  }

LPARAMS -> EXPR REST_PARAMS 
LPARAMS -> {NullLeaf}

REST_PARAMS -> SYM_COMMA EXPR REST_PARAMS 
REST_PARAMS -> {NullLeaf}

LINSTRS -> SYM_LBRACE INSTR INSTRS SYM_RBRACE {Node(Tblock, [$2; $3])}
LINSTRS -> INSTR {Node(Tlistinstr, [$1])}

INSTRS -> INSTR INSTRS {Node(Tlistinstr, [$1; $2])}
INSTRS -> {NullLeaf}

INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_LBRACE LINSTRS SYM_RBRACE ELSE SYM_SEMICOLON { Node (Tif, [$3; $6; $8]) }
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON {Node(Treturn, [$2])}
INSTR -> SYM_PRINT SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_SEMICOLON {Node(Tprint, [$3])}
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS LINSTRS SYM_SEMICOLON {Node(Twhile, [$3; $5])}
INSTR -> IDENTIFIER SYM_ASSIGN EXPR SYM_SEMICOLON {Node(Tassign, [$1; $3])}

ELSE -> SYM_ELSE SYM_LBRACE LINSTRS SYM_RBRACE {Node(Telse,$3)}
ELSE -> {NullLeaf}

EXPR -> ADD_EXPRS BOOL_EXPR {$1}

BOOL_EXPR -> CMP_EXPR {$1}
BOOL_EXPR -> EQ_EXPR {$1}
BOOL_EXPR -> {NullLeaf}


ADD_EXPRS -> MUL_EXPRS ADD_EXPR 
{ 
match $2 with 
|Node(tree_tag, tree::[]) -> renverser_peigne_binaire (Node(tree_tag, [$1; tree]))
|_ -> $1
}

ADD_EXPR -> SYM_PLUS MUL_EXPRS ADD_EXPR 
{resolve_associativity(Tadd, $2, $3)}
ADD_EXPR -> SYM_MINUS MUL_EXPRS ADD_EXPR
{resolve_associativity(Tsub, $2, $3)}
ADD_EXPR -> {NullLeaf}


MUL_EXPRS -> FACTOR MUL_EXPR
{ 
match $2 with 
|Node(tree_tag, tree::[]) -> renverser_peigne_binaire (Node(tree_tag, [$1; tree]))
|_ -> $1
}

MUL_EXPR -> SYM_ASTERISK FACTOR MUL_EXPR {resolve_associativity(Tmul, $2, $3)}
MUL_EXPR -> SYM_DIV FACTOR MUL_EXPR {resolve_associativity(Tdiv, $2, $3)}
MUL_EXPR -> SYM_MOD FACTOR MUL_EXPR {resolve_associativity(Tmod, $2, $3)}
MUL_EXPR -> {NullLeaf}

CMP_EXPR -> SYM_LT ADD_EXPRS BOOL_EXPR
CMP_EXPR -> SYM_LEQ ADD_EXPRS BOOL_EXPR
CMP_EXPR -> SYM_GT ADD_EXPRS BOOL_EXPR
CMP_EXPR -> SYM_GEQ ADD_EXPRS BOOL_EXPR


EQ_EXPR -> SYM_EQUALITY ADD_EXPRS BOOL_EXPR
EQ_EXPR -> SYM_NOTEQ ADD_EXPRS BOOL_EXPR

FACTOR -> SYM_MINUS FACTOR {Node(Tneg, [$2])}
FACTOR -> IDENTIFIER {$1}
FACTOR -> INTEGER {$1}


IDENTIFIER -> SYM_IDENTIFIER {StringLeaf ($1)}

INTEGER -> SYM_INTEGER {IntLeaf ($1)}

