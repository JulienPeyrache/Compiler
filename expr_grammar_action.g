tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA SYM_PRINT
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
non-terminals S INSTR INSTRS LINSTRS ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS
non-terminals IDENTIFIER INTEGER
non-terminals FUNDEF FUNDEFS
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
  
  let rec renverser_peigne_binaire (peigne : tree) : tree ->
  (match peigne with
  |Node(t1, tree1::tree2::[]) -> 
    (match tree2 with
    |Node(t2, tree3::tree4::[]) -> let peigne2 = Node(t2, [Node(t1, [tree1;tree3]) ; tree4]) in renverser_peigne_binaire peigne2
    |_ -> peigne)
  | _ -> peigne)

  let resolve_associativity tree_tag term other =
      (* TODO *)
    match other with 
    | Node(t, tree1::[]) -> Node(tree_tag, [Node(t, [term; tree1])]) 
    | _ -> Node(tree_tag, [term; other])


  let arbre_list arbre1 arbre2 = 
  let rec arbre_hauteur_1 arbre1 peigne_droit = 
  match (arbre1, peigne_droit) with 
  | (Node(t1, list), Node(t2, tree2::rest_params::[]) -> 
            arbre_hauteur_1 (Node(t1, tree2::list)) rest_params
  | (Node(t1, list), NullLeaf) -> arbre1
  | (Node(t1, list), _) -> Node(t1, peigne_droit::list)
  | _ -> Error "Ces arbres ne conviennent pas aux conditions de construction."

  in let tree1 = arbre_hauteur_1 arbre1 arbre2 in
  match tree with
  |Error msg -> Error msg
  |Node(tag, liste) -> Node(tag, List.rev liste)
  |_ -> tree

}



rules
S -> FUNDEF FUNDEFS SYM_EOF {
  arbre_list Node(Tlistglobdef, $1::[]) $2
  }

FUNDEFS -> FUNDEF FUNDEFS { 
  match $2 with 
  | NullLeaf-> $1
  |_->Node(Tfundef, $1::$2::[])
}
FUNDEFS -> { NullLeaf }


FUNDEF -> IDENTIFIER SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS LINSTRS {
      Node (Tfundef, [$1; $3; $5])
  }

LPARAMS -> IDENTIFIER REST_PARAMS { arbre_list Node(Tfunargs, [Node(Targ, [$1])]) $2}
LPARAMS -> {NullLeaf}

REST_PARAMS -> SYM_COMMA IDENTIFIER REST_PARAMS 
{
  match $3 with 
  | NullLeaf-> $2
  |_->Node(Targ, Node(Targ, $2)::$3::[])
  }
REST_PARAMS -> {NullLeaf}

LINSTRS -> SYM_LBRACE INSTR INSTRS SYM_RBRACE {arbre_list Node(Tblock, [$2]) $3}
LINSTRS -> INSTR {$1}

INSTRS -> INSTR INSTRS 
{
match $2 with
|NullLeaf -> $1
|_ -> Node(Targ, [$1; $2])
}
INSTRS -> {NullLeaf}

INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_LBRACE LINSTRS SYM_RBRACE ELSE SYM_SEMICOLON 
{ Node (Tif, [$3; $6; $8]) }
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON {Node(Treturn, [$2])}
INSTR -> SYM_PRINT SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_SEMICOLON {Node(Tprint, [$3])}
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS LINSTRS SYM_SEMICOLON {Node(Twhile, [$3; $5])}
INSTR -> IDENTIFIER SYM_ASSIGN EXPR SYM_SEMICOLON {Node(Tassign, [$1; $3])}

ELSE -> SYM_ELSE SYM_LBRACE LINSTRS SYM_RBRACE {Node(Telse,$3)}
ELSE -> {NullLeaf}

EXPR -> ADD_EXPRS BOOL_EXPR
  { 
match $2 with 
|Node(tree_tag, tree::[]) -> Node(tree_tag, [$1; tree])
|_ -> $1
  }

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
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tclt, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}
CMP_EXPR -> SYM_LEQ ADD_EXPRS BOOL_EXPR
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tcle, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}
CMP_EXPR -> SYM_GT ADD_EXPRS BOOL_EXPR
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tcgt, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}
CMP_EXPR -> SYM_GEQ ADD_EXPRS BOOL_EXPR
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tcge, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}


EQ_EXPR -> SYM_EQUALITY ADD_EXPRS BOOL_EXPR
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tceq, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}
EQ_EXPR -> SYM_NOTEQ ADD_EXPRS BOOL_EXPR
{
match $3 with
|Node(tree_tag, tree::[]) -> Node(Tne, [Node(tree_tag, [$2; tree])])
|_ -> Node(Tclt, [$2])
}

FACTOR -> SYM_MINUS FACTOR {Node(Tneg, [$2])}
FACTOR -> IDENTIFIER {$1}
FACTOR -> INTEGER {$1}


IDENTIFIER -> SYM_IDENTIFIER {StringLeaf ($1)}

INTEGER -> SYM_INTEGER {IntLeaf ($1)}

