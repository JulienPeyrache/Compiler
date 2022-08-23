open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop =
  function
    Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tne  -> true
  | _    -> false

  let binop_is_compare =
    function
      Ecle -> true
    | Eclt -> true
    | Ecge -> true
    | Ecgt -> true
    | Eceq -> true
    | Ecne  -> true
    | _    -> false


let binop_of_tag =
  function
    Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tne -> Ecne
  | _ -> assert false

let compatible t1 t2 = match t1, t2 with
  |Tvoid, Tvoid -> true
  |Tint, Tint -> true
  |Tchar, Tchar -> true
  |Tint, Tchar -> true
  |Tchar, Tint -> true
  |_, _ -> false


  let rec type_expr (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e : expr) : typ res = 
    match e with
    | Eint _ -> OK Tint
    | Echar _-> OK Tchar
    | Ebinop (b, e1, e2) -> type_expr typ_var typ_fun e1 >>= fun t1 -> type_expr typ_var typ_fun e2 >>= fun t2 -> if (t1 = Tvoid)||(t2 = Tvoid) then Error "Binop appliqué à du void" else (if (compatible t1 t2) then (if (binop_is_compare b)||(t1 <> t2) then OK(Tint) else OK(t1)) else Error "Type error : les expressions ne sont pas de même type")
    | Eunop (u, e1) -> type_expr typ_var typ_fun e1 >>= fun t1 -> OK t1
    | Evar s -> if Hashtbl.mem typ_var s then OK (Hashtbl.find typ_var s) else Error "Type error : var non définie dans la fonction courante"
    | Ecall (s, l) -> if Hashtbl.mem typ_fun s then let (l1, t) = Hashtbl.find typ_fun s in 
                          if List.length l1 = List.length l then list_map_res (type_expr typ_var typ_fun) l >>= fun l2 -> 
                            if l1 = l2 then OK t 
                            else Error "Type error : les expressions données en argument ne sont pas du bon type" 
                          else Error ("Type error : pas le bon nombre d'arguments dans la fonction appelée :"^s) 
                      else Error ("Type error : fonction appelée non définie :"^s)
  
  
    let verif_typ_var_fun (fname : string) (arg_list : expr list) (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t): bool res =
      if Hashtbl.mem typ_fun fname then let (l1, t) = Hashtbl.find typ_fun fname in 
        if List.length l1 = List.length arg_list then list_map_res (type_expr typ_var typ_fun) arg_list >>= fun l2 -> 
          if (List.fold_right2 (fun typ1 typ2 boo -> (boo)&&(compatible typ1 typ2)) l1 l2 true) then OK(true) 
          else Error "Type error : les expressions données en argument ne sont pas du bon type" 
        else Error ("Type error : pas le bon nombre d'arguments dans la fonction appelée :"^fname) 
      else Error ("Type error : fonction appelée non définie :"^fname)
  
  
    let remplir_type_var (type_var : (string,typ) Hashtbl.t) (argnode_list : Ast.tree list): (string list * typ list) res = 
    let rec aux (arg_acc : string list) (typ_acc : typ list) (argnode_list : Ast.tree list) : (string list *typ list) res= 
      match argnode_list with
    | [] -> OK (arg_acc, typ_acc)
    | t::q -> match t with 
              |Node(Targ, [Node(Tvartype, [TypeLeaf(typ)]);s]) -> Hashtbl.replace type_var (string_of_stringleaf s) typ; (aux (arg_acc@[string_of_stringleaf s]) (typ_acc@[typ]) q)
              | _ -> Error "Erreur remplir_type_var : les noeuds en entrée ne sont pas du bon type."
    in aux [] [] argnode_list


(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (a: tree): expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t -> (match make_eexpr_of_ast typ_var typ_fun e1, make_eexpr_of_ast typ_var typ_fun e2 with
                                                |OK exp1, OK exp2 -> OK(Ebinop(binop_of_tag t, exp1, exp2))
                                                | Error msg, _ -> Error msg
                                                | _, Error msg -> Error msg
                                                )
    | Node(Tneg, [e1])  -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression -> OK (Eunop(Eneg, expression))
    | IntLeaf i -> OK(Eint i)
    | Node(Tcall, [StringLeaf fun_name; NullLeaf]) -> OK(Ecall(fun_name, []))
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> list_map_res (make_eexpr_of_ast typ_var typ_fun) argslist >>= 
        fun args -> verif_typ_var_fun fun_name args typ_var typ_fun >>= 
        fun bool -> if bool then  OK(Ecall(fun_name, args)) 
                    else Error ("Les types des arguments ne correspondent pas à l'appel de la fonction :"^fun_name)
    | StringLeaf s -> OK (Evar s)
    | CharLeaf c -> OK (Echar c)
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let rec make_einstr_of_ast (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (a: tree) : instr res =
  let res =
    match a with
    | Node(Tassign,[Node(Tassignvar, [Node(Tvartype, [TypeLeaf typ]); StringLeaf s; e1])]) -> 
      make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression ->
      type_expr typ_var typ_fun expression >>= fun typ_expr -> if (typ_expr = Tvoid)||(typ = Tvoid)||not(compatible typ typ_expr) then Error "Les types pour assigner la variable de sont pas cohérents" else
      (Hashtbl.replace typ_var s typ; 
      OK (Iassign(s,expression)))
    | Node(Tassign,[Node(Tassignvar, [StringLeaf s; e1])]) -> (match Hashtbl.find_option typ_var s with
        |Some(typ) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression ->
                      type_expr typ_var typ_fun expression >>= fun typ_expr -> if (typ_expr = Tvoid)||(typ = Tvoid)||not(compatible typ typ_expr) then Error "Les types pour assigner la variable de sont pas cohérents" else
                      (Hashtbl.replace typ_var s typ; 
                      OK (Iassign(s,expression)))
        |None -> Error ("Variable non définie précedemment assignée :"^s))
    | Node(Tdecl, [Node(Tvartype, [TypeLeaf typ]); StringLeaf s]) -> if typ = Tvoid then Error "Variable déclarée void" else (Hashtbl.replace typ_var s typ; OK(Iblock([])))
    | Node(Tif, [e1; e2; e3]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun instr2 -> make_einstr_of_ast typ_var typ_fun e3 >>= fun instr3 ->OK (Iif(expr1, instr2, instr3))
    | Node(Tif, [e1; e2]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun instr2 -> OK (Iif(expr1, instr2, Iblock([])))
    | Node(Twhile, [e1; e2]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun expr2 -> OK (Iwhile(expr1, expr2))
    | Node(Treturn, [e1]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression -> OK (Ireturn(expression))
    | Node(Tblock, l) -> list_map_res (make_einstr_of_ast typ_var typ_fun) l >>= fun liste -> OK (Iblock(liste))
    | Node(Telse, l) -> list_map_res (make_einstr_of_ast typ_var typ_fun) l >>= fun liste -> OK (Iblock(liste))
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> 
    list_map_res (make_eexpr_of_ast typ_var typ_fun) argslist >>= fun args -> verif_typ_var_fun fun_name args typ_var typ_fun >>= fun bool -> if bool then  OK(Icall(fun_name, args)) else Error ("Les types des arguments ne correspondent pas à l'appel de la fonction :"^fun_name)
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : string res =
  match a with
  | Node (Targ, [Node(Tvartype, [TypeLeaf(typ)]);s]) ->
    OK (string_of_stringleaf s)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) (typ_fun : (string, typ list * typ) Hashtbl.t): (string * efun) option res =
  let typ_var = Hashtbl.create 17 in
  match a with
  (* Tri entre les déclarations de fonctions et les définitions de fonctions*)
  (*déclarations*)
  | Node (Tfundef, [Node(Tfuntype, [TypeLeaf typ]);Node(Tfunname,[fname]); Node (Tfunargs, fargs); NullLeaf]) ->
    remplir_type_var typ_var fargs >>= fun (arg_list, typ_list) -> 
      Hashtbl.replace typ_fun (string_of_stringleaf fname) (typ_list, typ);
      OK(None)
  
  | Node (Tfundef, [Node(Tfuntype, [TypeLeaf typ]);Node(Tfunname,[fname]); NullLeaf; NullLeaf]) ->
    Hashtbl.replace typ_fun (string_of_stringleaf fname) ([], typ);
    OK(None)

  (*définition*)
  | Node (Tfundef, [Node(Tfuntype, [TypeLeaf typ]);Node(Tfunname,[fname]); Node (Tfunargs, fargs); Node(Tfunbody, [fbody])]) ->
    remplir_type_var typ_var fargs >>= fun (arg_list, typ_list) -> 
      Hashtbl.replace typ_fun (string_of_stringleaf fname) (typ_list, typ);
      make_einstr_of_ast typ_var typ_fun fbody >>= fun fbody ->
    OK(Some(string_of_stringleaf fname, {funargs = arg_list; funbody = fbody ; funrettype = typ ; funvartyp = typ_var}))

  | Node (Tfundef, [Node(Tfuntype, [TypeLeaf typ]);Node(Tfunname,[fname]); NullLeaf; Node(Tfunbody, [fbody])]) ->
    Hashtbl.replace typ_fun (string_of_stringleaf fname) ([], typ);   
    make_einstr_of_ast typ_var typ_fun fbody >>= fun fbody -> 
    OK(Some(string_of_stringleaf fname, {funargs = []; funbody = fbody ; funrettype = typ ; funvartyp = typ_var}))

  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  let typ_fun = Hashtbl.create 2 in
  Hashtbl.replace typ_fun "print" ([Tint], Tvoid);
  Hashtbl.replace typ_fun "print_int" ([Tint], Tvoid);
  Hashtbl.replace typ_fun "print_char" ([Tchar], Tvoid);
  match a with
  | Node (Tlistglobdef, l) ->
    list_map_res (fun a -> make_fundef_of_ast a typ_fun >>= function  |None -> OK(None) |Some(fname, efun) -> OK(Some(fname, Gfun efun))) l >>=
    fun list -> OK(List.filter_map (fun a -> a) list)
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
             (string_of_ast a))

let pass_elang ast =
  match make_eprog_of_ast ast with
  | Error msg ->
    record_compile_result ~error:(Some msg) "Elang";
    Error msg
  | OK  ep ->
    dump !e_dump dump_e ep (fun file () ->
        add_to_report "e" "E" (Code (file_contents file))); OK ep

