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
    | Node(Tint, [IntLeaf i]) -> OK(Eint i)
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> list_map_res (make_eexpr_of_ast typ_var typ_fun) argslist >>= fun args -> OK(Ecall(fun_name, args))
    | StringLeaf s -> OK (Evar s)
    | CharLeaf c -> OK (Evar (String.of_list [c]))
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
    | Node(Tassign,[Node(Tassignvar, [StringLeaf s; e1])]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression -> OK (Iassign(s,expression))
    | Node(Tif, [e1; e2; e3]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun instr2 -> make_einstr_of_ast typ_var typ_fun e3 >>= fun instr3 ->OK (Iif(expr1, instr2, instr3))
    | Node(Tif, [e1; e2]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun instr2 -> OK (Iif(expr1, instr2, Iblock([])))
    | Node(Twhile, [e1; e2]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expr1 -> make_einstr_of_ast typ_var typ_fun e2 >>= fun expr2 -> OK (Iwhile(expr1, expr2))
    | Node(Treturn, [e1]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression -> OK (Ireturn(expression))
    | Node(Tprint, [e1]) -> make_eexpr_of_ast typ_var typ_fun e1 >>= fun expression -> OK (Iprint(expression))
    | Node(Tblock, l) -> list_map_res (make_einstr_of_ast typ_var typ_fun) l >>= fun liste -> OK (Iblock(liste))
    | Node(Telse, l) -> list_map_res (make_einstr_of_ast typ_var typ_fun) l >>= fun liste -> OK (Iblock(liste))
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> list_map_res (make_eexpr_of_ast typ_var typ_fun) argslist >>= fun args -> OK(Icall(fun_name, args))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : (typ * string) res =
  match a with
  | Node (Targ, [Node(Tvartype, [TypeLeaf(typ)]);s]) ->
    OK (typ, string_of_stringleaf s)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) (typ_fun : (string, typ list * typ) Hashtbl.t): (string * efun) res =
  let typ_var = Hashtbl.create 17 in
  
  match a with
  | Node (Tfundef, [Node(Tfuntype, [typ]);Node(Tfunname,[fname]); Node (Tfunargs, fargs); fbody]) ->
    list_map_res (fun x -> make_ident x >>= fun (t,v) -> Hashtbl.replace type_var v t; OK(v)) fargs >>= fun fargs -> 
     (* TODO *)
    make_einstr_of_ast typ_var typ_fun fbody >>= fun fbody ->
    OK(fname, {funargs = fargs; funbody = fbody})
  | Node (Tfundef, [Node(Tfuntype, [typ]);Node(Tfunname,[fname]); NullLeaf; fbody]) ->  
      make_einstr_of_ast typ_var typ_fun fbody >>= fun fbody -> OK(fname, {funargs = []; funbody = fbody})
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    list_map_res (fun a -> make_fundef_of_ast a >>= fun (fname, efun) -> OK (fname, Gfun efun)) l
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

let rec type_expr (typ_var : (string,typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e : expr) : typ res = 
  match e with
  | Eint _ -> OK Tint
  | Echar _-> OK Tchar
  | Ebinop (b, e1, e2) -> type_expr typ_var typ_fun e1 >>= fun t1 -> type_expr typ_var typ_fun e2 >>= fun t2 -> if t1 = t2 then OK t1 else Error "Type error : les expressions ne sont pas de même type"
  | Eunop (u, e1) -> type_expr typ_var typ_fun e1 >>= fun t1 -> OK t1
  | Evar s -> if Hashtbl.mem typ_var s then OK (Hashtbl.find typ_var s) else Error "Type error : var non définie dans la fonction courante"
  | Ecall (s, l) -> if Hashtbl.mem typ_fun s then let (l1, t) = Hashtbl.find typ_fun s in if List.length l1 = List.length l then list_map_res (type_expr typ_var typ_fun) l >>= fun l2 -> if l1 = l2 then OK t else Error "Type error : les expressions données en argument ne sont pas du bon type" else Error "Type error : pas le bon nombre d'arguments dans la fonction appelée :"^s else Error "Type error : fonction appelée non définie :"^s


  let compatible t1 t2 = match t1, t2 with
  |Tvoid, Tvoid -> true
  |Tint, Tint -> true
  |Tchar, Tchar -> true
  |Tint, Tchar -> true
  |Tchar, Tint -> true
  |_, _ -> false