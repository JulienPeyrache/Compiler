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
let rec make_eexpr_of_ast (a: tree) : expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t -> (match make_eexpr_of_ast e1, make_eexpr_of_ast e2 with
                                                |OK exp1, OK exp2 -> OK(Ebinop(binop_of_tag t, exp1, exp2))
                                                | Error msg, _ -> Error msg
                                                | _, Error msg -> Error msg
                                                )
    | Node(Tneg, [e1])  -> make_eexpr_of_ast e1 >>= fun expression -> OK (Eunop(Eneg, expression))
    | Node(Tint, [IntLeaf i]) -> OK(Eint i)
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> list_map_res make_eexpr_of_ast argslist >>= fun args -> OK(Ecall(fun_name, args))
    | StringLeaf s -> OK (Evar s)
    | CharLeaf c -> OK (Evar (String.of_list [c]))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let rec make_einstr_of_ast (a: tree) : instr res =
  let res =
    match a with
    | Node(Tassign,[Node(Tassignvar, [StringLeaf s; e1])]) -> make_eexpr_of_ast e1 >>= fun expression -> OK (Iassign(s,expression))
    | Node(Tif, [e1; e2; e3]) -> make_eexpr_of_ast e1 >>= fun expr1 -> make_einstr_of_ast e2 >>= fun instr2 -> make_einstr_of_ast e3 >>= fun instr3 ->OK (Iif(expr1, instr2, instr3))
    | Node(Tif, [e1; e2]) -> make_eexpr_of_ast e1 >>= fun expr1 -> make_einstr_of_ast e2 >>= fun instr2 -> OK (Iif(expr1, instr2, Iblock([])))
    | Node(Twhile, [e1; e2]) -> make_eexpr_of_ast e1 >>= fun expr1 -> make_einstr_of_ast e2 >>= fun expr2 -> OK (Iwhile(expr1, expr2))
    | Node(Treturn, [e1]) -> make_eexpr_of_ast e1 >>= fun expression -> OK (Ireturn(expression))
    | Node(Tblock, l) -> list_map_res make_einstr_of_ast l >>= fun liste -> OK (Iblock(liste))
    | Node(Telse, l) -> list_map_res make_einstr_of_ast l >>= fun liste -> OK (Iblock(liste))
    | Node(Tcall, [StringLeaf fun_name;Node(Targs, argslist)]) -> list_map_res make_eexpr_of_ast argslist >>= fun args -> OK(Icall(fun_name, args))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : string res =
  match a with
  | Node (Targ, [s]) ->
    OK (string_of_stringleaf s)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) : (string * efun) res =
  match a with
  | Node (Tfundef, [StringLeaf fname; Node (Tfunargs, fargs); fbody]) ->
    list_map_res make_ident fargs >>= fun fargs -> 
     (* TODO *)
    make_einstr_of_ast fbody >>= fun fbody ->
    OK(fname, {funargs = fargs; funbody = fbody})
  | Node (Tfundef, [StringLeaf fname; NullLeaf; fbody]) ->  
      make_einstr_of_ast fbody >>= fun fbody -> OK(fname, {funargs = []; funbody = fbody})
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

