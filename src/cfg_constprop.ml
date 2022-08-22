open Batteries
open Cfg
open Elang_run
open Prog
open Utils
open Report
open Cfg_print
open Options

(* [simple_eval_eexpr e] evaluates an expression [e] with no variables. Raises
   an exception if the expression contains variables. *)
let rec simple_eval_eexpr (e: expr) : int =
  match e with
  |Eint i -> i
  |Eunop(u, e) ->
    let i = simple_eval_eexpr e in eval_unop u i
  |Ebinop(b, e1, e2) ->
    let i1 = simple_eval_eexpr e1 in
    let i2 = simple_eval_eexpr e2 in
    eval_binop b i1 i2
  |_ -> raise (Failure "simple_eval_eexpr: variable in expression")

(* If an expression contains variables, we cannot simply evaluate it. *)

(* [has_vars e] indicates whether [e] contains variables. *)
let rec has_vars (e: expr) =
  try let _ = simple_eval_eexpr e in false
  with Failure _ -> true
  

let const_prop_binop b e1 e2 =
  let e = Ebinop (b, e1, e2) in
  if has_vars e
  then e
  else Eint (simple_eval_eexpr e)

let const_prop_unop u e =
  let e = Eunop (u, e) in
  if has_vars e
  then e
  else Eint (simple_eval_eexpr e)


let rec const_prop_expr (e: expr) =
   e

let constant_propagation_instr (i: cfg_node) : cfg_node =
    i

let constant_propagation_fun ({ cfgfunargs; cfgfunbody; cfgentry } as f: cfg_fun) =
  let ht = Hashtbl.map (fun n m ->
      constant_propagation_instr m
    ) cfgfunbody in
  { f with cfgfunbody = ht}

let constant_propagation_gdef = function
    Gfun f ->
    Gfun (constant_propagation_fun f)

let constant_propagation p =
  if !Options.no_cfg_constprop
  then p
  else assoc_map constant_propagation_gdef p

let pass_constant_propagation p =
  let cfg = constant_propagation p in
  record_compile_result "Constprop";
  dump (!cfg_dump >*> fun s -> s ^ "1") dump_cfg_prog cfg
    (call_dot "cfg-after-cstprop" "CFG after Constant Propagation");
  OK cfg
