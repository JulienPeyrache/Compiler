open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins

let rec eval_cfgexpr (oc : Format.formatter) st (e: expr) (cp : cprog): int res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr oc st e1 cp >>= fun v1 ->
    eval_cfgexpr oc st e2 cp >>= fun v2 ->
    let v = eval_binop b v1 v2 in
    OK v
  | Eunop(u, e) ->
    eval_cfgexpr oc st e cp>>= fun v1 ->
    let v = (eval_unop u v1) in
    OK v
  | Eint i -> OK i
  | Evar s ->
    (begin match Hashtbl.find_option st.env s with
      | Some v -> OK v
      | None -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end)
  | Ecall(funname, args) -> find_function cp funname >>= fun f ->
    let n = List.length f.cfgfunargs in
    let params = take n args in
    list_map_res (fun expr -> eval_cfgexpr oc st expr cp) params >>= 
    fun params -> eval_cfgfun oc st funname f params cp >>= fun (v_opt, st) -> match v_opt with |None -> Error "Funcall but no return" |Some(v) -> OK(v)
   

and eval_cfginstr (oc : Format.formatter) (st : int state) ht (n: int) (cp : cprog): (int * int state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr oc st ht succ cp
    | Cassign(v, e, succ) ->
      eval_cfgexpr oc st e cp>>= fun i ->
      Hashtbl.replace st.env v i;
      eval_cfginstr oc st ht succ cp
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr oc st cond cp >>= fun i ->
      if i = 0 then eval_cfginstr oc st ht i2 cp else eval_cfginstr oc st ht i1 cp
    | Creturn(e) ->
      eval_cfgexpr oc st e cp>>= fun e ->
      OK (e, st)
    | Ccall(s, args, succ) -> (match find_function cp s with 
        | OK f -> let n = List.length f.cfgfunargs in
        let params = take n args in
        list_map_res (fun expr -> eval_cfgexpr oc st expr cp) params >>= 
        fun params -> eval_cfgfun oc st s f params cp >>= fun (v, st) ->
        eval_cfginstr oc st ht succ cp
        | Error msg-> if String.starts_with msg "Unknown function" then 
                      list_map_res (fun expr -> eval_cfgexpr oc st expr cp) args >>= fun params -> do_builtin oc st.mem s params >>= fun v-> eval_cfginstr oc st ht succ cp
                     else Error msg )
and eval_cfgfun oc st cfgfunname { cfgfunargs;
                                      cfgfunbody;
                                      cfgentry} (vargs : int list) (cp : cprog) =
  let st' = { st with env = Hashtbl.create 17 } in
  match List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs with
  | () -> eval_cfginstr oc st' cfgfunbody cfgentry cp >>= fun (v, st') ->
    OK (Some(v), {st' with env = st.env})
  | exception Invalid_argument _ ->
    Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length cfgfunargs)
          )

let eval_cfgprog oc cp memsize params =
  let st = init_state memsize in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st "main" f params cp >>= fun (v, st) ->
  OK v


