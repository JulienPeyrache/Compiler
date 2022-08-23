open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
   |Eadd -> ( + )
   |Esub -> ( - ) 
   |Emul -> ( * )
   |Ediv -> ( / )
   |Emod -> (mod)
   |Eceq -> binop_bool_to_int (=)
   |Ecne -> binop_bool_to_int (<>)
   |Eclt -> binop_bool_to_int (<)
   |Ecgt -> binop_bool_to_int (>)
   |Ecle -> binop_bool_to_int (<=)
   |Ecge -> binop_bool_to_int (>=)
   |Exor -> fun  x y -> match (x,y) with 
                        |(0,0) -> 0
                        |(0, _ ) -> 1
                        |(_, 0) -> 1
                        | _ -> 0

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
  match u with
  |Eneg -> fun x -> -x

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
let rec eval_eexpr (oc : Format.formatter) (st : int state) (e : expr) (ep: eprog) : int res =
match e with
|Ebinop(b,e1,e2) -> 
  let x = eval_eexpr oc st e1 ep in
  let y = eval_eexpr oc st e2 ep in
  (match x,y with
  |OK x,OK y -> OK (eval_binop b x y)
  |Error s, _ -> Error s
  |_, Error s -> Error s)
|Eunop(u,e) -> 
  let x = eval_eexpr oc st e ep in
  (match x with
  |OK x -> OK (eval_unop u x)
  |Error s -> Error s)
|Eint n -> OK n
|Evar(s) -> (match Batteries.Hashtbl.find_option st.env s with
  |Some x -> OK x
  |None -> Error ("Variable non définie : "^s))
|Ecall(fname,el) -> let retour = (find_function ep fname >>= fun fonction -> eval_efun oc st fonction fname el ep)
   in(match retour with
      |OK(Some(ret), st') -> OK(ret)
      |OK(None, st) -> Error("Fonction "^fname^" ne renvoie rien")
      |Error s -> Error s)

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].
   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr (oc : Format.formatter) (st: int state) (instruction: instr) (ep : eprog): ((int option * int state) res) =
 match instruction with
|Ireturn e ->
   let x = eval_eexpr oc st e ep in
   (function
   |OK x -> OK (Some x, st)
   |Error msg -> Error msg) x
 |Iassign (s,e) ->
   let x = eval_eexpr oc st e ep in
   (match x with
   |OK x -> (Batteries.Hashtbl.replace st.env s x; OK (None, st))
   |Error msg -> Error msg)
|Iblock liste -> 
   (match liste with
   |[] -> OK (None, st)
   |ins::suite ->
     eval_einstr oc st ins ep >>= fun (ret, st') ->
     (match ret with
     |Some x -> OK(Some x, st')
     |None -> eval_einstr oc st' (Iblock(suite)) ep 
     )
   )
|Iif(e,i1,i2) ->
   let x = eval_eexpr oc st e ep in
   (match x with
   |OK x -> if x=0 then eval_einstr oc st i2 ep else eval_einstr oc st i1 ep 
   |Error msg -> Error msg)
|Iwhile(e,i) ->
   let x = eval_eexpr oc st e ep in
   (match x with
   |Error msg -> Error msg
   |OK x -> if x=0 then OK(None, st) 
            else eval_einstr oc st i ep >>= fun (ret, st') ->
               (match ret with
                  |Some _ -> OK (ret, st')
                  |None -> eval_einstr oc st' instruction ep ))
|Icall(fname,el) -> match find_function ep fname with 
                     |OK fonction -> eval_efun oc st fonction fname el ep
                     |Error msg -> if String.starts_with msg "Unknown function" then 
                        list_map_res (fun e -> eval_eexpr oc st e ep) el >>= fun params -> do_builtin oc st.mem fname params >>= fun intopt -> OK(intopt, st)
                                  else Error msg



(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun (oc : Format.formatter) (st: int state) ({ funargs; funbody}: efun)
    (fname: string) (vargs: expr list) (ep : eprog)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Batteries.Hashtbl.copy st.env in
  let env = Batteries.Hashtbl.create 17 in
  let vargs_int = list_map_res (fun e -> eval_eexpr oc st e ep) vargs in
  vargs_int >>= fun vargs_int ->
  match Batteries.List.iter2 (fun a v -> Batteries.Hashtbl.replace env a v) funargs vargs_int with
  | () ->
    eval_einstr oc { st with env } funbody ep >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (Batteries.List.length vargs) (Batteries.List.length funargs)
          )

(* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
   arguments [params].

   Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
   disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
   mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
   nos programmes.

   Renvoie:

   - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

   - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

   - [Error msg] lorsqu'une erreur survient.
   *)


let eval_eprog oc (ep: eprog) (memsize: int) (params: int list)
  : int option res =
  let st = init_state memsize in
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = Batteries.List.length f.funargs in
  let params = take n params in
  eval_efun oc st f "main" (List.map (fun x -> Eint x) params) ep >>= fun (v, st) ->
  OK v


