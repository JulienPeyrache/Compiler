open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins
open Utils

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
   |Eadd -> fun  x y -> x + y
   |Esub -> fun  x y -> x - y
   |Emul -> fun  x y -> x * y
   |Ediv -> fun  x y -> x / y
   |Emod -> fun  x y -> x mod y 
   |Eceq  -> fun  x y -> (x=y)
   |Ecne -> fun  x y -> (x<>y)
   |Eclt  -> fun  x y -> (x<y)
   |Ecgt  -> fun  x y -> (x>y)
   |Ecle  -> fun  x y -> (x<=y)
   |Ecge  -> fun  x y -> (x>=y)
   (* EXOR RESTE À COMPLÉTER*)
   | _ -> fun x y -> 0

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
  match u with
  |Eneg -> fun x -> -x
   | _ -> fun x -> 0

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
let rec eval_eexpr st (e : expr) : int res =
match e with
|Ebinop(b,e1,e2) -> 
  let x = eval_eexpr st e1 in
  let y = eval_eexpr st e2 in
  (match x,y with
  |Ok x,Ok y -> Ok (eval_binop b x y)
  |Error s, _ -> Error s
  |_, Error s -> Error s)
|Eunop(u,e) -> 
  let x = eval_eexpr st e in
  (match x with
  |Ok x -> Ok (eval_unop u x)
  |Error s -> Error s)
|Eint n -> Ok n
|Evar(s) -> match Hashtbl.find_option st.env s with
  |Some x -> Ok x
  |None -> Error ("Variable non définie : "^s)
|_ -> Error "eval_eexpr not implemented yet."

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
let rec eval_einstr oc (st: int state) (ins: instr) :
  (int option * int state) res =
match ins with
|Iassign(s,e) ->
   let x = eval_eexpr st e in
   match x with
   |Ok x -> (None, {st with env = Hashtbl.replace st.env s x})
   |Error msg -> Error msg
|Iprint(e) ->
   let x = eval_eexpr st e in
   match x with
   |Ok x -> (None, st)
   |Error msg -> Error msg
|Ireturn(e) ->
   let x = eval_eexpr st e in
   match x with
   |Ok x -> (Some x, st)
   |Error msg -> Error msg
|Iblock liste -> match liste with
   |[] -> (None, st)
   |ins::suite ->
     let (ret, st') = eval_einstr oc st ins in
     match ret with
     |Some x -> (Some x, st')
     |None -> eval_einstr oc st' Iblock(suite)
|Iif(e,i1,i2) ->
   let x = eval_eexpr st e in
   match x with
   |Ok x -> if x=0 then eval_einstr oc st i2 else eval_einstr oc st i1
   |Error msg -> Error msg
|Iwhile(e,i) ->
   let x = eval_eexpr st e in
   match x with
   |Error msg -> Error msg
   |Ok x -> if x=0 then (None, st) else 
       let (ret, st') = eval_einstr oc st i in
       match ret with
       |Some _ -> (ret, st')
       |None -> eval_einstr oc st' ins
|_ -> Error "eval_einstr not implemented yet."


(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
let eval_efun oc (st: int state) ({ funargs; funbody}: efun)
    (fname: string) (vargs: int list)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let env = Hashtbl.create 17 in
  match List.iter2 (fun a v -> Hashtbl.replace env a v) funargs vargs with
  | () ->
    eval_einstr oc { st with env } funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length funargs)
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
  let n = List.length f.funargs in
  let params = take n params in
  List.iter2 (fun a v -> Hashtbl.replace st.env a v) f.funargs params >>= fun () ->
  eval_efun oc st f "main" params >>= fun (v, st) ->
  OK v
