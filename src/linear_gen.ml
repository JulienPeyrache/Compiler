open Batteries
open Rtl
open Linear
open Prog
open Utils
open Report
open Linear_print
open Options
open Linear_liveness

let succs_of_rtl_instr (i: rtl_instr) =
  match i with
  | Rtl.Rbranch (_, _, _, s1) -> [s1]
  | Rtl.Rjmp s -> [s]
  | _ -> []

let rec succs_of_rtl_instrs il : int list =
  List.concat (List.map succs_of_rtl_instr il)

(* effectue un tri topologique des blocs.  *)
let sort_blocks (nodes: (int, rtl_instr list) Hashtbl.t) entry =
  let rec add_block order n =
   (* TODO *)
   if List.mem n order then order else
   let rtl_liste = Hashtbl.find_option nodes n in
   match rtl_liste with 
   |Some(liste) -> let successeurs = succs_of_rtl_instrs liste in
   List.fold_left (fun ordre instruct -> add_block ordre instruct) (order@[n]) successeurs
  |None -> List.of_enum (Hashtbl.keys nodes) in
  add_block [] entry


  (* Explication de la fonction sort_blocks :
  On commence par ajouter le bloc d'entrée à la liste order.
  On regarde ensuite si le bloc d'entrée est dans la liste order, si c'est le cas on ne fait rien.
  Sinon on regarde si le bloc d'entrée est dans la table de hachage nodes, si c'est le cas on récupère la liste des instructions du bloc d'entrée.
  On récupère ensuite la liste des successeurs du bloc d'entrée.
  On ajoute ensuite le bloc d'entrée à la liste order.
  On ajoute ensuite les successeurs du bloc d'entrée à la liste order.
  On répète l'opération pour chaque successeur du bloc d'entrée.
  On répète l'opération pour chaque bloc de la liste order.
  On retourne la liste order.*)

(* Supprime les jumps inutiles (Jmp à un label défini juste en dessous). *)
let rec remove_useless_jumps (l: rtl_instr list) =
   (* TODO *)
   match l with
   |Rjmp(label1)::Rlabel(label2)::suite -> if label1 = label2 then (Rlabel(label2)::(remove_useless_jumps suite))
   else Rjmp(label1)::Rlabel(label2)::(remove_useless_jumps suite)
   |t::q -> t::(remove_useless_jumps q)
   |[] -> []


(* Remove labels that are never jumped to. *)
let remove_useless_labels (l: rtl_instr list) =
   (* TODO *)
   let labels_avec_jump = List.fold (fun ensemble rtlinstr -> match rtlinstr with |Rjmp(label) -> Set.add label ensemble |_ -> ensemble)
                          Set.empty l in
    let rec parcours liste = match liste with
    |Rlabel(label)::q -> if Set.mem label labels_avec_jump then Rlabel(label)::(parcours q) else parcours q
    |t::q -> t::(parcours q)
    |[] -> []
in parcours l

let linear_of_rtl_fun
    ({ rtlfunargs; rtlfunbody; rtlfunentry; rtlfuninfo }: rtl_fun) =
  let block_order = sort_blocks rtlfunbody rtlfunentry in
  let linearinstrs =
    Rjmp rtlfunentry ::
    List.fold_left (fun l n ->
        match Hashtbl.find_option rtlfunbody n with
        | None -> l
        | Some li -> l @ Rlabel(n) :: li
      ) [] block_order in
  { linearfunargs = rtlfunargs;
    linearfunbody =
      linearinstrs |> remove_useless_jumps |> remove_useless_labels;
    linearfuninfo = rtlfuninfo;
  }

let linear_of_rtl_gdef = function
    Gfun f -> Gfun (linear_of_rtl_fun f)

let linear_of_rtl r =
  assoc_map linear_of_rtl_gdef r

let pass_linearize rtl =
  let linear = linear_of_rtl rtl in
  let lives = liveness_linear_prog linear in
  dump !linear_dump (fun oc -> dump_linear_prog oc (Some lives)) linear
    (fun file () -> add_to_report "linear" "Linear" (Code (file_contents file)));
  OK (linear, lives)
