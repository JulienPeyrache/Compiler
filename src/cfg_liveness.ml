open Batteries
open Cfg
open Prog
open Utils

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) =
   (* TODO *)
   match e with
   |Evar(s) -> Set.singleton s
   |Eint(i) -> Set.empty
   |Eunop(u,exp) -> vars_in_expr exp
   |Ebinop(b,e1,e2) -> Set.union (vars_in_expr e1) (vars_in_expr e2)

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
   (* TODO *)
   match node with
   | Cassign(v,e,s) -> Set.remove v (Set.union (vars_in_expr e) live_after)
   | Creturn(e) -> Set.union (vars_in_expr e) live_after
   | Cprint(e,i) -> Set.union (vars_in_expr e) live_after
   | Ccmp(e, i1, i2) -> Set.union (vars_in_expr e) live_after
   | Cnop(i) -> live_after

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives: (int, string Set.t) Hashtbl.t) : string Set.t =
   (* TODO *)
   match (Hashtbl.find cfg n) with 
   |(Cnop succ) -> (Hashtbl.find lives succ) 
   |(Cprint (_, succ)) -> (Hashtbl.find lives succ) 
   |(Cassign (_, _, succ)) -> (Hashtbl.find lives succ) 
   |(Creturn _) -> Set.empty   
   |(Ccmp (_, s1, s2)) -> Set.union (Hashtbl.find lives s1) (Hashtbl.find lives s2)
   

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
   let lives = Hashtbl.create 17 in
     (* TODO *)
 lives

   

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)


let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in
     (* TODO *)
 lives
