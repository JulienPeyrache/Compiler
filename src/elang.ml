open Ast
open Batteries
open Prog
open Utils

type binop = Eadd | Emul | Emod | Exor | Ediv | Esub (* binary operations *)
           | Eclt | Ecle | Ecgt | Ecge | Eceq | Ecne (* comparisons *)
type unop = Eneg

type expr =
    Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Eint of int
  | Evar of string
  | Echar of char
  | Ecall of string * expr list


type instr =
  | Iassign of string * expr
  | Iif of expr * instr * instr
  | Iwhile of expr * instr
  | Iblock of instr list
  | Ireturn of expr
  | Iprint of expr
  | Icall of string * expr list

type efun = {
  funargs: ( string ) list;
  funbody: instr;
  funvartyp : (string, typ) Hashtbl.t;
  funrettype : typ;
}

type eprog = efun prog
