open BinNums
open CoqUtil
open IntFuncs
open Mysexplib.Std [@@warning "-33"]
open Number






type constant =
| ConstInt of int_constant
| ConstReal of real_constant
| ConstStr of string

(** val constant_eqb : constant -> constant -> bool **)

let constant_eqb c1 c2 =
  match c1 with
  | ConstInt i1 ->
    (match c2 with
     | ConstInt i2 -> int_constant_eqb i1 i2
     | _ -> false)
  | ConstReal r1 ->
    (match c2 with
     | ConstReal r2 -> real_constant_eqb r1 r2
     | _ -> false)
  | ConstStr s1 -> (match c2 with
                    | ConstStr s2 -> (=) s1 s2
                    | _ -> false)

(** val compare_const_aux : bool -> constant -> constant -> Stdlib.Int.t **)

let compare_const_aux structural c1 c2 =
  match c1 with
  | ConstInt i1 ->
    (match c2 with
     | ConstInt i2 ->
       let c =
         if structural
         then int_literal_kind_compare i1.il_kind i2.il_kind
         else Stdlib.Int.zero
       in
       lex_comp c (BigInt.compare i1.il_int i2.il_int)
     | _ -> Stdlib.Int.minus_one)
  | ConstReal r1 ->
    (match c2 with
     | ConstInt _ -> Stdlib.Int.one
     | ConstReal r2 ->
       let c =
         if structural
         then real_literal_kind_compare r1.rl_kind r2.rl_kind
         else Stdlib.Int.zero
       in
       lex_comp c (compare_real_aux structural r1.rl_real r2.rl_real)
     | ConstStr _ -> Stdlib.Int.minus_one)
  | ConstStr s1 ->
    (match c2 with
     | ConstStr s2 -> String.compare s1 s2
     | _ -> Stdlib.Int.one)

(** val str_hash : string -> BigInt.t **)

let str_hash s =
  ZCompat.of_Z_big (Zpos (str_to_pos s))

(** val constant_hash : constant -> BigInt.t **)

let constant_hash = function
| ConstInt i -> int_constant_hash i
| ConstReal r -> real_constant_hash r
| ConstStr s -> str_hash s

(** val int_const1 : int_literal_kind -> BigInt.t -> constant **)

let int_const1 k n =
  ConstInt { il_kind = k; il_int = n }

(** val int_const_of_int : Stdlib.Int.t -> constant **)

let int_const_of_int n =
  int_const1 ILitUnk (BigInt.of_int n)

(** val string_const : string -> constant **)

let string_const s =
  ConstStr s
(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)




(** Construction *)

(* type constant =
  | ConstInt  of int_constant
  | ConstReal of real_constant
  | ConstStr  of string
[@@deriving sexp] *)

let sexp_of_constant x =
  match x with
  | ConstInt i -> Sexplib0.Sexp.List [
    Sexplib0.Sexp.Atom "ConstInt";
    Number.sexp_of_int_constant i
  ]
  | ConstReal r -> Sexplib0.Sexp.List [
    Sexplib0.Sexp.Atom "ConstReal";
    sexp_of_real_constant r
  ] 
  | ConstStr s -> Sexplib0.Sexp.List [
    Sexplib0.Sexp.Atom "ConstStr";
    Sexplib0.Sexp_conv.sexp_of_string s
  ] 

let constant_of_sexp x =
  match x with
  | Sexplib0.Sexp.List [ Sexplib0.Sexp.Atom s; a] ->
    begin match s with
    | "ConstInt" -> ConstInt (int_constant_of_sexp a)
    | "ConstReal" -> ConstReal (real_constant_of_sexp a)
    | "ConstStr" -> ConstStr (Sexplib0.Sexp_conv.string_of_sexp a)
    | _ -> Sexplib0.Sexp_conv.of_sexp_error "constant_of_sexp" x
    end
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "constant_of_sexp" x

let compare_const ?(structural=true) c1 c2 =
  compare_const_aux structural c1 c2 
(* 
  match c1, c2 with
  | ConstInt { il_kind = k1; il_int = i1 }, ConstInt { il_kind = k2; il_int = i2 } ->
      let c = if structural then Stdlib.compare k1 k2 else 0 in
      if c <> 0 then c else BigInt.compare i1 i2
  | ConstReal { rl_kind = k1; rl_real = r1 }, ConstReal { rl_kind = k2; rl_real = r2 } ->
      let c = if structural then Stdlib.compare k1 k2 else 0 in
      if c <> 0 then c else compare_real ~structural r1 r2
  | _, _ ->
      Stdlib.compare c1 c2 *)

let int_const ?(il_kind=ILitUnk) n =
int_const1 il_kind n
  (* ConstInt { il_kind; il_int = n } *)

(* let int_const_of_int n =
  int_const (BigInt.of_int n) *)

let real_const ?(pow2 = BigInt.zero) ?(pow5 = BigInt.zero) i =
  ConstReal { rl_kind = RLitUnk; rl_real = real_value ~pow2 ~pow5 i }

let real_const_from_string ~radix ~neg ~int ~frac ~exp =
  ConstReal (real_literal ~radix ~neg ~int ~frac ~exp)

(* let string_const s =
  ConstStr s *)

type escape_map = char -> string

let default_escape c = match c with
  | '\\' -> "\\\\"
  | '\n' -> "\\n"
  | '\r' -> "\\r"
  | '\t' -> "\\t"
  | '\b' -> "\\b"
  | '\"'  -> "\\\""
  | '\032' .. '\126' -> Format.sprintf "%c" c
  | '\000' .. '\031'
  | '\127' .. '\255' -> Format.sprintf "\\x%02X" (Char.code c)

let unsupported_escape = fun _ -> assert false

let escape f s =
  let open Buffer in
  let b = create (String.length s) in
  String.iter (fun c -> add_string b (f c)) s;
  contents b

let print_string_constant string_escape fmt s =
  Format.fprintf fmt "\"%s\"" (escape string_escape s)

let print_string_def fmt s =
  print_string_constant default_escape fmt s

let print support string_escape fmt = function
  | ConstInt i  -> print_int_constant support fmt i
  | ConstReal r -> print_real_constant support fmt r
  | ConstStr s  -> print_string_constant string_escape fmt s

let print_def = print full_support default_escape
