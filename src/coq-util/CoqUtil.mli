open BinNums
open Byte
open CommonList
open Datatypes
open List0

val bits_to_pos : bool list -> positive

val bittup_to_bits :
  (bool*(bool*(bool*(bool*(bool*(bool*(bool*bool))))))) -> bool list

val byte_to_bits : char -> bool list

val str_to_pos : string -> positive

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val fold_right2 :
  ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option

val map_fold_left : ('a1 -> 'a2 -> 'a1*'a3) -> 'a1 -> 'a2 list -> 'a1*'a3 list

val null : 'a1 list -> bool

val opt_fold : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_fold : 'a2 -> ('a1 -> 'a2) -> 'a1 option -> 'a2

val list_find_opt : ('a1 -> bool) -> 'a1 list -> 'a1 option

val list_inb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

type ('a, 'b, 'c) ocaml_tup3 = 'a * 'b * 'c

val rev_map_aux : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list

val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fun_flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3
