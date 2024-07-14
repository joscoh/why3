open Datatypes
open List0
open Base
open Fin_maps
open Zmap

module type HashedType =
 sig
  type t

  val equal : t -> t -> bool

  val hash : t -> BigInt.t
 end

type ('key, 'a) hashtbl = ('key*'a) list coq_Zmap

val create_hashtbl : ('a1, 'a2) hashtbl

val find_opt_hashtbl :
  ('a1 -> BigInt.t) -> ('a1 -> 'a1 -> bool) -> ('a1, 'a2) hashtbl -> 'a1 ->
  ('a1*'a2) option

val add_hashtbl :
  ('a1 -> BigInt.t) -> ('a1, 'a2) hashtbl -> 'a1 -> 'a2 -> ('a1, 'a2) hashtbl

val comb : unit -> unit -> unit

val comb_list : unit list -> unit

val iter_hashtbl_unsafe : ('a1, 'a2) hashtbl -> ('a1 -> 'a2 -> unit) -> unit

type 'key hashset = ('key, unit) hashtbl

val create_hashset : 'a1 hashset

val find_opt_hashset :
  ('a1 -> BigInt.t) -> ('a1 -> 'a1 -> bool) -> 'a1 hashset -> 'a1 -> 'a1
  option

val add_hashset : ('a1 -> BigInt.t) -> 'a1 hashset -> 'a1 -> 'a1 hashset

val iter_hashset_unsafe : ('a1 -> unit) -> 'a1 hashset -> unit
