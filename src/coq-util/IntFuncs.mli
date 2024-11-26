open Datatypes
open List0

type __ = Obj.t

val int_length : 'a1 list -> BigInt.t

val option_compare :
  ('a1 -> 'a1 -> Stdlib.Int.t) -> 'a1 option -> 'a1 option -> Stdlib.Int.t

val int_rect_aux :
  (BigInt.t -> __ -> 'a1) -> 'a1 -> (BigInt.t -> __ -> __ -> 'a1 -> 'a1) ->
  BigInt.t -> 'a1

val int_rect :
  (BigInt.t -> __ -> 'a1) -> 'a1 -> (BigInt.t -> __ -> __ -> 'a1 -> 'a1) ->
  BigInt.t -> 'a1

val iota : BigInt.t -> BigInt.t list

val iota2 : BigInt.t -> BigInt.t list

val lex_comp : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t

val big_nth : 'a1 list -> BigInt.t -> 'a1 option

val mapi : (BigInt.t -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val find_index : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> BigInt.t option

val change_nth : 'a1 list -> 'a1 -> BigInt.t -> 'a1 list

val init : BigInt.t -> (BigInt.t -> 'a1) -> 'a1 list
