open List0

val int_length : 'a1 list -> BigInt.t

val option_compare :
  ('a1 -> 'a1 -> Stdlib.Int.t) -> 'a1 option -> 'a1 option -> Stdlib.Int.t

val iota_aux : BigInt.t -> BigInt.t list

val iota : BigInt.t -> BigInt.t list

val iota2 : BigInt.t -> BigInt.t list

val lex_comp : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t


