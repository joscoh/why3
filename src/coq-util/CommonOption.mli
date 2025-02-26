open Datatypes
open List0

val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val isSome : 'a1 option -> bool

val isNone : 'a1 option -> bool

val option_eqb : ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool

val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list
