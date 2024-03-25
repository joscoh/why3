
val negb : bool -> bool

type nat =
| O
| S of nat

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type comparison =
| Eq
| Lt
| Gt

val coq_CompOpp : comparison -> comparison
