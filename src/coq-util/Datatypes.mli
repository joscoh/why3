
val negb : bool -> bool

type nat =
| O
| S of nat

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val coq_CompOpp : comparison -> comparison
