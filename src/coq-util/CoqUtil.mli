open Datatypes

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val isSome : 'a1 option -> bool

val option_eqb : ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val fold_right2 :
  ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option

val null : 'a1 list -> bool

val option_fold : 'a1 -> ('a2 -> 'a1) -> 'a2 option -> 'a1

val dec_from_eqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool
