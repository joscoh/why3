open Datatypes
open List0

type __ = Obj.t

val null : 'a1 list -> bool

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val fold_left2 :
  ('a3 -> 'a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option

val dep_map : ('a1 -> __ -> 'a2) -> 'a1 list -> 'a2 list

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val inb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val uniq : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

val unionb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list
