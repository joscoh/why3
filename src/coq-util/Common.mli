open List0

val null : 'a1 list -> bool

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val tuple_eqb :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1*'a2) -> ('a1*'a2) ->
  bool
