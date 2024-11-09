
val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val tuple_eqb :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1*'a2) -> ('a1*'a2) ->
  bool
