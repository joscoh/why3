
(** val tuple_eqb :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) ->
    ('a1 * 'a2) -> bool **)

let tuple_eqb eq1 eq2 x y =
  (&&) (eq1 (fst x) (fst y)) (eq2 (snd x) (snd y))
