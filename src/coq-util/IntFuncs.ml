
(** val int_length : 'a1 list -> BigInt.t **)

let rec int_length = function
| [] -> BigInt.zero
| _ :: t -> BigInt.succ (int_length t)

(** val option_compare :
    ('a1 -> 'a1 -> Stdlib.Int.t) -> 'a1 option -> 'a1 option -> Stdlib.Int.t **)

let option_compare cmp o1 o2 =
  match o1 with
  | Some v0 -> (match o2 with
                | Some v1 -> cmp v0 v1
                | None -> Stdlib.Int.one)
  | None ->
    (match o2 with
     | Some _ -> Stdlib.Int.minus_one
     | None -> Stdlib.Int.zero)
