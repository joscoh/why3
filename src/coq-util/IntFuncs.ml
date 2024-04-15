
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

(** val iota_aux : BigInt.t -> BigInt.t list **)

let rec iota_aux z =
  if BigInt.lt z BigInt.zero
  then []
  else if BigInt.eq z BigInt.zero then [] else z :: (iota_aux (BigInt.pred z))

(** val iota : BigInt.t -> BigInt.t list **)

let iota =
  iota_aux

(** val lex_comp : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t **)

let lex_comp x1 x2 =
  if (fun x -> Stdlib.Int.equal x Stdlib.Int.zero) x1 then x2 else x1
