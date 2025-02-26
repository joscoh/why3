open Datatypes
open List0

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind o f =
  match o with
  | Some x -> f x
  | None -> None

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

(** val isNone : 'a1 option -> bool **)

let isNone x =
  negb (isSome x)

(** val option_eqb :
    ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool **)

let option_eqb eq o1 o2 =
  match o1 with
  | Some x -> (match o2 with
               | Some y -> eq x y
               | None -> false)
  | None -> (match o2 with
             | Some _ -> false
             | None -> true)

(** val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let omap f l =
  fold_right (fun x acc -> match f x with
                           | Some y -> y::acc
                           | None -> acc) [] l
