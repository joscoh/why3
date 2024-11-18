open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _::_ -> false

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f l1 l2 =
  match l1 with
  | [] -> []
  | x1::t1 -> (match l2 with
               | [] -> []
               | x2::t2 -> (f x1 x2)::(map2 f t1 t2))

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind o f =
  match o with
  | Some x -> f x
  | None -> None

(** val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let omap f l =
  fold_right (fun x acc -> match f x with
                           | Some y -> y::acc
                           | None -> acc) [] l

(** val tuple_eqb :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1*'a2) -> ('a1*'a2) ->
    bool **)

let tuple_eqb eq1 eq2 x y =
  (&&) (eq1 (fst x) (fst y)) (eq2 (snd x) (snd y))

(** val dep_map : ('a1 -> __ -> 'a2) -> 'a1 list -> 'a2 list **)

let rec dep_map f = function
| [] -> []
| x::tl -> (f x __)::(dep_map f tl)
