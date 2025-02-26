open Datatypes
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

(** val fold_left2 :
    ('a3 -> 'a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option **)

let rec fold_left2 f l1 l2 accu =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some accu
           | _::_ -> None)
  | a1::l3 ->
    (match l2 with
     | [] -> None
     | a2::l4 -> fold_left2 f l3 l4 (f accu a1 a2))

(** val dep_map : ('a1 -> __ -> 'a2) -> 'a1 list -> 'a2 list **)

let rec dep_map f = function
| [] -> []
| x::tl -> (f x __)::(dep_map f tl)

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb eq l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | x1::t1 ->
    (match l2 with
     | [] -> false
     | x2::t2 -> (&&) (eq x1 x2) (list_eqb eq t1 t2))

(** val inb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let inb eq x l =
  existsb (eq x) l

(** val uniq : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec uniq eq = function
| [] -> true
| x::xs -> (&&) (negb (inb eq x xs)) (uniq eq xs)

(** val unionb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list **)

let unionb eq l1 l2 =
  fold_right (fun x acc -> if inb eq x acc then acc else x::acc) l2 l1
