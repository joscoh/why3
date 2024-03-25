open Datatypes

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb eq l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: t1 ->
    (match l2 with
     | [] -> false
     | x2 :: t2 -> (&&) (eq x1 x2) (list_eqb eq t1 t2))

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

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

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f l1 l2 =
  match l1 with
  | [] -> []
  | x1 :: t1 ->
    (match l2 with
     | [] -> []
     | x2 :: t2 -> (f x1 x2) :: (map2 f t1 t2))

(** val fold_right2 :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option **)

let rec fold_right2 f l1 l2 accu =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some accu
           | _ :: _ -> None)
  | a1 :: l3 ->
    (match l2 with
     | [] -> None
     | a2 :: l4 -> option_map (f a1 a2) (fold_right2 f l3 l4 accu))

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _ :: _ -> false

(** val option_fold : 'a1 -> ('a2 -> 'a1) -> 'a2 option -> 'a1 **)

let option_fold none some = function
| Some x -> some x
| None -> none

(** val dec_from_eqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let dec_from_eqb f x y =
  let b = f x y in if b then true else false
