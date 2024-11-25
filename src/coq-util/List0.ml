open Datatypes

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x::l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

(** val partition : ('a1 -> bool) -> 'a1 list -> 'a1 list*'a1 list **)

let rec partition f = function
| [] -> [],[]
| x::tl -> let g,d = partition f tl in if f x then (x::g),d else g,(x::d)

(** val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl -> (match l' with
              | [] -> []
              | y::tl' -> (x,y)::(combine tl tl'))
