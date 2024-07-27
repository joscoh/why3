open CoqHashtbl
open List0

type __ = Obj.t

type 'a errorM = 'a

(** val errorM_list : 'a1 errorM list -> 'a1 list errorM **)

let errorM_list l =
  fold_right (fun x acc -> (@@) (fun h -> (@@) (fun t ->  (h::t)) acc) x)
    ( []) l

(** val ignore : 'a1 errorM -> unit errorM **)

let ignore x =
  (@@) (fun _ ->  ()) x

type ('a, 'b) st = 'b

(** val st_list : ('a1, 'a2) st list -> ('a1, 'a2 list) st **)

let st_list l =
  fold_right (fun x acc ->
    (@@) (fun h -> (@@) (fun t -> (fun x -> x) (h::t)) acc) x)
    ((fun x -> x) []) l

type ('a, 'b) errState = 'b

(** val errst_list : ('a1, 'a2) errState list -> ('a1, 'a2 list) errState **)

let errst_list l =
  fold_right (fun x acc ->
    (@@) (fun h -> (@@) (fun t -> (fun x -> x) (h::t)) acc) x)
    ((fun x -> x) []) l

type 'k hashcons_ty = { hashcons_ctr : BigInt.t; hashcons_hash : 'k hashset }

(** val get_hashcons : 'a1 hashcons_ty -> BigInt.t*'a1 hashset **)

let get_hashcons h =
  h.hashcons_ctr,h.hashcons_hash

(** val foldr_err :
    ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM **)

let rec foldr_err f l x =
  match l with
  | [] ->  x
  | h::t -> (@@) (fun i -> f i h) (foldr_err f t x)

(** val foldl_err :
    ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM **)

let rec foldl_err f l x =
  match l with
  | [] ->  x
  | h::t -> (@@) (fun j -> foldl_err f t j) (f x h)

(** val fold_left2_err :
    ('a3 -> 'a1 -> 'a2 -> 'a3 errorM) -> 'a3 -> 'a1 list -> 'a2 list -> 'a3
    option errorM **)

let rec fold_left2_err f accu l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] ->  (Some accu)
           | _::_ ->  None)
  | a1::l3 ->
    (match l2 with
     | [] ->  None
     | a2::l4 -> (@@) (fun x -> fold_left2_err f x l3 l4) (f accu a1 a2))

(** val iter_err : ('a1 -> unit errorM) -> 'a1 list -> unit errorM **)

let iter_err f l =
  foldl_err (fun _ -> f) l ()

(** val iter2_err :
    ('a1 -> 'a2 -> unit errorM) -> 'a1 list -> 'a2 list -> unit errorM **)

let iter2_err f l1 l2 =
  (@@) (fun o ->
    match o with
    | Some x ->  x
    | None -> raise (Invalid_argument "iter2"))
    (fold_left2_err (fun _ -> f) () l1 l2)

(** val foldl_st :
    ('a2 -> 'a3 -> ('a1, 'a2) st) -> 'a3 list -> 'a2 -> ('a1, 'a2) st **)

let rec foldl_st f l x =
  match l with
  | [] -> (fun x -> x) x
  | h::t -> (@@) (fun j -> foldl_st f t j) (f x h)

(** val foldr_errst :
    ('a3 -> 'a2 -> ('a1, 'a2) errState) -> 'a2 -> 'a3 list -> ('a1, 'a2)
    errState **)

let rec foldr_errst f base = function
| [] -> (fun x -> x) base
| h::t -> (@@) (fun r -> f h r) (foldr_errst f base t)

(** val foldl_errst :
    ('a2 -> 'a3 -> ('a1, 'a2) errState) -> 'a3 list -> 'a2 -> ('a1, 'a2)
    errState **)

let rec foldl_errst f l x =
  match l with
  | [] -> (fun x -> x) x
  | h::t -> (@@) (fun j -> foldl_errst f t j) (f x h)

(** val fold_left2_errst :
    ('a3 -> 'a1 -> 'a2 -> ('a4, 'a3) errState) -> 'a3 -> 'a1 list -> 'a2 list
    -> ('a4, 'a3 option) errState **)

let rec fold_left2_errst f accu l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] ->  ( (Some accu))
           | _::_ ->  ( None))
  | a1::l3 ->
    (match l2 with
     | [] ->  ( None)
     | a2::l4 -> (@@) (fun x -> fold_left2_errst f x l3 l4) (f accu a1 a2))

(** val map2_errst :
    ('a1 -> 'a2 -> ('a4, 'a3) errState) -> 'a1 list -> 'a2 list -> ('a4, 'a3
    list option) errState **)

let rec map2_errst f l1 l2 =
  match l1 with
  | [] ->
    (match l2 with
     | [] -> (fun x -> x) (Some [])
     | _::_ -> (fun x -> x) None)
  | x1::t1 ->
    (match l2 with
     | [] -> (fun x -> x) None
     | x2::t2 ->
       (@@) (fun y ->
         (@@) (fun o ->
           match o with
           | Some ys -> (fun x -> x) (Some (y::ys))
           | None -> (fun x -> x) None) (map2_errst f t1 t2)) (f x1 x2))

(** val map_join_left_errst :
    'a2 -> ('a1 -> ('a3, 'a2) errState) -> ('a2 -> 'a2 -> ('a3, 'a2)
    errState) -> 'a1 list -> ('a3, 'a2) errState **)

let map_join_left_errst d map join = function
| [] -> (fun x -> x) d
| x::xl ->
  (@@) (fun y ->
    foldl_errst (fun acc x0 -> (@@) (fun l1 -> join acc l1) (map x0)) xl y)
    (map x)
