open Datatypes
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val int_length : 'a1 list -> BigInt.t **)

let rec int_length = function
| [] -> BigInt.zero
| _::t -> BigInt.succ (int_length t)

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

(** val int_rect_aux :
    (BigInt.t -> __ -> 'a1) -> 'a1 -> (BigInt.t -> __ -> __ -> 'a1 -> 'a1) ->
    BigInt.t -> 'a1 **)

let rec int_rect_aux neg_case zero_case ind_case z =
  if BigInt.lt z BigInt.zero
  then neg_case z __
  else if BigInt.eq z BigInt.zero
       then zero_case
       else ind_case z __ __
              (int_rect_aux neg_case zero_case ind_case (BigInt.pred z))

(** val int_rect :
    (BigInt.t -> __ -> 'a1) -> 'a1 -> (BigInt.t -> __ -> __ -> 'a1 -> 'a1) ->
    BigInt.t -> 'a1 **)

let int_rect =
  int_rect_aux

(** val iota : BigInt.t -> BigInt.t list **)

let iota z =
  int_rect (fun _ _ -> []) [] (fun z0 _ _ rec0 -> z0::rec0) z

(** val iota2 : BigInt.t -> BigInt.t list **)

let iota2 z =
  rev (map BigInt.pred (iota z))

(** val lex_comp : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t **)

let lex_comp x1 x2 =
  if (fun x -> Stdlib.Int.equal x Stdlib.Int.zero) x1 then x2 else x1

(** val big_nth : 'a1 list -> BigInt.t -> 'a1 option **)

let big_nth l z =
  int_rect (fun _ _ _ -> None) (fun l0 ->
    match l0 with
    | [] -> None
    | x::_ -> Some x) (fun _ _ _ rec0 l0 ->
    match l0 with
    | [] -> None
    | _::t -> rec0 t) z l

(** val mapi : (BigInt.t -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f l =
  map (fun x -> f (fst x) (snd x)) (combine (iota2 (int_length l)) l)

(** val find_index :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> BigInt.t option **)

let rec find_index eqb l x =
  match l with
  | [] -> None
  | h::t ->
    if eqb h x
    then Some BigInt.zero
    else option_map BigInt.succ (find_index eqb t x)
