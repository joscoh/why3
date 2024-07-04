open BinNums
open Byte
open Datatypes
open List0

(** val bits_to_pos : bool list -> positive **)

let rec bits_to_pos = function
| [] -> Coq_xH
| b :: tl -> if b then Coq_xI (bits_to_pos tl) else Coq_xO (bits_to_pos tl)

(** val bittup_to_bits :
    (bool * (bool * (bool * (bool * (bool * (bool * (bool * bool))))))) ->
    bool list **)

let bittup_to_bits = function
| (b1, p) ->
  let (b2, p0) = p in
  let (b3, p1) = p0 in
  let (b4, p2) = p1 in
  let (b5, p3) = p2 in
  let (b6, p4) = p3 in
  let (b7, b8) = p4 in
  b1 :: (b2 :: (b3 :: (b4 :: (b5 :: (b6 :: (b7 :: (b8 :: [])))))))

(** val byte_to_bits : char -> bool list **)

let byte_to_bits b =
  bittup_to_bits (to_bits b)

(** val str_to_pos : string -> positive **)

let str_to_pos s =
  bits_to_pos
    (concat
      (map byte_to_bits
        ((fun s -> List.init (String.length s) (fun i -> s.[i])) s)))

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

let rec fold_right2 f l1 l2 base =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some base
           | _ :: _ -> None)
  | x1 :: t1 ->
    (match l2 with
     | [] -> None
     | x2 :: t2 -> option_map (f x1 x2) (fold_right2 f t1 t2 base))

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _ :: _ -> false

(** val combineWith :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec combineWith f l1 l2 =
  match l1 with
  | [] -> []
  | x1 :: xs ->
    (match l2 with
     | [] -> []
     | y1 :: ys -> (f x1 y1) :: (combineWith f xs ys))

(** val option_fold : 'a1 -> ('a2 -> 'a1) -> 'a2 option -> 'a1 **)

let option_fold none some = function
| Some x -> some x
| None -> none

(** val map_fold_left :
    ('a1 -> 'a2 -> 'a1 * 'a3) -> 'a1 -> 'a2 list -> 'a1 * 'a3 list **)

let map_fold_left f acc l =
  let res =
    fold_left (fun x e ->
      let y = f (fst x) e in ((fst y), ((snd y) :: (snd x)))) l (acc, [])
  in
  ((fst res), (rev' (snd res)))

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind x f =
  match x with
  | Some y -> f y
  | None -> None

(** val list_find_opt : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let list_find_opt p l =
  fold_right (fun x acc -> if p x then Some x else acc) None l

type ('a, 'b, 'c) ocaml_tup3 = 'a * 'b * 'c
