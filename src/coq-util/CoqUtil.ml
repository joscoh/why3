open BinNums
open Byte
open CommonList
open Datatypes
open List0

(** val bits_to_pos : bool list -> positive **)

let rec bits_to_pos = function
| [] -> Coq_xH
| b::tl -> if b then Coq_xI (bits_to_pos tl) else Coq_xO (bits_to_pos tl)

(** val bittup_to_bits :
    (bool*(bool*(bool*(bool*(bool*(bool*(bool*bool))))))) -> bool list **)

let bittup_to_bits = function
| b1,p ->
  let b2,p0 = p in
  let b3,p1 = p0 in
  let b4,p2 = p1 in
  let b5,p3 = p2 in
  let b6,p4 = p3 in
  let b7,b8 = p4 in b1::(b2::(b3::(b4::(b5::(b6::(b7::(b8::[])))))))

(** val byte_to_bits : char -> bool list **)

let byte_to_bits b =
  bittup_to_bits (to_bits b)

(** val str_to_pos : string -> positive **)

let str_to_pos s =
  bits_to_pos
    (concat
      (map byte_to_bits
        ((fun s -> List.init (String.length s) (fun i -> s.[i])) s)))

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let map2 =
  map2

(** val fold_right2 :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3 option **)

let rec fold_right2 f l1 l2 x =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some x
           | _::_ -> None)
  | x1::t1 ->
    (match l2 with
     | [] -> None
     | x2::t2 -> option_map (f x1 x2) (fold_right2 f t1 t2 x))

(** val map_fold_left :
    ('a1 -> 'a2 -> 'a1*'a3) -> 'a1 -> 'a2 list -> 'a1*'a3 list **)

let map_fold_left f acc l =
  let res =
    fold_left (fun x e -> let y = f (fst x) e in (fst y),((snd y)::(snd x)))
      l (acc,[])
  in
  (fst res),(rev' (snd res))

(** val null : 'a1 list -> bool **)

let null =
  null

(** val opt_fold : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let opt_fold f d = function
| Some y -> f d y
| None -> d

(** val option_fold : 'a2 -> ('a1 -> 'a2) -> 'a1 option -> 'a2 **)

let option_fold none some o =
  opt_fold (fun _ -> some) none o

(** val list_find_opt : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let list_find_opt p l =
  fold_right (fun x acc -> if p x then Some x else acc) None l

(** val list_inb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let list_inb eq x l =
  existsb (fun y -> eq x y) l

type ('a, 'b, 'c) ocaml_tup3 = 'a * 'b * 'c

(** val rev_map_aux : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list **)

let rec rev_map_aux f accu = function
| [] -> accu
| a::l0 -> rev_map_aux f ((f a)::accu) l0

(** val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rev_map f l =
  rev_map_aux f [] l

(** val fun_flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let fun_flip f x y =
  f y x
