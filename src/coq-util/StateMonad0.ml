open List0

type __ = Obj.t

type ('a, 'b) st = 'b

(** val st_list : ('a1, 'a2) st list -> ('a1, 'a2 list) st **)

let st_list l =
  fold_right (fun x acc ->
    (@@) (fun h -> (@@) (fun t -> (fun x -> x) (h :: t)) acc) x)
    ((fun x -> x) []) l

type ('a, 'b) errState = 'b

(** val errst_list : ('a1, 'a2) errState list -> ('a1, 'a2 list) errState **)

let errst_list l =
  fold_right (fun x acc -> (@@) (fun h -> (@@) (fun t ->  (h :: t)) acc) x)
    ( []) l

type ('k, 'v) hash_unit = (('k, 'v) CoqHashtbl.hashtbl) ref

type 'k hashcons_unit = (BigInt.t * 'k CoqHashtbl.hashset) ref
