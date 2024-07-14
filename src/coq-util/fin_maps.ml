open Datatypes
open Base

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('k, 'a, 'm) coq_MapFold =
  __ -> ('k -> 'a -> __ -> __) -> __ -> 'm -> __

(** val map_fold :
    ('a1, 'a2, 'a3) coq_MapFold -> ('a1 -> 'a2 -> 'a4 -> 'a4) -> 'a4 -> 'a3
    -> 'a4 **)

let map_fold mapFold x x0 x1 =
  Obj.magic mapFold __ x x0 x1

(** val diag_None :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option **)

let diag_None f mx my =
  match mx with
  | Some _ -> f mx my
  | None -> (match my with
             | Some _ -> f mx my
             | None -> None)

(** val map_insert :
    ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a2, 'a3) coq_Insert **)

let map_insert h i x =
  partial_alter h (fun _ -> Some x) i

(** val map_delete :
    ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a3) coq_Delete **)

let map_delete h =
  partial_alter h (fun _ -> None)

(** val map_singleton :
    ('a1, 'a2, 'a3) coq_PartialAlter -> 'a3 coq_Empty -> ('a1, 'a2, 'a3)
    coq_SingletonM **)

let map_singleton h h0 i x =
  insert (map_insert h) i x (empty h0)

(** val map_size : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 coq_Size **)

let map_size h =
  map_fold h (fun _ _ x -> S x) O

(** val map_to_list : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 -> ('a1*'a2) list **)

let map_to_list h =
  map_fold h (fun i x x0 -> (i,x)::x0) []
