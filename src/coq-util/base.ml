open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_Empty = 'a

(** val empty : 'a1 coq_Empty -> 'a1 **)

let empty empty0 =
  empty0

type 'm coq_MBind = __ -> __ -> (__ -> 'm) -> 'm -> 'm

(** val mbind : 'a1 coq_MBind -> ('a2 -> 'a1) -> 'a1 -> 'a1 **)

let mbind mBind x x0 =
  Obj.magic mBind __ __ x x0

type 'm coq_FMap = __ -> __ -> (__ -> __) -> 'm -> 'm

(** val fmap : 'a1 coq_FMap -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let fmap fMap x x0 =
  Obj.magic fMap __ __ x x0

type ('k, 'a, 'm) coq_Lookup = 'k -> 'm -> 'a option

(** val lookup : ('a1, 'a2, 'a3) coq_Lookup -> 'a1 -> 'a3 -> 'a2 option **)

let lookup lookup0 =
  lookup0

type ('k, 'a, 'm) coq_SingletonM = 'k -> 'a -> 'm

(** val singletonM : ('a1, 'a2, 'a3) coq_SingletonM -> 'a1 -> 'a2 -> 'a3 **)

let singletonM singletonM0 =
  singletonM0

type ('k, 'a, 'm) coq_Insert = 'k -> 'a -> 'm -> 'm

(** val insert : ('a1, 'a2, 'a3) coq_Insert -> 'a1 -> 'a2 -> 'a3 -> 'a3 **)

let insert insert0 =
  insert0

type ('k, 'm) coq_Delete = 'k -> 'm -> 'm

(** val delete : ('a1, 'a2) coq_Delete -> 'a1 -> 'a2 -> 'a2 **)

let delete delete0 =
  delete0

type ('k, 'a, 'm) coq_PartialAlter =
  ('a option -> 'a option) -> 'k -> 'm -> 'm

(** val partial_alter :
    ('a1, 'a2, 'a3) coq_PartialAlter -> ('a2 option -> 'a2 option) -> 'a1 ->
    'a3 -> 'a3 **)

let partial_alter partialAlter =
  partialAlter

type 'm coq_Merge =
  __ -> __ -> __ -> (__ option -> __ option -> __ option) -> 'm -> 'm -> 'm

(** val merge :
    'a1 coq_Merge -> ('a2 option -> 'a3 option -> 'a4 option) -> 'a1 -> 'a1
    -> 'a1 **)

let merge merge0 x x0 x1 =
  Obj.magic merge0 __ __ __ x x0 x1

type 'c coq_Size = 'c -> nat
