open Datatypes
open Base

type __ = Obj.t

type ('k, 'a, 'm) coq_MapFold =
  __ -> ('k -> 'a -> __ -> __) -> __ -> 'm -> __

val map_fold :
  ('a1, 'a2, 'a3) coq_MapFold -> ('a1 -> 'a2 -> 'a4 -> 'a4) -> 'a4 -> 'a3 ->
  'a4

val diag_None :
  ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3
  option

val map_insert :
  ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a2, 'a3) coq_Insert

val map_delete : ('a1, 'a2, 'a3) coq_PartialAlter -> ('a1, 'a3) coq_Delete

val map_singleton :
  ('a1, 'a2, 'a3) coq_PartialAlter -> 'a3 coq_Empty -> ('a1, 'a2, 'a3)
  coq_SingletonM

val map_size : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 coq_Size

val map_to_list : ('a1, 'a2, 'a3) coq_MapFold -> 'a3 -> ('a1*'a2) list
