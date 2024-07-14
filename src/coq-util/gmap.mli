open BinNums
open Datatypes
open Base
open Countable
open Numbers

type __ = Obj.t

type 'a gmap_dep_ne =
| GNode001 of 'a gmap_dep_ne
| GNode010 of 'a
| GNode011 of 'a * 'a gmap_dep_ne
| GNode100 of 'a gmap_dep_ne
| GNode101 of 'a gmap_dep_ne * 'a gmap_dep_ne
| GNode110 of 'a gmap_dep_ne * 'a
| GNode111 of 'a gmap_dep_ne * 'a * 'a gmap_dep_ne

type 'a gmap_dep =
| GEmpty
| GNodes of 'a gmap_dep_ne

type ('k, 'a) gmap = { gmap_car : 'a gmap_dep }

val gmap_dep_ne_case :
  'a1 gmap_dep_ne -> ('a1 gmap_dep -> (__*'a1) option -> 'a1 gmap_dep -> 'a2)
  -> 'a2

val gmap_empty :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2) gmap coq_Empty

val gmap_dep_ne_singleton : positive -> 'a1 -> 'a1 gmap_dep_ne

val gmap_partial_alter_aux :
  (positive -> __ -> 'a1 gmap_dep_ne -> 'a1 gmap_dep) -> ('a1 option -> 'a1
  option) -> positive -> 'a1 gmap_dep -> 'a1 gmap_dep

val gmap_dep_ne_partial_alter :
  ('a1 option -> 'a1 option) -> positive -> 'a1 gmap_dep_ne -> 'a1 gmap_dep

val gmap_dep_partial_alter :
  ('a1 option -> 'a1 option) -> positive -> 'a1 gmap_dep -> 'a1 gmap_dep

val gmap_partial_alter :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
  gmap) coq_PartialAlter

val gmap_fold_aux :
  (positive -> 'a2 -> 'a1 gmap_dep_ne -> 'a2) -> positive -> 'a2 -> 'a1
  gmap_dep -> 'a2

val gmap_dep_ne_fold :
  (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 gmap_dep_ne -> 'a2

val gmap_dep_fold :
  (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 gmap_dep -> 'a2

val gmap_fold :
  ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 -> 'a2 -> __ -> __)
  -> __ -> ('a1, 'a2) gmap -> __
