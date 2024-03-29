open BinNums
open Base
open Fin_maps
open Numbers
open Option0

type __ = Obj.t

type 'a coq_Pmap_ne =
| PNode001 of 'a coq_Pmap_ne
| PNode010 of 'a
| PNode011 of 'a * 'a coq_Pmap_ne
| PNode100 of 'a coq_Pmap_ne
| PNode101 of 'a coq_Pmap_ne * 'a coq_Pmap_ne
| PNode110 of 'a coq_Pmap_ne * 'a
| PNode111 of 'a coq_Pmap_ne * 'a * 'a coq_Pmap_ne

type 'a coq_Pmap =
| PEmpty
| PNodes of 'a coq_Pmap_ne

val coq_PNode : 'a1 coq_Pmap -> 'a1 option -> 'a1 coq_Pmap -> 'a1 coq_Pmap

val coq_Pmap_ne_case :
  'a1 coq_Pmap_ne -> ('a1 coq_Pmap -> 'a1 option -> 'a1 coq_Pmap -> 'a2) ->
  'a2

val coq_Pmap_ne_lookup : (positive, 'a1, 'a1 coq_Pmap_ne) coq_Lookup

val coq_Pmap_lookup : (positive, 'a1, 'a1 coq_Pmap) coq_Lookup

val coq_Pmap_empty : 'a1 coq_Pmap coq_Empty

val coq_Pmap_ne_singleton : positive -> 'a1 -> 'a1 coq_Pmap_ne

val coq_Pmap_partial_alter_aux :
  (positive -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap) -> ('a1 option -> 'a1 option)
  -> positive -> 'a1 coq_Pmap -> 'a1 coq_Pmap

val coq_Pmap_ne_partial_alter :
  ('a1 option -> 'a1 option) -> positive -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap

val coq_Pmap_partial_alter : (positive, 'a1, 'a1 coq_Pmap) coq_PartialAlter

val coq_Pmap_ne_fmap : ('a1 -> 'a2) -> 'a1 coq_Pmap_ne -> 'a2 coq_Pmap_ne

val coq_Pmap_fmap : (__ -> __) -> __ coq_Pmap -> __ coq_Pmap

val coq_Pmap_omap_aux :
  ('a1 coq_Pmap_ne -> 'a2 coq_Pmap) -> 'a1 coq_Pmap -> 'a2 coq_Pmap

val coq_Pmap_ne_omap : ('a1 -> 'a2 option) -> 'a1 coq_Pmap_ne -> 'a2 coq_Pmap

val coq_Pmap_merge_aux :
  ('a1 coq_Pmap_ne -> 'a2 coq_Pmap_ne -> 'a3 coq_Pmap) -> ('a1 option -> 'a2
  option -> 'a3 option) -> 'a1 coq_Pmap -> 'a2 coq_Pmap -> 'a3 coq_Pmap

val coq_Pmap_ne_merge :
  ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 coq_Pmap_ne -> 'a2
  coq_Pmap_ne -> 'a3 coq_Pmap

val coq_Pmap_merge :
  (__ option -> __ option -> __ option) -> __ coq_Pmap -> __ coq_Pmap -> __
  coq_Pmap

val coq_Pmap_fold_aux :
  (positive -> 'a2 -> 'a1 coq_Pmap_ne -> 'a2) -> positive -> 'a2 -> 'a1
  coq_Pmap -> 'a2

val coq_Pmap_ne_fold :
  (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 coq_Pmap_ne -> 'a2

val coq_Pmap_fold : (positive -> 'a1 -> __ -> __) -> __ -> 'a1 coq_Pmap -> __
