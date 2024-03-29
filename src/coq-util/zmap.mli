open Basics
open BinNums
open Base
open Fin_maps
open Option0
open Pmap

type __ = Obj.t

type 'a coq_Zmap = { coq_Zmap_0 : 'a option; coq_Zmap_pos : 'a coq_Pmap;
                     coq_Zmap_neg : 'a coq_Pmap }

val coq_Zmap_empty : 'a1 coq_Zmap coq_Empty

val coq_Zmap_lookup : (coq_Z, 'a1, 'a1 coq_Zmap) coq_Lookup

val coq_Zmap_partial_alter : (coq_Z, 'a1, 'a1 coq_Zmap) coq_PartialAlter

val coq_Zmap_fmap : (__ -> __) -> __ coq_Zmap -> __ coq_Zmap

val coq_Zmap_merge :
  (__ option -> __ option -> __ option) -> __ coq_Zmap -> __ coq_Zmap -> __
  coq_Zmap

val coq_Zmap_fold : (coq_Z -> 'a1 -> __ -> __) -> __ -> 'a1 coq_Zmap -> __
