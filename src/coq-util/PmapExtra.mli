open CommonOption
open Pmap
open Zmap

val pmap_ne_eqb :
  ('a1 -> 'a1 -> bool) -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap_ne -> bool

val pmap_eqb : ('a1 -> 'a1 -> bool) -> 'a1 coq_Pmap -> 'a1 coq_Pmap -> bool

val zmap_eqb : ('a1 -> 'a1 -> bool) -> 'a1 coq_Zmap -> 'a1 coq_Zmap -> bool
