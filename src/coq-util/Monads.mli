open CoqHashtbl
open List0

type __ = Obj.t

type 'a errorM = 'a

val errorM_list : 'a1 errorM list -> 'a1 list errorM

val ignore : 'a1 errorM -> unit errorM

type ('a, 'b) st = 'b

val st_list : ('a1, 'a2) st list -> ('a1, 'a2 list) st

type ('a, 'b) errState = 'b

val errst_list : ('a1, 'a2) errState list -> ('a1, 'a2 list) errState

type 'k hashcons_ty = { hashcons_ctr : BigInt.t; hashcons_hash : 'k hashset }

val get_hashcons : 'a1 hashcons_ty -> BigInt.t*'a1 hashset

val foldr_err : ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM

val foldl_err : ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM

val fold_left2_err :
  ('a3 -> 'a1 -> 'a2 -> 'a3 errorM) -> 'a3 -> 'a1 list -> 'a2 list -> 'a3
  option errorM

val iter_err : ('a1 -> unit errorM) -> 'a1 list -> unit errorM

val iter2_err :
  ('a1 -> 'a2 -> unit errorM) -> 'a1 list -> 'a2 list -> unit errorM

val foldl_st :
  ('a2 -> 'a3 -> ('a1, 'a2) st) -> 'a3 list -> 'a2 -> ('a1, 'a2) st

val foldl_errst :
  ('a2 -> 'a3 -> ('a1, 'a2) errState) -> 'a3 list -> 'a2 -> ('a1, 'a2)
  errState

val fold_left2_errst :
  ('a3 -> 'a1 -> 'a2 -> ('a4, 'a3) errState) -> 'a3 -> 'a1 list -> 'a2 list
  -> ('a4, 'a3 option) errState

val map_join_left_errst :
  'a2 -> ('a1 -> ('a3, 'a2) errState) -> ('a2 -> 'a2 -> ('a3, 'a2) errState)
  -> 'a1 list -> ('a3, 'a2) errState
