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
