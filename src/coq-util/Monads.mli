open List0

type __ = Obj.t

type 'a errorM = 'a

val ignore : 'a1 errorM -> unit errorM

type ('a, 'b) st = 'b

val st_list : ('a1, 'a2) st list -> ('a1, 'a2 list) st

type ('a, 'b) errState = 'b

val errst_list : ('a1, 'a2) errState list -> ('a1, 'a2 list) errState

type ('k, 'v) hash_unit = (('k, 'v) CoqHashtbl.hashtbl) ref

type 'k hashcons_unit = (BigInt.t * 'k CoqHashtbl.hashset) ref
