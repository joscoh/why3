open List0

type __ = Obj.t

type 'ty ctr = 'ty

type ('ty, 'ty2, 'ty3) hash_st = 'ty3

type ('k, 'v) hash_unit = (('k, 'v) CoqHashtbl.hashtbl) ref

type ('ty, 'ty2) hashcons_st = 'ty2

val hashcons_list : ('a1, 'a2) hashcons_st list -> ('a1, 'a2 list) hashcons_st

type 'k hashcons_unit = (BigInt.t * 'k CoqHashtbl.hashset) ref

type ('ty, 'ty2) errorHashconsT = 'ty2

val errorHashcons_list :
  ('a1, 'a2) errorHashconsT list -> ('a1, 'a2 list) errorHashconsT

type ('ty, 'ty2, 'ty3) hash_ctr = 'ty3


