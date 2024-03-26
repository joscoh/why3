open CoqHashtbl
open List0
open StateMonad

module type HashedType =
 sig
  type t

  val equal : t -> t -> bool

  val hash : t -> BigInt.t

  val tag : BigInt.t -> t -> t
 end

module type S =
 sig
  type t

  val hashcons : t -> (t, t) hashcons_st

  val unique : t -> (t, t) hashcons_st

  val iter : (t -> unit) -> (t, unit) hashcons_st

  val stats :
    unit -> (t, ((((Int.t * Int.t) * Int.t) * Int.t) * Int.t) * Int.t)
    hashcons_st
 end

module Make :
 functor (H:HashedType) ->
 sig
  type t = H.t

  val hash_st : H.t hashcons_unit

  val unique : t -> (H.t, t) hashcons_st

  val hashcons : t -> (H.t, t) hashcons_st

  val iter : (t -> unit) -> (H.t, unit) hashcons_st

  val stats :
    unit -> (H.t, ((((Int.t * Int.t) * Int.t) * Int.t) * Int.t) * Int.t)
    hashcons_st
 end

val combine : Int.t -> Int.t -> Int.t

val combine_list : ('a1 -> Int.t) -> Int.t -> 'a1 list -> Int.t

val combine_big : BigInt.t -> BigInt.t -> BigInt.t

val combine2_big : BigInt.t -> BigInt.t -> BigInt.t -> BigInt.t

val combine_big_list : ('a1 -> BigInt.t) -> BigInt.t -> 'a1 list -> BigInt.t

val combine_big_option : ('a1 -> BigInt.t) -> 'a1 option -> BigInt.t
