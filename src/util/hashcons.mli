open CoqHashtbl
open List0
open Monads

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

  val hashcons : t -> (BigInt.t * t hashset, t) st

  val unique : t -> (BigInt.t * t hashset, t) st

  val iter : (t -> unit) -> (BigInt.t * t hashset, unit) st

  val stats :
    unit -> (BigInt.t * t hashset,
    ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t)
    st
 end

module Make :
 functor (H:HashedType) ->
 sig
  type t = H.t

  val hash_st : H.t hashcons_unit

  val unique : t -> (BigInt.t * H.t hashset, t) st

  val hashcons : t -> (BigInt.t * H.t hashset, t) st

  val iter : (t -> unit) -> (BigInt.t * H.t hashset, unit) st

  val stats :
    unit -> (BigInt.t * H.t hashset,
    ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t)
    st
 end

val combine : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t

val combine_list :
  ('a1 -> Stdlib.Int.t) -> Stdlib.Int.t -> 'a1 list -> Stdlib.Int.t

val combine_big : BigInt.t -> BigInt.t -> BigInt.t

val combine2_big : BigInt.t -> BigInt.t -> BigInt.t -> BigInt.t

val combine_big_list : ('a1 -> BigInt.t) -> BigInt.t -> 'a1 list -> BigInt.t

val combine_big_option : ('a1 -> BigInt.t) -> 'a1 option -> BigInt.t
