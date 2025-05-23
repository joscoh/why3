open CoqHashtbl
open List0
open Monads
open State

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

  val add_builtins : t list -> BigInt.t -> (t hashcons_ty, unit) st

  val hashcons : t -> (t hashcons_ty, t) st

  val unique : t -> (t hashcons_ty, t) st

  val iter : (t -> unit) -> (t hashcons_ty, unit) st

  val stats :
    unit -> (t hashcons_ty,
    ((((Stdlib.Int.t*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)
    st
 end

module Make :
 functor (H:HashedType) ->
 sig
  type t = H.t

  module HashconsTy :
   sig
    type t = H.t hashcons_ty

    val initial : H.t hashcons_ty
   end

  module HashconsSt :
   sig
    val st_ref : HashconsTy.t st_ty

    val create : (HashconsTy.t, unit) st

    val get : unit -> (HashconsTy.t, HashconsTy.t) st

    val set : HashconsTy.t -> (HashconsTy.t, unit) st

    val runState : (HashconsTy.t, 'a1) st -> 'a1
   end

  val add_builtins : t list -> BigInt.t -> (t hashcons_ty, unit) st

  val incr : unit -> (H.t hashcons_ty, unit) st

  val unique : t -> (H.t hashcons_ty, t) st

  val hashcons : t -> (H.t hashcons_ty, t) st

  val iter : (t -> unit) -> (H.t hashcons_ty, unit) st

  val stats :
    unit -> (H.t hashcons_ty,
    ((((Stdlib.Int.t*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)*Stdlib.Int.t)
    st
 end

val combine : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t

val combine_list :
  ('a1 -> Stdlib.Int.t) -> Stdlib.Int.t -> 'a1 list -> Stdlib.Int.t

val combine2 : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t

val combine3 :
  Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t

val combine_option : ('a1 -> Stdlib.Int.t) -> 'a1 option -> Stdlib.Int.t

val combine_pair :
  ('a1 -> Stdlib.Int.t) -> ('a2 -> Stdlib.Int.t) -> ('a1*'a2) -> Stdlib.Int.t

val combine_big : BigInt.t -> BigInt.t -> BigInt.t

val combine2_big : BigInt.t -> BigInt.t -> BigInt.t -> BigInt.t

val combine_big_list : ('a1 -> BigInt.t) -> BigInt.t -> 'a1 list -> BigInt.t

val combine_big_option : ('a1 -> BigInt.t) -> 'a1 option -> BigInt.t
