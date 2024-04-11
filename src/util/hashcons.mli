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
  
      val hashcons : t -> t
        (** [hashcons n] hash-cons value [n] i.e. returns any existing
            value in the table equal to [n], if any; otherwise, creates
            a new value with function [tag], stores it in the table and
            returns it. *)
  
      val unique : t -> t
        (** [unique n] registers the new value [n] without hash-consing.
            This should be used in case where the value is guaranteed to
            be unique, i.e. not equal to any other value, old or future.
            Unique values are not visited by [iter]. *)
  
      val iter : (t -> unit) -> unit
        (** [iter f] iterates [f] over all elements of the table. *)
  
        val stats :
        unit ->
        ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t
        (** Return statistics on the table.  The numbers are, in order:
            table length, number of entries, sum of bucket lengths,
            smallest bucket length, median bucket length, biggest
            bucket length. *)
    end
  
  module Make(H : HashedType) : (S with type t = H.t)
  
  
  (* helpers *)
  
  val combine : int -> int -> int
  val combine2 : int -> int -> int -> int
  val combine3 : int -> int -> int -> int -> int
  val combine_list : ('a -> int) -> int -> 'a list -> int
  val combine_option : ('a -> int) -> 'a option -> int
  val combine_pair : ('a -> int) -> ('b -> int) -> 'a * 'b -> int


val combine_option : ('a1 -> Stdlib.Int.t) -> 'a1 option -> Stdlib.Int.t

val combine_big : BigInt.t -> BigInt.t -> BigInt.t

val combine2_big : BigInt.t -> BigInt.t -> BigInt.t -> BigInt.t

val combine_big_list : ('a1 -> BigInt.t) -> BigInt.t -> 'a1 list -> BigInt.t

val combine_big_option : ('a1 -> BigInt.t) -> 'a1 option -> BigInt.t
  
