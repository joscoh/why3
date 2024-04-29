open Monads
open State

module type Ctr =
 sig
  val create : (BigInt.t, unit) st

  val incr : unit -> (BigInt.t, unit) st

  val get : unit -> (BigInt.t, BigInt.t) st
 end

module type BigIntVal =
 sig
  val coq_val : BigInt.t
 end

module BigIntTy =
 functor (B:BigIntVal) ->
 struct
  type t = BigInt.t

  (** val initial : BigInt.t **)

  let initial =
    B.coq_val
 end

module MakeCtr =
 functor (B:BigIntVal) ->
 struct
  module B1 = BigIntTy(B)

  module St = MakeState(B1)

  (** val create : (BigInt.t, unit) st **)

  let create =
    St.create

  (** val incr : unit -> (BigInt.t, unit) st **)

  let incr _ =
    (@@) (fun i -> St.set (BigInt.succ i)) (St.get ())

  (** val get : unit -> (BigInt.t, BigInt.t) st **)

  let get _ =
    St.get ()
 end
