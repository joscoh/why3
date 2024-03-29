open Monads

module MakeCtr :
 sig
  val ctr_ref : BigInt.t ref

  val create : BigInt.t -> (BigInt.t, unit) st

  val incr : unit -> (BigInt.t, unit) st

  val get : unit -> (BigInt.t, BigInt.t) st
 end
