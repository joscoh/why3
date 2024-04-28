open Monads
open State

module BigIntTy :
 sig
  type t = BigInt.t

  val default : BigInt.t
 end

module MakeCtr :
 sig
  module St :
   sig
    val st_ref : BigIntTy.t st_ty

    val create : BigIntTy.t -> (BigIntTy.t, unit) st

    val get : unit -> (BigIntTy.t, BigIntTy.t) st

    val set : BigIntTy.t -> (BigIntTy.t, unit) st
   end

  val create : BigInt.t -> (BigInt.t, unit) st

  val incr : unit -> (BigInt.t, unit) st

  val get : unit -> (BigInt.t, BigInt.t) st
 end
