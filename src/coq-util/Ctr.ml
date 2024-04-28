open Monads
open State

module BigIntTy =
 struct
  type t = BigInt.t

  (** val default : BigInt.t **)

  let default =
    BigInt.zero
 end

module MakeCtr =
 struct
  module St = MakeState(BigIntTy)

  (** val create : BigInt.t -> (BigInt.t, unit) st **)

  let create =
    St.create

  (** val incr : unit -> (BigInt.t, unit) st **)

  let incr _ =
    (@@) (fun i -> St.set (BigInt.succ i)) (St.get ())

  (** val get : unit -> (BigInt.t, BigInt.t) st **)

  let get _ =
    St.get ()
 end
