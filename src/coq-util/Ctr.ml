open StateMonad0

module MakeCtr =
 struct
  (** val ctr_ref : BigInt.t ref **)

  let ctr_ref =
    ref BigInt.zero

  (** val create : BigInt.t -> (BigInt.t, unit) st **)

  let create =
    fun x -> ctr_ref := x

  (** val incr : unit -> (BigInt.t, unit) st **)

  let incr _ =
    (ctr_ref := BigInt.succ !ctr_ref)

  (** val get : unit -> (BigInt.t, BigInt.t) st **)

  let get _ =
    !ctr_ref
 end
