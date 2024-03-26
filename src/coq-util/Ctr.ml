open StateMonad

module MakeCtr =
 struct
  (** val ctr_ref : BigInt.t ref **)

  let ctr_ref =
    ref BigInt.zero

  (** val create : BigInt.t -> unit ctr **)

  let create =
    fun x -> ctr_ref := x

  (** val incr : unit -> unit ctr **)

  let incr _ =
    (ctr_ref := BigInt.succ !ctr_ref)

  (** val get : unit -> BigInt.t ctr **)

  let get _ =
    !ctr_ref
 end
