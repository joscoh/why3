open StateMonad

module MakeCtr :
 sig
  val ctr_ref : BigInt.t ref

  val create : BigInt.t -> unit ctr

  val incr : unit ctr

  val get : BigInt.t ctr
 end
