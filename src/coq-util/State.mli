open Monads

type 'a st_ty = 'a ref

module type ModTy =
 sig
  type t

  val default : t
 end

module MakeState :
 functor (T:ModTy) ->
 sig
  val st_ref : T.t st_ty

  val create : T.t -> (T.t, unit) st

  val get : unit -> (T.t, T.t) st

  val set : T.t -> (T.t, unit) st
 end
