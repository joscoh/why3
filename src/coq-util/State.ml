open Monads

type 'a st_ty = 'a ref

module type ModTy =
 sig
  type t

  val default : t
 end

module MakeState =
 functor (T:ModTy) ->
 struct
  (** val st_ref : T.t st_ty **)

  let st_ref =
    ref T.default

  (** val create : T.t -> (T.t, unit) st **)

  let create =
    (fun x -> st_ref := x)

  (** val get : unit -> (T.t, T.t) st **)

  let get _ =
    !st_ref

  (** val set : T.t -> (T.t, unit) st **)

  let set =
    (fun x -> st_ref := x)
 end
