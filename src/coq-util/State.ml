open Monads

type 'a st_ty = 'a ref

module type ModTy =
 sig
  type t

  val initial : t
 end

module MakeState =
 functor (T:ModTy) ->
 struct
  (** val st_ref : T.t st_ty **)

  let st_ref =
    ref T.initial

  (** val create : (T.t, unit) st **)

  let create =
    (fun x -> st_ref := x) T.initial

  (** val get : unit -> (T.t, T.t) st **)

  let get _ =
    !st_ref

  (** val set : T.t -> (T.t, unit) st **)

  let set =
    (fun x -> st_ref := x)

  (** val runState : (T.t, 'a1) st -> 'a1 **)

  let runState s =
    (fun _ x -> st_ref := T.initial; x) T.initial s
 end
