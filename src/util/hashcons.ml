open CoqHashtbl
open List0
open Monads
open State

module type HashedType =
 sig
  type t

  val equal : t -> t -> bool

  val hash : t -> BigInt.t

  val tag : BigInt.t -> t -> t
 end

module type S =
 sig
  type t

  val add_builtins : t list -> BigInt.t -> (t hashcons_ty, unit) st

  val hashcons : t -> (t hashcons_ty, t) st

  val unique : t -> (t hashcons_ty, t) st

  val iter : (t -> unit) -> (t hashcons_ty, unit) st

  val stats :
    unit -> (t hashcons_ty,
    ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t)
    st
 end

module Make =
 functor (H:HashedType) ->
 struct
  type t = H.t

  module HashconsTy =
   struct
    type t = BigInt.t * H.t hashset

    (** val initial : BigInt.t * H.t hashset **)

    let initial =
      (BigInt.zero, create_hashset)
   end

  module HashconsSt = MakeState(HashconsTy)

  (** val add_builtins : t list -> BigInt.t -> (t hashcons_ty, unit) st **)

  let add_builtins l next =
    (@@) (fun x ->
      let (_, h) = x in
      let h' = fold_right (fun x0 acc -> add_hashset H.hash acc x0) h l in
      HashconsSt.set (next, h')) (HashconsSt.get ())

  (** val incr : unit -> (H.t hashcons_ty, unit) st **)

  let incr _ =
    (@@) (fun x -> let (i, h) = x in HashconsSt.set ((BigInt.succ i), h))
      (HashconsSt.get ())

  (** val unique : t -> (H.t hashcons_ty, t) st **)

  let unique d =
    (@@) (fun x ->
      let (i, _) = x in
      let d0 = H.tag i d in (@@) (fun _ -> (fun x -> x) d0) (incr ()))
      (HashconsSt.get ())

  (** val hashcons : t -> (H.t hashcons_ty, t) st **)

  let hashcons d =
    (@@) (fun x ->
      let (i, h) = x in
      let o = find_opt_hashset H.hash H.equal h d in
      (match o with
       | Some k -> (fun x -> x) k
       | None ->
         let d1 = H.tag i d in
         (@@) (fun _ -> (@@) (fun _ -> (fun x -> x) d1) (incr ()))
           (HashconsSt.set (i, (add_hashset H.hash h d1)))))
      (HashconsSt.get ())

  (** val iter : (t -> unit) -> (H.t hashcons_ty, unit) st **)

  let iter f =
    (@@) (fun x -> let (_, h) = x in (fun x -> x) (iter_hashset_unsafe f h))
      (HashconsSt.get ())

  (** val stats :
      unit -> (H.t hashcons_ty,
      ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t)
      st **)

  let stats _ =
    (fun x -> x) (((((Stdlib.Int.zero, Stdlib.Int.zero), Stdlib.Int.zero),
      Stdlib.Int.zero), Stdlib.Int.zero), Stdlib.Int.zero)
 end

(** val combine : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t **)

let combine acc n =
  Stdlib.Int.add (Stdlib.Int.mul acc 65599) n

(** val combine_list :
    ('a1 -> Stdlib.Int.t) -> Stdlib.Int.t -> 'a1 list -> Stdlib.Int.t **)

let combine_list f acc l =
  fold_left (fun acc0 x -> combine acc0 (f x)) l acc

(** val combine2 :
    Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t **)

let combine2 acc n1 n2 =
  combine (combine acc n1) n2

(** val combine3 :
    Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t ->
    Stdlib.Int.t **)

let combine3 acc n1 n2 n3 =
  combine (combine2 acc n1 n2) n3

(** val combine_option :
    ('a1 -> Stdlib.Int.t) -> 'a1 option -> Stdlib.Int.t **)

let combine_option h = function
| Some s -> h s
| None -> Stdlib.Int.minus_one

(** val combine_pair :
    ('a1 -> Stdlib.Int.t) -> ('a2 -> Stdlib.Int.t) -> ('a1 * 'a2) ->
    Stdlib.Int.t **)

let combine_pair h1 h2 x =
  combine (h1 (fst x)) (h2 (snd x))

(** val combine_big : BigInt.t -> BigInt.t -> BigInt.t **)

let combine_big acc n =
  BigInt.add (BigInt.mul_int 65599 acc) n

(** val combine2_big : BigInt.t -> BigInt.t -> BigInt.t -> BigInt.t **)

let combine2_big acc n1 n2 =
  combine_big (combine_big acc n1) n2

(** val combine_big_list :
    ('a1 -> BigInt.t) -> BigInt.t -> 'a1 list -> BigInt.t **)

let combine_big_list f acc l =
  fold_left (fun acc0 x -> combine_big acc0 (f x)) l acc

(** val combine_big_option : ('a1 -> BigInt.t) -> 'a1 option -> BigInt.t **)

let combine_big_option h = function
| Some s -> h s
| None -> (BigInt.of_int (-1))
