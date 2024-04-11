open CoqHashtbl
open List0
open Monads

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

  val hashcons : t -> (BigInt.t * t hashset, t) st

  val unique : t -> (BigInt.t * t hashset, t) st

  val iter : (t -> unit) -> (BigInt.t * t hashset, unit) st

  val stats :
    unit -> (BigInt.t * t hashset,
    ((((Stdlib.Int.t * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t) * Stdlib.Int.t)
    st
 end

module Make =
 functor (H:HashedType) ->
 struct
  type t = H.t

  (** val hash_st : H.t hashcons_unit **)

  let hash_st =
    ref (BigInt.one, CoqHashtbl.create_hashset)

  (** val unique : t -> (BigInt.t * H.t hashset, t) st **)
  let unique d =
    (@@) (fun i ->
      let d0 = H.tag i d in
      (@@) (fun _ -> (fun x -> x) d0)
        (let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old))))
      (fst !hash_st)
  (** val hashcons : t -> (BigInt.t * H.t hashset, t) st **)

  let hashcons d =
    (@@) (fun o ->
      match o with
      | Some k -> (fun x -> x) k
      | None ->
        (@@) (fun i ->
          let d1 = H.tag i d in
          (@@) (fun _ ->
            (@@) (fun _ -> (fun x -> x) d1)
              (let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old))))
            ((fun _ k -> let old = !hash_st in
              hash_st := (fst old, CoqHashtbl.add_hashset H.hash (snd old) k))
              H.hash d1)) (fst !hash_st))
      ((fun _ _ k -> CoqHashtbl.find_opt_hashset H.hash H.equal (snd !hash_st) k)
        H.hash H.equal d)

  (** val iter : (t -> unit) -> (BigInt.t * H.t hashset, unit) st **)

  let iter f =
    (@@) (fun h -> (fun x -> x) (iter_hashset_unsafe f h)) (snd !hash_st)

  (** val stats :
      unit -> (BigInt.t * H.t hashset,
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
