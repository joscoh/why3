open CoqHashtbl
open List0
open StateMonad

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

  val hashcons : t -> (t, t) hashcons_st

  val unique : t -> (t, t) hashcons_st

  val iter : (t -> unit) -> (t, unit) hashcons_st

  val stats :
    unit -> (t, ((((Int.t * Int.t) * Int.t) * Int.t) * Int.t) * Int.t)
    hashcons_st
 end

module Make =
 functor (H:HashedType) ->
 struct
  type t = H.t

  (** val hash_st : H.t hashcons_unit **)

  let hash_st =
    ref (BigInt.one, CoqHashtbl.create_hashset)

  (** val unique : t -> (H.t, t) hashcons_st **)

  let unique d =
    (@@) (fun i ->
      let d0 = H.tag i d in
      (@@) (fun _ ->  d0)
        (let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old))))
      (fst !hash_st)

  (** val hashcons : t -> (H.t, t) hashcons_st **)

  let hashcons d =
    (@@) (fun o ->
      match o with
      | Some k ->  k
      | None ->
        (@@) (fun i ->
          let d1 = H.tag i d in
          (@@) (fun _ ->
            (@@) (fun _ ->  d1)
              (let old = !hash_st in
    hash_st := (BigInt.succ (fst old), (snd old))))
            ((fun _ k -> let old = !hash_st in
              hash_st := (fst old, CoqHashtbl.add_hashset H.hash (snd old) k))
              H.hash d1)) (fst !hash_st))
      ((fun _ _ k -> CoqHashtbl.find_opt_hashset H.hash H.equal (snd !hash_st) k)
        H.hash H.equal d)

  (** val iter : (t -> unit) -> (H.t, unit) hashcons_st **)

  let iter f =
    (@@) (fun h ->  (iter_hashset_unsafe f h)) (snd !hash_st)

  (** val stats :
      unit -> (H.t, ((((Int.t * Int.t) * Int.t) * Int.t) * Int.t) * Int.t)
      hashcons_st **)

  let stats _ =
     (((((Int.zero, Int.zero), Int.zero), Int.zero), Int.zero), Int.zero)
 end

(** val combine : Int.t -> Int.t -> Int.t **)

let combine acc n =
  Int.add (Int.mul acc 65599) n

(** val combine_list : ('a1 -> Int.t) -> Int.t -> 'a1 list -> Int.t **)

let combine_list f acc l =
  fold_left (fun acc0 x -> combine acc0 (f x)) l acc

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
