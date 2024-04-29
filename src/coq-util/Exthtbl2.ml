open CoqHashtbl
open Datatypes
open Monads
open State
open Extmap

module type S =
 sig
  type key

  type value

  val create : Stdlib.Int.t -> ((key, value) hashtbl, unit) st

  val add : key -> value -> ((key, value) hashtbl, unit) st

  val find_opt : key -> ((key, value) hashtbl, value option) st

  val memo : (key -> value) -> key -> ((key, value) hashtbl, value) st
 end

module type ModTySimpl =
 sig
  type t
 end

module MakeExthtbl =
 functor (X:TaggedType) ->
 functor (Y:ModTySimpl) ->
 struct
  type key = X.t

  type value = Y.t

  module HashtblTy =
   struct
    type t = (key, value) hashtbl

    (** val initial : (key, value) hashtbl **)

    let initial =
      create_hashtbl
   end

  module HashSt = MakeState(HashtblTy)

  (** val create : Stdlib.Int.t -> ((key, value) hashtbl, unit) st **)

  let create _ =
    HashSt.create

  (** val add : key -> value -> ((key, value) hashtbl, unit) st **)

  let add k v =
    (@@) (fun h -> HashSt.set (add_hashtbl X.tag h k v)) (HashSt.get ())

  (** val find_opt : key -> ((key, value) hashtbl, value option) st **)

  let find_opt k =
    (@@) (fun h ->
      (fun x -> x) (option_map snd (find_opt_hashtbl X.tag X.equal h k)))
      (HashSt.get ())

  (** val memo : (key -> value) -> key -> ((key, value) hashtbl, value) st **)

  let memo f k =
    (@@) (fun h ->
      match find_opt_hashtbl X.tag X.equal h k with
      | Some v -> (fun x -> x) (snd v)
      | None ->
        let y = f k in
        (@@) (fun _ -> (fun x -> x) y) (HashSt.set (add_hashtbl X.tag h k y)))
      (HashSt.get ())
 end
