open CoqHashtbl
open Datatypes
open StateMonad
open Extmap

module type S =
 sig
  type key

  type value

  type t

  val create : Stdlib.Int.t -> (key, value, unit) hash_st

  val add : key -> value -> (key, value, unit) hash_st

  val find_opt : key -> (key, value, value option) hash_st
 end

module type TyMod =
 sig
  type t
 end

module Make =
 functor (X:TaggedType) ->
 functor (Y:TyMod) ->
 struct
  type key = X.t

  type value = Y.t

  type t = (key, value) hashtbl

  (** val hash_ref : (key, value) hash_unit **)

  let hash_ref : t ref =
    ref CoqHashtbl.create_hashtbl

  (** val create : Stdlib.Int.t -> (key, value, unit) hash_st **)

  let create _ =
    (fun x -> hash_ref := x) create_hashtbl

  (** val add : key -> value -> (key, value, unit) hash_st **)

  let add k v =
    (@@) (fun h -> (fun x -> hash_ref := x) (add_hashtbl X.tag h k v))
      !hash_ref

  (** val find_opt : key -> (key, value, value option) hash_st **)

  let find_opt k =
    (@@) (fun h ->
      
        (option_map snd
          (find_opt_hashtbl X.tag (fun x y ->  (X.equal x y)) h k))) !hash_ref
 end
