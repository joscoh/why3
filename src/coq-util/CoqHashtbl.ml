open Datatypes
open List0
open Base
open Fin_maps
open Zmap

module type HashedType =
 sig
  type t

  val equal : t -> t -> bool

  val hash : t -> BigInt.t
 end

type ('key, 'a) hashtbl = ('key*'a) list coq_Zmap

(** val create_hashtbl : ('a1, 'a2) hashtbl **)

let create_hashtbl =
  coq_Zmap_empty

(** val find_opt_hashtbl :
    ('a1 -> BigInt.t) -> ('a1 -> 'a1 -> bool) -> ('a1, 'a2) hashtbl -> 'a1 ->
    ('a1*'a2) option **)

let find_opt_hashtbl hash0 eqb m k =
  match lookup coq_Zmap_lookup (ZCompat.to_Z_big (hash0 k)) m with
  | Some l1 -> find (fun x -> eqb k (fst x)) l1
  | None -> None

(** val add_hashtbl :
    ('a1 -> BigInt.t) -> ('a1, 'a2) hashtbl -> 'a1 -> 'a2 -> ('a1, 'a2)
    hashtbl **)

let add_hashtbl hash0 m k v =
  let val0 = fun k1 -> ZCompat.to_Z_big (hash0 k1) in
  (match lookup coq_Zmap_lookup (ZCompat.to_Z_big (hash0 k)) m with
   | Some l1 ->
     insert (map_insert coq_Zmap_partial_alter) (val0 k) ((k,v)::l1) m
   | None -> insert (map_insert coq_Zmap_partial_alter) (val0 k) ((k,v)::[]) m)

(** val comb : unit -> unit -> unit **)

let comb _ x2 =
  x2

(** val comb_list : unit list -> unit **)

let comb_list l =
  fold_right comb () l

(** val iter_hashtbl_unsafe :
    ('a1, 'a2) hashtbl -> ('a1 -> 'a2 -> unit) -> unit **)

let iter_hashtbl_unsafe m f =
  Obj.magic coq_Zmap_fold (fun _ l acc ->
    Obj.magic comb (comb_list (map (fun t0 -> f (fst t0) (snd t0)) l)) acc)
    () m

type 'key hashset = ('key, unit) hashtbl

(** val create_hashset : 'a1 hashset **)

let create_hashset =
  create_hashtbl

(** val find_opt_hashset :
    ('a1 -> BigInt.t) -> ('a1 -> 'a1 -> bool) -> 'a1 hashset -> 'a1 -> 'a1
    option **)

let find_opt_hashset hash0 eqb m k =
  option_map fst (find_opt_hashtbl hash0 eqb m k)

(** val add_hashset :
    ('a1 -> BigInt.t) -> 'a1 hashset -> 'a1 -> 'a1 hashset **)

let add_hashset hash0 m k =
  add_hashtbl hash0 m k ()

(** val iter_hashset_unsafe : ('a1 -> unit) -> 'a1 hashset -> unit **)

let iter_hashset_unsafe f m =
  iter_hashtbl_unsafe m (fun k _ -> f k)
