(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Set, Map, Hashtbl on ints and strings *)

module Int = struct
  type t = int
  let compare (x : int) y = Stdlib.compare x y
  let equal (x : int) y = x = y
  let hash  (x : int) = BigInt.of_int x
  let tag t = BigInt.of_int t
end

module Mint = Extmap.Make(Int)
module Sint = Extset.MakeOfMap(Mint)
module Hint = Exthtbl.Make(struct
  type t = Int.t
  let compare = Int.compare
  let equal = Int.equal
  let hash x = x
end)

module Str = struct
  type t = string
  (*JOSH TODO bad could overwrite*)
  let tag (s: string) : BigInt.t = (BigInt.of_int (Hashtbl.hash s))
end

module Mstr = Extmap.Make(Str)
module Sstr = Extset.MakeOfMap(Mstr)
module Hstr = Exthtbl.Make(struct
  type t    = String.t
  let hash  = (Hashtbl.hash : string -> int)
  let equal = ((=) : string -> string -> bool)
end)


module Float = struct
  type t = float
  (* JOSH TODO Same with hash*)
  let tag (x: float) : BigInt.t = BigInt.of_int (Exthtbl.hash x)
  let compare (x : float) y = Stdlib.compare x y
  let equal (x : float) y = x = y
  let hash  (x : float) = Exthtbl.hash x
end

module Mfloat = Extmap.Make(Float)
module Sfloat = Extset.MakeOfMap(Mfloat)
module Hfloat = Exthtbl.Make(Float)


(* Set, Map, Hashtbl on structures with a unique tag *)

module type TaggedType =
sig
  type t
  val tag : t -> BigInt.t
end

module type OrderedHashedType =
sig
  type t
  val hash : t -> BigInt.t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHashed (X : TaggedType) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = BigInt.compare (X.tag ts1) (X.tag ts2)
end

module TaggedList (X: TaggedType) =
struct
  type t = X.t list
  let tag = Hashcons.combine_big_list X.tag (BigInt.of_int 3)
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let eq = Lists.equal equ_ts
end

module OrderedHashedList (X : TaggedType) =
struct
  type t = X.t list
  let hash = Hashcons.combine_big_list X.tag (BigInt.of_int 3)
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = BigInt.compare (X.tag ts1) (X.tag ts2)
  let compare = Lists.compare cmp_ts
end

module OrderedIntHashed (X: OrderedHashedType) =
struct
type t = X.t
let hash x = BigInt.hash (X.hash x)
let equal = X.equal
let compare = X.compare
end

module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(X)
  module S = Extset.MakeOfMap(M)
  module O = OrderedIntHashed(T)
  module H = Exthtbl.Make(O)
end

module MakeTagged (X : Weakhtbl.Weakey) =
struct
  type t = X.t
  let tag t = Weakhtbl.tag_hash (X.tag t)
end

module MakeMSHW (X : Weakhtbl.Weakey) =
struct
  module Tg = MakeTagged(X)
  module T = OrderedHashed(Tg)
  module M = Extmap.Make(Tg)
  module S = Extset.MakeOfMap(M)
  module O = OrderedIntHashed(T)
  module H = Exthtbl.Make(O)
  module W = Weakhtbl.Make(X)
end
