open BinNums
open Ctr
open CoqUtil
open Weakhtbl
open Wstdlib
open Datatypes
open Loc
open Monads
open Specif
open Pmap
open Zmap
open CommonOption











type attribute = { attr_string : string; attr_tag : BigInt.t }

(** val attr_string : attribute -> string **)

let attr_string a =
  a.attr_string

(** val attr_tag : attribute -> BigInt.t **)

let attr_tag a =
  a.attr_tag

(** val attr_eqb : attribute -> attribute -> bool **)

let attr_eqb a1 a2 =
  (&&) ((=) a1.attr_string a2.attr_string) (BigInt.eq a1.attr_tag a2.attr_tag)

module AttrTag =
 struct
  module AttrDecTag =
   struct
    type t = attribute

    (** val tag : attribute -> BigInt.t **)

    let tag x =
      x.attr_tag

    (** val equal : attribute -> attribute -> bool **)

    let equal =
      attr_eqb
   end

  type t = AttrDecTag.t

  (** val tag : AttrDecTag.t -> BigInt.t **)

  let tag =
    AttrDecTag.tag

  (** val equal : AttrDecTag.t -> AttrDecTag.t -> bool **)

  let equal =
    AttrDecTag.equal
 end

module Attr = MakeMS(AttrTag)

module Sattr = Attr.S

module Mattr = Attr.M

(** val attr_equal : attribute -> attribute -> bool **)

let attr_equal =
  attr_eqb

(** val attr_hash : attribute -> BigInt.t **)

let attr_hash a =
  a.attr_tag

(** val attr_compare : attribute -> attribute -> Stdlib.Int.t **)

let attr_compare a1 a2 =
  BigInt.compare a1.attr_tag a2.attr_tag

type notation =
| SNword of string
| SNinfix of string
| SNtight of string
| SNprefix of string
| SNget of string
| SNset of string
| SNupdate of string
| SNcut of string
| SNlcut of string
| SNrcut of string

(** val op_infix : string -> string **)

let op_infix s =
  (^) "infix " s

(** val op_prefix : string -> string **)

let op_prefix s =
  (^) "prefix " s

(** val op_get : string -> string **)

let op_get s =
  (^) "mixfix []" s

(** val op_set : string -> string **)

let op_set s =
  (^) "mixfix []<-" s

(** val op_update : string -> string **)

let op_update s =
  (^) "mixfix [<-]" s

(** val op_cut : string -> string **)

let op_cut s =
  (^) "mixfix [..]" s

(** val op_lcut : string -> string **)

let op_lcut s =
  (^) "mixfix [.._]" s

(** val op_rcut : string -> string **)

let op_rcut s =
  (^) "mixfix [_..]" s

(** val op_equ : string **)

let op_equ =
  op_infix "="

(** val op_neq : string **)

let op_neq =
  op_infix "<>"

(** val op_tight : string -> string **)

let op_tight =
  op_prefix

type ident = { id_string : string; id_attrs : Sattr.t;
               id_loc : position option; id_tag : tag }

(** val id_string : ident -> string **)

let id_string i =
  i.id_string

(** val id_attrs : ident -> Sattr.t **)

let id_attrs i =
  i.id_attrs

(** val id_loc : ident -> position option **)

let id_loc i =
  i.id_loc

(** val id_tag : ident -> tag **)

let id_tag i =
  i.id_tag

(** val ident_eqb : ident -> ident -> bool **)

let ident_eqb i1 i2 =
  (&&)
    ((&&)
      ((&&) (tag_equal i1.id_tag i2.id_tag) ((=) i1.id_string i2.id_string))
      (Sattr.equal i1.id_attrs i2.id_attrs))
    (option_eqb equal i1.id_loc i2.id_loc)

module IdentTag =
 struct
  type t = ident

  (** val tag : ident -> tag **)

  let tag x =
    x.id_tag

  (** val equal : ident -> ident -> bool **)

  let equal =
    (fun x y -> x == y || ident_eqb x y)
 end

module Id = MakeMSWeak(IdentTag)

module Sid = Id.S

module Mid = Id.M

type preid = { pre_name : string; pre_attrs : Sattr.t;
               pre_loc : position option }

(** val pre_name : preid -> string **)

let pre_name p =
  p.pre_name

(** val pre_attrs : preid -> Sattr.t **)

let pre_attrs p =
  p.pre_attrs

(** val pre_loc : preid -> position option **)

let pre_loc p =
  p.pre_loc

(** val id_equal : ident -> ident -> bool **)

let id_equal =
  (fun x y -> x == y || ident_eqb x y)

(** val id_hash : ident -> BigInt.t **)

let id_hash i =
  tag_hash i.id_tag

(** val id_compare : ident -> ident -> Stdlib.Int.t **)

let id_compare id1 id2 =
  BigInt.compare (id_hash id1) (id_hash id2)

module CtrStart =
 struct
  (** val coq_val : BigInt.t **)

  let coq_val =
    (BigInt.of_int 80)
 end

module IdCtr = MakeCtr(CtrStart)

(** val id_ctr : (BigInt.t, unit) st **)

let id_ctr =
  IdCtr.create

(** val id_register : preid -> (BigInt.t, ident) st **)

let id_register p =
  (@@) (fun _ ->
    (@@) (fun i ->
      (fun x -> x) { id_string = p.pre_name; id_attrs = p.pre_attrs; id_loc =
        p.pre_loc; id_tag = (create_tag i) }) (IdCtr.get ())) (IdCtr.incr ())

(** val id_builtin : string -> BigInt.t -> ident **)

let id_builtin name tag0 =
  { id_string = name; id_attrs = Sattr.empty; id_loc = None; id_tag = tag0 }

(** val id_int : ident **)

let id_int =
  id_builtin "int" (create_tag BigInt.one)

(** val id_real : ident **)

let id_real =
  id_builtin "real" (create_tag (BigInt.of_int 2))

(** val id_bool : ident **)

let id_bool =
  id_builtin "bool" (create_tag (BigInt.of_int 3))

(** val id_str : ident **)

let id_str =
  id_builtin "string" (create_tag (BigInt.of_int 4))

(** val id_a : ident **)

let id_a =
  id_builtin "a" (create_tag (BigInt.of_int 5))

(** val id_b : ident **)

let id_b =
  id_builtin "b" (create_tag (BigInt.of_int 6))

(** val id_fun : ident **)

let id_fun =
  id_builtin (op_infix "->") (create_tag (BigInt.of_int 7))

(** val id_eq : ident **)

let id_eq =
  id_builtin (op_infix "=") (create_tag (BigInt.of_int 8))

(** val id_true : ident **)

let id_true =
  id_builtin "True" (create_tag (BigInt.of_int 9))

(** val id_false : ident **)

let id_false =
  id_builtin "False" (create_tag (BigInt.of_int 10))

(** val id_app : ident **)

let id_app =
  id_builtin (op_infix "@") (create_tag (BigInt.of_int 11))

(** val create_ident : string -> Sattr.t -> position option -> preid **)

let create_ident name attrs loc =
  { pre_name = name; pre_attrs = attrs; pre_loc = loc }

(** val id_fresh1 : string -> preid **)

let id_fresh1 s =
  create_ident s Sattr.empty None

(** val id_clone1 : position option -> unit Sattr.M.t -> ident -> preid **)

let id_clone1 loc attrs i =
  let aa = Sattr.union attrs i.id_attrs in
  let loc0 = match loc with
             | Some _ -> loc
             | None -> i.id_loc in
  create_ident i.id_string aa loc0

(** val id_derive1 : string -> ident -> preid **)

let id_derive1 nm i =
  create_ident nm i.id_attrs i.id_loc

(** val id_tup0 : ident **)

let id_tup0 =
  id_builtin "tuple0" (create_tag (BigInt.of_int 12))

(** val id_tup1 : ident **)

let id_tup1 =
  id_builtin "tuple1" (create_tag (BigInt.of_int 13))

(** val id_tup2 : ident **)

let id_tup2 =
  id_builtin "tuple2" (create_tag (BigInt.of_int 14))

(** val id_tup3 : ident **)

let id_tup3 =
  id_builtin "tuple3" (create_tag (BigInt.of_int 15))

(** val id_tup4 : ident **)

let id_tup4 =
  id_builtin "tuple4" (create_tag (BigInt.of_int 16))

(** val id_tup5 : ident **)

let id_tup5 =
  id_builtin "tuple5" (create_tag (BigInt.of_int 17))

(** val id_tup6 : ident **)

let id_tup6 =
  id_builtin "tuple6" (create_tag (BigInt.of_int 18))

(** val id_tup7 : ident **)

let id_tup7 =
  id_builtin "tuple7" (create_tag (BigInt.of_int 19))

(** val id_tup8 : ident **)

let id_tup8 =
  id_builtin "tuple8" (create_tag (BigInt.of_int 20))

(** val id_tup9 : ident **)

let id_tup9 =
  id_builtin "tuple9" (create_tag (BigInt.of_int 21))

(** val id_tup10 : ident **)

let id_tup10 =
  id_builtin "tuple10" (create_tag (BigInt.of_int 22))

(** val id_tup11 : ident **)

let id_tup11 =
  id_builtin "tuple11" (create_tag (BigInt.of_int 23))

(** val id_tup12 : ident **)

let id_tup12 =
  id_builtin "tuple12" (create_tag (BigInt.of_int 24))

(** val id_tup13 : ident **)

let id_tup13 =
  id_builtin "tuple13" (create_tag (BigInt.of_int 25))

(** val id_tup14 : ident **)

let id_tup14 =
  id_builtin "tuple14" (create_tag (BigInt.of_int 26))

(** val id_tup15 : ident **)

let id_tup15 =
  id_builtin "tuple15" (create_tag (BigInt.of_int 27))

(** val id_tup16 : ident **)

let id_tup16 =
  id_builtin "tuple16" (create_tag (BigInt.of_int 28))

(** val id_tup17 : ident **)

let id_tup17 =
  id_builtin "tuple17" (create_tag (BigInt.of_int 29))

(** val id_tup18 : ident **)

let id_tup18 =
  id_builtin "tuple18" (create_tag (BigInt.of_int 30))

(** val id_tup19 : ident **)

let id_tup19 =
  id_builtin "tuple19" (create_tag (BigInt.of_int 31))

(** val id_tup20 : ident **)

let id_tup20 =
  id_builtin "tuple20" (create_tag (BigInt.of_int 32))

(** val id_tup_list : ident list **)

let id_tup_list =
  id_tup0::(id_tup1::(id_tup2::(id_tup3::(id_tup4::(id_tup5::(id_tup6::(id_tup7::(id_tup8::(id_tup9::(id_tup10::(id_tup11::(id_tup12::(id_tup13::(id_tup14::(id_tup15::(id_tup16::(id_tup17::(id_tup18::(id_tup19::(id_tup20::[]))))))))))))))))))))

(** val id_c : ident **)

let id_c =
  id_builtin "c" (create_tag (BigInt.of_int 33))

(** val id_d : ident **)

let id_d =
  id_builtin "d" (create_tag (BigInt.of_int 34))

(** val id_e : ident **)

let id_e =
  id_builtin "e" (create_tag (BigInt.of_int 35))

(** val id_f : ident **)

let id_f =
  id_builtin "f" (create_tag (BigInt.of_int 36))

(** val id_g : ident **)

let id_g =
  id_builtin "g" (create_tag (BigInt.of_int 37))

(** val id_h : ident **)

let id_h =
  id_builtin "h" (create_tag (BigInt.of_int 38))

(** val id_i : ident **)

let id_i =
  id_builtin "i" (create_tag (BigInt.of_int 39))

(** val id_j : ident **)

let id_j =
  id_builtin "j" (create_tag (BigInt.of_int 40))

(** val id_k : ident **)

let id_k =
  id_builtin "k" (create_tag (BigInt.of_int 41))

(** val id_l : ident **)

let id_l =
  id_builtin "l" (create_tag (BigInt.of_int 42))

(** val id_m : ident **)

let id_m =
  id_builtin "m" (create_tag (BigInt.of_int 43))

(** val id_n : ident **)

let id_n =
  id_builtin "n" (create_tag (BigInt.of_int 44))

(** val id_o : ident **)

let id_o =
  id_builtin "o" (create_tag (BigInt.of_int 45))

(** val id_p : ident **)

let id_p =
  id_builtin "p" (create_tag (BigInt.of_int 46))

(** val id_q : ident **)

let id_q =
  id_builtin "q" (create_tag (BigInt.of_int 47))

(** val id_r : ident **)

let id_r =
  id_builtin "r" (create_tag (BigInt.of_int 48))

(** val id_s : ident **)

let id_s =
  id_builtin "s" (create_tag (BigInt.of_int 49))

(** val id_t : ident **)

let id_t =
  id_builtin "t" (create_tag (BigInt.of_int 50))

(** val id_a1 : ident **)

let id_a1 =
  id_builtin "a1" (create_tag (BigInt.of_int 51))

(** val id_a2 : ident **)

let id_a2 =
  id_builtin "a2" (create_tag (BigInt.of_int 52))

(** val id_a3 : ident **)

let id_a3 =
  id_builtin "a3" (create_tag (BigInt.of_int 53))

(** val id_a4 : ident **)

let id_a4 =
  id_builtin "a4" (create_tag (BigInt.of_int 54))

(** val id_a5 : ident **)

let id_a5 =
  id_builtin "a5" (create_tag (BigInt.of_int 55))

(** val id_a6 : ident **)

let id_a6 =
  id_builtin "a6" (create_tag (BigInt.of_int 56))

(** val id_a7 : ident **)

let id_a7 =
  id_builtin "a7" (create_tag (BigInt.of_int 57))

(** val id_a8 : ident **)

let id_a8 =
  id_builtin "a8" (create_tag (BigInt.of_int 58))

(** val id_a9 : ident **)

let id_a9 =
  id_builtin "a9" (create_tag (BigInt.of_int 59))

(** val id_b0 : ident **)

let id_b0 =
  id_builtin "b0" (create_tag (BigInt.of_int 60))

(** val id_b1 : ident **)

let id_b1 =
  id_builtin "b1" (create_tag (BigInt.of_int 61))

(** val id_b2 : ident **)

let id_b2 =
  id_builtin "b2" (create_tag (BigInt.of_int 62))

(** val id_b3 : ident **)

let id_b3 =
  id_builtin "b3" (create_tag (BigInt.of_int 63))

(** val id_b4 : ident **)

let id_b4 =
  id_builtin "b4" (create_tag (BigInt.of_int 64))

(** val id_b5 : ident **)

let id_b5 =
  id_builtin "b5" (create_tag (BigInt.of_int 65))

(** val id_b6 : ident **)

let id_b6 =
  id_builtin "b6" (create_tag (BigInt.of_int 66))

(** val id_tup21 : ident **)

let id_tup21 =
  id_builtin "tuple21" (create_tag (BigInt.of_int 67))

(** val id_tup22 : ident **)

let id_tup22 =
  id_builtin "tuple22" (create_tag (BigInt.of_int 68))

(** val id_tup23 : ident **)

let id_tup23 =
  id_builtin "tuple23" (create_tag (BigInt.of_int 69))

(** val id_tup24 : ident **)

let id_tup24 =
  id_builtin "tuple24" (create_tag (BigInt.of_int 70))

(** val id_tup25 : ident **)

let id_tup25 =
  id_builtin "tuple25" (create_tag (BigInt.of_int 71))

(** val id_tup26 : ident **)

let id_tup26 =
  id_builtin "tuple26" (create_tag (BigInt.of_int 72))

(** val id_tup27 : ident **)

let id_tup27 =
  id_builtin "tuple27" (create_tag (BigInt.of_int 73))

(** val id_tup28 : ident **)

let id_tup28 =
  id_builtin "tuple28" (create_tag (BigInt.of_int 74))

(** val id_tup29 : ident **)

let id_tup29 =
  id_builtin "tuple29" (create_tag (BigInt.of_int 75))

(** val id_tup30 : ident **)

let id_tup30 =
  id_builtin "tuple30" (create_tag (BigInt.of_int 76))

(** val id_tup31 : ident **)

let id_tup31 =
  id_builtin "tuple31" (create_tag (BigInt.of_int 77))

(** val id_tup33 : ident **)

let id_tup33 =
  id_builtin "tuple33" (create_tag (BigInt.of_int 78))

(** val id_tup36 : ident **)

let id_tup36 =
  id_builtin "tuple36" (create_tag (BigInt.of_int 79))
module Hsattr = Hashcons.Make (struct
  type t = attribute
  let equal a1 a2 = a1.attr_string = a2.attr_string
  let hash a = BigInt.of_int (Hashtbl.hash a.attr_string)
  let tag n a = { a with attr_tag = n }
end)

let create_attribute s = Hsattr.hashcons {
  attr_string = s;
  attr_tag    = BigInt.of_int (-1)
}

let list_attributes () =
  let acc = ref [] in
  Hsattr.iter (fun a -> acc := a.attr_string :: !acc);
  !acc

module Id2 = MakeMSHW(IdentTag)
module Hid = Id2.H
module Wid = Id2.W

let sexp_of_attribute (a:attribute) =
  Mysexplib.sexp_of_string a.attr_string
[@@warning "-32"]

let attribute_of_sexp (s : Mysexplib.sexp) =
  create_attribute (Mysexplib.string_of_sexp s)
[@@warning "-32"]

let print_sn fmt w =
  let lspace p = if p.[0] = '*' then " " else "" in
  let rspace p = if p.[String.length p - 1] = '*' then " " else "" in
  match w with (* infix/prefix never empty, mixfix cannot have stars *)
  | SNinfix  p -> Format.fprintf fmt "(%s%s%s)" (lspace p) p (rspace p)
  | SNtight  p -> Format.fprintf fmt "(%s%s)" p (rspace p)
  | SNprefix p -> Format.fprintf fmt "(%s%s_)" (lspace p) p
  | SNget    p -> Format.fprintf fmt "([]%s)" p
  | SNset    p -> Format.fprintf fmt "([]%s<-)" p
  | SNupdate p -> Format.fprintf fmt "([<-]%s)" p
  | SNcut    p -> Format.fprintf fmt "([..]%s)" p
  | SNlcut   p -> Format.fprintf fmt "([.._]%s)" p
  | SNrcut   p -> Format.fprintf fmt "([_..]%s)" p
  | SNword   p -> Format.pp_print_string fmt p


(* The function below recognizes the following strings as notations:
      "infix " (opchar+ [']* as p) (['_] [^'_] .* as q)
      "prefix " (opchar+ [']* as p) (['_] [^'_] .* as q)
      "mixfix " .* "]" opchar* ([']* as p) (['_] [^'_] .* as q)
   It will fail if you add a mixfix that contains a non-opchar after
   the closing square bracket, or a mixfix that does not use brackets.
   Be careful when working with this code, it may eat your brain. *)

  let sn_decode s =
  let len = String.length s in
  if len <= 6 then SNword s else
  if s.[5] <> ' ' && s.[6] <> ' ' then SNword s else
  let k = match String.sub s 0 6 with
    | "infix " -> 6
    | "prefix" -> 7
    | "mixfix" -> (try succ (String.index_from s 7 ']') with Not_found -> 0)
    | _ -> 0 in
  if k = 0 then SNword s else
  let rec skip_opchar i =
    if i = len then i else match s.[i] with
      | '@' | '!' | '^' | '$' | '=' | '%' | '>' | '#'
      | '.' | '<' | '-' | '&' | '/' | '+' | '?' | ':'
      | '*' | '~' | '|' | '\\' -> skip_opchar (succ i)
      | _ -> i in
  let l = skip_opchar k in
  let rec skip_quote i =
    if i = len then i else
    if s.[i] = '\'' then skip_quote (succ i) else
    if i = l || s.[i] = '_' then i else pred i in
  let m = skip_quote l in
  let prefix o =
    if o.[0] <> '!' && o.[0] <> '?' then SNprefix o
    else try for i = 1 to l - 8 do match o.[i] with
      | '!' | '$' | '&' | '?' | '@'
      | '^' | '.' | ':' | '|' | '#' -> ()
      | _ -> raise Exit done; SNtight o
    with Exit -> SNprefix o in
  if l = k && k < 8 then SNword s (* null infix/prefix *) else
  let w = if k = 6 then SNinfix (String.sub s 6 (m - 6)) else
          if k = 7 then prefix (String.sub s 7 (m - 7)) else
          let p = if l < m then String.sub s l (m - l) else "" in
          match String.sub s 8 (l - 8) with
          | "]"   -> SNget p | "]<-"  -> SNset p  | "<-]"  -> SNupdate p
          | "..]" -> SNcut p | ".._]" -> SNlcut p | "_..]" -> SNrcut p
          | _ -> SNword (if m = len then s else String.sub s 0 m) in
  if m = len then w (* no appended suffix *) else
  if s.[m] <> '\'' && s.[m] <> '_' then SNword s else
  SNword (Format.asprintf "%a%s" print_sn w (String.sub s m (len - m)))

let print_decoded fmt s = print_sn fmt (sn_decode s)

let id_fresh ?(attrs = Sattr.empty) ?loc nm =
  create_ident nm attrs loc


let id_user ?(attrs = Sattr.empty) nm loc =
  create_ident nm attrs (Some loc)

let id_attr id attrs =
  create_ident id.id_string attrs id.id_loc

let id_clone ?loc ?(attrs = Sattr.empty) id =
  id_clone1 loc attrs id
  (* let aa = Sattr.union attrs id.id_attrs in
  let loc = match loc with
    | None -> id.id_loc
    | Some _ -> loc
  in
  create_ident id.id_string aa loc *)

let id_derive ?(attrs = Sattr.empty) nm id =
  let aa = Sattr.union attrs id.id_attrs in
  create_ident nm aa id.id_loc

let preid_name id = id.pre_name

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : int Hstr.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

(* name is already sanitized *)
let find_unique indices name =
  let specname ind =
    (* If the symbol is infix/prefix *and* the name has not been
       sanitized for provers, we don't want to disambiguate with
       a number but with a quote symbol: "+" becomes "+'" "+''" etc.
       This allows to parse the ident again (for transformations). *)
    if ind <= 0 then name else
    match sn_decode name with
    | SNword _ -> name ^ string_of_int ind
    | _        -> name ^ String.make ind '\'' in
  let testname ind = Hstr.mem indices (specname ind) in
  let rec advance ind =
    if testname ind then advance (succ ind) else ind in
  let rec retreat ind =
    if ind = 1 || testname (pred ind) then ind else retreat (pred ind) in
  let fetch ind =
    if testname ind then advance (succ ind) else retreat ind in
  let name = try
    let ind = fetch (succ (Hstr.find indices name)) in
    Hstr.replace indices name ind;
    specname ind
  with Not_found -> name in
  Hstr.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hstr.create 1997 in
  List.iter (reserve indices) sl;
  { indices   = indices;
    values    = Hid.create 1997;
    sanitizer = sanitizer;
    blacklist = sl }

let duplicate_ident_printer id_printer =
  {id_printer with
   indices = Hstr.copy id_printer.indices;
   values  = Hid.copy id_printer.values;
  }

let known_id printer id =
  try
    (let _ = Hid.find printer.values id in true)
  with Not_found ->
    false

let id_unique printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let name = sanitizer (printer.sanitizer id.id_string) in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let string_unique printer s = find_unique printer.indices (printer.sanitizer s)

let forget_id printer id =
  try
    let name = Hid.find printer.values id in
    Hstr.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hstr.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

let char_to_alpha c = match c with
  | 'a'..'z' | 'A'..'Z' -> String.make 1 c
  | ' ' -> "sp" | '_'  -> "us" | '#' -> "sh"
  | '`' -> "bq" | '~'  -> "tl" | '!' -> "ex"
  | '@' -> "at" | '$'  -> "dl" | '%' -> "pc"
  | '^' -> "cf" | '&'  -> "et" | '*' -> "as"
  | '(' -> "lp" | ')'  -> "rp" | '-' -> "mn"
  | '+' -> "pl" | '='  -> "eq" | '[' -> "lb"
  | ']' -> "rb" | '{'  -> "lc" | '}' -> "rc"
  | ':' -> "cl" | '\'' -> "qt" | '"' -> "dq"
  | '<' -> "ls" | '>'  -> "gt" | '/' -> "sl"
  | '?' -> "qu" | '\\' -> "bs" | '|' -> "br"
  | ';' -> "sc" | ','  -> "cm" | '.' -> "dt"
  | '0' -> "zr" | '1'  -> "un" | '2' -> "du"
  | '3' -> "tr" | '4'  -> "qr" | '5' -> "qn"
  | '6' -> "sx" | '7'  -> "st" | '8' -> "oc"
  | '9' -> "nn" | '\n' -> "nl" |  _  -> "zz"

let char_to_lalpha c = Strings.uncapitalize (char_to_alpha c)
let char_to_ualpha c = Strings.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_lalnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_lalpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let char_to_lalnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_lalnum c

let sanitizer' head rest last n =
  let lst = ref [] in
  let n = if n = "" then "zilch" else n in
  let len = String.length n in
  let code i c = lst :=
    (if i = 0 then head
     else if i = len - 1 then last
     else rest) c :: !lst in
  String.iteri code n;
  String.concat "" (List.rev !lst)

let sanitizer head rest n = sanitizer' head rest rest n

(** {2 functions for working with counterexample attributes} *)

let is_field_id_attr = create_attribute "is_field_id"

let builtin_attr = create_attribute "builtin"

let proxy_attr = create_attribute "mlw:proxy_symbol"

let useraxiom_attr = create_attribute "useraxiom"

let funlit = create_attribute "funlit"

let model_projected_attr = create_attribute "model_projected"
let model_vc_post_attr = create_attribute "model_vc_post"

let create_model_trace_attr s = create_attribute ("model_trace:" ^ s)

let is_model_trace_attr a =
  Strings.has_prefix "model_trace:" a.attr_string

let is_written_attr a =
  Strings.has_prefix "vc:written:" a.attr_string

let eid_attribute_prefix = "eid:"

let is_eid_attr a = Strings.has_prefix eid_attribute_prefix a.attr_string

let create_loc_attr prefix loc =
  let f,bl,bc,el,ec = Loc.get loc in
  (* The file comes last to permit filenames that contain colons *)
  let s = Format.sprintf "%s:%i:%i:%i:%i:%s" prefix bl bc el ec f in
  create_attribute s

let get_loc_attr prefix attr =
  match Strings.remove_prefix (prefix^":") attr.attr_string with
  | exception Not_found -> None
  | str -> match Strings.bounded_split ':' str 5 with
    | [stline; stcol; endline; endcol; file] ->
        begin try
            let stline = int_of_string stline in
            let stcol = int_of_string stcol in
            let endline = int_of_string endline in
            let endcol = int_of_string endcol in
            Some (Loc.user_position file stline stcol endline endcol)
          with _ -> None
        end
    | _ -> None

let create_written_attr = create_loc_attr "vc:written"

let get_written_loc = get_loc_attr "vc:written"

let is_counterexample_attr a =
  is_model_trace_attr a || attr_equal a model_projected_attr ||
  is_written_attr a || is_eid_attr a

let has_a_model_attr id =
  Sattr.exists_ is_counterexample_attr id.id_attrs

let relevant_for_counterexample id =
  (id.id_loc <> None && not (Sattr.mem proxy_attr id.id_attrs))
  || has_a_model_attr id

let remove_model_attrs ~attrs =
  Sattr.filter (fun l -> not (is_counterexample_attr l)) attrs

let call_result_name = "call_result"

let create_call_result_attr = create_loc_attr call_result_name

let get_call_result_loc = get_loc_attr call_result_name

let search_attribute_value f attrs =
  try Some (Lists.first f (Sattr.elements attrs)) with Not_found -> None

let get_eid_attr =
  search_attribute_value
    (fun a ->
      try
        let i = Strings.remove_prefix eid_attribute_prefix a.attr_string in
        Some (int_of_string i)
      with Not_found -> None)


let get_model_trace_attr ~attrs =
  Sattr.choose (Sattr.filter is_model_trace_attr attrs)

let has_rac_assume =
  Sattr.exists_ (fun a -> a.attr_string = "RAC:assume")

let transform_model_trace_attr attrs trans_fun =
  try
    let trace_attr = get_model_trace_attr ~attrs in
    let attrs_without_trace = Sattr.remove trace_attr attrs in
    let new_trace_attr = create_attribute (trans_fun trace_attr.attr_string) in
    Sattr.add new_trace_attr attrs_without_trace
  with Not_found -> attrs

let append_to_model_element_name ~attrs ~to_append =
  let trans attr_str =
    let splitted = Strings.bounded_split '@' attr_str 2 in
    match splitted with
    | [before; after] -> before ^ to_append ^ "@" ^ after
    | _ -> attr_str^to_append
  in
  transform_model_trace_attr attrs trans

let append_to_model_trace_attr ~attrs ~to_append =
    let trans attr_str = attr_str ^ to_append in
    transform_model_trace_attr attrs trans

let get_model_element_name ~attrs =
  let trace_attr = get_model_trace_attr ~attrs in
  let splitted1 = Strings.bounded_split ':' trace_attr.attr_string 2 in
  match splitted1 with
  | [_; content] ->
    begin
      let splitted2 = Strings.bounded_split '@' content 2 in
      match splitted2 with
      | [el_name; _] -> el_name
      | [el_name] -> el_name
      | _ -> assert false
    end;
  | [_] -> ""
  | _ -> assert false

let get_model_trace_string ~name ~attrs =
  match get_model_trace_attr ~attrs with
  | exception Not_found -> name
  | tl ->
      let splitted = Strings.bounded_split ':' tl.attr_string 2 in
      match splitted with
      | [_; t_str] -> t_str
      | _ -> ""

let compute_model_trace_field pj d =
  match pj with
  | None -> Sattr.empty
  | Some pj ->
      let name = get_model_trace_string
          ~name:pj.id_string ~attrs:pj.id_attrs in
      let name = if name = "" then pj.id_string else name in
      let attr = "field:" ^ (string_of_int d) ^ ":" ^ name in
      Sattr.singleton (create_attribute attr)

let extract_field attr =
  try
    match Strings.bounded_split ':' attr.attr_string 3 with
    | ["field"; n; field_name] -> Some (int_of_string n, field_name)
    | _ -> None
  with
  | _ -> None

(* Attributes used to name hypothesis *)
let is_hyp_name_attr a =
  Strings.has_prefix "hyp_name:" a.attr_string

let get_hyp_name ~attrs =
  try Some (Strings.remove_prefix "hyp_name:"
              (Sattr.choose (Sattr.filter is_hyp_name_attr attrs)).attr_string)
  with Not_found -> None

(* Functions for working with ITP attributes *)

let is_name_attr a =
  Strings.has_prefix "name:" a.attr_string

let get_name_attr ~attrs =
  try Some (Sattr.choose (Sattr.filter is_name_attr attrs))
  with Not_found -> None

let get_element_name ~attrs =
  match get_name_attr ~attrs with
  | None -> None
  | Some name_attr ->
    let splitted1 = Strings.bounded_split ':' name_attr.attr_string 2 in
    let correct_word = Re.Str.regexp "^\\([A-Za-z]+\\)\\([A-Za-z0-9_']*\\)$" in
    match splitted1 with
    | ["name"; content] when Re.Str.string_match correct_word content 0 ->
        Some content
    | _ -> None

let suffix_attr_name ~attrs suffix =
  Sattr.fold (fun x acc ->
      if is_name_attr x then
          Sattr.add (create_attribute (x.attr_string ^ suffix)) acc
      else
        Sattr.add x acc) attrs Sattr.empty

let id_unique_attr printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let attrs = id.id_attrs in
    let name =
      match (get_element_name ~attrs) with
      | Some x -> x
      | None -> printer.sanitizer id.id_string
    in
    let name = sanitizer name in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let unused_attr = create_attribute "id:unused"

let unused_suffix = "'unused"
