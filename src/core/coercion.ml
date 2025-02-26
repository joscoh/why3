open CommonList
open Ident
open Ty
open Term




type coercion_kind =
| CRCleaf of lsymbol
| CRCcomp of coercion_kind * coercion_kind

(** val coercion_kind_rect :
    (lsymbol -> 'a1) -> (coercion_kind -> 'a1 -> coercion_kind -> 'a1 -> 'a1)
    -> coercion_kind -> 'a1 **)

let rec coercion_kind_rect f f0 = function
| CRCleaf l -> f l
| CRCcomp (c0, c1) ->
  f0 c0 (coercion_kind_rect f f0 c0) c1 (coercion_kind_rect f f0 c1)

(** val coercion_kind_rec :
    (lsymbol -> 'a1) -> (coercion_kind -> 'a1 -> coercion_kind -> 'a1 -> 'a1)
    -> coercion_kind -> 'a1 **)

let rec coercion_kind_rec f f0 = function
| CRCleaf l -> f l
| CRCcomp (c0, c1) ->
  f0 c0 (coercion_kind_rec f f0 c0) c1 (coercion_kind_rec f f0 c1)

type coercion = { crc_kind : coercion_kind;
                  crc_src_ts : (ty_node_c ty_o) tysymbol_o;
                  crc_src_tl : ty_node_c ty_o list;
                  crc_tar_ts : (ty_node_c ty_o) tysymbol_o;
                  crc_tar_tl : ty_node_c ty_o list }

(** val crc_kind : coercion -> coercion_kind **)

let crc_kind c =
  c.crc_kind

(** val crc_src_ts : coercion -> (ty_node_c ty_o) tysymbol_o **)

let crc_src_ts c =
  c.crc_src_ts

(** val crc_src_tl : coercion -> ty_node_c ty_o list **)

let crc_src_tl c =
  c.crc_src_tl

(** val crc_tar_ts : coercion -> (ty_node_c ty_o) tysymbol_o **)

let crc_tar_ts c =
  c.crc_tar_ts

(** val crc_tar_tl : coercion -> ty_node_c ty_o list **)

let crc_tar_tl c =
  c.crc_tar_tl

type t = coercion Mts.t Mts.t

(** val coercion_kind_eqb : coercion_kind -> coercion_kind -> bool **)

let rec coercion_kind_eqb c1 c2 =
  match c1 with
  | CRCleaf l1 ->
    (match c2 with
     | CRCleaf l2 -> ls_equal l1 l2
     | CRCcomp (_, _) -> false)
  | CRCcomp (c3, c4) ->
    (match c2 with
     | CRCleaf _ -> false
     | CRCcomp (c5, c6) ->
       (&&) (coercion_kind_eqb c3 c5) (coercion_kind_eqb c4 c6))

(** val coercion_eqb : coercion -> coercion -> bool **)

let coercion_eqb c1 c2 =
  (&&)
    ((&&)
      ((&&)
        ((&&) (coercion_kind_eqb c1.crc_kind c2.crc_kind)
          (ts_equal c1.crc_src_ts c2.crc_src_ts))
        (list_eqb ty_eqb c1.crc_src_tl c2.crc_src_tl))
      (ts_equal c1.crc_tar_ts c2.crc_tar_ts))
    (list_eqb ty_eqb c1.crc_tar_tl c2.crc_tar_tl)

(** val t_eqb : t -> t -> bool **)

let t_eqb t1 t2 =
  Mts.equal (Mts.equal coercion_eqb) t1 t2
(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)





(* type coercion_kind =
  | CRCleaf of lsymbol
  | CRCcomp of coercion_kind * coercion_kind

type coercion =  {
  crc_kind   : coercion_kind;
  crc_src_ts : tysymbol;
  crc_src_tl : ty list;
  crc_tar_ts : tysymbol;
  crc_tar_tl : ty list;
} *)

(* type t = (coercion Mts.t) Mts.t *)
(** invariant: transitively closed *)

let empty = Mts.empty

exception NotACoercion of lsymbol
exception CoercionCycle of coercion
exception CoercionAlreadyDefined of coercion

let create_crc ls =
  match ls.ls_args, ls.ls_value with
  | [{ty_node = Tyapp (ts1,tl1)}], Some ({ty_node = Tyapp (ts2, tl2)}) ->
      if ts_equal ts1 ts2 then raise (NotACoercion ls);
      { crc_kind = CRCleaf ls;
        crc_src_ts = ts1; crc_src_tl = tl1;
        crc_tar_ts = ts2; crc_tar_tl = tl2; }
  | _ -> raise (NotACoercion ls)

let mem crcmap ts1 ts2 =
  try let m = Mts.find ts1 crcmap in Mts.mem ts2 m
  with Not_found -> false

let rec may_match ty1 ty2 =
  match (ty1.ty_node, ty2.ty_node) with
  | Tyapp (ts1, tl1), Tyapp (ts2, tl2) ->
      if not (ts_equal ts1 ts2) then raise Not_found;
      List.iter2 may_match tl1 tl2
  | _  -> ()

let find_crc crcmap ts1 ts2 = Mts.find ts2 (Mts.find ts1 crcmap)

let find crcmap ty1 ty2 =
  match ty1, ty2 with
  | {ty_node = Tyapp (ts1, tl1)}, {ty_node = Tyapp (ts2, tl2)} ->
      let rec ls_list_of acc = function
        | CRCleaf ls -> ls :: acc
        | CRCcomp (k1, k2) -> ls_list_of (ls_list_of acc k2) k1 in
      let crc = find_crc crcmap ts1 ts2 in
      List.iter2 may_match tl1 crc.crc_src_tl;
      List.iter2 may_match tl2 crc.crc_tar_tl;
      ls_list_of [] crc.crc_kind
  | _ -> raise Not_found

(* replace an old coercion by a new one, or fail *)
let rec ck_eq ck_old ck_new =
  match ck_old, ck_new with
  | CRCleaf ls_old, CRCleaf ls_new when ls_equal ls_old ls_new -> ()
  | CRCcomp (old_ck1, old_ck2), CRCcomp (new_ck1, new_ck2) ->
      ck_eq old_ck1 new_ck1;
      ck_eq old_ck2 new_ck2
  | _  -> raise Not_found

(* replace an old coercion by a new one, or fail *)
let replace c_old c_new _m1 m =
  try ck_eq c_old.crc_kind c_new.crc_kind; m
  with Not_found -> raise (CoercionAlreadyDefined c_old)

(* add a new coercion c, without making the transitive closure *)
let insert crc m =
  let put crc m1 m2 =
    Mts.add crc.crc_src_ts (Mts.add crc.crc_tar_ts crc m1) m2 in
  if mem m crc.crc_tar_ts crc.crc_src_ts then
    raise (CoercionCycle (find_crc m crc.crc_tar_ts crc.crc_src_ts));
  let m1 = Mts.find_def Mts.empty crc.crc_src_ts m in
  if Mts.mem crc.crc_tar_ts m1 then
    replace (Mts.find crc.crc_tar_ts m1) crc m1 m
  else put crc m1 m

let compose crc1 crc2 = {
  crc_kind = CRCcomp (crc1.crc_kind, crc2.crc_kind);
  crc_src_ts = crc1.crc_src_ts;
  crc_src_tl = crc1.crc_src_tl;
  crc_tar_ts = crc2.crc_tar_ts;
  crc_tar_tl = crc2.crc_tar_tl;
}

(* add a new coercion crc, and make the transitive closure *)
let add_crc crcmap crc =
  let close_right c1 _ty c2 macc = insert (compose c1 c2) macc in
  let close_left_right _ty1 m1 macc =
    if Mts.mem crc.crc_src_ts m1 then
      let c1 = Mts.find crc.crc_src_ts m1 in
      let m2 = Mts.find_def Mts.empty crc.crc_tar_ts macc in
      Mts.fold (close_right c1) (Mts.add crc.crc_tar_ts crc m2) macc
    else macc in
  let crcmap_uc1 = insert crc crcmap in
  let crcmap_uc2 =
    let m1 = Mts.find_def Mts.empty crc.crc_tar_ts crcmap_uc1 in
    Mts.fold (close_right crc) m1 crcmap_uc1 in
  Mts.fold (close_left_right) crcmap_uc2 crcmap_uc2

let add crcmap ls =
  add_crc crcmap (create_crc ls)

let union crcmap1 crcmap2 =
  let add _ty2 crc crcmap =
    match crc.crc_kind with
    | CRCleaf _ -> add_crc crcmap crc
    | CRCcomp _ -> crcmap in
  Mts.fold (fun _ty1 m1 crcmap -> Mts.fold add m1 crcmap) crcmap2 crcmap1

let print_kind fmt crc =
  let ty_str_of ls =
    match ls.ls_args, ls.ls_value with
    | [{ty_node = Tyapp (ty1,_)}], Some {ty_node = Tyapp (ty2,_)} ->
        ty1.ts_name.id_string, ty2.ts_name.id_string
    | _  -> assert false in
  let rec print_kind fmt = function
    | CRCleaf ls -> let s1, s2 = ty_str_of ls in
        Format.fprintf fmt "%s: %s -> %s" ls.ls_name.id_string s1 s2
    | CRCcomp (k1, k2) ->
        Format.fprintf fmt "%a@\n%a" print_kind k1 print_kind k2
  in print_kind fmt crc

let already_a_coercion fmt crc =
  Format.fprintf fmt "There is already a coercion from type %s to type %s:@\n%a"
    crc.crc_src_ts.ts_name.id_string
    crc.crc_tar_ts.ts_name.id_string
    print_kind crc.crc_kind

let () = Exn_printer.register
    begin fun fmt exn -> match exn with
      | NotACoercion ls ->
          Format.fprintf fmt "Function %s cannot be used as a coercion"
            ls.ls_name.id_string
      | CoercionCycle crc ->
          Format.fprintf fmt "This coercion introduces a cycle;@ ";
          already_a_coercion fmt crc
      | CoercionAlreadyDefined crc ->
          already_a_coercion fmt crc
      | _ -> raise exn end
