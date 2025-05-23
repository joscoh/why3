open BinNums
open Bool0
open Coercion
open Common
open CommonList
open CoqUtil
open Weakhtbl
open Wstdlib
open Datatypes
open IntFuncs

open Monads
open PmapExtra
open Specif
open State
open Base
open Fin_maps
open Hashcons
open Pmap
open Strings0
open Zmap

open Format
open Ident
open Ty
open Term
open Decl























(** val pmap_to_mstr : (string*'a1) coq_Pmap -> 'a1 Mstr.t **)

let pmap_to_mstr z =
  Obj.magic coq_Pmap_fold (fun _ y -> Obj.magic Mstr.add (fst y) (snd y))
    Mstr.empty z

(** val mstr_to_pmap : 'a1 Mstr.t -> (string*'a1) coq_Pmap **)

let mstr_to_pmap m =
  Mstr.fold (fun s x acc ->
    insert (map_insert coq_Pmap_partial_alter) (string_to_pos s) (s,x) acc) m
    coq_Pmap_empty

type namespace = { ns_ts : (ty_node_c ty_o) tysymbol_o Mstr.t;
                   ns_ls : lsymbol Mstr.t; ns_pr : prsymbol Mstr.t;
                   ns_ns : namespace Mstr.t }

(** val ns_ts : namespace -> (ty_node_c ty_o) tysymbol_o Mstr.t **)

let ns_ts n =
  n.ns_ts

(** val ns_ls : namespace -> lsymbol Mstr.t **)

let ns_ls n =
  n.ns_ls

(** val ns_pr : namespace -> prsymbol Mstr.t **)

let ns_pr n =
  n.ns_pr

(** val ns_ns : namespace -> namespace Mstr.t **)

let ns_ns n =
  n.ns_ns

(** val make_namespace_o :
    (ty_node_c ty_o) tysymbol_o Mstr.t -> lsymbol Mstr.t -> prsymbol Mstr.t
    -> namespace Mstr.t -> namespace **)

let make_namespace_o ns_ts0 ns_ls0 ns_pr0 ns_ns0 =
  { ns_ts = ns_ts0; ns_ls = ns_ls0; ns_pr = ns_pr0; ns_ns = ns_ns0 }

type meta_arg_type =
| MTty
| MTtysymbol
| MTlsymbol
| MTprsymbol
| MTstring
| MTint
| MTid

type meta_arg =
| MAty of ty_node_c ty_o
| MAts of (ty_node_c ty_o) tysymbol_o
| MAls of lsymbol
| MApr of prsymbol
| MAstr of string
| MAint of BigInt.t
| MAid of ident

type meta = { meta_name : string; meta_type : meta_arg_type list;
              meta_excl : bool; meta_desc : Pp.formatted; meta_tag : 
              BigInt.t }

(** val meta_name : meta -> string **)

let meta_name m =
  m.meta_name

(** val meta_type : meta -> meta_arg_type list **)

let meta_type m =
  m.meta_type

(** val meta_excl : meta -> bool **)

let meta_excl m =
  m.meta_excl

(** val meta_desc : meta -> Pp.formatted **)

let meta_desc m =
  m.meta_desc

(** val meta_tag : meta -> BigInt.t **)

let meta_tag m =
  m.meta_tag

type symbol_map = { sm_ty : ty_node_c ty_o Mts.t;
                    sm_ts : (ty_node_c ty_o) tysymbol_o Mts.t;
                    sm_ls : lsymbol Mls.t; sm_pr : prsymbol Mpr.t }

(** val sm_ty : symbol_map -> ty_node_c ty_o Mts.t **)

let sm_ty s =
  s.sm_ty

(** val sm_ts : symbol_map -> (ty_node_c ty_o) tysymbol_o Mts.t **)

let sm_ts s =
  s.sm_ts

(** val sm_ls : symbol_map -> lsymbol Mls.t **)

let sm_ls s =
  s.sm_ls

(** val sm_pr : symbol_map -> prsymbol Mpr.t **)

let sm_pr s =
  s.sm_pr

type 'a tdecl_o = { td_node : 'a; td_tag : BigInt.t }

(** val td_node : 'a1 tdecl_o -> 'a1 **)

let td_node t0 =
  t0.td_node

(** val td_tag : 'a1 tdecl_o -> BigInt.t **)

let td_tag t0 =
  t0.td_tag

type 'a theory_o = { th_name : ident; th_path : string list;
                     th_decls : 'a tdecl_o list;
                     th_ranges : 'a tdecl_o Mts.t;
                     th_floats : 'a tdecl_o Mts.t; th_crcmap : t;
                     th_proved_wf : (prsymbol*lsymbol) Mls.t;
                     th_export : namespace; th_known : known_map;
                     th_local : Sid.t; th_used : Sid.t }

(** val th_name : 'a1 theory_o -> ident **)

let th_name t0 =
  t0.th_name

(** val th_path : 'a1 theory_o -> string list **)

let th_path t0 =
  t0.th_path

(** val th_decls : 'a1 theory_o -> 'a1 tdecl_o list **)

let th_decls t0 =
  t0.th_decls

(** val th_ranges : 'a1 theory_o -> 'a1 tdecl_o Mts.t **)

let th_ranges t0 =
  t0.th_ranges

(** val th_floats : 'a1 theory_o -> 'a1 tdecl_o Mts.t **)

let th_floats t0 =
  t0.th_floats

(** val th_crcmap : 'a1 theory_o -> t **)

let th_crcmap t0 =
  t0.th_crcmap

(** val th_proved_wf : 'a1 theory_o -> (prsymbol*lsymbol) Mls.t **)

let th_proved_wf t0 =
  t0.th_proved_wf

(** val th_export : 'a1 theory_o -> namespace **)

let th_export t0 =
  t0.th_export

(** val th_known : 'a1 theory_o -> known_map **)

let th_known t0 =
  t0.th_known

(** val th_local : 'a1 theory_o -> Sid.t **)

let th_local t0 =
  t0.th_local

(** val th_used : 'a1 theory_o -> Sid.t **)

let th_used t0 =
  t0.th_used

type tdecl_node =
| Decl of decl
| Use of tdecl_node theory_o
| Clone of tdecl_node theory_o * symbol_map
| Meta of meta * meta_arg list

(** val zmap_to_mts :
    ((ty_node_c ty_o) tysymbol_o*'a1) coq_Zmap -> 'a1 Mts.t **)

let zmap_to_mts z =
  Obj.magic coq_Zmap_fold (fun _ y acc ->
    Obj.magic Mts.add (fst y) (snd y) acc) Mts.empty z

(** val mts_to_zmap :
    'a1 Mts.t -> ((ty_node_c ty_o) tysymbol_o*'a1) coq_Zmap **)

let mts_to_zmap m =
  Mts.fold (fun t0 y acc ->
    insert (map_insert coq_Zmap_partial_alter)
      (ZCompat.to_Z_big (tag_hash (ts_name t0).id_tag)) (t0,y) acc) m
    coq_Zmap_empty

type tdecl = tdecl_node tdecl_o

type theory = tdecl_node theory_o

(** val build_tdecl_o : tdecl_node -> BigInt.t -> tdecl **)

let build_tdecl_o t0 z =
  { td_node = t0; td_tag = z }

(** val build_theory_o :
    ident -> string list -> tdecl list -> tdecl Mts.t -> tdecl Mts.t -> t ->
    (prsymbol*lsymbol) Mls.t -> namespace -> known_map -> Sid.t -> Sid.t ->
    theory **)

let build_theory_o th_name0 th_path0 th_decls0 th_ranges0 th_floats0 th_crcmap0 th_proved_wf0 th_export0 th_known0 th_local0 th_used0 =
  { th_name = th_name0; th_path = th_path0; th_decls = th_decls0; th_ranges =
    th_ranges0; th_floats = th_floats0; th_crcmap = th_crcmap0;
    th_proved_wf = th_proved_wf0; th_export = th_export0; th_known =
    th_known0; th_local = th_local0; th_used = th_used0 }

(** val namespace_eqb : namespace -> namespace -> bool **)

let rec namespace_eqb n1 n2 =
  (&&)
    ((&&)
      ((&&) (Mstr.equal ts_equal (ns_ts n1) (ns_ts n2))
        (Mstr.equal ls_equal (ns_ls n1) (ns_ls n2)))
      (Mstr.equal pr_equal (ns_pr n1) (ns_pr n2)))
    (pmap_eqb (tuple_eqb (=) namespace_eqb)
      ((fun x -> mstr_to_pmap (ns_ns x)) n1)
      ((fun x -> mstr_to_pmap (ns_ns x)) n2))

(** val meta_arg_type_beq : meta_arg_type -> meta_arg_type -> bool **)

let meta_arg_type_beq x y =
  match x with
  | MTty -> (match y with
             | MTty -> true
             | _ -> false)
  | MTtysymbol -> (match y with
                   | MTtysymbol -> true
                   | _ -> false)
  | MTlsymbol -> (match y with
                  | MTlsymbol -> true
                  | _ -> false)
  | MTprsymbol -> (match y with
                   | MTprsymbol -> true
                   | _ -> false)
  | MTstring -> (match y with
                 | MTstring -> true
                 | _ -> false)
  | MTint -> (match y with
              | MTint -> true
              | _ -> false)
  | MTid -> (match y with
             | MTid -> true
             | _ -> false)

(** val meta_arg_type_eq_dec : meta_arg_type -> meta_arg_type -> bool **)

let meta_arg_type_eq_dec x y =
  let b = meta_arg_type_beq x y in if b then true else false

(** val meta_arg_type_eqb : meta_arg_type -> meta_arg_type -> bool **)

let meta_arg_type_eqb =
  meta_arg_type_beq

(** val meta_arg_eqb : meta_arg -> meta_arg -> bool **)

let meta_arg_eqb m1 m2 =
  match m1 with
  | MAty t1 -> (match m2 with
                | MAty t2 -> ty_equal t1 t2
                | _ -> false)
  | MAts t1 -> (match m2 with
                | MAts t2 -> ts_equal t1 t2
                | _ -> false)
  | MAls l1 -> (match m2 with
                | MAls l2 -> ls_equal l1 l2
                | _ -> false)
  | MApr p1 -> (match m2 with
                | MApr p2 -> pr_equal p1 p2
                | _ -> false)
  | MAstr s1 -> (match m2 with
                 | MAstr s2 -> (=) s1 s2
                 | _ -> false)
  | MAint i1 -> (match m2 with
                 | MAint i2 -> BigInt.eq i1 i2
                 | _ -> false)
  | MAid i1 -> (match m2 with
                | MAid i2 -> id_equal i1 i2
                | _ -> false)

(** val meta_eqb : meta -> meta -> bool **)

let meta_eqb m1 m2 =
  (&&)
    ((&&)
      ((&&)
        ((&&) (BigInt.eq m1.meta_tag m2.meta_tag)
          ((=) m1.meta_name m2.meta_name))
        (list_eqb meta_arg_type_eqb m1.meta_type m2.meta_type))
      (eqb m1.meta_excl m2.meta_excl)) ((=) m1.meta_desc m2.meta_desc)

(** val symbol_map_eqb : symbol_map -> symbol_map -> bool **)

let symbol_map_eqb s1 s2 =
  (&&)
    ((&&)
      ((&&) (Mts.equal ty_eqb s1.sm_ty s2.sm_ty)
        (Mts.equal ts_equal s1.sm_ts s2.sm_ts))
      (Mls.equal ls_equal s1.sm_ls s2.sm_ls))
    (Mpr.equal pr_equal s1.sm_pr s2.sm_pr)

(** val theory_eqb : tdecl_node theory_o -> tdecl_node theory_o -> bool **)

let rec theory_eqb t1 t2 =
  (&&)
    ((&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&)
                    ((&&) (id_equal (th_name t1) (th_name t2))
                      (list_eqb (=) (th_path t1) (th_path t2)))
                    (list_eqb tdecl_eqb (th_decls t1) (th_decls t2)))
                  (zmap_eqb (tuple_eqb ts_equal tdecl_eqb)
                    ((fun x -> mts_to_zmap (th_ranges x)) t1)
                    ((fun x -> mts_to_zmap (th_ranges x)) t2)))
                (zmap_eqb (tuple_eqb ts_equal tdecl_eqb)
                  ((fun x -> mts_to_zmap (th_floats x)) t1)
                  ((fun x -> mts_to_zmap (th_floats x)) t2)))
              (t_eqb (th_crcmap t1) (th_crcmap t2)))
            (Mls.equal (tuple_eqb pr_equal ls_equal) (th_proved_wf t1)
              (th_proved_wf t2)))
          (namespace_eqb (th_export t1) (th_export t2)))
        (Mid.equal d_equal (th_known t1) (th_known t2)))
      (Sid.equal (th_local t1) (th_local t2)))
    (Sid.equal (th_used t1) (th_used t2))

(** val tdecl_eqb : tdecl_node tdecl_o -> tdecl_node tdecl_o -> bool **)

and tdecl_eqb t1 t2 =
  (&&) (BigInt.eq (td_tag t1) (td_tag t2))
    (tdecl_node_eqb (td_node t1) (td_node t2))

(** val tdecl_node_eqb : tdecl_node -> tdecl_node -> bool **)

and tdecl_node_eqb t1 t2 =
  match t1 with
  | Decl d1 -> (match t2 with
                | Decl d2 -> d_equal d1 d2
                | _ -> false)
  | Use t3 -> (match t2 with
               | Use t4 -> theory_eqb t3 t4
               | _ -> false)
  | Clone (t3, s1) ->
    (match t2 with
     | Clone (t4, s2) -> (&&) (theory_eqb t3 t4) (symbol_map_eqb s1 s2)
     | _ -> false)
  | Meta (m1, a1) ->
    (match t2 with
     | Meta (m2, a2) -> (&&) (meta_eqb m1 m2) (list_eqb meta_arg_eqb a1 a2)
     | _ -> false)

(** val meta_equal : meta -> meta -> bool **)

let meta_equal =
  (fun x y -> x == y || meta_eqb x y)

(** val meta_hash : meta -> BigInt.t **)

let meta_hash m =
  m.meta_tag

module MetaTag =
 struct
  module MetaTagDec =
   struct
    type t = meta

    (** val tag : meta -> BigInt.t **)

    let tag m =
      m.meta_tag

    (** val equal : meta -> meta -> bool **)

    let equal =
      (fun x y -> x == y || meta_eqb x y)
   end

  type t = MetaTagDec.t

  (** val tag : MetaTagDec.t -> BigInt.t **)

  let tag =
    MetaTagDec.tag

  (** val equal : MetaTagDec.t -> MetaTagDec.t -> bool **)

  let equal =
    MetaTagDec.equal
 end

module SMmeta1 = MakeMS(MetaTag)

module Smeta = SMmeta1.S

module Mmeta = SMmeta1.M

module TdeclTag =
 struct
  module TdeclTagDec =
   struct
    type t = tdecl_node tdecl_o

    (** val tag : tdecl_node tdecl_o -> BigInt.t **)

    let tag =
      td_tag

    (** val equal : tdecl_node tdecl_o -> tdecl_node tdecl_o -> bool **)

    let equal =
      tdecl_eqb
   end

  type t = TdeclTagDec.t

  (** val tag : TdeclTagDec.t -> BigInt.t **)

  let tag =
    TdeclTagDec.tag

  (** val equal : TdeclTagDec.t -> TdeclTagDec.t -> bool **)

  let equal =
    TdeclTagDec.equal
 end

module Tdecl1 = MakeMS(TdeclTag)

module Stdecl1 = Tdecl1.S

module Mtdecl1 = Tdecl1.M

(** val td_equal : tdecl_node tdecl_o -> tdecl_node tdecl_o -> bool **)

let td_equal =
  (fun x y -> x == y || tdecl_eqb x y)

(** val td_hash : tdecl_node tdecl_o -> BigInt.t **)

let td_hash =
  td_tag

module TdeclHash =
 struct
  type t = tdecl_node tdecl_o

  (** val eq_marg : meta_arg -> meta_arg -> bool **)

  let eq_marg m1 m2 =
    match m1 with
    | MAty t1 -> (match m2 with
                  | MAty t2 -> ty_equal t1 t2
                  | _ -> false)
    | MAts t1 -> (match m2 with
                  | MAts t2 -> ts_equal t1 t2
                  | _ -> false)
    | MAls l1 -> (match m2 with
                  | MAls l2 -> ls_equal l1 l2
                  | _ -> false)
    | MApr p1 -> (match m2 with
                  | MApr p2 -> pr_equal p1 p2
                  | _ -> false)
    | MAstr s1 -> (match m2 with
                   | MAstr s2 -> (=) s1 s2
                   | _ -> false)
    | MAint i1 -> (match m2 with
                   | MAint i2 -> BigInt.eq i1 i2
                   | _ -> false)
    | MAid _ -> false

  (** val eq_smap : symbol_map -> symbol_map -> bool **)

  let eq_smap =
    symbol_map_eqb

  (** val equal : tdecl_node tdecl_o -> tdecl_node tdecl_o -> bool **)

  let equal td1 td2 =
    match td_node td1 with
    | Decl d1 ->
      (match td_node td2 with
       | Decl d2 -> d_equal d1 d2
       | _ -> false)
    | Use th1 ->
      (match td_node td2 with
       | Use th2 -> id_equal (th_name th1) (th_name th2)
       | _ -> false)
    | Clone (th1, sm1) ->
      (match td_node td2 with
       | Clone (th2, sm2) ->
         (&&) (id_equal (th_name th1) (th_name th2)) (eq_smap sm1 sm2)
       | _ -> false)
    | Meta (t1, al1) ->
      (match td_node td2 with
       | Meta (t2, al2) ->
         (&&) ((fun x y -> x == y || meta_eqb x y) t1 t2)
           (list_eqb eq_marg al1 al2)
       | _ -> false)

  (** val hs_cl_ty : 'a1 -> ty_node_c ty_o -> BigInt.t -> BigInt.t **)

  let hs_cl_ty _ ty acc =
    combine_big acc (ty_hash ty)

  (** val hs_cl_ts :
      'a1 -> (ty_node_c ty_o) tysymbol_o -> BigInt.t -> BigInt.t **)

  let hs_cl_ts _ ts acc =
    combine_big acc (ts_hash ts)

  (** val hs_cl_ls : 'a1 -> lsymbol -> BigInt.t -> BigInt.t **)

  let hs_cl_ls _ ls acc =
    combine_big acc (ls_hash ls)

  (** val hs_cl_pr : 'a1 -> prsymbol -> BigInt.t -> BigInt.t **)

  let hs_cl_pr _ pr acc =
    combine_big acc (pr_hash pr)

  (** val hs_ta : meta_arg -> tag **)

  let hs_ta = function
  | MAty ty -> ty_hash ty
  | MAts ts -> ts_hash ts
  | MAls ls -> ls_hash ls
  | MApr pr -> pr_hash pr
  | MAstr s -> (fun s -> (BigInt.of_int (Hashtbl.hash s))) s
  | MAint i -> i
  | MAid i -> id_hash i

  (** val hs_smap : symbol_map -> BigInt.t -> BigInt.t **)

  let hs_smap sm h =
    Mts.fold hs_cl_ty sm.sm_ty
      (Mts.fold hs_cl_ts sm.sm_ts
        (Mls.fold hs_cl_ls sm.sm_ls (Mpr.fold hs_cl_pr sm.sm_pr h)))

  (** val hash : tdecl_node tdecl_o -> BigInt.t **)

  let hash td =
    match td_node td with
    | Decl d -> d_hash d
    | Use th -> id_hash (th_name th)
    | Clone (th, sm) -> hs_smap sm (id_hash (th_name th))
    | Meta (t0, al) -> combine_big_list hs_ta (meta_hash t0) al

  (** val tag : BigInt.t -> tdecl_node tdecl_o -> tdecl_node tdecl_o **)

  let tag n td =
    (fun (x1, x2) -> build_tdecl_o x1 x2) ((td_node td), n)
 end

module Hstdecl = Make(TdeclHash)

(** val mk_tdecl :
    tdecl_node -> (tdecl_node tdecl_o hashcons_ty, tdecl_node tdecl_o) st **)

let mk_tdecl n =
  Hstdecl.hashcons ((fun (x1, x2) -> build_tdecl_o x1 x2) (n,
    (BigInt.of_int (-1))))

(** val create_decl :
    decl -> (tdecl_node tdecl_o hashcons_ty, tdecl_node tdecl_o) st **)

let create_decl d =
  mk_tdecl (Decl d)
exception BadMetaArity of meta * BigInt.t
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type








(** val get_meta_arg_type : meta_arg -> meta_arg_type **)

let get_meta_arg_type = function
| MAty _ -> MTty
| MAts _ -> MTtysymbol
| MAls _ -> MTlsymbol
| MApr _ -> MTprsymbol
| MAstr _ -> MTstring
| MAint _ -> MTint
| MAid _ -> MTid

(** val create_meta :
    meta -> meta_arg list -> (ty_node_c ty_o hashcons_ty*tdecl_node tdecl_o
    hashcons_ty, tdecl_node tdecl_o) errState **)

let create_meta m al =
  let get_meta_arg = fun aty a ->
    (@@) (fun a0 ->
      let mt = get_meta_arg_type a0 in
      if meta_arg_type_eqb aty mt
      then (fun x -> x) a0
      else 
             (raise
               ((fun ((x, y), z) -> MetaTypeMismatch (x, y, z)) ((m,aty),mt))))
      (match aty with
       | MTty ->
         (match a with
          | MAts ts ->
            (match ts_args ts with
             | [] -> (@@) (fun t1 -> (fun x -> x) (MAty t1)) (ty_app ts [])
             | _::_ -> (fun x -> x) a)
          | _ -> (fun x -> x) a)
       | MTtysymbol ->
         (match a with
          | MAty t ->
            (fun x -> x)
              (match ty_node t with
               | Tyvar _ -> a
               | Tyapp (ts, l) -> if null l then MAts ts else a)
          | _ -> (fun x -> x) a)
       | _ -> (fun x -> x) a)
  in
  if (&&) (null m.meta_type) (list_eqb meta_arg_eqb ((MAstr "")::[]) al)
  then  ( (mk_tdecl (Meta (m, []))))
  else (@@) (fun o ->
         match o with
         | Some al0 ->  ( (mk_tdecl (Meta (m, al0))))
         | None ->  (raise (BadMetaArity (m,(int_length al)))))
         ( (map2_errst get_meta_arg m.meta_type al))

(** val create_use :
    tdecl_node theory_o -> (tdecl_node tdecl_o hashcons_ty,
    tdecl_node tdecl_o) st **)

let create_use th =
  mk_tdecl (Use th)
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


let warning_clone_not_abstract =
  Loc.register_warning "clone_not_abstract" "Warn about theories cloned without substituting any abstract symbols"

(** Namespace *)

(* type namespace = {
  ns_ts : tysymbol Mstr.t;   (* type symbols *)
  ns_ls : lsymbol Mstr.t;    (* logic symbols *)
  ns_pr : prsymbol Mstr.t;   (* propositions *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
} *)

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ls = Mstr.empty;
  ns_pr = Mstr.empty;
  ns_ns = Mstr.empty;
}

exception ClashSymbol of string

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let merge_ts = ns_replace ts_equal
let merge_ls = ns_replace ls_equal
let merge_pr = ns_replace pr_equal

let rec merge_ns chk _ no nn =
  if no == nn then no else
  let union merge o n =
    let merge x vo vn = Some (merge chk x vo vn) in
    if o == n then o else Mstr.union merge o n in
  { ns_ts = union merge_ts no.ns_ts nn.ns_ts;
    ns_ls = union merge_ls no.ns_ls nn.ns_ls;
    ns_pr = union merge_pr no.ns_pr nn.ns_pr;
    ns_ns = union merge_ns no.ns_ns nn.ns_ns }

let ns_add merge chk x vn m = Mstr.change (function
  | Some vo -> Some (merge chk x vo vn)
  | None    -> Some vn) x m

let add_ts chk x ts ns =
  let loc = x.id_loc in
  { ns with ns_ts = Loc.try5 ?loc ns_add merge_ts chk x.id_string ts ns.ns_ts }
let add_ls chk x ps ns =
  let loc = x.id_loc in
  { ns with ns_ls = Loc.try5 ?loc ns_add merge_ls chk x.id_string ps ns.ns_ls }
let add_pr chk x xs ns =
  let loc = x.id_loc in
  { ns with ns_pr = Loc.try5 ?loc ns_add merge_pr chk x.id_string xs ns.ns_pr }
let add_ns chk x nn ns = { ns with ns_ns = ns_add merge_ns chk x nn ns.ns_ns }

let merge_ns chk nn no = merge_ns chk "" no nn (* swap arguments *)

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ls = ns_find (fun ns -> ns.ns_ls)
let ns_find_pr = ns_find (fun ns -> ns.ns_pr)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(** Meta properties *)

(* type meta_arg_type =
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint
  | MTid

type meta_arg =
  | MAty  of ty
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int
  | MAid of ident

type meta = {
  meta_name : string;
  meta_type : meta_arg_type list;
  meta_excl : bool;
  meta_desc : Pp.formatted;
  meta_tag  : BigInt.t;
} *)

let print_meta_desc fmt m =
  fprintf fmt "@[%s@\n  @[%a@]@]"
    m.meta_name Pp.formatted m.meta_desc

module SMmeta = MakeMSH(struct type t = meta let tag m = m.meta_tag let equal = (==) (*JOSH TODO equal*) end)

(* module Smeta = SMmeta.S
module Mmeta = SMmeta.M *)
module Hmeta = SMmeta.H

(* let meta_equal : meta -> meta -> bool = (==)

let meta_hash m = m.meta_tag *)

exception KnownMeta of meta
exception UnknownMeta of string
(* exception BadMetaArity of meta * int *)
(* exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type *)
exception IllFormedMeta of meta * string

let meta_table = Hstr.create 17

(*JOSH TODO reduce duplication*)
let big_incr =
  fun r -> r := BigInt.succ !r

let mk_meta =
  let c = ref (BigInt.of_int (-1)) in
  fun desc s al excl -> {
    meta_name = s;
    meta_type = al;
    meta_excl = excl;
    meta_desc = desc;
    meta_tag  = (big_incr c; !c);
  }

let register_meta ~desc s al excl =
  try
    let m = Hstr.find meta_table s in
    if al = m.meta_type && excl = m.meta_excl then m
    else raise (KnownMeta m)
  with Not_found ->
    let m = mk_meta desc s al excl in
    Hstr.add meta_table s m;
    m

let register_meta_excl ~desc s al = register_meta ~desc s al true
let register_meta      ~desc s al = register_meta ~desc s al false

let lookup_meta s = Hstr.find_exn meta_table (UnknownMeta s) s

let list_metas () = Hstr.fold (fun _ v acc -> v::acc) meta_table []

let meta_range = register_meta "range_type" [MTtysymbol; MTlsymbol]
    ~desc:"Projection@ of@ a@ range@ type."

let meta_float = register_meta "float_type" [MTtysymbol; MTlsymbol; MTlsymbol]
    ~desc:"Projection@ and@ finiteness@ of@ a@ floating-point@ type."

let meta_proved_wf =
  register_meta "vc:proved_wf" [MTlsymbol; MTprsymbol]
    ~desc:"Declares that the given predicate is proved well-founded by the given goal"

let meta_model_projection = register_meta "model_projection" [MTlsymbol]
  ~desc:"Declare@ the@ projection."

let meta_record = register_meta "model_record" [MTlsymbol]
  ~desc:"Declare@ the@ record field."

(** Theory *)
(* 
type theory = {
  th_name   : ident;          (* theory name *)
  th_path   : string list;    (* environment qualifiers *)
  th_decls  : tdecl list;     (* theory declarations *)
  th_ranges : tdecl Mts.t;    (* range type projections *)
  th_floats : tdecl Mts.t;    (* float type projections *)
  th_crcmap : Coercion.t;     (* implicit coercions *)
  th_proved_wf : (prsymbol * lsymbol) Mls.t; (* predicates proved well-founded *)
  th_export : namespace;      (* exported namespace *)
  th_known  : known_map;      (* known identifiers *)
  th_local  : Sid.t;          (* locally declared idents *)
  th_used   : Sid.t;          (* used theories *)
}

and tdecl = {
  td_node : tdecl_node;
  td_tag  : BigInt.t;
}

and tdecl_node =
  | Decl  of decl
  | Use   of theory
  | Clone of theory * symbol_map
  | Meta  of meta * meta_arg list

and symbol_map = {
  sm_ty : ty Mts.t;
  sm_ts : tysymbol Mts.t;
  sm_ls : lsymbol Mls.t;
  sm_pr : prsymbol Mpr.t;
} *)

(** Theory declarations *)

(* module Hstdecl = Hashcons.Make (struct

  type t = tdecl

  let eq_marg a1 a2 = match a1,a2 with
    | MAty ty1, MAty ty2 -> ty_equal ty1 ty2
    | MAts ts1, MAts ts2 -> ts_equal ts1 ts2
    | MAls ls1, MAls ls2 -> ls_equal ls1 ls2
    | MApr pr1, MApr pr2 -> pr_equal pr1 pr2
    | MAstr s1, MAstr s2 -> s1 = s2
    | MAint i1, MAint i2 -> i1 = i2
    | _,_ -> false

  let eq_smap sm1 sm2 =
    Mts.equal ty_equal sm1.sm_ty sm2.sm_ty &&
    Mts.equal ts_equal sm1.sm_ts sm2.sm_ts &&
    Mls.equal ls_equal sm1.sm_ls sm2.sm_ls &&
    Mpr.equal pr_equal sm1.sm_pr sm2.sm_pr

  let equal td1 td2 = match td1.td_node, td2.td_node with
    | Decl d1, Decl d2 -> d_equal d1 d2
    | Use th1, Use th2 -> id_equal th1.th_name th2.th_name
    | Clone (th1,sm1), Clone (th2,sm2) ->
        id_equal th1.th_name th2.th_name && eq_smap sm1 sm2
    | Meta (t1,al1), Meta (t2,al2) ->
        t1 = t2 && Lists.equal eq_marg al1 al2
    | _,_ -> false

  let hs_cl_ty _ ty acc = Hashcons.combine_big acc (ty_hash ty)
  let hs_cl_ts _ ts acc = Hashcons.combine_big acc (ts_hash ts)
  let hs_cl_ls _ ls acc = Hashcons.combine_big acc (ls_hash ls)
  let hs_cl_pr _ pr acc = Hashcons.combine_big acc (pr_hash pr)

  let hs_ta = function
    | MAty ty -> ty_hash ty
    | MAts ts -> ts_hash ts
    | MAls ls -> ls_hash ls
    | MApr pr -> pr_hash pr
    | MAstr s -> BigInt.of_int (Hashtbl.hash s)
    | MAint i -> BigInt.of_int (Hashtbl.hash i)
    | MAid i -> Ident.id_hash i

  let hs_smap sm h =
    Mts.fold hs_cl_ty sm.sm_ty
      (Mts.fold hs_cl_ts sm.sm_ts
        (Mls.fold hs_cl_ls sm.sm_ls
          (Mpr.fold hs_cl_pr sm.sm_pr h)))

  let hash td =  (match td.td_node with
    | Decl d -> d_hash d 
    | Use th -> id_hash th.th_name 
    | Clone (th,sm) -> hs_smap sm  (id_hash th.th_name)
    | Meta (t,al) -> Hashcons.combine_big_list hs_ta (BigInt.of_int (Hashtbl.hash t)) al) 

  let tag n td = { td with td_tag = n }

end)

let mk_tdecl n = Hstdecl.hashcons { td_node = n ; td_tag = BigInt.of_int(-1) } *)

module Tdecl = MakeMSH (struct
  type t = tdecl
  let tag td = td.td_tag
  let equal = (==) (*JOSH TODO equal*)
end)

module Stdecl = Tdecl.S
module Mtdecl = Tdecl.M
module Htdecl = Tdecl.H

(* let td_equal : tdecl -> tdecl -> bool = (==) *)
(* let td_hash td = td.td_tag *)

(** Constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_path   : string list;
  uc_decls  : tdecl list;
  uc_ranges : tdecl Mts.t;
  uc_floats : tdecl Mts.t;
  uc_crcmap : Coercion.t;
  uc_proved_wf : (prsymbol * lsymbol) Mls.t;
  uc_prefix : string list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_known  : known_map;
  uc_local  : Sid.t;
  uc_used   : Sid.t;
}

exception CloseTheory
exception NoOpenedNamespace

let empty_theory n p = {
  uc_name   = id_register n;
  uc_path   = p;
  uc_decls  = [];
  uc_ranges = Mts.empty;
  uc_floats = Mts.empty;
  uc_crcmap = Coercion.empty;
  uc_proved_wf = Mls.empty;
  uc_prefix = [];
  uc_import = [empty_ns];
  uc_export = [empty_ns];
  uc_known  = Mid.empty;
  uc_local  = Sid.empty;
  uc_used   = Sid.empty;
}

let close_theory uc = match uc.uc_export with
  | [e] ->
    { th_name   = uc.uc_name;
      th_path   = uc.uc_path;
      th_decls  = List.rev uc.uc_decls;
      th_ranges = uc.uc_ranges;
      th_floats = uc.uc_floats;
      th_crcmap = uc.uc_crcmap;
      th_proved_wf = uc.uc_proved_wf;
      th_export = e;
      th_known  = uc.uc_known;
      th_local  = uc.uc_local;
      th_used   = uc.uc_used }
  | _ -> raise CloseTheory

let get_namespace uc = List.hd uc.uc_import

let open_scope uc s = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_prefix =        s :: uc.uc_prefix;
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

let close_scope uc ~import =
  match uc.uc_prefix, uc.uc_import, uc.uc_export with
  | s :: prf, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with uc_prefix = prf; uc_import = i1::sti; uc_export = e1::ste; }
  | [], [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

let import_namespace ns ql =
  match ns_find_ns ns ql with
  | e0 -> merge_ns false e0 ns
  | exception Not_found ->
      Loc.errorm "unknown scope %s" (String.concat "." ql)

let import_scope uc ql =
  match uc.uc_import with
  | i1 :: sti ->
     let i1 = import_namespace i1 ql in
     { uc with uc_import = i1::sti }
  | _ -> assert false

(* Base constructors *)

let known_ty kn ty =
  ty_s_fold (fun () ts -> known_id kn ts.ts_name) () ty

let known_clone kn sm =
  Mts.iter (fun _ ty -> known_ty kn ty) sm.sm_ty;
  Mts.iter (fun _ ts -> known_id kn ts.ts_name) sm.sm_ts;
  Mls.iter (fun _ ls -> known_id kn ls.ls_name) sm.sm_ls;
  Mpr.iter (fun _ pr -> known_id kn pr.pr_name) sm.sm_pr

let known_meta kn al =
  let check = function
    | MAty ty -> known_ty kn ty
    | MAts ts -> known_id kn ts.ts_name
    | MAls ls -> known_id kn ls.ls_name
    | MApr pr -> known_id kn pr.pr_name
    | _ -> ()
  in
  List.iter check al

(* FIXME: proper description *)
let meta_coercion = register_meta ~desc:"coercion" "coercion" [MTlsymbol]

exception RangeConflict of tysymbol
exception FloatConflict of tysymbol
exception ProvedWfConflict of lsymbol
exception IllFormedWf of prsymbol * lsymbol

let add_tdecl uc td = match td.td_node with
  | Decl d -> 
    let (d1, kn) = known_add_decl uc.uc_known d in
    let td1 = mk_tdecl (Decl d1) in
    { uc with
      uc_decls = td1 :: uc.uc_decls;
      uc_known = kn;
      uc_local = Sid.union uc.uc_local d.d_news }
  | Use th when Sid.mem th.th_name uc.uc_used -> uc
  | Use th -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = merge_known uc.uc_known th.th_known;
      uc_used  = Sid.union uc.uc_used (Sid.add th.th_name th.th_used) }
  | Clone (_,sm) -> known_clone uc.uc_known sm;
      { uc with uc_decls = td :: uc.uc_decls }
  | Meta (m,((MAts ts :: _) as al)) when meta_equal m meta_range ->
      known_meta uc.uc_known al;
      let add b = match b with
        | None -> Some td
        | Some d when td_equal d td -> b
        | _ -> raise (RangeConflict ts) in
      { uc with uc_ranges = Mts.change add ts uc.uc_ranges;
                uc_decls = td :: uc.uc_decls }
  | Meta (m,((MAts ts :: _) as al)) when meta_equal m meta_float ->
      known_meta uc.uc_known al;
      let add b = match b with
        | None -> Some td
        | Some d when td_equal d td -> b
        | _ -> raise (FloatConflict ts) in
      { uc with uc_floats = Mts.change add ts uc.uc_floats;
                uc_decls = td :: uc.uc_decls }
  | Meta (m,([MAls ls] as al)) when meta_equal m meta_coercion ->
      known_meta uc.uc_known al;
      { uc with uc_crcmap = Coercion.add uc.uc_crcmap ls;
                uc_decls = td :: uc.uc_decls }
  | Meta (m,([MAls ls; MApr pr] as al)) when meta_equal m meta_proved_wf ->
      let p =
        match (Mid.find pr.pr_name uc.uc_known).d_node with
        | exception Not_found ->
            raise (UnknownIdent pr.pr_name)
        | Dprop (_,_,{ t_node = Tapp(p,[t])}) ->
            let (vl,_,u) = t_open_lambda t in
            begin match vl,u.t_node with
              | [x;y],Tapp(r,[{t_node = Tvar a};{t_node = Tvar b}])
                when vs_equal x a && vs_equal y b && ls_equal r ls ->
                  p
              | _ ->
                  raise (IllFormedWf(pr,ls))
            end
        | _ ->
            raise (IllFormedWf(pr,ls))
      in
      known_meta uc.uc_known al;
      { uc with uc_proved_wf = Mls.add ls (pr,p) uc.uc_proved_wf;
                uc_decls = td :: uc.uc_decls }
  | Meta (m, ([MAls ls] as al)) when meta_equal m meta_model_projection ->
    begin match ls.ls_args with
      | [ty] ->
          begin
            match ty.ty_node with
            | Tyvar _ ->
                raise (IllFormedMeta(m,"the given lsymbol should not be polymorphic"))
            | Tyapp ({ ts_def = Ty.Alias _; _},_) ->
                raise (IllFormedMeta(m,"the type of the given lsymbol should not be an alias type"))
            | _ -> ()
          end
      | _ -> raise (IllFormedMeta(m,"the given lsymbol should have exactly one argument"))
    end;
    known_meta uc.uc_known al;
    { uc with uc_decls = td :: uc.uc_decls }
  | Meta (_,al) ->
      known_meta uc.uc_known al;
      { uc with uc_decls = td :: uc.uc_decls }

(** Declarations *)

let store_path, store_theory, restore_path, restore_theory =
  let id_to_path = Wid.create 17 in
  let id_to_th = Wid.create 17 in
  let store_path uc path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.uc_prefix) in
    Wid.set id_to_path id (uc.uc_path, uc.uc_name.id_string, prefix)
  in
  let store_theory th =
    let id = th.th_name in
    (* this symbol is already a theory *)
    if Wid.mem id_to_path id then () else begin
        Wid.set id_to_path id (th.th_path, id.id_string, []);
        Sid.iter (fun id -> Wid.set id_to_th id th) th.th_local;
        Wid.set id_to_th id th;
      end
  in
  let restore_path id = Wid.find id_to_path id in
  let restore_theory id = Wid.find id_to_th id in
  store_path, store_theory, restore_path, restore_theory

let close_theory uc =
  let th = close_theory uc in
  store_theory th;
  th

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id v i0 :: sti;
      uc_export = add true  id v e0 :: ste }
  | _ -> assert false

let add_symbol_ts uc ts = add_symbol add_ts ts.ts_name ts uc

let add_symbol_ls uc ({ls_name = id} as ls) =
  let {id_string = nm; id_loc = loc} = id in
  if (nm = Ident.op_equ || nm = Ident.op_neq) &&
      uc.uc_path <> ["why3";"BuiltIn"] then
    Loc.errorm ?loc "Logical equality cannot be redefined";
  add_symbol add_ls id ls uc

let add_symbol_pr uc pr = add_symbol add_pr pr.pr_name pr uc

(* let create_decl d = mk_tdecl (Decl d) *)

let print_id fmt id = Ident.print_decoded fmt id.id_string

let warn_axiom_abstract =
  Loc.register_warning "axiom_abstract" "Warn when some axiom does not contain any abstract symbol"

let warn_dubious_axiom uc k p syms =
  match k with
  | Plemma | Pgoal -> ()
  | Paxiom ->
    try
      Sid.iter
        (fun id ->
          if Sid.mem id uc.uc_local then
          match (Ident.Mid.find id uc.uc_known).d_node with
          | Dtype { ts_def = NoDef } | Dparam _ -> raise Exit
          | _ -> ())
        syms;
      Loc.warning warn_axiom_abstract ?loc:p.id_loc
        "@[axiom %s does not contain any local abstract symbol@ \
          (contains: @[%a@])@]" p.id_string
        (Pp.print_list Pp.comma print_id) (Sid.elements syms)
    with Exit -> ()

let attr_w_non_conservative_extension_no =
  Ident.create_attribute "W:non_conservative_extension:N"

let should_be_conservative id =
  not (Sattr.mem attr_w_non_conservative_extension_no id.id_attrs)

let add_decl ?(warn=true) uc d =
  let uc = add_tdecl uc (create_decl d) in
  match d.d_node with
  | Dtype ts  ->
      add_symbol_ts uc ts
  | Ddata dl  ->
      let add_field uc = function
        | Some pj -> add_symbol_ls uc pj
        | None -> uc in
      let add_constr uc (cs,pl) =
        let uc = add_symbol_ls uc cs in
        List.fold_left add_field uc pl in
      let add_data uc (ts,csl) =
        let uc = add_symbol_ts uc ts in
        List.fold_left add_constr uc csl in
      List.fold_left add_data uc dl
  | Dparam ls ->
      add_symbol_ls uc ls
  | Dlogic dl ->
      let add_logic uc (ls,_) = add_symbol_ls uc ls in
      List.fold_left add_logic uc dl
  | Dind (_, dl) ->
      let add_ind uc (ps,la) =
        let uc = add_symbol_ls uc ps in
        let add uc (pr,_) = add_symbol_pr uc pr in
        List.fold_left add uc la in
      List.fold_left add_ind uc dl
  | Dprop (k,pr,_) ->
      if warn && should_be_conservative uc.uc_name &&
         should_be_conservative pr.pr_name
      then warn_dubious_axiom uc k pr.pr_name (get_used_syms_decl d);
      add_symbol_pr uc pr

(** Declaration constructors + add_decl *)

let add_ty_decl uc ts = add_decl ~warn:false uc (create_ty_decl ts)
let add_data_decl uc dl = add_decl ~warn:false uc (create_data_decl dl)
let add_param_decl uc ls = add_decl ~warn:false uc (create_param_decl ls)
let add_logic_decl uc dl = add_decl ~warn:false uc (create_logic_decl dl)
let add_ind_decl uc s dl = add_decl ~warn:false uc (create_ind_decl s dl)
let add_prop_decl ?warn uc k p f = add_decl ?warn uc (create_prop_decl k p f)

(** Use *)

let create_use th = mk_tdecl (Use th)

let use_export uc th =
  let uc = add_tdecl uc (create_use th) in
  let urng ts d1 d2 = if td_equal d1 d2 then Some d1
                      else raise (RangeConflict ts) in
  let uflt ts d1 d2 = if td_equal d1 d2 then Some d1
                      else raise (FloatConflict ts) in
  let upwf ls (pr1,ls1) (pr2,ls2) = if pr_equal pr1 pr2 && ls_equal ls1 ls2 then Some (pr1,ls1)
                      else raise (ProvedWfConflict ls) in
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false th.th_export i0 :: sti;
      uc_export = merge_ns true  th.th_export e0 :: ste;
      uc_ranges = Mts.union urng uc.uc_ranges th.th_ranges;
      uc_floats = Mts.union uflt uc.uc_floats th.th_floats;
      uc_proved_wf = Mls.union upwf uc.uc_proved_wf th.th_proved_wf;
      uc_crcmap = Coercion.union uc.uc_crcmap th.th_crcmap }
  | _ -> assert false

(** Clone *)

type th_inst = {
  inst_ty : ty Mts.t;
  inst_ts : tysymbol Mts.t;
  inst_ls : lsymbol Mls.t;
  inst_pr : prop_kind Mpr.t;
  inst_df : prop_kind;
}

let empty_inst = {
  inst_ty = Mts.empty;
  inst_ts = Mts.empty;
  inst_ls = Mls.empty;
  inst_pr = Mpr.empty;
  inst_df = Plemma;
}

exception CannotInstantiate of ident

type clones = {
  cl_local : Sid.t;
  mutable ty_table : ty Mts.t;
  mutable ts_table : tysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
}

let empty_clones th = {
  cl_local = th.th_local;
  ty_table = Mts.empty;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
}

(* populate the clone structure *)

let rec sm_trans_ty tym tsm ty = match ty.ty_node with
  | Tyapp (ts, tyl) ->
      let tyl = List.map (sm_trans_ty tym tsm) tyl in
      begin match Mts.find_opt ts tsm with
      | Some ts -> ty_app ts tyl
      | None -> begin match Mts.find_opt ts tym with
      | Some ty -> ty_inst (ts_match_args ts tyl) ty
      | None -> ty_app ts tyl
      end end
  | Tyvar _ -> ty

let cl_trans_ty cl ty = sm_trans_ty cl.ty_table cl.ts_table ty

let cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then
    match ts.ts_def with
      | Alias ty ->
          let td = cl_trans_ty cl ty in
          if ty_equal td ty then ts else
          let id = id_clone ts.ts_name in
          create_tysymbol id ts.ts_args (Alias td)
      | NoDef | Range _ | Float _ -> ts
  else
  try Mts.find ts cl.ts_table with Not_found -> raise EmptyDecl

let cl_clone_ts cl ts =
  (* cl_clone_ts is only called for local non-instantiated symbols *)
  let td' =
    match ts.ts_def with
    | Alias t -> Alias (cl_trans_ty cl t)
    | NoDef -> NoDef
    | Range ir -> Range ir
    | Float irf -> Float irf in
  let ts' = create_tysymbol (id_clone ts.ts_name) ts.ts_args td' in
  cl.ts_table <- Mts.add ts ts' cl.ts_table;
  ts'

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls else
  try Mls.find ls cl.ls_table with Not_found ->
    let constr = ls.ls_constr in
    let proj = ls.ls_proj in
    let id  = id_clone ls.ls_name in
    let ta' = List.map (cl_trans_ty cl) ls.ls_args in
    let vt' = Option.map (cl_trans_ty cl) ls.ls_value in
    let ls' = create_lsymbol ~proj ~constr id ta' vt' in
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    ls'

let cl_trans_fmla cl f = t_s_map (cl_trans_ty cl) (cl_find_ls cl) f

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr else
  try Mpr.find pr cl.pr_table with Not_found -> raise EmptyDecl

let cl_clone_pr cl pr =
  let attr = Sattr.remove Ident.useraxiom_attr pr.pr_name.id_attrs in
  let pr' = create_prsymbol (id_attr pr.pr_name attr) in
  cl.pr_table <- Mpr.add pr pr' cl.pr_table;
  pr'

(* initialize the clone structure *)

type bad_instance =
  | BadI of ident
  | BadI_ty_vars of tysymbol (* type variable mismatch *)
  | BadI_ty_ner of tysymbol (* non-empty record -> ty *)
  | BadI_ty_impure of tysymbol (* impure type -> ty *)
  | BadI_ty_arity of tysymbol (* tysymbol arity mismatch *)
  | BadI_ty_rec of tysymbol (* instance with a rectype *)
  | BadI_ty_mut_lhs of tysymbol (* incompatible mutability *)
  | BadI_ty_mut_rhs of tysymbol (* incompatible mutability *)
  | BadI_ty_alias of tysymbol (* added aliased fields *)
  | BadI_field of tysymbol * vsymbol (* field not found *)
  | BadI_field_type of tysymbol * vsymbol (* incompatible field type *)
  | BadI_field_ghost of tysymbol * vsymbol (* incompatible ghost status *)
  | BadI_field_mut of tysymbol * vsymbol (* incompatible mutability *)
  | BadI_field_inv of tysymbol * vsymbol (* strengthened invariant *)
  | BadI_ls_type of lsymbol * ty * ty (* lsymbol type mismatch *)
  | BadI_ls_kind of lsymbol (* function/predicate mismatch *)
  | BadI_ls_arity of lsymbol (* lsymbol arity mismatch *)
  | BadI_ls_rs of lsymbol (* "val function" -> "function" *)
  | BadI_rs_arity of ident (* incompatible rsymbol arity *)
  | BadI_rs_type of ident * exn (* rsymbol type mismatch *)
  | BadI_rs_kind of ident (* incompatible rsymbol kind *)
  | BadI_rs_ghost of ident (* incompatible ghost status *)
  | BadI_rs_mask of ident (* incompatible result mask *)
  | BadI_rs_reads of ident * Svs.t (* incompatible dependencies *)
  | BadI_rs_writes of ident * Svs.t (* incompatible write effect *)
  | BadI_rs_taints of ident * Svs.t (* incompatible ghost writes *)
  | BadI_rs_covers of ident * Svs.t (* incompatible written regions *)
  | BadI_rs_resets of ident * Svs.t (* incompatible reset regions *)
  | BadI_rs_raises of ident * Sid.t (* incompatible exception set *)
  | BadI_rs_spoils of ident * Stv.t (* incompatible spoiled tyvars *)
  | BadI_rs_oneway of ident (* incompatible partiality status *)
  | BadI_xs_type of ident (* xsymbol type mismatch *)
  | BadI_xs_mask of ident (* incompatible exception mask *)

exception NonLocal of ident
exception BadInstance of bad_instance

let cl_init_ty cl ({ts_name = id} as ts) ty =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let stv = Stv.of_list ts.ts_args in
  if not (ty_v_all (Stv.contains stv) ty) then raise (BadInstance (BadI id));
  cl.ty_table <- Mts.add ts ty cl.ty_table

let cl_init_ts cl ({ts_name = id} as ts) ts' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  if List.length ts.ts_args <> List.length ts'.ts_args then
    raise (BadInstance (BadI id));
  cl.ts_table <- Mts.add ts ts' cl.ts_table

let cl_init_ls cl ({ls_name = id} as ls) ls' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let mtch sb ty ty' =
    try ty_match sb ty' (cl_trans_ty cl ty)
    with TypeMismatch _ -> raise (BadInstance (BadI id))
  in
  let sb = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> mtch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance (BadI id))
  in
  ignore (try List.fold_left2 mtch sb ls.ls_args ls'.ls_args
    with Invalid_argument _ -> raise (BadInstance (BadI id)));
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl {pr_name = id} _ =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let cl_init th inst =
  let cl = empty_clones th in
  Mts.iter (cl_init_ty cl) inst.inst_ty;
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Mpr.iter (cl_init_pr cl) inst.inst_pr;
  cl

(* clone declarations *)

let cl_type cl inst ts =
  if Mts.mem ts inst.inst_ts || Mts.mem ts inst.inst_ty then
    if ts.ts_def = NoDef then raise EmptyDecl
    else raise (CannotInstantiate ts.ts_name);
  create_ty_decl (cl_clone_ts cl ts)

let cl_data cl inst tdl =
  let add_ls ls =
    if Mls.mem ls inst.inst_ls then raise (CannotInstantiate ls.ls_name);
    cl_find_ls cl ls in
  let add_constr (ls,pl) = add_ls ls, List.map (Option.map add_ls) pl in
  let add_type ts' (_,csl) = ts', List.map add_constr csl in
  let get_type (ts,_) =
    if Mts.mem ts inst.inst_ts || Mts.mem ts inst.inst_ty then
      raise (CannotInstantiate ts.ts_name);
    cl_clone_ts cl ts in
  create_data_decl (List.map2 add_type (List.map get_type tdl) tdl)

let extract_ls_defn f =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  match f.t_node with
    | Tapp (_, [{t_node = Tapp (ls,_)}; f])
    | Tbinop (_, {t_node = Tapp (ls,_)}, f) -> make_ls_defn ls vl f
    | _ -> assert false

let cl_param cl inst ls =
  if Mls.mem ls inst.inst_ls then raise EmptyDecl;
  create_param_decl (cl_find_ls cl ls)

let cl_logic cl inst ldl =
  let add_logic (ls,ld) =
    if Mls.mem ls inst.inst_ls then raise (CannotInstantiate ls.ls_name);
    extract_ls_defn (cl_trans_fmla cl (ls_defn_axiom ld))
  in
  create_logic_decl (List.map add_logic ldl)

let cl_ind cl inst (s, idl) =
  let add_case (pr,f) =
    if Mpr.mem pr inst.inst_pr then raise (CannotInstantiate pr.pr_name);
    cl_clone_pr cl pr, cl_trans_fmla cl f
  in
  let add_ind (ps,la) =
    if Mls.mem ps inst.inst_ls
      then raise (CannotInstantiate ps.ls_name)
      else cl_find_ls cl ps, List.map add_case la
  in
  create_ind_decl s (List.map add_ind idl)

let cl_prop cl inst (k,pr,f) =
  let k' = match k, Mpr.find_opt pr inst.inst_pr with
    | Pgoal, _ -> raise EmptyDecl
    | Plemma, Some Pgoal -> raise EmptyDecl
    | Plemma, _ -> Plemma
    | Paxiom, Some k -> k
    | Paxiom, None -> inst.inst_df in
  let pr' = cl_clone_pr cl pr in
  let f' = cl_trans_fmla cl f in
  create_prop_decl k' pr' f'

let cl_decl cl inst d = match d.d_node with
  | Dtype ts -> cl_type cl inst ts
  | Ddata tdl -> cl_data cl inst tdl
  | Dparam ls -> cl_param cl inst ls
  | Dlogic ldl -> cl_logic cl inst ldl
  | Dind idl -> cl_ind cl inst idl
  | Dprop p -> cl_prop cl inst p

let cl_marg cl = function
  | MAty ty -> MAty (cl_trans_ty cl ty)
  | MAts ts -> MAts (cl_find_ts cl ts)
  | MAls ls -> MAls (cl_find_ls cl ls)
  | MApr pr -> MApr (cl_find_pr cl pr)
  | a -> a

let cl_smap cl sm = {
  sm_ty = Mts.map (cl_trans_ty cl) sm.sm_ty;
  sm_ts = Mts.map (cl_find_ts cl) sm.sm_ts;
  sm_ls = Mls.map (cl_find_ls cl) sm.sm_ls;
  sm_pr = Mpr.map (cl_find_pr cl) sm.sm_pr}

let cl_tdecl cl inst td = match td.td_node with
  | Decl d -> Decl (cl_decl cl inst d)
  | Use th -> Use th
  | Clone (th,sm) -> Clone (th, cl_smap cl sm)
  | Meta (id,al) -> Meta (id, List.map (cl_marg cl) al)

let warn_clone_not_abstract loc th =
  try
    List.iter (fun d -> match d.td_node with
      | Decl d ->
        begin match d.d_node with
        | Dtype { ts_def = NoDef }
        | Dparam _ -> raise Exit
        | Dprop(Paxiom, _,_) -> raise Exit
        | _ -> ()
        end
      | _ -> ()
    ) th.th_decls;
    Loc.warning warning_clone_not_abstract ~loc "cloned theory %a.%s does not contain \
        any abstract symbol; it should be used instead"
      (Pp.print_list (Pp.constant_string ".") Pp.string) th.th_path
      th.th_name.id_string
  with Exit -> ()

let clone_theory cl add_td acc th inst =
  let add acc td =
    let td =
      try  Some (mk_tdecl (cl_tdecl cl inst td))
      with EmptyDecl -> None
    in
    Opt.fold add_td acc td
  in
  let acc = List.fold_left add acc th.th_decls in
  let sm = {
    sm_ty = cl.ty_table;
    sm_ts = cl.ts_table;
    sm_ls = cl.ls_table;
    sm_pr = cl.pr_table}
  in
  add_td acc (mk_tdecl (Clone (th, sm)))

let clone_export uc th inst =
  let cl = cl_init th inst in
  let uc = clone_theory cl add_tdecl uc th inst in

  let f_ts p ts =
    if Mid.mem ts.ts_name th.th_local then
    if Mts.mem ts inst.inst_ts then None else
    if Mts.mem ts inst.inst_ty then None else
    try let ts = Mts.find ts cl.ts_table in
        store_path uc p ts.ts_name; Some ts
    with Not_found -> None else Some ts in

  let f_ls p ls =
    if Mid.mem ls.ls_name th.th_local then
    if Mls.mem ls inst.inst_ls then None else
    try let ls = Mls.find ls cl.ls_table in
        store_path uc p ls.ls_name; Some ls
    with Not_found -> None else Some ls in

  let f_pr p pr =
    if Mid.mem pr.pr_name th.th_local then
    try let pr = Mpr.find pr cl.pr_table in
        store_path uc p pr.pr_name; Some pr
    with Not_found -> None else Some pr in

  let rec f_ns p ns = {
    ns_ts = Mstr.map_filter (f_ts p) ns.ns_ts;
    ns_ls = Mstr.map_filter (f_ls p) ns.ns_ls;
    ns_pr = Mstr.map_filter (f_pr p) ns.ns_pr;
    ns_ns = Mstr.mapi (fun n -> f_ns (n::p)) ns.ns_ns; } in

  let ns = f_ns [] th.th_export in

  match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste -> { uc with
        uc_import = merge_ns false ns i0 :: sti;
        uc_export = merge_ns true  ns e0 :: ste; }
    | _ -> assert false

let clone_theory add_td acc th inst =
  clone_theory (cl_init th inst) add_td acc th inst

let add_clone_unsafe uc th sm =
  add_tdecl uc (mk_tdecl (Clone (th, sm)))

let add_clone_internal =
  let used = ref false in fun () -> if !used
    then invalid_arg "Theory.add_clone_internal"
    else begin used := true; add_clone_unsafe end

(** Meta properties *)

(* let get_meta_arg_type = function
  | MAty  _ -> MTty
  | MAts  _ -> MTtysymbol
  | MAls  _ -> MTlsymbol
  | MApr  _ -> MTprsymbol
  | MAstr _ -> MTstring
  | MAint _ -> MTint
  | MAid _ -> MTid

let create_meta m al =
  let get_meta_arg at a =
    (* we allow "constant tysymbol <=> ty" conversion *)
    let a = match at,a with
      | MTtysymbol, MAty ({ ty_node = Tyapp (ts,[]) }) -> MAts ts
      | MTty, MAts ({ts_args = []} as ts) -> MAty (ty_app ts [])
      | _, _ -> a
    in
    let mt = get_meta_arg_type a in
    if at = mt then a else raise (MetaTypeMismatch (m,at,mt))
  in
  if m.meta_type = [] && al = [MAstr ""] then
    (* backward compatibility *)
    mk_tdecl (Meta (m, []))
  else
    let al = try
        List.map2 get_meta_arg m.meta_type al
      with Invalid_argument _ ->
        raise (BadMetaArity (m, List.length al)) in
    mk_tdecl (Meta (m,al)) *)

let add_meta uc s al = add_tdecl uc (create_meta s al)

let clone_meta tdt th sm = match tdt.td_node with
  | Meta (t,al) ->
      let find_ts ts = if Mid.mem ts.ts_name th.th_local
        then Mts.find ts sm.sm_ts else ts in
      let find_ls ls = if Mid.mem ls.ls_name th.th_local
        then Mls.find ls sm.sm_ls else ls in
      let find_pr pr = if Mid.mem pr.pr_name th.th_local
        then Mpr.find pr sm.sm_pr else pr in
      let cl_marg = function
        | MAty ty -> MAty (sm_trans_ty sm.sm_ty sm.sm_ts ty)
        | MAts ts -> MAts (find_ts ts)
        | MAls ls -> MAls (find_ls ls)
        | MApr pr -> MApr (find_pr pr)
        | a -> a
      in
      begin try Some (mk_tdecl (Meta (t, List.map cl_marg al)))
      with Not_found -> None end
  | _ -> invalid_arg "Theory.clone_meta"

(** Base theories *)

let builtin_theory =
  let uc = empty_theory (id_fresh "BuiltIn") ["why3";"BuiltIn"] in
  let uc = add_ty_decl uc ts_int in
  let uc = add_ty_decl uc ts_real in
  let uc = add_ty_decl uc ts_str in
  let uc = add_param_decl uc ps_equ in
  close_theory uc

let create_theory ?(path=[]) n =
  use_export (empty_theory n path) builtin_theory

let ignore_theory =
  let uc = empty_theory (id_fresh "Ignore") ["why3";"Ignore"] in
  let uc = add_param_decl uc ps_ignore in
  close_theory uc

let bool_theory =
  let uc = empty_theory (id_fresh "Bool") ["why3";"Bool"] in
  let uc = add_data_decl uc [ts_bool, [fs_bool_true,[]; fs_bool_false,[]]] in
  close_theory uc

let highord_theory =
  let uc = empty_theory (id_fresh "HighOrd") ["why3";"HighOrd"] in
  let uc = add_ty_decl uc ts_func in
  let uc = add_param_decl uc fs_func_app in
  close_theory uc

let tuple_theory (n: BigInt.t) = Hint.memo 17 (fun n ->
  let ts = ts_tuple (BigInt.of_int n) and fs = fs_tuple n in (*Josh of_int*)
  let pl = List.map (fun _ -> None) ts.ts_args in
  let nm = "Tuple" ^ string_of_int n in
  let attrs = Sattr.singleton builtin_attr in
  let uc = empty_theory (id_fresh ~attrs nm) ["why3";nm] in
  let uc = add_data_decl uc [ts, [fs,pl]] in
  close_theory uc) (BigInt.to_int n) (*JOSH: bad*)

let tuple_theory_name s =
  let l = String.length s in
  if l < 6 then None else
  let p = String.sub s 0 5 in
  if p <> "Tuple" then None else
  let q = String.sub s 5 (l - 5) in
  let i = try int_of_string q with _ -> 0 in
  (* we only accept the decimal notation *)
  if q <> string_of_int i then None else
  Some i

let add_decl_with_tuples uc d =
  let ids = Mid.set_diff (get_used_syms_decl d) uc.uc_known in
  let add id s = match is_ts_tuple_id id with
    | Some n -> Sint.add (BigInt.to_int n) s (*JOSH to_int*)
    | None -> s in
  let ixs = Sid.fold add ids Sint.empty in
  let add n uc = use_export uc (tuple_theory (BigInt.of_int n)) in (*Josh of_int*)
  add_decl ~warn:false (Sint.fold add ixs uc) d
