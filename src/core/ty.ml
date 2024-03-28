open BinNums
open Exthtbl2
open CoqHashtbl
open Number
open CoqUtil
open Weakhtbl
open Wstdlib
open ErrorMonad
open Ident
open IntFuncs
open List0
open Specif
open StateMonad
open StateMonad0
open Base
open Hashcons
open Pmap
open Zmap

type tvsymbol = { tv_name : ident }

(** val tv_name : tvsymbol -> ident **)

let tv_name t0 =
  t0.tv_name

(** val tvsymbol_eqb : tvsymbol -> tvsymbol -> bool **)

let tvsymbol_eqb t1 t2 =
  id_equal t1.tv_name t2.tv_name

(** val tvsymbol_eq : (tvsymbol, tvsymbol) coq_RelDecision **)

let tvsymbol_eq =
  dec_from_eqb tvsymbol_eqb

module TvarTagged =
 struct
  type t = tvsymbol

  (** val tag : tvsymbol -> tag **)

  let tag tv =
    tv.tv_name.id_tag

  (** val equal : (tvsymbol, tvsymbol) coq_RelDecision **)

  let equal =
    tvsymbol_eq
 end

module Tvar = MakeMSWeak(TvarTagged)

module Stv = Tvar.S

module Mtv = Tvar.M

(** val tv_equal : tvsymbol -> tvsymbol -> bool **)

let tv_equal =
  tvsymbol_eqb

(** val tv_hash : tvsymbol -> BigInt.t **)

let tv_hash tv =
  id_hash tv.tv_name

(** val tv_compare : tvsymbol -> tvsymbol -> Stdlib.Int.t **)

let tv_compare tv1 tv2 =
  id_compare tv1.tv_name tv2.tv_name

(** val create_tvsymbol : preid -> (BigInt.t, tvsymbol) st **)

let create_tvsymbol n =
  (@@) (fun i ->  { tv_name = i }) (id_register n)

module Tvsym_t =
 struct
  type t = tvsymbol
 end

module Hstr_tv = Exthtbl2.Make(Str2)(Tvsym_t)

(** val tv_hashtbl : ((string, tvsymbol) hashtbl, unit) st **)

let tv_hashtbl =
  Hstr_tv.create Stdlib.Int.one

(** val tv_of_string :
    string -> (BigInt.t * (string, tvsymbol) hashtbl, tvsymbol) state **)

let tv_of_string s =
  (@@) (fun o ->
    match o with
    | Some v ->  v
    | None ->
      let tv = create_tvsymbol (id_fresh1 s) in
      (@@) (fun i -> (@@) (fun _ ->  i) ( (Hstr_tv.add s i))) ( tv))
    ( (Hstr_tv.find_opt s))

type 'a type_def =
| NoDef
| Alias of 'a
| Range of int_range
| Float of float_format

type 'a ty_o = { ty_node : 'a; ty_tag : tag }

(** val ty_node : 'a1 ty_o -> 'a1 **)

let ty_node t0 =
  t0.ty_node

(** val ty_tag : 'a1 ty_o -> tag **)

let ty_tag t0 =
  t0.ty_tag

type 'a tysymbol_o = { ts_name : ident; ts_args : tvsymbol list;
                       ts_def : 'a type_def }

(** val ts_name : 'a1 tysymbol_o -> ident **)

let ts_name t0 =
  t0.ts_name

(** val ts_args : 'a1 tysymbol_o -> tvsymbol list **)

let ts_args t0 =
  t0.ts_args

(** val ts_def : 'a1 tysymbol_o -> 'a1 type_def **)

let ts_def t0 =
  t0.ts_def

type ty_node_c =
| Tyvar of tvsymbol
| Tyapp of (ty_node_c ty_o) tysymbol_o * ty_node_c ty_o list

type ty = ty_node_c ty_o

type tysymbol = ty tysymbol_o

(** val build_tysym_o :
    ident -> tvsymbol list -> ty_node_c ty_o type_def -> ty_node_c ty_o
    tysymbol_o **)

let build_tysym_o i l t0 =
  { ts_name = i; ts_args = l; ts_def = t0 }

(** val build_ty_o : ty_node_c -> tag -> ty_node_c ty_o **)

let build_ty_o n i =
  { ty_node = n; ty_tag = i }

(** val ty_eqb : ty_node_c ty_o -> ty_node_c ty_o -> bool **)

let rec ty_eqb t1 t2 =
  (&&) (tag_equal (ty_tag t1) (ty_tag t2))
    (ty_node_eqb (ty_node t1) (ty_node t2))

(** val ty_node_eqb : ty_node_c -> ty_node_c -> bool **)

and ty_node_eqb t1 t2 =
  match t1 with
  | Tyvar v1 ->
    (match t2 with
     | Tyvar v2 -> tvsymbol_eqb v1 v2
     | Tyapp (_, _) -> false)
  | Tyapp (ts1, tys1) ->
    (match t2 with
     | Tyvar _ -> false
     | Tyapp (ts2, tys2) ->
       (&&)
         ((&&) (tysymbol_eqb ts1 ts2)
           (BigInt.eq (int_length tys1) (int_length tys2)))
         (forallb (fun x -> x) (map2 ty_eqb tys1 tys2)))

(** val tysymbol_eqb :
    (ty_node_c ty_o) tysymbol_o -> (ty_node_c ty_o) tysymbol_o -> bool **)

and tysymbol_eqb t1 t2 =
  (&&)
    ((&&) (id_equal (ts_name t1) (ts_name t2))
      (list_eqb tvsymbol_eqb (ts_args t1) (ts_args t2)))
    (match ts_def t1 with
     | NoDef -> (match ts_def t2 with
                 | NoDef -> true
                 | _ -> false)
     | Alias a1 ->
       (match ts_def t2 with
        | Alias a2 -> ty_eqb a1 a2
        | _ -> false)
     | Range n1 ->
       (match ts_def t2 with
        | Range n2 -> int_range_eqb n1 n2
        | _ -> false)
     | Float f1 ->
       (match ts_def t2 with
        | Float f2 -> float_format_eqb f1 f2
        | _ -> false))

(** val tysymbol_eq :
    ((ty_node_c ty_o) tysymbol_o, (ty_node_c ty_o) tysymbol_o) coq_RelDecision **)

let tysymbol_eq =
  dec_from_eqb tysymbol_eqb

module TsymTagged =
 struct
  type t = (ty_node_c ty_o) tysymbol_o

  (** val tag : (ty_node_c ty_o) tysymbol_o -> tag **)

  let tag ts =
    (ts_name ts).id_tag

  (** val equal :
      ((ty_node_c ty_o) tysymbol_o, (ty_node_c ty_o) tysymbol_o)
      coq_RelDecision **)

  let equal =
    tysymbol_eq
 end

module Tsym = MakeMSWeak(TsymTagged)

module Sts = Tsym.S

module Mts = Tsym.M

(** val ts_equal :
    (ty_node_c ty_o) tysymbol_o -> (ty_node_c ty_o) tysymbol_o -> bool **)

let ts_equal =
  tysymbol_eqb

(** val ty_equal : ty_node_c ty_o -> ty_node_c ty_o -> bool **)

let ty_equal =
  ty_eqb

(** val ts_hash : (ty_node_c ty_o) tysymbol_o -> BigInt.t **)

let ts_hash ts =
  id_hash (ts_name ts)

(** val ty_hash : ty_node_c ty_o -> tag **)

let ty_hash t0 =
  tag_hash (ty_tag t0)

(** val ts_compare :
    (ty_node_c ty_o) tysymbol_o -> (ty_node_c ty_o) tysymbol_o -> Stdlib.Int.t **)

let ts_compare ts1 ts2 =
  id_compare (ts_name ts1) (ts_name ts2)

(** val ty_compare : ty_node_c ty_o -> ty_node_c ty_o -> Stdlib.Int.t **)

let ty_compare ty1 ty2 =
  BigInt.compare (ty_hash ty1) (ty_hash ty2)

module TyHash =
 struct
  type t = ty_node_c ty_o

  (** val equal : ty_node_c ty_o -> ty_node_c ty_o -> bool **)

  let equal ty1 ty2 =
    match ty_node ty1 with
    | Tyvar n1 ->
      (match ty_node ty2 with
       | Tyvar n2 -> tv_equal n1 n2
       | Tyapp (_, _) -> false)
    | Tyapp (s1, l1) ->
      (match ty_node ty2 with
       | Tyvar _ -> false
       | Tyapp (s2, l2) ->
         (&&) (ts_equal s1 s2) (forallb (fun x -> x) (map2 ty_equal l1 l2)))

  (** val hash : ty_node_c ty_o -> BigInt.t **)

  let hash t0 =
    match ty_node t0 with
    | Tyvar v -> tv_hash v
    | Tyapp (s, tl) -> combine_big_list ty_hash (ts_hash s) tl

  (** val tag : BigInt.t -> ty_node_c ty_o -> ty_node_c ty_o **)

  let tag n ty0 =
    (fun (a, b) -> build_ty_o a b) ((ty_node ty0), (create_tag n))
 end

module Hsty = Make(TyHash)

(** val mk_ts :
    preid -> tvsymbol list -> ty_node_c ty_o type_def -> (BigInt.t,
    (ty_node_c ty_o) tysymbol_o) st **)

let mk_ts name args d =
  (@@) (fun i ->  ((fun (a,b,c) -> build_tysym_o a b c) (i, args, d)))
    (id_register name)

(** val ty_eq : (ty_node_c ty_o, ty_node_c ty_o) coq_RelDecision **)

let ty_eq =
  dec_from_eqb ty_eqb

module TyTagged =
 struct
  type t = ty_node_c ty_o

  (** val tag : ty_node_c ty_o -> tag **)

  let tag =
    ty_tag

  (** val equal : (ty_node_c ty_o, ty_node_c ty_o) coq_RelDecision **)

  let equal =
    ty_eq
 end

module TyM = MakeMSWeak(TyTagged)

module Sty = TyM.S

module Mty = TyM.M


exception BadTypeArity of tysymbol * BigInt.t
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVar of tvsymbol
exception IllegalTypeParameters
exception BadFloatSpec
exception EmptyRange
exception UnexpectedProp
exception TypeMismatch of ty * ty
open CoqHashtbl
open Number
open CoqUtil
open Weakhtbl
open Datatypes
open ErrorMonad
open Ident
open IntFuncs
open List0
open StateMonad0


(** val mk_ty : ty_node_c -> ty_node_c ty_o **)

let mk_ty n =
  (fun (a, b) -> build_ty_o a b) (n, dummy_tag)

(** val ty_var :
    tvsymbol -> (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_var n =
  Hsty.hashcons (mk_ty (Tyvar n))

(** val ty_app1 :
    (ty_node_c ty_o) tysymbol_o -> ty_node_c ty_o list ->
    (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_app1 s tl =
  Hsty.hashcons (mk_ty (Tyapp (s, tl)))

(** val ty_map :
    (ty_node_c ty_o -> ty_node_c ty_o) -> ty_node_c ty_o ->
    (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_map fn t0 =
  match ty_node t0 with
  | Tyvar _ ->  t0
  | Tyapp (f, tl) -> ty_app1 f (map fn tl)

(** val ty_fold :
    ('a1 -> ty_node_c ty_o -> 'a1) -> 'a1 -> ty_node_c ty_o -> 'a1 **)

let ty_fold fn acc t0 =
  match ty_node t0 with
  | Tyvar _ -> acc
  | Tyapp (_, tl) -> fold_left fn tl acc

(** val ty_all : (ty_node_c ty_o -> bool) -> ty_node_c ty_o -> bool **)

let ty_all pr t0 =
  ty_fold (fun acc x -> (&&) acc (pr x)) true t0

(** val ty_any : (ty_node_c ty_o -> bool) -> ty_node_c ty_o -> bool **)

let ty_any pr t0 =
  ty_fold (fun acc x -> (||) acc (pr x)) false t0

(** val type_def_map : ('a1 -> 'a1) -> 'a1 type_def -> 'a1 type_def **)

let type_def_map fn x = match x with
| Alias t0 -> Alias (fn t0)
| _ -> x

(** val type_def_fold : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 type_def -> 'a1 **)

let type_def_fold fn acc = function
| Alias t1 -> fn acc t1
| _ -> acc

(** val is_alias_type_def : 'a1 type_def -> bool **)

let is_alias_type_def = function
| Alias _ -> true
| _ -> false

(** val is_range_type_def : 'a1 type_def -> bool **)

let is_range_type_def = function
| Range _ -> true
| _ -> false

(** val is_float_type_def : 'a1 type_def -> bool **)

let is_float_type_def = function
| Float _ -> true
| _ -> false

(** val ty_v_map :
    (tvsymbol -> ty_node_c ty_o) -> ty_node_c ty_o -> (BigInt.t * TyHash.t
    hashset, ty_node_c ty_o) st **)

let rec ty_v_map fn t0 =
  match ty_node t0 with
  | Tyvar v ->  (fn v)
  | Tyapp (f, tl) ->
    (@@) (fun l -> ty_app1 f l) (st_list (map (ty_v_map fn) tl))

(** val ty_v_fold :
    ('a1 -> tvsymbol -> 'a1) -> 'a1 -> ty_node_c ty_o -> 'a1 **)

let rec ty_v_fold fn acc t0 =
  match ty_node t0 with
  | Tyvar v -> fn acc v
  | Tyapp (_, tl) -> fold_left (ty_v_fold fn) tl acc

(** val ty_v_all : (tvsymbol -> bool) -> ty_node_c ty_o -> bool **)

let ty_v_all pr t0 =
  ty_v_fold (fun acc v -> (&&) acc (pr v)) true t0

(** val ty_v_any : (tvsymbol -> bool) -> ty_node_c ty_o -> bool **)

let ty_v_any pr t0 =
  ty_v_fold (fun acc v -> (||) acc (pr v)) false t0

(** val ty_v_map_err :
    (tvsymbol -> ty_node_c ty_o errorM) -> ty_node_c ty_o ->
    (BigInt.t * ty_node_c ty_o hashset, ty_node_c ty_o) errState **)

let rec ty_v_map_err fn t0 =
  match ty_node t0 with
  | Tyvar v ->  (fn v)
  | Tyapp (f, tl) ->
    (@@) (fun l ->  (ty_app1 f l)) (errst_list (map (ty_v_map_err fn) tl))

(** val ty_full_inst :
    ty_node_c ty_o Mtv.t -> ty_node_c ty_o -> (BigInt.t * ty_node_c ty_o
    hashset, ty_node_c ty_o) errState **)

let ty_full_inst m t0 =
  ty_v_map_err (fun v -> Mtv.find v m) t0

(** val ty_freevars : Stv.t -> ty_node_c ty_o -> Stv.t **)

let ty_freevars s t0 =
  ty_v_fold Stv.add_left s t0

(** val ty_closed : ty_node_c ty_o -> bool **)

let ty_closed t0 =
  ty_v_all (fun _ -> false) t0

(** val mk_errtype : 'a1 -> exn **)

let mk_errtype x =
  (Obj.magic x)

(** val fold_errorM' :
    ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM **)

let rec fold_errorM' f l x =
  match l with
  | [] ->  x
  | h :: t0 -> (@@) (fun i -> f i h) (fold_errorM' f t0 x)

(** val ty_v_fold_err :
    ('a1 -> tvsymbol -> 'a1 errorM) -> 'a1 -> ty_node_c ty_o -> 'a1 errorM **)

let rec ty_v_fold_err fn acc t0 =
  match ty_node t0 with
  | Tyvar v -> fn acc v
  | Tyapp (_, tl) -> fold_errorM' (ty_v_fold_err fn) tl acc

(** val ty_v_all_err :
    (tvsymbol -> bool errorM) -> ty_node_c ty_o -> bool errorM **)

let ty_v_all_err pr t0 =
  ty_v_fold_err (fun acc v -> (@@) (fun i ->  ((&&) i acc)) (pr v)) true t0

(** val create_tysymbol :
    preid -> tvsymbol list -> ty_node_c ty_o type_def -> (BigInt.t,
    (ty_node_c ty_o) tysymbol_o) st errorM **)

let create_tysymbol name args d =
  let add0 = fun s v -> Stv.add_new (DuplicateTypeVar v) v s in
  let s1 = fold_errorM' add0 args Stv.empty in
  let check = fun v ->
    (@@) (fun m -> if Stv.mem v m then  true else raise (UnboundTypeVar v)) s1
  in
  let c =
    match d with
    | NoDef ->  ()
    | Alias d' -> ignore (ty_v_all_err check d')
    | Range ir ->
      if negb (null args)
      then raise IllegalTypeParameters
      else if BigInt.lt ir.ir_upper ir.ir_lower then raise EmptyRange else  ()
    | Float fp ->
      if negb (null args)
      then raise IllegalTypeParameters
      else if (||) (BigInt.lt fp.fp_exponent_digits BigInt.one)
                (BigInt.lt fp.fp_significand_digits BigInt.one)
           then raise BadFloatSpec
           else  ()
  in
  (@@) (fun _ ->  (mk_ts name args d)) c

(** val ts_match_args :
    (ty_node_c ty_o) tysymbol_o -> 'a1 list -> 'a1 Mtv.t errorM **)

let ts_match_args s tl =
  match fold_right2 Mtv.add (ts_args s) tl Mtv.empty with
  | Some m ->  m
  | None -> raise (BadTypeArity (s, (int_length tl)))

(** val ty_match_args : ty_node_c ty_o -> ty_node_c ty_o Mtv.t errorM **)

let ty_match_args t0 =
  match ty_node t0 with
  | Tyvar _ -> raise (Invalid_argument "Ty.ty_match_args")
  | Tyapp (s, tl) -> ts_match_args s tl

(** val ty_app :
    (ty_node_c ty_o) tysymbol_o -> ty_node_c ty_o list ->
    (BigInt.t * ty_node_c ty_o hashset, ty_node_c ty_o) errState **)

let ty_app s tl =
  match ts_def s with
  | Alias t0 -> (@@) (fun m -> ty_full_inst m t0) ( (ts_match_args s tl))
  | _ ->
    if negb (BigInt.eq (int_length (ts_args s)) (int_length tl))
    then  (raise (BadTypeArity (s, (int_length tl))))
    else  (ty_app1 s tl)

(** val ty_s_map :
    ((ty_node_c ty_o) tysymbol_o -> (ty_node_c ty_o) tysymbol_o) ->
    ty_node_c ty_o -> (BigInt.t * ty_node_c ty_o hashset, ty_node_c ty_o)
    errState **)

let rec ty_s_map fn t0 =
  match ty_node t0 with
  | Tyvar _ ->  t0
  | Tyapp (f, tl) ->
    (@@) (fun l -> ty_app (fn f) l) (errst_list (map (ty_s_map fn) tl))

(** val ty_s_fold :
    ('a1 -> (ty_node_c ty_o) tysymbol_o -> 'a1) -> 'a1 -> ty_node_c ty_o ->
    'a1 **)

let rec ty_s_fold fn acc t0 =
  match ty_node t0 with
  | Tyvar _ -> acc
  | Tyapp (f, tl) -> fold_left (ty_s_fold fn) tl (fn acc f)

(** val ty_s_all :
    ((ty_node_c ty_o) tysymbol_o -> bool) -> ty_node_c ty_o -> bool **)

let ty_s_all pr t0 =
  ty_s_fold (fun x y -> (&&) x (pr y)) true t0

(** val ty_s_any :
    ((ty_node_c ty_o) tysymbol_o -> bool) -> ty_node_c ty_o -> bool **)

let ty_s_any pr t0 =
  ty_s_fold (fun x y -> (||) x (pr y)) false t0

(** val ty_mapM :
    (ty_node_c ty_o -> (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st) ->
    ty_node_c ty_o -> (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_mapM fn t0 =
  match ty_node t0 with
  | Tyvar _ ->  t0
  | Tyapp (f, tl) -> (@@) (fun l -> ty_app1 f l) (st_list (map fn tl))

(** val ty_inst :
    ty_node_c ty_o Mtv.t -> ty_node_c ty_o -> (BigInt.t * TyHash.t hashset,
    ty_node_c ty_o) st **)

let rec ty_inst s t0 =
  match ty_node t0 with
  | Tyvar n ->  (Mtv.find_def t0 n s)
  | Tyapp (_, _) -> ty_mapM (ty_inst s) t0

(** val fold_right2_error :
    ('a3 -> 'a1 -> 'a2 -> 'a3 errorM) -> 'a1 list -> 'a2 list -> 'a3 -> 'a3
    errorM **)

let rec fold_right2_error f l1 l2 accu =
  match l1 with
  | [] ->
    (match l2 with
     | [] ->  accu
     | _ :: _ -> raise (Invalid_argument "fold_right2"))
  | a1 :: l3 ->
    (match l2 with
     | [] -> raise (Invalid_argument "fold_right2")
     | a2 :: l4 -> (@@) (fun x -> f x a1 a2) (fold_right2_error f l3 l4 accu))

(** val ty_match_aux :
    ty_node_c ty_o -> ty_node_c ty_o -> ty_node_c ty_o Mtv.t ->
    ty_node_c ty_o -> ty_node_c ty_o -> ty_node_c ty_o Mtv.t errorM **)

let rec ty_match_aux err1 err2 s ty1 ty2 =
  match ty_node ty1 with
  | Tyvar n1 ->
    (match Mtv.find_opt n1 s with
     | Some ty3 ->
       if ty_equal ty3 ty2 then  s else raise (TypeMismatch (err1, err2))
     | None ->  (Mtv.add n1 ty2 s))
  | Tyapp (f1, l1) ->
    (match ty_node ty2 with
     | Tyvar _ -> raise (TypeMismatch (err1, err2))
     | Tyapp (f2, l2) ->
       if ts_equal f1 f2
       then fold_right2_error (ty_match_aux err1 err2) l1 l2 s
       else raise (TypeMismatch (err1, err2)))

(** val ty_match :
    ty_node_c ty_o Mtv.t -> ty_node_c ty_o -> ty_node_c ty_o ->
    (BigInt.t * TyHash.t hashset, ty_node_c ty_o Mtv.t) errState **)

let ty_match s ty1 ty2 =
  (@@) (fun t1 ->  (ty_match_aux t1 ty2 s ty1 ty2)) ( (ty_inst s ty1))

(** val mk_ts_builtin :
    ident -> tvsymbol list -> ty_node_c ty_o type_def ->
    (ty_node_c ty_o) tysymbol_o **)

let mk_ts_builtin name args d =
  (fun (a,b,c) -> build_tysym_o a b c) (name, args, d)

(** val ts_int : (ty_node_c ty_o) tysymbol_o **)

let ts_int =
  mk_ts_builtin id_int [] NoDef

(** val ts_real : (ty_node_c ty_o) tysymbol_o **)

let ts_real =
  mk_ts_builtin id_real [] NoDef

(** val ts_bool : (ty_node_c ty_o) tysymbol_o **)

let ts_bool =
  mk_ts_builtin id_bool [] NoDef

(** val ts_str : (ty_node_c ty_o) tysymbol_o **)

let ts_str =
  mk_ts_builtin id_str [] NoDef

(** val ty_int : (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_int =
  ty_app1 ts_int []

(** val ty_real : (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_real =
  ty_app1 ts_real []

(** val ty_bool : (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_bool =
  ty_app1 ts_bool []

(** val ty_str : (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_str =
  ty_app1 ts_str []

(** val create_builtin_tvsymbol : ident -> tvsymbol **)

let create_builtin_tvsymbol i =
  { tv_name = i }

(** val ts_func : (ty_node_c ty_o) tysymbol_o **)

let ts_func =
  let tv_a = create_builtin_tvsymbol id_a in
  let tv_b = create_builtin_tvsymbol id_b in
  mk_ts_builtin id_fun (tv_a :: (tv_b :: [])) NoDef

(** val ty_func :
    ty_node_c ty_o -> ty_node_c ty_o -> (BigInt.t * TyHash.t hashset,
    ty_node_c ty_o) st **)

let ty_func ty_a ty_b =
  ty_app1 ts_func (ty_a :: (ty_b :: []))

(** val ty_pred :
    ty_node_c ty_o -> (BigInt.t * TyHash.t hashset, ty_node_c ty_o) st **)

let ty_pred ty_a =
  (@@) (fun t0 -> ty_app1 ts_func (ty_a :: (t0 :: []))) ty_bool

(** val oty_equal : ty_node_c ty_o option -> ty_node_c ty_o option -> bool **)

let oty_equal o1 o2 =
  option_eqb ty_equal o1 o2

(** val oty_hash : ty_node_c ty_o option -> BigInt.t **)

let oty_hash o =
  option_fold BigInt.one ty_hash o

(** val oty_compare :
    ty_node_c ty_o option -> ty_node_c ty_o option -> Stdlib.Int.t **)

let oty_compare o1 o2 =
  option_compare ty_compare o1 o2

(** val oty_match :
    ty_node_c ty_o Mtv.t -> ty_node_c ty_o option -> ty_node_c ty_o option ->
    (BigInt.t * TyHash.t hashset, ty_node_c ty_o Mtv.t) errState **)

let oty_match m o1 o2 =
  match o1 with
  | Some ty1 ->
    (match o2 with
     | Some ty2 -> ty_match m ty1 ty2
     | None ->  (raise UnexpectedProp))
  | None -> (match o2 with
             | Some _ ->  (raise UnexpectedProp)
             | None ->  m)

(** val oty_inst :
    ty_node_c ty_o Mtv.t -> ty_node_c ty_o option -> (BigInt.t * TyHash.t
    hashset, ty_node_c ty_o) st option **)

let oty_inst m o =
  option_map (ty_inst m) o

(** val opt_fold : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 option -> 'a1 **)

let opt_fold f d = function
| Some x -> f d x
| None -> d

(** val oty_freevars : Stv.t -> ty_node_c ty_o option -> Stv.t **)

let oty_freevars =
  opt_fold ty_freevars

(** val oty_cons :
    ty_node_c ty_o list -> ty_node_c ty_o option -> ty_node_c ty_o list **)

let oty_cons l o =
  opt_fold (fun tl t0 -> t0 :: tl) l o

(** val ty_equal_check : ty_node_c ty_o -> ty_node_c ty_o -> unit errorM **)

let ty_equal_check ty1 ty2 =
  if negb (ty_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2)) else  ()
let oty_type = function Some ty -> ty | None -> raise UnexpectedProp
let ts_tuple_ids = Hid.create 17

(*JOSH: remove memoization*)
let ts_tuple = Hint.memo 17 (fun n ->
  let vl = ref [] in
  for _i = 1 to n do vl := create_tvsymbol (id_fresh "a") :: !vl done;
  let ts = create_tysymbol (id_fresh ("tuple" ^ string_of_int n)) !vl NoDef in
  Hid.add ts_tuple_ids ts.ts_name n;
  ts)

let ty_tuple tyl = ty_app (ts_tuple (List.length tyl)) tyl

let is_ts_tuple ts = ts_equal ts (ts_tuple (List.length ts.ts_args))

let is_ts_tuple_id id =
  try Some (Hid.find ts_tuple_ids id) with Not_found -> None

module Ty2 = MakeMSHW(TyTagged)
module Hty = Ty2.H
module Wty = Ty2.W

module Tsym2 = MakeMSHW(TsymTagged)
module Wts = Tsym2.W

module Tvar2 = MakeMSHW(TvarTagged)
module Htv = Tvar2.H