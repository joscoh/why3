open BinNums
open Bool0
open Constant
open CoqUtil
open Weakhtbl
open Wstdlib
open Datatypes
open Ident
open IntFuncs
open List0
open Loc
open Monads
open Specif
open Ty
open Pmap
open Zmap
open Number
open Hashcons
open CommonList
open CommonOption




















type vsymbol = { vs_name : ident; vs_ty : ty_node_c ty_o }

(** val vs_name : vsymbol -> ident **)

let vs_name v =
  v.vs_name

(** val vs_ty : vsymbol -> ty_node_c ty_o **)

let vs_ty v =
  v.vs_ty

(** val vsymbol_eqb : vsymbol -> vsymbol -> bool **)

let vsymbol_eqb v1 v2 =
  (&&) (id_equal v1.vs_name v2.vs_name) (ty_equal v1.vs_ty v2.vs_ty)

module VsymTag =
 struct
  type t = vsymbol

  (** val tag : vsymbol -> tag **)

  let tag vs =
    vs.vs_name.id_tag

  (** val equal : vsymbol -> vsymbol -> bool **)

  let equal =
    vsymbol_eqb
 end

module Vsym = MakeMSWeak(VsymTag)

module Svs = Vsym.S

module Mvs = Vsym.M

(** val vs_equal : vsymbol -> vsymbol -> bool **)

let vs_equal =
  vsymbol_eqb

(** val vs_hash : vsymbol -> BigInt.t **)

let vs_hash vs =
  id_hash vs.vs_name

(** val vs_compare : vsymbol -> vsymbol -> Stdlib.Int.t **)

let vs_compare vs1 vs2 =
  id_compare vs1.vs_name vs2.vs_name

(** val create_vsymbol : preid -> ty_node_c ty_o -> (BigInt.t, vsymbol) st **)

let create_vsymbol name t0 =
  (@@) (fun i -> (fun x -> x) { vs_name = i; vs_ty = t0 }) (id_register name)

type lsymbol = { ls_name : ident; ls_args : ty_node_c ty_o list;
                 ls_value : ty_node_c ty_o option; ls_constr : BigInt.t;
                 ls_proj : bool }

(** val ls_name : lsymbol -> ident **)

let ls_name l =
  l.ls_name

(** val ls_args : lsymbol -> ty_node_c ty_o list **)

let ls_args l =
  l.ls_args

(** val ls_value : lsymbol -> ty_node_c ty_o option **)

let ls_value l =
  l.ls_value

(** val ls_constr : lsymbol -> BigInt.t **)

let ls_constr l =
  l.ls_constr

(** val ls_proj : lsymbol -> bool **)

let ls_proj l =
  l.ls_proj

(** val lsymbol_eqb : lsymbol -> lsymbol -> bool **)

let lsymbol_eqb l1 l2 =
  (&&)
    ((&&)
      ((&&)
        ((&&) (id_equal l1.ls_name l2.ls_name)
          (list_eqb ty_equal l1.ls_args l2.ls_args))
        (option_eqb ty_equal l1.ls_value l2.ls_value))
      (BigInt.eq l1.ls_constr l2.ls_constr)) (eqb l1.ls_proj l2.ls_proj)

module LsymTag =
 struct
  type t = lsymbol

  (** val tag : lsymbol -> tag **)

  let tag ls =
    ls.ls_name.id_tag

  (** val equal : lsymbol -> lsymbol -> bool **)

  let equal =
    lsymbol_eqb
 end

module Lsym = MakeMSWeak(LsymTag)

module Sls = Lsym.S

module Mls = Lsym.M

(** val ls_equal : lsymbol -> lsymbol -> bool **)

let ls_equal =
  lsymbol_eqb

(** val ls_hash : lsymbol -> BigInt.t **)

let ls_hash ls =
  id_hash ls.ls_name

(** val ls_compare : lsymbol -> lsymbol -> Stdlib.Int.t **)

let ls_compare ls1 ls2 =
  id_compare ls1.ls_name ls2.ls_name

(** val check_constr :
    BigInt.t -> ty_node_c ty_o option -> BigInt.t errorM **)

let check_constr constr value =
  if (||) (BigInt.is_zero constr) ((&&) (BigInt.pos constr) (isSome value))
  then  constr
  else raise (Invalid_argument "Term.create_lsymbol")

(** val check_proj :
    bool -> BigInt.t -> ty_node_c ty_o list -> ty_node_c ty_o option -> bool
    errorM **)

let check_proj proj constr args value =
  if (||) (negb proj)
       ((&&) ((&&) (BigInt.is_zero constr) (isSome value))
         (BigInt.eq (int_length args) BigInt.one))
  then  proj
  else raise (Invalid_argument "Term.create_lsymbol")

(** val create_lsymbol_gen :
    BigInt.t -> bool -> preid -> ty_node_c ty_o list -> ty_node_c ty_o option
    -> (BigInt.t, lsymbol) st **)

let create_lsymbol_gen constr proj name args value =
  (@@) (fun i ->
    (fun x -> x) { ls_name = i; ls_args = args; ls_value = value; ls_constr =
      constr; ls_proj = proj }) (id_register name)

(** val create_lsymbol1 :
    preid -> ty_node_c ty_o list -> ty_node_c ty_o option -> (BigInt.t,
    lsymbol) st **)

let create_lsymbol1 name args value =
  create_lsymbol_gen BigInt.zero false name args value

(** val create_fsymbol1 :
    preid -> ty_node_c ty_o list -> ty_node_c ty_o -> (BigInt.t, lsymbol) st **)

let create_fsymbol1 nm al vl =
  create_lsymbol1 nm al (Some vl)

(** val create_fsymbol2 :
    BigInt.t -> bool -> preid -> ty_node_c ty_o list -> ty_node_c ty_o ->
    (BigInt.t, lsymbol) st **)

let create_fsymbol2 constr proj name args value =
  create_lsymbol_gen constr proj name args (Some value)

(** val create_psymbol :
    preid -> ty_node_c ty_o list -> (BigInt.t, lsymbol) st **)

let create_psymbol nm al =
  create_lsymbol1 nm al None

(** val create_lsymbol_builtin :
    BigInt.t -> bool -> ident -> ty_node_c ty_o list -> ty_node_c ty_o option
    -> lsymbol **)

let create_lsymbol_builtin constr proj i args value =
  { ls_name = i; ls_args = args; ls_value = value; ls_constr = constr;
    ls_proj = proj }

(** val create_fsymbol_builtin :
    BigInt.t -> bool -> ident -> ty_node_c ty_o list -> ty_node_c ty_o ->
    lsymbol **)

let create_fsymbol_builtin constr proj nm al vl =
  create_lsymbol_builtin constr proj nm al (Some vl)

(** val create_psymbol_builtin : ident -> ty_node_c ty_o list -> lsymbol **)

let create_psymbol_builtin nm al =
  create_lsymbol_builtin BigInt.zero false nm al None

(** val ls_ty_freevars : lsymbol -> Stv.t **)

let ls_ty_freevars ls =
  let acc = oty_freevars Stv.empty ls.ls_value in
  fold_left ty_freevars ls.ls_args acc

type 'a pattern_o = { pat_node : 'a; pat_vars : Svs.t; pat_ty : ty_node_c ty_o }

(** val pat_node : 'a1 pattern_o -> 'a1 **)

let pat_node p =
  p.pat_node

(** val pat_vars : 'a1 pattern_o -> Svs.t **)

let pat_vars p =
  p.pat_vars

(** val pat_ty : 'a1 pattern_o -> ty_node_c ty_o **)

let pat_ty p =
  p.pat_ty

type pattern_node =
| Pwild
| Pvar of vsymbol
| Papp of lsymbol * (pattern_node pattern_o) list
| Por of (pattern_node pattern_o) * (pattern_node pattern_o)
| Pas of (pattern_node pattern_o) * vsymbol

type pattern = pattern_node pattern_o

(** val build_pattern_o :
    pattern_node -> Svs.t -> ty_node_c ty_o -> pattern_node pattern_o **)

let build_pattern_o p s t0 =
  { pat_node = p; pat_vars = s; pat_ty = t0 }

(** val pattern_eqb :
    (pattern_node pattern_o) -> (pattern_node pattern_o) -> bool **)

let rec pattern_eqb p1 p2 =
  (&&)
    ((&&) (pattern_node_eqb (pat_node p1) (pat_node p2))
      (Svs.equal (pat_vars p1) (pat_vars p2)))
    (ty_equal (pat_ty p1) (pat_ty p2))

(** val pattern_node_eqb : pattern_node -> pattern_node -> bool **)

and pattern_node_eqb p1 p2 =
  match p1 with
  | Pwild -> (match p2 with
              | Pwild -> true
              | _ -> false)
  | Pvar v1 -> (match p2 with
                | Pvar v2 -> vs_equal v1 v2
                | _ -> false)
  | Papp (l1, ps1) ->
    (match p2 with
     | Papp (l2, ps2) ->
       (&&)
         ((&&) (ls_equal l1 l2) (BigInt.eq (int_length ps1) (int_length ps2)))
         (forallb (fun x -> x) (map2 pattern_eqb ps1 ps2))
     | _ -> false)
  | Por (p3, p4) ->
    (match p2 with
     | Por (p5, p6) -> (&&) (pattern_eqb p3 p5) (pattern_eqb p4 p6)
     | _ -> false)
  | Pas (p3, v1) ->
    (match p2 with
     | Pas (p4, v2) -> (&&) (pattern_eqb p3 p4) (vs_equal v1 v2)
     | _ -> false)

type quant =
| Tforall
| Texists

type binop =
| Tand
| Tor
| Timplies
| Tiff

type 'a term_o = { t_node : 'a; t_ty : ty_node_c ty_o option;
                   t_attrs : Sattr.t; t_loc : position option }

(** val t_node : 'a1 term_o -> 'a1 **)

let t_node t0 =
  t0.t_node

(** val t_ty : 'a1 term_o -> ty_node_c ty_o option **)

let t_ty t0 =
  t0.t_ty

(** val t_attrs : 'a1 term_o -> Sattr.t **)

let t_attrs t0 =
  t0.t_attrs

(** val t_loc : 'a1 term_o -> position option **)

let t_loc t0 =
  t0.t_loc

type bind_info = { bv_vars : BigInt.t Mvs.t }

(** val bv_vars : bind_info -> BigInt.t Mvs.t **)

let bv_vars b =
  b.bv_vars

type term_node =
| Tvar of vsymbol
| Tconst of constant
| Tapp of lsymbol * (term_node term_o) list
| Tif of (term_node term_o) * (term_node term_o) * (term_node term_o)
| Tlet of (term_node term_o) * ((vsymbol*bind_info)*(term_node term_o))
| Tcase of (term_node term_o)
   * (((pattern_node pattern_o)*bind_info)*(term_node term_o)) list
| Teps of ((vsymbol*bind_info)*(term_node term_o))
| Tquant of quant
   * (((vsymbol list*bind_info)*(term_node term_o) list
     list)*(term_node term_o))
| Tbinop of binop * (term_node term_o) * (term_node term_o)
| Tnot of (term_node term_o)
| Ttrue
| Tfalse

type term_bound = (vsymbol*bind_info)*(term_node term_o)

type term_branch = ((pattern_node pattern_o)*bind_info)*(term_node term_o)

type trigger = (term_node term_o) list list

type term_quant = ((vsymbol list*bind_info)*trigger)*(term_node term_o)

type term = term_node term_o

(** val build_term_o :
    term_node -> ty_node_c ty_o option -> Sattr.t -> position option ->
    term_node term_o **)

let build_term_o t0 o a l =
  { t_node = t0; t_ty = o; t_attrs = a; t_loc = l }

(** val bind_info_eqb : bind_info -> bind_info -> bool **)

let bind_info_eqb b1 b2 =
  Mvs.equal BigInt.eq b1.bv_vars b2.bv_vars

(** val quant_eqb : quant -> quant -> bool **)

let quant_eqb q1 q2 =
  match q1 with
  | Tforall -> (match q2 with
                | Tforall -> true
                | Texists -> false)
  | Texists -> (match q2 with
                | Tforall -> false
                | Texists -> true)

(** val binop_eqb : binop -> binop -> bool **)

let binop_eqb b1 b2 =
  match b1 with
  | Tand -> (match b2 with
             | Tand -> true
             | _ -> false)
  | Tor -> (match b2 with
            | Tor -> true
            | _ -> false)
  | Timplies -> (match b2 with
                 | Timplies -> true
                 | _ -> false)
  | Tiff -> (match b2 with
             | Tiff -> true
             | _ -> false)

(** val term_eqb : (term_node term_o) -> (term_node term_o) -> bool **)

let rec term_eqb t1 t2 =
  (&&)
    ((&&)
      ((&&) (term_node_eqb (t_node t1) (t_node t2))
        (option_eqb ty_eqb (t_ty t1) (t_ty t2)))
      (Sattr.equal (t_attrs t1) (t_attrs t2)))
    (option_eqb position_eqb (t_loc t1) (t_loc t2))

(** val term_node_eqb : term_node -> term_node -> bool **)

and term_node_eqb t1 t2 =
  match t1 with
  | Tvar v1 -> (match t2 with
                | Tvar v2 -> vsymbol_eqb v1 v2
                | _ -> false)
  | Tconst c1 -> (match t2 with
                  | Tconst c2 -> constant_eqb c1 c2
                  | _ -> false)
  | Tapp (l1, ts1) ->
    (match t2 with
     | Tapp (l2, ts2) -> (&&) (lsymbol_eqb l1 l2) (list_eqb term_eqb ts1 ts2)
     | _ -> false)
  | Tif (t3, t4, t5) ->
    (match t2 with
     | Tif (e1, e2, e3) ->
       (&&) ((&&) (term_eqb t3 e1) (term_eqb t4 e2)) (term_eqb t5 e3)
     | _ -> false)
  | Tlet (t3, p) ->
    let p0,t4 = p in
    let v1,b1 = p0 in
    (match t2 with
     | Tlet (t5, p1) ->
       let p2,t6 = p1 in
       let v2,b2 = p2 in
       (&&)
         ((&&) ((&&) (term_eqb t3 t5) (vsymbol_eqb v1 v2))
           (bind_info_eqb b1 b2)) (term_eqb t4 t6)
     | _ -> false)
  | Tcase (t3, tbs1) ->
    (match t2 with
     | Tcase (t4, tbs2) ->
       (&&) (term_eqb t3 t4)
         (list_eqb (fun x1 x2 ->
           let y,t5 = x1 in
           let p1,b1 = y in
           let p,t6 = x2 in
           let p2,b2 = p in
           (&&) ((&&) (pattern_eqb p1 p2) (bind_info_eqb b1 b2))
             (term_eqb t5 t6)) tbs1 tbs2)
     | _ -> false)
  | Teps p ->
    let p0,t3 = p in
    let v1,b1 = p0 in
    (match t2 with
     | Teps p1 ->
       let p2,t4 = p1 in
       let v2,b2 = p2 in
       (&&) ((&&) (vsymbol_eqb v1 v2) (bind_info_eqb b1 b2)) (term_eqb t3 t4)
     | _ -> false)
  | Tquant (q1, p) ->
    let p0,t3 = p in
    let p1,tr1 = p0 in
    let l1,b1 = p1 in
    (match t2 with
     | Tquant (q2, p2) ->
       let p3,t4 = p2 in
       let p4,tr2 = p3 in
       let l2,b2 = p4 in
       (&&)
         ((&&)
           ((&&) ((&&) (quant_eqb q1 q2) (list_eqb vsymbol_eqb l1 l2))
             (bind_info_eqb b1 b2)) (list_eqb (list_eqb term_eqb) tr1 tr2))
         (term_eqb t3 t4)
     | _ -> false)
  | Tbinop (b1, t3, t4) ->
    (match t2 with
     | Tbinop (b2, t5, t6) ->
       (&&) ((&&) (binop_eqb b1 b2) (term_eqb t3 t5)) (term_eqb t4 t6)
     | _ -> false)
  | Tnot t3 -> (match t2 with
                | Tnot t4 -> term_eqb t3 t4
                | _ -> false)
  | Ttrue -> (match t2 with
              | Ttrue -> true
              | _ -> false)
  | Tfalse -> (match t2 with
               | Tfalse -> true
               | _ -> false)

(** val term_bound_eqb : term_bound -> term_bound -> bool **)

let term_bound_eqb t1 t2 =
  let p,t3 = t1 in
  let v1,b1 = p in
  let p0,t4 = t2 in
  let v2,b2 = p0 in
  (&&) ((&&) (vsymbol_eqb v1 v2) (bind_info_eqb b1 b2)) (term_eqb t3 t4)

(** val term_branch_eqb : term_branch -> term_branch -> bool **)

let term_branch_eqb tb1 tb2 =
  let p,t1 = tb1 in
  let p1,b1 = p in
  let p0,t2 = tb2 in
  let p2,b2 = p0 in
  (&&) ((&&) (pattern_eqb p1 p2) (bind_info_eqb b1 b2)) (term_eqb t1 t2)

(** val term_quant_eqb : term_quant -> term_quant -> bool **)

let term_quant_eqb tq1 tq2 =
  let p,t1 = tq1 in
  let p0,tr1 = p in
  let vs1,b1 = p0 in
  let p1,t2 = tq2 in
  let p2,tr2 = p1 in
  let vs2,b2 = p2 in
  (&&)
    ((&&) ((&&) (list_eqb vsymbol_eqb vs1 vs2) (bind_info_eqb b1 b2))
      (list_eqb (list_eqb term_eqb) tr1 tr2)) (term_eqb t1 t2)




exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

exception BadArity of lsymbol * BigInt.t
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol

exception TermExpected of term
exception FmlaExpected of term

(*TODO: move*)
exception AssertFail of string

exception InvalidIntegerLiteralType of ty
exception InvalidRealLiteralType of ty
exception InvalidStringLiteralType of ty

exception EmptyCase

















(** val mk_pattern :
    pattern_node -> Svs.t -> ty_node_c ty_o -> (pattern_node pattern_o) **)

let mk_pattern n vs t0 =
  (fun (a, b, c) -> build_pattern_o a b c) (n, vs, t0)

(** val pat_wild : ty_node_c ty_o -> (pattern_node pattern_o) **)

let pat_wild t0 =
  mk_pattern Pwild Svs.empty t0

(** val pat_var : vsymbol -> (pattern_node pattern_o) **)

let pat_var v =
  mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty

(** val pat_as_aux :
    (pattern_node pattern_o) -> vsymbol -> (pattern_node pattern_o) errorM **)

let pat_as_aux p v =
  (@@) (fun s ->  (mk_pattern (Pas (p, v)) s v.vs_ty))
    (Svs.add_new (DuplicateVar v) v (pat_vars p))

(** val pat_or_aux :
    (pattern_node pattern_o) -> (pattern_node pattern_o) ->
    (pattern_node pattern_o) errorM **)

let pat_or_aux p q =
  if Svs.equal (pat_vars p) (pat_vars q)
  then  (mk_pattern (Por (p, q)) (pat_vars p) (pat_ty p))
  else let s = Mvs.union (fun _ _ _ -> None) (pat_vars p) (pat_vars q) in
       (@@) (fun x -> raise (UncoveredVar x)) (Svs.choose s)

(** val pat_app_aux :
    lsymbol -> (pattern_node pattern_o) list -> ty_node_c ty_o ->
    (pattern_node pattern_o) errorM **)

let pat_app_aux f pl t0 =
  let dups =
    fold_left (fun s p ->
      (@@) (fun s1 ->
        let dups = Mvs.inter (fun _ _ _ -> Some ()) s1 (pat_vars p) in
        if negb (Mvs.is_empty dups)
        then (@@) (fun x -> raise (DuplicateVar (fst x))) (Mvs.choose dups)
        else  (Mvs.union (fun _ _ _ -> None) s1 (pat_vars p))) s) pl
      ( Svs.empty)
  in
  (@@) (fun s ->  (mk_pattern (Papp (f, pl)) s t0)) dups

(** val pat_map_aux :
    ((pattern_node pattern_o) -> (pattern_node pattern_o) errorM) ->
    (pattern_node pattern_o) -> (pattern_node pattern_o) errorM **)

let pat_map_aux fn p =
  match pat_node p with
  | Papp (s, pl) ->
    (@@) (fun l -> pat_app_aux s l (pat_ty p)) (errorM_list (map fn pl))
  | Por (p0, q) ->
    (@@) (fun p1 -> (@@) (fun q1 -> pat_or_aux p1 q1) (fn q)) (fn p0)
  | Pas (p0, v) -> (@@) (fun p1 -> pat_as_aux p1 v) (fn p0)
  | _ ->  p

(** val pat_map :
    ((pattern_node pattern_o) -> (pattern_node pattern_o)) ->
    (pattern_node pattern_o) -> (pattern_node pattern_o) errorM **)

let pat_map fn =
  pat_map_aux (fun p ->
    let res = fn p in
    (@@) (fun _ ->  res) (ty_equal_check (pat_ty p) (pat_ty res)))

(** val pat_map_err :
    ((pattern_node pattern_o) -> (pattern_node pattern_o) errorM) ->
    (pattern_node pattern_o) -> (pattern_node pattern_o) errorM **)

let pat_map_err fn =
  pat_map_aux (fun p ->
    (@@) (fun res ->
      (@@) (fun _ ->  res) (ty_equal_check (pat_ty p) (pat_ty res))) 
      (fn p))

(** val pat_fold :
    ('a1 -> (pattern_node pattern_o) -> 'a1) -> 'a1 ->
    (pattern_node pattern_o) -> 'a1 **)

let pat_fold fn acc pat =
  match pat_node pat with
  | Papp (_, pl) -> fold_left fn pl acc
  | Por (p, q) -> fn (fn acc p) q
  | Pas (p, _) -> fn acc p
  | _ -> acc

(** val pat_all :
    ((pattern_node pattern_o) -> bool) -> (pattern_node pattern_o) -> bool **)

let pat_all pr pat =
  pat_fold (fun x y -> (&&) x (pr y)) true pat

(** val pat_any :
    ((pattern_node pattern_o) -> bool) -> (pattern_node pattern_o) -> bool **)

let pat_any pr pat =
  pat_fold (fun x y -> (||) x (pr y)) false pat

(** val pat_app :
    lsymbol -> (pattern_node pattern_o) list -> ty_node_c ty_o -> (TyHash.t
    hashcons_ty, (pattern_node pattern_o)) errState **)

let pat_app fs pl t0 =
  (@@) (fun s ->
    let mtch = fun s0 ty p -> ty_match s0 ty (pat_ty p) in
    (@@) (fun o ->
      
        (match o with
         | Some _ ->
           if BigInt.is_zero fs.ls_constr
           then raise (ConstructorExpected fs)
           else pat_app_aux fs pl t0
         | None -> raise (BadArity (fs,(int_length pl)))))
      (fold_left2_errst mtch s fs.ls_args pl))
    (match fs.ls_value with
     | Some vty -> ty_match Mtv.empty vty t0
     | None ->  (raise (FunctionSymbolExpected fs)))

(** val pat_as :
    (pattern_node pattern_o) -> vsymbol -> (pattern_node pattern_o) errorM **)

let pat_as p v =
  (@@) (fun _ -> pat_as_aux p v) (ty_equal_check (pat_ty p) v.vs_ty)

(** val pat_or :
    (pattern_node pattern_o) -> (pattern_node pattern_o) ->
    (pattern_node pattern_o) errorM **)

let pat_or p q =
  (@@) (fun _ -> pat_or_aux p q) (ty_equal_check (pat_ty p) (pat_ty q))

(** val pat_app_unsafe :
    lsymbol -> (pattern_node pattern_o) list -> ty_node_c ty_o ->
    (pattern_node pattern_o) **)

let pat_app_unsafe f pl t0 =
  let un = fold_left (fun s p -> Svs.union s (pat_vars p)) pl Svs.empty in
  mk_pattern (Papp (f, pl)) un t0

(** val pat_as_unsafe :
    (pattern_node pattern_o) -> vsymbol -> (pattern_node pattern_o) **)

let pat_as_unsafe p v =
  let s = Svs.add v (pat_vars p) in mk_pattern (Pas (p, v)) s v.vs_ty

(** val pat_or_unsafe :
    (pattern_node pattern_o) -> (pattern_node pattern_o) ->
    (pattern_node pattern_o) **)

let pat_or_unsafe p q =
  mk_pattern (Por (p, q)) (pat_vars p) (pat_ty p)

(** val pat_map_unsafe :
    ((pattern_node pattern_o) -> (pattern_node pattern_o)) ->
    (pattern_node pattern_o) -> (pattern_node pattern_o) **)

let pat_map_unsafe fn p =
  match pat_node p with
  | Papp (s, pl) -> pat_app_unsafe s (map fn pl) (pat_ty p)
  | Por (p0, q) -> pat_or_unsafe (fn p0) (fn q)
  | Pas (p0, v) -> pat_as_unsafe (fn p0) v
  | _ -> p

(** val pat_rename_all :
    vsymbol Mvs.t -> (pattern_node pattern_o) -> (pattern_node pattern_o) **)

let rec pat_rename_all m p =
  match pat_node p with
  | Pvar v -> (match Mvs.find_opt v m with
               | Some v1 -> pat_var v1
               | None -> p)
  | Pas (p0, v) ->
    let p1 = pat_rename_all m p0 in
    pat_as_unsafe p1 (match Mvs.find_opt v m with
                      | Some v1 -> v1
                      | None -> v)
  | _ -> pat_map_unsafe (pat_rename_all m) p

(** val list_comp : Stdlib.Int.t list -> Stdlib.Int.t **)

let list_comp l =
  fold_left lex_comp l Stdlib.Int.zero

(** val var_compare :
    BigInt.t Mvs.t -> BigInt.t Mvs.t -> vsymbol -> vsymbol -> Stdlib.Int.t **)

let var_compare m1 m2 v1 v2 =
  match Mvs.find_opt v1 m1 with
  | Some i1 ->
    (match Mvs.find_opt v2 m2 with
     | Some i2 -> BigInt.compare i1 i2
     | None -> Stdlib.Int.minus_one)
  | None ->
    (match Mvs.find_opt v2 m2 with
     | Some _ -> Stdlib.Int.one
     | None -> vs_compare v1 v2)

(** val quant_compare : quant -> quant -> Stdlib.Int.t **)

let quant_compare q1 q2 =
  match q1 with
  | Tforall ->
    (match q2 with
     | Tforall -> Stdlib.Int.zero
     | Texists -> Stdlib.Int.minus_one)
  | Texists ->
    (match q2 with
     | Tforall -> Stdlib.Int.one
     | Texists -> Stdlib.Int.zero)

(** val binop_compare : binop -> binop -> Stdlib.Int.t **)

let binop_compare b1 b2 =
  match b1 with
  | Tand ->
    (match b2 with
     | Tand -> Stdlib.Int.zero
     | _ -> Stdlib.Int.minus_one)
  | Tor ->
    (match b2 with
     | Tand -> Stdlib.Int.one
     | Tor -> Stdlib.Int.zero
     | _ -> Stdlib.Int.minus_one)
  | Timplies ->
    (match b2 with
     | Timplies -> Stdlib.Int.zero
     | Tiff -> Stdlib.Int.minus_one
     | _ -> Stdlib.Int.one)
  | Tiff -> (match b2 with
             | Tiff -> Stdlib.Int.zero
             | _ -> Stdlib.Int.one)

(** val fold_left2_def :
    ('a1 -> 'a2 -> 'a3 -> 'a1) -> 'a1 -> 'a1 -> 'a2 list -> 'a3 list -> 'a1
    -> 'a1 **)

let rec fold_left2_def f d1 d2 l1 l2 acc =
  match l1 with
  | [] -> (match l2 with
           | [] -> acc
           | _::_ -> d1)
  | x1::t1 ->
    (match l2 with
     | [] -> d2
     | x2::t2 -> fold_left2_def f d1 d2 t1 t2 (f acc x1 x2))

(** val or_cmp_vsym :
    BigInt.t Mvs.t -> BigInt.t Mvs.t -> vsymbol -> vsymbol -> Stdlib.Int.t **)

let or_cmp_vsym bv1 bv2 v1 v2 =
  match Mvs.find_opt v1 bv1 with
  | Some i1 ->
    (match Mvs.find_opt v2 bv2 with
     | Some i2 -> BigInt.compare i1 i2
     | None -> Stdlib.Int.minus_one)
  | None ->
    (match Mvs.find_opt v2 bv2 with
     | Some _ -> Stdlib.Int.one
     | None -> Stdlib.Int.zero)

(** val or_cmp :
    BigInt.t Mvs.t -> BigInt.t Mvs.t -> (pattern_node pattern_o) ->
    (pattern_node pattern_o) -> Stdlib.Int.t **)

let rec or_cmp bv1 bv2 q1 q2 =
  match pat_node q1 with
  | Pwild ->
    (match pat_node q2 with
     | Pwild -> Stdlib.Int.zero
     | _ -> Stdlib.Int.minus_one)
  | Pvar v1 ->
    (match pat_node q2 with
     | Pwild -> Stdlib.Int.one
     | Pvar v2 -> or_cmp_vsym bv1 bv2 v1 v2
     | _ -> Stdlib.Int.minus_one)
  | Papp (s1, l1) ->
    (match pat_node q2 with
     | Pwild -> Stdlib.Int.one
     | Pvar _ -> Stdlib.Int.one
     | Papp (s2, l2) ->
       let i1 = ls_compare s1 s2 in
       lex_comp i1
         (fold_left2_def (fun i p1 p2 -> lex_comp i (or_cmp bv1 bv2 p1 p2))
           Stdlib.Int.minus_one Stdlib.Int.one l1 l2 Stdlib.Int.zero)
     | _ -> Stdlib.Int.minus_one)
  | Por (p1, q3) ->
    (match pat_node q2 with
     | Por (p2, q4) ->
       let i1 = or_cmp bv1 bv2 p1 p2 in lex_comp i1 (or_cmp bv1 bv2 q3 q4)
     | Pas (_, _) -> Stdlib.Int.minus_one
     | _ -> Stdlib.Int.one)
  | Pas (p1, v1) ->
    (match pat_node q2 with
     | Pas (p2, v2) ->
       let i1 = or_cmp bv1 bv2 p1 p2 in
       lex_comp i1 (or_cmp_vsym bv1 bv2 v1 v2)
     | _ -> Stdlib.Int.one)

(** val pat_compare :
    ((BigInt.t*BigInt.t Mvs.t)*BigInt.t Mvs.t) -> (pattern_node pattern_o) ->
    (pattern_node pattern_o) -> ((Stdlib.Int.t*BigInt.t)*BigInt.t
    Mvs.t)*BigInt.t Mvs.t **)

let rec pat_compare state p1 p2 =
  let p,bv2 = state in
  let bnd,bv1 = p in
  (match pat_node p1 with
   | Pwild ->
     (match pat_node p2 with
      | Pwild -> ((Stdlib.Int.zero,bnd),bv1),bv2
      | _ -> ((Stdlib.Int.minus_one,bnd),bv1),bv2)
   | Pvar v1 ->
     (match pat_node p2 with
      | Pwild -> ((Stdlib.Int.one,bnd),bv1),bv2
      | Pvar v2 ->
        ((Stdlib.Int.zero,(BigInt.succ bnd)),(Mvs.add v1 bnd bv1)),(Mvs.add
                                                                    v2 bnd
                                                                    bv2)
      | _ -> ((Stdlib.Int.minus_one,bnd),bv1),bv2)
   | Papp (s1, l1) ->
     (match pat_node p2 with
      | Pwild -> ((Stdlib.Int.one,bnd),bv1),bv2
      | Pvar _ -> ((Stdlib.Int.one,bnd),bv1),bv2
      | Papp (s2, l2) ->
        let i1 = ls_compare s1 s2 in
        let p0,sm2 = state in
        let sbnd,sm1 = p0 in
        let p3,bv3 =
          fold_left2_def (fun acc p3 p4 ->
            let y,m2 = acc in
            let y0,m1 = y in
            let i,bnd1 = y0 in
            let p5,m2' = pat_compare ((bnd1,m1),m2) p3 p4 in
            let p6,m1' = p5 in
            let j,bnd2 = p6 in (((lex_comp i j),bnd2),m1'),m2')
            (((Stdlib.Int.minus_one,sbnd),sm1),sm2)
            (((Stdlib.Int.one,sbnd),sm1),sm2) l1 l2
            (((Stdlib.Int.zero,sbnd),sm1),sm2)
        in
        let p4,bv4 = p3 in
        let i2,bnd0 = p4 in (((lex_comp i1 i2),bnd0),bv4),bv3
      | _ -> ((Stdlib.Int.minus_one,bnd),bv1),bv2)
   | Por (p3, q1) ->
     (match pat_node p2 with
      | Por (p4, q2) ->
        let p0,bv3 = pat_compare state p3 p4 in
        let p5,bv4 = p0 in
        let i1,bnd1 = p5 in
        if negb ((fun x -> Stdlib.Int.equal x Stdlib.Int.zero) i1)
        then ((i1,bnd1),bv4),bv3
        else let i2 = or_cmp bv4 bv4 q1 q2 in ((i2,bnd1),bv4),bv3
      | Pas (_, _) -> ((Stdlib.Int.minus_one,bnd),bv1),bv2
      | _ -> ((Stdlib.Int.one,bnd),bv1),bv2)
   | Pas (p3, v1) ->
     (match pat_node p2 with
      | Pas (p4, v2) ->
        let p0,bv3 = pat_compare state p3 p4 in
        let p5,bv4 = p0 in
        let i1,bnd0 = p5 in
        ((i1,(BigInt.succ bnd0)),(Mvs.add v1 bnd0 bv4)),(Mvs.add v2 bnd0 bv3)
      | _ -> ((Stdlib.Int.one,bnd),bv1),bv2))

(** val list_compare :
    ('a1 -> 'a2 -> Stdlib.Int.t) -> 'a1 list -> 'a2 list -> Stdlib.Int.t **)

let list_compare cmp l1 l2 =
  fold_left2_def (fun acc x1 x2 -> lex_comp acc (cmp x1 x2))
    Stdlib.Int.minus_one Stdlib.Int.one l1 l2 Stdlib.Int.zero

(** val t_compare_aux :
    bool -> bool -> bool -> bool -> BigInt.t -> BigInt.t Mvs.t -> BigInt.t
    Mvs.t -> (term_node term_o) -> (term_node term_o) -> Stdlib.Int.t **)

let rec t_compare_aux trigger0 attr loc const bnd vml1 vml2 t1 t2 =
  let i1 = oty_compare (t_ty t1) (t_ty t2) in
  lex_comp i1
    (let i2 =
       if attr
       then Sattr.compare (t_attrs t1) (t_attrs t2)
       else Stdlib.Int.zero
     in
     lex_comp i2
       (let i3 =
          if loc
          then option_compare compare (t_loc t1) (t_loc t2)
          else Stdlib.Int.zero
        in
        lex_comp i3
          (match t_node t1 with
           | Tvar v1 ->
             (match t_node t2 with
              | Tvar v2 -> var_compare vml1 vml2 v1 v2
              | _ -> Stdlib.Int.minus_one)
           | Tconst c1 ->
             (match t_node t2 with
              | Tvar _ -> Stdlib.Int.one
              | Tconst c2 -> compare_const_aux const c1 c2
              | _ -> Stdlib.Int.minus_one)
           | Tapp (s1, l1) ->
             (match t_node t2 with
              | Tvar _ -> Stdlib.Int.one
              | Tconst _ -> Stdlib.Int.one
              | Tapp (s2, l2) ->
                let i4 = ls_compare s1 s2 in
                lex_comp i4
                  (fold_left2_def (fun acc t3 t4 ->
                    lex_comp acc
                      (t_compare_aux trigger0 attr loc const bnd vml1 vml2 t3
                        t4)) Stdlib.Int.minus_one Stdlib.Int.one l1 l2
                    Stdlib.Int.zero)
              | _ -> Stdlib.Int.minus_one)
           | Tif (f1, t3, e1) ->
             (match t_node t2 with
              | Tvar _ -> Stdlib.Int.one
              | Tconst _ -> Stdlib.Int.one
              | Tapp (_, _) -> Stdlib.Int.one
              | Tif (f2, t4, e2) ->
                let i4 =
                  t_compare_aux trigger0 attr loc const bnd vml1 vml2 f1 f2
                in
                lex_comp i4
                  (let i5 =
                     t_compare_aux trigger0 attr loc const bnd vml1 vml2 t3 t4
                   in
                   lex_comp i5
                     (t_compare_aux trigger0 attr loc const bnd vml1 vml2 e1
                       e2))
              | _ -> Stdlib.Int.minus_one)
           | Tlet (t3, p) ->
             let p0,e1 = p in
             let v1,_ = p0 in
             (match t_node t2 with
              | Tvar _ -> Stdlib.Int.one
              | Tconst _ -> Stdlib.Int.one
              | Tapp (_, _) -> Stdlib.Int.one
              | Tif (_, _, _) -> Stdlib.Int.one
              | Tlet (t4, p1) ->
                let p2,e2 = p1 in
                let v2,_ = p2 in
                let i4 =
                  t_compare_aux trigger0 attr loc const bnd vml1 vml2 t3 t4
                in
                lex_comp i4
                  (let vml3 = Mvs.add v1 bnd vml1 in
                   let vml4 = Mvs.add v2 bnd vml2 in
                   t_compare_aux trigger0 attr loc const (BigInt.succ bnd)
                     vml3 vml4 e1 e2)
              | _ -> Stdlib.Int.minus_one)
           | Tcase (t3, bl1) ->
             (match t_node t2 with
              | Tvar _ -> Stdlib.Int.one
              | Tconst _ -> Stdlib.Int.one
              | Tapp (_, _) -> Stdlib.Int.one
              | Tif (_, _, _) -> Stdlib.Int.one
              | Tlet (_, _) -> Stdlib.Int.one
              | Tcase (t4, bl2) ->
                let i4 =
                  t_compare_aux trigger0 attr loc const bnd vml1 vml2 t3 t4
                in
                lex_comp i4
                  (let b_compare = fun x1 x2 ->
                     let y,t5 = x1 in
                     let p1,_ = y in
                     let y0,t6 = x2 in
                     let p2,_ = y0 in
                     let p,bv2 = pat_compare ((bnd,Mvs.empty),Mvs.empty) p1 p2
                     in
                     let p0,bv1 = p in
                     let ip,bnd0 = p0 in
                     lex_comp ip
                       (let vml3 = Mvs.union (fun _ n1 _ -> Some n1) bv1 vml1
                        in
                        let vml4 = Mvs.union (fun _ n1 _ -> Some n1) bv2 vml2
                        in
                        t_compare_aux trigger0 attr loc const bnd0 vml3 vml4
                          t5 t6)
                   in
                   list_compare b_compare bl1 bl2)
              | _ -> Stdlib.Int.minus_one)
           | Teps p ->
             let p0,e1 = p in
             let v1,_ = p0 in
             (match t_node t2 with
              | Teps p1 ->
                let p2,e2 = p1 in
                let v2,_ = p2 in
                let vml3 = Mvs.add v1 bnd vml1 in
                let vml4 = Mvs.add v2 bnd vml2 in
                t_compare_aux trigger0 attr loc const (BigInt.succ bnd) vml3
                  vml4 e1 e2
              | Tquant (_, _) -> Stdlib.Int.minus_one
              | Tbinop (_, _, _) -> Stdlib.Int.minus_one
              | Tnot _ -> Stdlib.Int.minus_one
              | Ttrue -> Stdlib.Int.minus_one
              | Tfalse -> Stdlib.Int.minus_one
              | _ -> Stdlib.Int.one)
           | Tquant (q1, p) ->
             let p0,f1 = p in
             let p1,tr1 = p0 in
             let vl1,_ = p1 in
             (match t_node t2 with
              | Tquant (q2, p2) ->
                let p3,f2 = p2 in
                let p4,tr2 = p3 in
                let vl2,_ = p4 in
                let i4 = quant_compare q1 q2 in
                lex_comp i4
                  (let add0 = fun bnd0 bv1 bv2 vl3 vl4 ->
                     fold_left2_def (fun acc v1 v2 ->
                       let y,bv3 = acc in
                       let y0,bv4 = y in
                       let val0,bnd1 = y0 in
                       ((val0,(BigInt.succ bnd1)),(Mvs.add v1 bnd1 bv4)),
                       (Mvs.add v2 bnd1 bv3))
                       (((Stdlib.Int.minus_one,bnd0),bv1),bv2)
                       (((Stdlib.Int.one,bnd0),bv1),bv2) vl3 vl4
                       (((Stdlib.Int.zero,bnd0),bv1),bv2)
                   in
                   let p5,bv2 = add0 bnd Mvs.empty Mvs.empty vl1 vl2 in
                   let p6,bv1 = p5 in
                   let i5,bnd0 = p6 in
                   lex_comp i5
                     (let vml3 = Mvs.union (fun _ n1 _ -> Some n1) bv1 vml1 in
                      let vml4 = Mvs.union (fun _ n1 _ -> Some n1) bv2 vml2 in
                      let tr_cmp = fun t3 t4 ->
                        t_compare_aux trigger0 attr loc const bnd0 vml3 vml4
                          t3 t4
                      in
                      let i6 =
                        if trigger0
                        then list_compare (list_compare tr_cmp) tr1 tr2
                        else Stdlib.Int.zero
                      in
                      lex_comp i6
                        (t_compare_aux trigger0 attr loc const bnd0 vml3 vml4
                          f1 f2)))
              | Tbinop (_, _, _) -> Stdlib.Int.minus_one
              | Tnot _ -> Stdlib.Int.minus_one
              | Ttrue -> Stdlib.Int.minus_one
              | Tfalse -> Stdlib.Int.minus_one
              | _ -> Stdlib.Int.one)
           | Tbinop (op1, f1, g1) ->
             (match t_node t2 with
              | Tbinop (op2, f2, g2) ->
                let i4 = binop_compare op1 op2 in
                lex_comp i4
                  (let i5 =
                     t_compare_aux trigger0 attr loc const bnd vml1 vml2 g1 g2
                   in
                   lex_comp i5
                     (t_compare_aux trigger0 attr loc const bnd vml1 vml2 f1
                       f2))
              | Tnot _ -> Stdlib.Int.minus_one
              | Ttrue -> Stdlib.Int.minus_one
              | Tfalse -> Stdlib.Int.minus_one
              | _ -> Stdlib.Int.one)
           | Tnot f1 ->
             (match t_node t2 with
              | Tnot f2 ->
                t_compare_aux trigger0 attr loc const bnd vml1 vml2 f1 f2
              | Ttrue -> Stdlib.Int.minus_one
              | Tfalse -> Stdlib.Int.minus_one
              | _ -> Stdlib.Int.one)
           | Ttrue ->
             (match t_node t2 with
              | Ttrue -> Stdlib.Int.zero
              | Tfalse -> Stdlib.Int.minus_one
              | _ -> Stdlib.Int.one)
           | Tfalse ->
             (match t_node t2 with
              | Tfalse -> Stdlib.Int.zero
              | _ -> Stdlib.Int.one))))

(** val t_compare_full :
    bool -> bool -> bool -> bool -> (term_node term_o) -> (term_node term_o)
    -> Stdlib.Int.t **)

let t_compare_full trigger0 attr loc const t1 t2 =
  t_compare_aux trigger0 attr loc const BigInt.zero Mvs.empty Mvs.empty t1 t2

(** val t_similar : (term_node term_o) -> (term_node term_o) -> bool **)

let t_similar t1 t2 =
  (&&) (oty_equal (t_ty t1) (t_ty t2))
    (match t_node t1 with
     | Tvar v1 ->
       (match t_node t2 with
        | Tvar v2 -> vs_equal v1 v2
        | _ -> false)
     | Tconst c1 ->
       (match t_node t2 with
        | Tconst c2 ->
          Stdlib.Int.equal (compare_const_aux true c1 c2) Stdlib.Int.zero
        | _ -> false)
     | Tapp (s1, l1) ->
       (match t_node t2 with
        | Tapp (s2, l2) ->
          (&&) (ls_equal s1 s2)
            (list_eqb (fun x y -> x == y || term_eqb x y) l1 l2)
        | _ -> false)
     | Tif (f1, t3, e1) ->
       (match t_node t2 with
        | Tif (f2, t4, e2) ->
          (&&)
            ((&&) ((fun x y -> x == y || term_eqb x y) f1 f2)
              ((fun x y -> x == y || term_eqb x y) t3 t4))
            ((fun x y -> x == y || term_eqb x y) e1 e2)
        | _ -> false)
     | Tlet (t3, bv1) ->
       (match t_node t2 with
        | Tlet (t4, bv2) ->
          (&&) ((fun x y -> x == y || term_eqb x y) t3 t4)
            ((fun x y -> x == y || term_bound_eqb x y) bv1 bv2)
        | _ -> false)
     | Tcase (t3, bl1) ->
       (match t_node t2 with
        | Tcase (t4, bl2) ->
          (&&) ((fun x y -> x == y || term_eqb x y) t3 t4)
            (list_eqb (fun x y -> x == y || term_branch_eqb x y) bl1 bl2)
        | _ -> false)
     | Teps bv1 ->
       (match t_node t2 with
        | Teps bv2 -> (fun x y -> x == y || term_bound_eqb x y) bv1 bv2
        | _ -> false)
     | Tquant (q1, bv1) ->
       (match t_node t2 with
        | Tquant (q2, bv2) ->
          (&&) (quant_eqb q1 q2)
            ((fun x y -> x == y || term_quant_eqb x y) bv1 bv2)
        | _ -> false)
     | Tbinop (o1, f1, g1) ->
       (match t_node t2 with
        | Tbinop (o2, f2, g2) ->
          (&&)
            ((&&) (binop_eqb o1 o2)
              ((fun x y -> x == y || term_eqb x y) f1 f2))
            ((fun x y -> x == y || term_eqb x y) g1 g2)
        | _ -> false)
     | Tnot f1 ->
       (match t_node t2 with
        | Tnot f2 -> (fun x y -> x == y || term_eqb x y) f1 f2
        | _ -> false)
     | Ttrue -> (match t_node t2 with
                 | Ttrue -> true
                 | _ -> false)
     | Tfalse -> (match t_node t2 with
                  | Tfalse -> true
                  | _ -> false))

(** val or_hash : BigInt.t Mvs.t -> (pattern_node pattern_o) -> BigInt.t **)

let rec or_hash bv q =
  match pat_node q with
  | Pwild -> BigInt.zero
  | Pvar v ->
    BigInt.succ
      (match Mvs.find_opt v bv with
       | Some i -> i
       | None -> BigInt.zero)
  | Papp (s, l) -> combine_big_list (or_hash bv) (ls_hash s) l
  | Por (p, q0) -> combine_big (or_hash bv p) (or_hash bv q0)
  | Pas (p, v) ->
    let j = match Mvs.find_opt v bv with
            | Some i -> i
            | None -> BigInt.zero in
    combine_big (or_hash bv p) (BigInt.succ j)

(** val pat_hash :
    BigInt.t -> BigInt.t Mvs.t -> (pattern_node pattern_o) ->
    (BigInt.t*BigInt.t Mvs.t)*BigInt.t **)

let rec pat_hash bnd bv p =
  match pat_node p with
  | Pwild -> (bnd,bv),BigInt.zero
  | Pvar v -> ((BigInt.succ bnd),(Mvs.add v bnd bv)),(BigInt.succ bnd)
  | Papp (s, l) ->
    fold_left (fun acc p0 ->
      let y,h = acc in
      let bnd0,bv0 = y in
      let p1,hp = pat_hash bnd0 bv0 p0 in p1,(combine_big h hp)) l
      ((bnd,bv),(ls_hash s))
  | Por (p0, q) ->
    let p1,hp = pat_hash bnd bv p0 in
    let bnd1,bv1 = p1 in (bnd1,bv1),(combine_big hp (or_hash bv1 q))
  | Pas (p0, v) ->
    let p1,hp = pat_hash bnd bv p0 in
    let bnd1,_ = p1 in
    ((BigInt.succ bnd1),(Mvs.add v bnd bv)),(combine_big hp
                                              (BigInt.succ bnd1))

(** val q_hash : quant -> BigInt.t **)

let q_hash = function
| Tforall -> (BigInt.of_int 5)
| Texists -> (BigInt.of_int 7)

(** val binop_hash : binop -> BigInt.t **)

let binop_hash = function
| Tand -> (BigInt.of_int 11)
| Tor -> (BigInt.of_int 13)
| Timplies -> (BigInt.of_int 17)
| Tiff -> (BigInt.of_int 19)

(** val t_hash_aux :
    bool -> bool -> bool -> BigInt.t -> BigInt.t Mvs.t -> (term_node term_o)
    -> BigInt.t **)

let rec t_hash_aux trigger0 attr const bnd vml t0 =
  let h = oty_hash (t_ty t0) in
  let h1 =
    if attr
    then Sattr.fold (fun l h0 -> combine_big (attr_hash l) h0) (t_attrs t0) h
    else h
  in
  combine_big h1
    (match t_node t0 with
     | Tvar v ->
       (match Mvs.find_opt v vml with
        | Some i -> BigInt.succ i
        | None -> vs_hash v)
     | Tconst c ->
       if const
       then constant_hash c
       else (match c with
             | ConstInt i -> i.il_int
             | ConstReal r -> real_value_hash r.rl_real
             | ConstStr c0 -> str_hash c0)
     | Tapp (s, l) ->
       combine_big_list (t_hash_aux trigger0 attr const bnd vml) (ls_hash s) l
     | Tif (f, t1, e) ->
       combine2_big (t_hash_aux trigger0 attr const bnd vml f)
         (t_hash_aux trigger0 attr const bnd vml t1)
         (t_hash_aux trigger0 attr const bnd vml e)
     | Tlet (t1, p) ->
       let p0,e = p in
       let v,_ = p0 in
       combine_big (t_hash_aux trigger0 attr const bnd vml t1)
         (t_hash_aux trigger0 attr const (BigInt.succ bnd)
           (Mvs.add v bnd vml) e)
     | Tcase (_, bl) ->
       let b_hash = fun x ->
         let y,t1 = x in
         let p,_ = y in
         let p0,hp = pat_hash bnd Mvs.empty p in
         let bnd0,bv = p0 in
         let vml0 = Mvs.union (fun _ n1 _ -> Some n1) bv vml in
         combine_big hp (t_hash_aux trigger0 attr const bnd0 vml0 t1)
       in
       combine_big_list b_hash h bl
     | Teps p ->
       let p0,e = p in
       let v,_ = p0 in
       t_hash_aux trigger0 attr const (BigInt.succ bnd) (Mvs.add v bnd vml) e
     | Tquant (q, p) ->
       let p0,f = p in
       let p1,tr = p0 in
       let vl,_ = p1 in
       let h0 = q_hash q in
       let bnd0,bv =
         fold_left (fun acc v ->
           let bnd0,bv = acc in (BigInt.succ bnd0),(Mvs.add v bnd0 bv)) vl
           (bnd,Mvs.empty)
       in
       let vml0 = Mvs.union (fun _ n1 _ -> Some n1) bv vml in
       let h2 =
         if trigger0
         then fold_left
                (combine_big_list (t_hash_aux trigger0 attr const bnd0 vml0))
                tr h0
         else h0
       in
       combine_big h2 (t_hash_aux trigger0 attr const bnd0 vml0 f)
     | Tbinop (op, f, g) ->
       combine2_big (binop_hash op)
         (t_hash_aux trigger0 attr const bnd vml f)
         (t_hash_aux trigger0 attr const bnd vml g)
     | Tnot f ->
       combine_big BigInt.one (t_hash_aux trigger0 attr const bnd vml f)
     | Ttrue -> (BigInt.of_int 2)
     | Tfalse -> (BigInt.of_int 3))

(** val t_hash_full :
    bool -> bool -> bool -> (term_node term_o) -> BigInt.t **)

let t_hash_full trigger0 attr const t0 =
  t_hash_aux trigger0 attr const BigInt.zero Mvs.empty t0

(** val t_hash_strict : (term_node term_o) -> BigInt.t **)

let t_hash_strict t0 =
  t_hash_full true true true t0

(** val t_equal_strict : (term_node term_o) -> (term_node term_o) -> bool **)

let t_equal_strict t1 t2 =
  Stdlib.Int.equal (t_compare_full true true true true t1 t2) Stdlib.Int.zero

(** val t_compare_strict :
    (term_node term_o) -> (term_node term_o) -> Stdlib.Int.t **)

let t_compare_strict t1 t2 =
  t_compare_full true true true true t1 t2

(** val t_hash : (term_node term_o) -> BigInt.t **)

let t_hash t0 =
  t_hash_full false false false t0

(** val t_equal : (term_node term_o) -> (term_node term_o) -> bool **)

let t_equal t1 t2 =
  Stdlib.Int.equal (t_compare_full false false false false t1 t2)
    Stdlib.Int.zero

(** val t_compare :
    (term_node term_o) -> (term_node term_o) -> Stdlib.Int.t **)

let t_compare t1 t2 =
  t_compare_full false false false false t1 t2

(** val t_type : (term_node term_o) -> ty_node_c ty_o errorM **)

let t_type t0 =
  match t_ty t0 with
  | Some ty ->  ty
  | None -> raise (TermExpected t0)

(** val t_prop : (term_node term_o) -> (term_node term_o) errorM **)

let t_prop f =
  if negb (isSome (t_ty f)) then  f else raise (FmlaExpected f)

(** val t_ty_check :
    (term_node term_o) -> ty_node_c ty_o option -> unit errorM **)

let t_ty_check t0 = function
| Some l ->
  (match t_ty t0 with
   | Some r -> ty_equal_check l r
   | None -> raise (TermExpected t0))
| None -> (match t_ty t0 with
           | Some _ -> raise (FmlaExpected t0)
           | None ->  ())

(** val vs_check : vsymbol -> (term_node term_o) -> unit errorM **)

let vs_check v t0 =
  (@@) (fun typ -> ty_equal_check v.vs_ty typ) (t_type t0)

(** val tr_equal :
    (term_node term_o) list list -> (term_node term_o) list list -> bool **)

let tr_equal =
  list_eqb (list_eqb t_equal)

(** val tr_map : ('a1 -> 'a2) -> 'a1 list list -> 'a2 list list **)

let tr_map fn =
  map (map fn)

(** val tr_fold : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list list -> 'a1 **)

let tr_fold fn acc l =
  fold_left (fun acc0 tms -> fold_left fn tms acc0) l acc

(** val tr_map_fold :
    ('a1 -> 'a2 -> 'a1*'a3) -> 'a1 -> 'a2 list list -> 'a1*'a3 list list **)

let tr_map_fold fn =
  map_fold_left (map_fold_left fn)

(** val vars_union : BigInt.t Mvs.t -> BigInt.t Mvs.t -> BigInt.t Mvs.t **)

let vars_union s1 s2 =
  Mvs.union (fun _ m n -> Some (BigInt.add m n)) s1 s2

(** val add_b_vars :
    BigInt.t Mvs.t -> (('a1*bind_info)*'a2) -> BigInt.t Mvs.t **)

let add_b_vars s = function
| p,_ -> let _,b = p in vars_union s b.bv_vars

(** val t_vars : (term_node term_o) -> BigInt.t Mvs.t **)

let rec t_vars t0 =
  match t_node t0 with
  | Tvar v -> Mvs.singleton v BigInt.one
  | Tapp (_, tl) ->
    fold_left (fun s x -> vars_union s (t_vars x)) tl Mvs.empty
  | Tif (f, t1, e) ->
    vars_union (vars_union (t_vars f) (t_vars t1)) (t_vars e)
  | Tlet (t1, bt) -> add_b_vars (t_vars t1) bt
  | Tcase (t1, bl) -> fold_left add_b_vars bl (t_vars t1)
  | Teps p -> let p0,_ = p in let _,b = p0 in b.bv_vars
  | Tquant (_, p) ->
    let p0,_ = p in let p1,_ = p0 in let _,b = p1 in b.bv_vars
  | Tbinop (_, f1, f2) -> vars_union (t_vars f1) (t_vars f2)
  | Tnot f -> t_vars f
  | _ -> Mvs.empty

(** val add_t_vars :
    BigInt.t Mvs.t -> (term_node term_o) -> BigInt.t Mvs.t **)

let add_t_vars s t0 =
  vars_union s (t_vars t0)

(** val mk_term : term_node -> ty_node_c ty_o option -> (term_node term_o) **)

let mk_term n t0 =
  (fun (a, b, c, d) -> build_term_o a b c d) (n, t0, Sattr.empty, None)

(** val t_var : vsymbol -> (term_node term_o) **)

let t_var v =
  mk_term (Tvar v) (Some v.vs_ty)

(** val t_const1 : constant -> ty_node_c ty_o -> (term_node term_o) **)

let t_const1 c t0 =
  mk_term (Tconst c) (Some t0)

(** val t_app1 :
    lsymbol -> (term_node term_o) list -> ty_node_c ty_o option ->
    (term_node term_o) **)

let t_app1 f tl t0 =
  mk_term (Tapp (f, tl)) t0

(** val t_if1 :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) **)

let t_if1 f t1 t2 =
  mk_term (Tif (f, t1, t2)) (t_ty t2)

(** val t_let1 :
    (term_node term_o) -> ((vsymbol*bind_info)*(term_node term_o)) ->
    ty_node_c ty_o option -> (term_node term_o) **)

let t_let1 t1 bt t0 =
  mk_term (Tlet (t1, bt)) t0

(** val t_case1 :
    (term_node term_o) ->
    (((pattern_node pattern_o)*bind_info)*(term_node term_o)) list ->
    ty_node_c ty_o option -> (term_node term_o) **)

let t_case1 t1 bl t0 =
  mk_term (Tcase (t1, bl)) t0

(** val t_eps1 :
    ((vsymbol*bind_info)*(term_node term_o)) -> ty_node_c ty_o option ->
    (term_node term_o) **)

let t_eps1 bf t0 =
  mk_term (Teps bf) t0

(** val t_quant1 :
    quant -> (((vsymbol list*bind_info)*(term_node term_o) list
    list)*(term_node term_o)) -> (term_node term_o) **)

let t_quant1 q qf =
  mk_term (Tquant (q, qf)) None

(** val t_binary1 :
    binop -> (term_node term_o) -> (term_node term_o) -> (term_node term_o) **)

let t_binary1 op f g =
  mk_term (Tbinop (op, f, g)) None

(** val t_not1 : (term_node term_o) -> (term_node term_o) **)

let t_not1 f =
  mk_term (Tnot f) None

(** val t_true : (term_node term_o) **)

let t_true =
  mk_term Ttrue None

(** val t_false : (term_node term_o) **)

let t_false =
  mk_term Tfalse None

(** val t_attr_set1 :
    position option -> Sattr.t -> (term_node term_o) -> (term_node term_o) **)

let t_attr_set1 loc l t0 =
  (fun (a, b, c, d) -> build_term_o a b c d) ((t_node t0), (t_ty t0), l, loc)

(** val t_attr_add : attribute -> (term_node term_o) -> (term_node term_o) **)

let t_attr_add l t0 =
  (fun (a, b, c, d) -> build_term_o a b c d) ((t_node t0), (t_ty t0),
    (Sattr.add l (t_attrs t0)), (t_loc t0))

(** val t_attr_remove :
    attribute -> (term_node term_o) -> (term_node term_o) **)

let t_attr_remove l t0 =
  (fun (a, b, c, d) -> build_term_o a b c d) ((t_node t0), (t_ty t0),
    (Sattr.remove l (t_attrs t0)), (t_loc t0))

(** val t_attr_remove_name :
    string -> (term_node term_o) -> (term_node term_o) **)

let t_attr_remove_name s t0 =
  (fun (a, b, c, d) -> build_term_o a b c d) ((t_node t0), (t_ty t0),
    (Sattr.filter (fun a -> negb ((=) a.attr_string s)) (t_attrs t0)),
    (t_loc t0))

(** val t_attr_copy :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) **)

let t_attr_copy s t0 =
  if (&&) ((&&) (t_similar s t0) (Sattr.is_empty (t_attrs t0)))
       (negb (isSome (t_loc t0)))
  then s
  else let attrs = Sattr.union (t_attrs s) (t_attrs t0) in
       let loc = if isNone (t_loc t0) then t_loc s else t_loc t0 in
       (fun (a, b, c, d) -> build_term_o a b c d) ((t_node t0), (t_ty t0),
       attrs, loc)

(** val bound_map : ('a1 -> 'a2) -> (('a3*'a4)*'a1) -> ('a3*'a4)*'a2 **)

let bound_map f = function
| p,e -> p,(f e)

(** val t_map_unsafe :
    ((term_node term_o) -> (term_node term_o)) -> (term_node term_o) ->
    (term_node term_o) **)

let t_map_unsafe fn t0 =
  t_attr_copy t0
    (match t_node t0 with
     | Tapp (f, tl) -> t_app1 f (map fn tl) (t_ty t0)
     | Tif (f, t1, t2) -> t_if1 (fn f) (fn t1) (fn t2)
     | Tlet (e, b) -> t_let1 (fn e) (bound_map fn b) (t_ty t0)
     | Tcase (e, bl) -> t_case1 (fn e) (map (bound_map fn) bl) (t_ty t0)
     | Teps b -> t_eps1 (bound_map fn b) (t_ty t0)
     | Tquant (q, p) ->
       let p0,f = p in
       let p1,tl = p0 in t_quant1 q ((p1,(tr_map fn tl)),(fn f))
     | Tbinop (op, f1, f2) -> t_binary1 op (fn f1) (fn f2)
     | Tnot f1 -> t_not1 (fn f1)
     | _ -> t0)

(** val bound_map_errst :
    ('a2 -> ('a1, 'a3) errState) -> (('a4*'a5)*'a2) -> ('a1, ('a4*'a5)*'a3)
    errState **)

let bound_map_errst f = function
| p,e -> (@@) (fun e1 -> (fun x -> x) (p,e1)) (f e)

(** val errst_tr :
    ('a1, 'a2) errState list list -> ('a1, 'a2 list list) errState **)

let errst_tr l =
  errst_list (map errst_list l)

(** val tr_map_errst :
    ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
    (term_node term_o) list list -> ('a1, (term_node term_o) list list)
    errState **)

let tr_map_errst fn tl =
  errst_tr (tr_map fn tl)

(** val t_map_errst_unsafe :
    ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
    (term_node term_o) -> ('a1, (term_node term_o)) errState **)

let t_map_errst_unsafe fn t0 =
  (@@) (fun t1 -> (fun x -> x) (t_attr_copy t0 t1))
    (match t_node t0 with
     | Tapp (f, tl) ->
       (@@) (fun l -> (fun x -> x) (t_app1 f l (t_ty t0)))
         (errst_list (map fn tl))
     | Tif (f, t1, t2) ->
       (@@) (fun f1 ->
         (@@) (fun t1' ->
           (@@) (fun t2' -> (fun x -> x) (t_if1 f1 t1' t2')) (fn t2)) 
           (fn t1)) (fn f)
     | Tlet (e, b) ->
       (@@) (fun e1 ->
         (@@) (fun b1 -> (fun x -> x) (t_let1 e1 b1 (t_ty t0)))
           (bound_map_errst fn b)) (fn e)
     | Tcase (e, bl) ->
       (@@) (fun e1 ->
         (@@) (fun l -> (fun x -> x) (t_case1 e1 l (t_ty t0)))
           (errst_list (map (bound_map_errst fn) bl))) (fn e)
     | Teps b ->
       (@@) (fun b1 -> (fun x -> x) (t_eps1 b1 (t_ty t0)))
         (bound_map_errst fn b)
     | Tquant (q, p) ->
       let p0,f = p in
       let p1,tl = p0 in
       (@@) (fun l ->
         (@@) (fun f1 -> (fun x -> x) (t_quant1 q ((p1,l),f1))) (fn f))
         (tr_map_errst fn tl)
     | Tbinop (op, f1, f2) ->
       (@@) (fun f1' ->
         (@@) (fun f2' -> (fun x -> x) (t_binary1 op f1' f2')) (fn f2))
         (fn f1)
     | Tnot f1 -> (@@) (fun f1' -> (fun x -> x) (t_not1 f1')) (fn f1)
     | _ -> (fun x -> x) t0)

(** val bound_map_ctr :
    ('a1 -> (BigInt.t, 'a2) st) -> (('a3*'a4)*'a1) -> (BigInt.t,
    ('a3*'a4)*'a2) st **)

let bound_map_ctr f = function
| p,e -> (@@) (fun e1 -> (fun x -> x) (p,e1)) (f e)

(** val st_tr :
    (BigInt.t, 'a1) st list list -> (BigInt.t, 'a1 list list) st **)

let st_tr l =
  st_list (map st_list l)

(** val t_map_ctr_unsafe :
    ((term_node term_o) -> (BigInt.t, (term_node term_o)) st) ->
    (term_node term_o) -> (BigInt.t, (term_node term_o)) st **)

let t_map_ctr_unsafe fn t0 =
  (@@) (fun t1 -> (fun x -> x) (t_attr_copy t0 t1))
    (match t_node t0 with
     | Tapp (f, tl) ->
       (@@) (fun l -> (fun x -> x) (t_app1 f l (t_ty t0)))
         (st_list (map fn tl))
     | Tif (f, t1, t2) ->
       (@@) (fun f1 ->
         (@@) (fun t1' ->
           (@@) (fun t2' -> (fun x -> x) (t_if1 f1 t1' t2')) (fn t2)) 
           (fn t1)) (fn f)
     | Tlet (e, b) ->
       (@@) (fun e1 ->
         (@@) (fun b1 -> (fun x -> x) (t_let1 e1 b1 (t_ty t0)))
           (bound_map_ctr fn b)) (fn e)
     | Tcase (e, bl) ->
       (@@) (fun e1 ->
         (@@) (fun l -> (fun x -> x) (t_case1 e1 l (t_ty t0)))
           (st_list (map (bound_map_ctr fn) bl))) (fn e)
     | Teps b ->
       (@@) (fun b1 -> (fun x -> x) (t_eps1 b1 (t_ty t0)))
         (bound_map_ctr fn b)
     | Tquant (q, p) ->
       let p0,f = p in
       let p1,tl = p0 in
       (@@) (fun l ->
         (@@) (fun f1 -> (fun x -> x) (t_quant1 q ((p1,l),f1))) (fn f))
         (st_tr (tr_map fn tl))
     | Tbinop (op, f1, f2) ->
       (@@) (fun f1' ->
         (@@) (fun f2' -> (fun x -> x) (t_binary1 op f1' f2')) (fn f2))
         (fn f1)
     | Tnot f1 -> (@@) (fun f1' -> (fun x -> x) (t_not1 f1')) (fn f1)
     | _ -> (fun x -> x) t0)

(** val bound_fold : ('a1 -> 'a2 -> 'a3) -> 'a1 -> (('a4*'a5)*'a2) -> 'a3 **)

let bound_fold fn acc = function
| _,e -> fn acc e

(** val t_fold_unsafe :
    ('a1 -> (term_node term_o) -> 'a1) -> 'a1 -> (term_node term_o) -> 'a1 **)

let t_fold_unsafe fn acc t0 =
  match t_node t0 with
  | Tapp (_, tl) -> fold_left fn tl acc
  | Tif (f, t1, t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (e, b) -> fn (bound_fold fn acc b) e
  | Tcase (e, bl) -> fold_left (bound_fold fn) bl (fn acc e)
  | Teps b -> bound_fold fn acc b
  | Tquant (_, p) ->
    let p0,f1 = p in let _,tl = p0 in fn (tr_fold fn acc tl) f1
  | Tbinop (_, f1, f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | _ -> acc

(** val bound_map_fold :
    ('a1 -> 'a2 -> 'a3*'a4) -> 'a1 -> (('a5*'a6)*'a2) -> 'a3*(('a5*'a6)*'a4) **)

let bound_map_fold fn acc = function
| p,e -> let acc0,e0 = fn acc e in acc0,(p,e0)

(** val t_map_fold_unsafe :
    ('a1 -> (term_node term_o) -> 'a1*(term_node term_o)) -> 'a1 ->
    (term_node term_o) -> 'a1*(term_node term_o) **)

let t_map_fold_unsafe fn acc t0 =
  match t_node t0 with
  | Tapp (f, tl) ->
    let acc0,sl = map_fold_left fn acc tl in
    acc0,(t_attr_copy t0 (t_app1 f sl (t_ty t0)))
  | Tif (f, t1, t2) ->
    let acc0,g = fn acc f in
    let acc1,s1 = fn acc0 t1 in
    let acc2,s2 = fn acc1 t2 in acc2,(t_attr_copy t0 (t_if1 g s1 s2))
  | Tlet (e, b) ->
    let acc0,e0 = fn acc e in
    let acc1,b0 = bound_map_fold fn acc0 b in
    acc1,(t_attr_copy t0 (t_let1 e0 b0 (t_ty t0)))
  | Tcase (e, bl) ->
    let acc0,e0 = fn acc e in
    let acc1,bl0 = map_fold_left (bound_map_fold fn) acc0 bl in
    acc1,(t_attr_copy t0 (t_case1 e0 bl0 (t_ty t0)))
  | Teps b ->
    let acc0,b0 = bound_map_fold fn acc b in
    acc0,(t_attr_copy t0 (t_eps1 b0 (t_ty t0)))
  | Tquant (q, p) ->
    let p0,f1 = p in
    let p1,tl = p0 in
    let acc0,tl0 = tr_map_fold fn acc tl in
    let acc1,f2 = fn acc0 f1 in
    acc1,(t_attr_copy t0 (t_quant1 q ((p1,tl0),f2)))
  | Tbinop (op, f1, f2) ->
    let acc0,g1 = fn acc f1 in
    let acc1,g2 = fn acc0 f2 in acc1,(t_attr_copy t0 (t_binary1 op g1 g2))
  | Tnot f1 -> let acc0,g1 = fn acc f1 in acc0,(t_attr_copy t0 (t_not1 g1))
  | _ -> acc,t0

(** val fresh_vsymbol : vsymbol -> (BigInt.t, vsymbol) st **)

let fresh_vsymbol v =
  create_vsymbol (id_clone1 None Sattr.empty v.vs_name) v.vs_ty

(** val vs_rename :
    (term_node term_o) Mvs.t -> vsymbol -> (BigInt.t, (term_node term_o)
    Mvs.t*vsymbol) st **)

let vs_rename h v =
  (@@) (fun u -> (fun x -> x) ((Mvs.add v (t_var u) h),u)) (fresh_vsymbol v)

(** val bnd_new : BigInt.t Mvs.t -> bind_info **)

let bnd_new s =
  { bv_vars = s }

(** val t_close_bound :
    vsymbol -> (term_node term_o) -> (vsymbol*bind_info)*(term_node term_o) **)

let t_close_bound v t0 =
  (v,(bnd_new (Mvs.remove v (t_vars t0)))),t0

(** val add_vars : vsymbol list -> (BigInt.t, vsymbol Mvs.t) st **)

let rec add_vars = function
| [] -> (fun x -> x) Mvs.empty
| v::vs ->
  (@@) (fun v1 ->
    (@@) (fun m -> (fun x -> x) (Mvs.add v v1 m)) (add_vars vs))
    (fresh_vsymbol v)

(** val pat_rename :
    (term_node term_o) Mvs.t -> (pattern_node pattern_o) -> (BigInt.t,
    (term_node term_o) Mvs.t*(pattern_node pattern_o)) st **)

let pat_rename h p =
  (@@) (fun m ->
    let p0 = pat_rename_all m p in
    (fun x -> x) ((Mvs.union (fun _ _ t0 -> Some t0) h (Mvs.map t_var m)),p0))
    (add_vars (Svs.elements (pat_vars p)))

(** val t_close_branch :
    (pattern_node pattern_o) -> (term_node term_o) ->
    ((pattern_node pattern_o)*bind_info)*(term_node term_o) **)

let t_close_branch p t0 =
  (p,(bnd_new (Mvs.set_diff (t_vars t0) (pat_vars p)))),t0

(** val t_close_quant_unsafe :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    ((vsymbol list*bind_info)*(term_node term_o) list list)*(term_node term_o) **)

let t_close_quant_unsafe vl tl f =
  let del_v = fun s v -> Mvs.remove v s in
  let s = tr_fold add_t_vars (t_vars f) tl in
  let s0 = fold_left del_v vl s in ((vl,(bnd_new s0)),tl),f

(** val t_close_quant :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    (((vsymbol list*bind_info)*(term_node term_o) list
    list)*(term_node term_o)) errorM **)

let t_close_quant vl tl f =
  let p,f0 = t_close_quant_unsafe vl tl f in
  (@@) (fun p0 ->  (p,p0)) (t_prop f0)

(** val vl_rename_aux :
    vsymbol list -> (BigInt.t, (term_node term_o) Mvs.t*vsymbol list) st ->
    (BigInt.t, (term_node term_o) Mvs.t*vsymbol list) st **)

let rec vl_rename_aux vl acc =
  match vl with
  | [] -> acc
  | v::vs ->
    (@@) (fun x ->
      let m,vls = x in
      (@@) (fun x1 ->
        let m1,v1 = x1 in vl_rename_aux vs ((fun x -> x) (m1,(v1::vls))))
        (vs_rename m v)) acc

(** val vl_rename :
    (term_node term_o) Mvs.t -> vsymbol list -> (BigInt.t, (term_node term_o)
    Mvs.t*vsymbol list) st **)

let vl_rename h vl =
  (@@) (fun x -> (fun x -> x) ((fst x),(rev' (snd x))))
    (vl_rename_aux vl ((fun x -> x) (h,[])))

(** val t_subst_unsafe_aux :
    (term_node term_o) Mvs.t -> (term_node term_o) -> (term_node term_o) **)

let rec t_subst_unsafe_aux m t0 =
  match t_node t0 with
  | Tvar u -> t_attr_copy t0 (Mvs.find_def t0 u m)
  | Tlet (e, p) ->
    let p0,t2 = p in
    let v,b = p0 in
    let e1 = t_subst_unsafe_aux m e in
    let m' = Mvs.remove v m in
    let m1 = Mvs.set_inter m' b.bv_vars in
    let e2 = if Mvs.is_empty m1 then t2 else t_subst_unsafe_aux m1 t2 in
    let b1 = bnd_new (Mvs.remove v (t_vars e2)) in
    t_attr_copy t0 (t_let1 e1 ((v,b1),e2) (t_ty t0))
  | Tcase (e, bl) ->
    let e1 = t_subst_unsafe_aux m e in
    let bl2 =
      map (fun x ->
        let m' = Mvs.set_diff m (pat_vars (fst (fst x))) in
        let m1 = Mvs.set_inter m' (snd (fst x)).bv_vars in
        let e2 =
          if Mvs.is_empty m1 then snd x else t_subst_unsafe_aux m1 (snd x)
        in
        let b1 = bnd_new (Mvs.set_diff (t_vars e2) (pat_vars (fst (fst x))))
        in
        ((fst (fst x)),b1),e2) bl
    in
    t_attr_copy t0 (t_case1 e1 bl2 (t_ty t0))
  | Teps p ->
    let p0,t1 = p in
    let v,b = p0 in
    let m' = Mvs.remove v m in
    let m1 = Mvs.set_inter m' b.bv_vars in
    let e2 = if Mvs.is_empty m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 = bnd_new (Mvs.remove v (t_vars e2)) in
    t_attr_copy t0 (t_eps1 ((v,b1),e2) (t_ty t0))
  | Tquant (q, p) ->
    let p0,t1 = p in
    let p1,tr = p0 in
    let vs,b = p1 in
    let m' = Mvs.set_diff m (Svs.of_list vs) in
    let m1 = Mvs.set_inter m' b.bv_vars in
    let e2 = if Mvs.is_empty m1 then t1 else t_subst_unsafe_aux m1 t1 in
    let b1 = bnd_new (Mvs.set_diff (t_vars e2) (Svs.of_list vs)) in
    let tr2 = tr_map (t_subst_unsafe_aux m) tr in
    t_attr_copy t0 (t_quant1 q (((vs,b1),tr2),e2))
  | _ -> t_map_unsafe (t_subst_unsafe_aux m) t0

(** val t_subst_unsafe :
    (term_node term_o) Mvs.t -> (term_node term_o) -> (term_node term_o) **)

let t_subst_unsafe m t0 =
  if Mvs.is_empty m then t0 else t_subst_unsafe_aux m t0

(** val t_view_bound : term_bound -> vsymbol*(term_node term_o) **)

let t_view_bound x =
  (fst (fst x)),(snd x)

(** val t_open_bound :
    term_bound -> (BigInt.t, vsymbol*(term_node term_o)) st **)

let t_open_bound = function
| p,t0 ->
  let v,_ = p in
  (@@) (fun y -> let m,v0 = y in (fun x -> x) (v0,(t_subst_unsafe m t0)))
    (vs_rename Mvs.empty v)

(** val t_view_branch :
    term_branch -> (pattern_node pattern_o)*(term_node term_o) **)

let t_view_branch x =
  (fst (fst x)),(snd x)

(** val t_open_branch :
    term_branch -> (BigInt.t, (pattern_node pattern_o)*(term_node term_o)) st **)

let t_open_branch = function
| p0,t0 ->
  let p,_ = p0 in
  (@@) (fun y -> let m,p1 = y in (fun x -> x) (p1,(t_subst_unsafe m t0)))
    (pat_rename Mvs.empty p)

(** val t_open_quant1 :
    term_quant -> (BigInt.t, (vsymbol list*trigger)*(term_node term_o)) st **)

let t_open_quant1 = function
| p,f ->
  let p0,tl = p in
  let vl,_ = p0 in
  (@@) (fun y ->
    let m,vl0 = y in
    (fun x -> x) ((vl0,(tr_map (t_subst_unsafe m) tl)),(t_subst_unsafe m f)))
    (vl_rename Mvs.empty vl)

(** val t_view_quant :
    term_quant -> (vsymbol list*trigger)*(term_node term_o) **)

let t_view_quant x =
  ((fst (fst (fst x))),(snd (fst x))),(snd x)

(** val t_open_bound_with :
    (term_node term_o) -> term_bound -> (term_node term_o) errorM **)

let t_open_bound_with e = function
| p,t0 ->
  let v,_ = p in
  (@@) (fun _ -> let m = Mvs.singleton v e in  (t_subst_unsafe m t0))
    (vs_check v e)

(** val t_view_quant_cb :
    term_quant -> ((vsymbol list*trigger)*(term_node term_o))*(vsymbol list
    -> trigger -> (term_node term_o) -> term_quant errorM) **)

let t_view_quant_cb fq =
  let p,f = t_view_quant fq in
  let vl,tl = p in
  let close = fun vl' tl' f' ->
    if (&&)
         ((&&) ((fun x y -> x == y || term_eqb x y) f f')
           (list_eqb (list_eqb (fun x y -> x == y || term_eqb x y)) tl tl'))
         (list_eqb vs_equal vl vl')
    then  fq
    else t_close_quant vl' tl' f'
  in
  ((vl,tl),f),close

(** val t_open_bound_cb1 :
    term_bound -> (BigInt.t, (vsymbol*(term_node term_o))*(vsymbol ->
    (term_node term_o) -> (vsymbol*bind_info)*(term_node term_o))) st **)

let t_open_bound_cb1 tb =
  (@@) (fun x ->
    let v,t0 = x in
    let close = fun v' t' ->
      if (&&) ((fun x y -> x == y || term_eqb x y) t0 t') (vs_equal v v')
      then tb
      else t_close_bound v' t'
    in
    (fun x -> x) ((v,t0),close)) (t_open_bound tb)

(** val t_open_branch_cb1 :
    term_branch -> (BigInt.t,
    ((pattern_node pattern_o)*(term_node term_o))*((pattern_node pattern_o)
    -> (term_node term_o) -> term_branch)) st **)

let t_open_branch_cb1 tbr =
  (@@) (fun x ->
    let p,t0 = x in
    let close = fun p' t' ->
      if (&&) ((fun x y -> x == y || term_eqb x y) t0 t')
           ((fun x y -> x == y || pattern_eqb x y) p p')
      then tbr
      else t_close_branch p' t'
    in
    (fun x -> x) ((p,t0),close)) (t_open_branch tbr)

(** val t_open_quant_cb1 :
    term_quant -> (BigInt.t, ((vsymbol
    list*trigger)*(term_node term_o))*(vsymbol list -> trigger ->
    (term_node term_o) -> (((vsymbol
    list*bind_info)*trigger)*(term_node term_o)) errorM)) st **)

let t_open_quant_cb1 fq =
  (@@) (fun x ->
    let y,f = x in
    let vl,tl = y in
    let close = fun vl' tl' f' ->
      if (&&)
           ((&&) ((fun x y -> x == y || term_eqb x y) f f')
             (list_eqb (list_eqb (fun x y -> x == y || term_eqb x y)) tl tl'))
           (list_eqb vs_equal vl vl')
      then  fq
      else t_close_quant vl' tl' f'
    in
    (fun x -> x) (((vl,tl),f),close)) (t_open_quant1 fq)

(** val t_peek_bound : term_bound -> ident **)

let t_peek_bound = function
| p,_ -> let v,_ = p in v.vs_name

(** val t_peek_branch : term_branch -> Sid.t **)

let t_peek_branch = function
| p0,_ ->
  let p,_ = p0 in
  Svs.fold (fun v a -> Sid.add v.vs_name a) (pat_vars p) Sid.empty

(** val t_peek_quant : term_quant -> ident list **)

let t_peek_quant = function
| p,_ -> let p0,_ = p in let vl,_ = p0 in map (fun v -> v.vs_name) vl

(** val ls_arg_inst :
    lsymbol -> (term_node term_o) list -> (ty_node_c ty_o hashcons_ty,
    ty_node_c ty_o Mtv.t) errState **)

let ls_arg_inst ls tl =
  let mtch = fun s typ t0 -> (@@) (fun t1 -> ty_match s typ t1) ( (t_type t0))
  in
  (@@) (fun o ->
    match o with
    | Some l -> (fun x -> x) l
    | None ->  (raise (BadArity (ls,(int_length tl)))))
    (fold_left2_errst mtch Mtv.empty ls.ls_args tl)

(** val ls_app_inst :
    lsymbol -> (term_node term_o) list -> ty_node_c ty_o option ->
    (ty_node_c ty_o hashcons_ty, ty_node_c ty_o Mtv.t) errState **)

let ls_app_inst ls tl typ =
  (@@) (fun s ->
    match ls.ls_value with
    | Some vty ->
      (match typ with
       | Some typ0 -> ty_match s vty typ0
       | None ->  (raise (PredicateSymbolExpected ls)))
    | None ->
      (match typ with
       | Some _ ->  (raise (FunctionSymbolExpected ls))
       | None -> (fun x -> x) s)) (ls_arg_inst ls tl)

(** val t_app_infer :
    lsymbol -> (term_node term_o) list -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_app_infer ls tl =
  (@@) (fun s ->
    let o = oty_inst s ls.ls_value in
    (match o with
     | Some h -> (@@) (fun h1 -> (fun x -> x) (t_app1 ls tl (Some h1))) ( h)
     | None -> (fun x -> x) (t_app1 ls tl None))) (ls_arg_inst ls tl)

(** val t_app :
    lsymbol -> (term_node term_o) list -> ty_node_c ty_o option ->
    (ty_node_c ty_o hashcons_ty, (term_node term_o)) errState **)

let t_app ls tl typ =
  (@@) (fun _ -> (fun x -> x) (t_app1 ls tl typ)) (ls_app_inst ls tl typ)

(** val fs_app :
    lsymbol -> (term_node term_o) list -> ty_node_c ty_o -> (ty_node_c ty_o
    hashcons_ty, (term_node term_o)) errState **)

let fs_app fs tl ty =
  t_app fs tl (Some ty)

(** val ps_app :
    lsymbol -> (term_node term_o) list -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let ps_app ps tl =
  t_app ps tl None

(** val coq_assert : bool -> string -> unit errorM **)

let coq_assert b msg =
  if b then  () else raise (AssertFail msg)

(** val assert_false : string -> 'a1 errorM **)

let assert_false msg =
  raise (AssertFail msg)

(** val t_nat_const : Stdlib.Int.t -> (term_node term_o) errorM **)

let t_nat_const n =
  (@@) (fun _ ->  (t_const1 (int_const_of_int n) ty_int))
    (coq_assert ((fun x y -> Stdlib.Int.compare x y >= 0) n Stdlib.Int.zero)
      "t_nat_const negative")

(** val t_int_const : BigInt.t -> (term_node term_o) **)

let t_int_const n =
  t_const1 (int_const1 ILitUnk n) ty_int

(** val t_string_const : string -> (term_node term_o) **)

let t_string_const s =
  t_const1 (string_const s) ty_str

(** val check_literal : constant -> ty_node_c ty_o -> unit errorM **)

let check_literal c t0 =
  (@@) (fun ts ->
    match c with
    | ConstInt n ->
      (match ts_def ts with
       | NoDef ->
         if ts_equal ts ts_int
         then  ()
         else raise (InvalidIntegerLiteralType t0)
       | Range ir -> check_range n ir
       | _ -> raise (InvalidIntegerLiteralType t0))
    | ConstReal x ->
      (match ts_def ts with
       | NoDef ->
         if ts_equal ts ts_real
         then  ()
         else raise (InvalidRealLiteralType t0)
       | Float fp -> Number.check_float x fp
       | _ -> raise (InvalidRealLiteralType t0))
    | ConstStr _ ->
      if ts_equal ts ts_str then  () else raise (InvalidStringLiteralType t0))
    (match ty_node t0 with
     | Tyvar _ ->
       (match c with
        | ConstInt _ -> raise (InvalidIntegerLiteralType t0)
        | ConstReal _ -> raise (InvalidRealLiteralType t0)
        | ConstStr _ -> raise (InvalidStringLiteralType t0))
     | Tyapp (ts, l) ->
       (match l with
        | [] ->  ts
        | _::_ ->
          (match c with
           | ConstInt _ -> raise (InvalidIntegerLiteralType t0)
           | ConstReal _ -> raise (InvalidRealLiteralType t0)
           | ConstStr _ -> raise (InvalidStringLiteralType t0))))

(** val t_const : constant -> ty_node_c ty_o -> (term_node term_o) errorM **)

let t_const c t0 =
  (@@) (fun _ ->  (t_const1 c t0)) (check_literal c t0)

(** val t_if :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) errorM **)

let t_if f t1 t2 =
  (@@) (fun _ -> (@@) (fun p ->  (t_if1 p t1 t2)) (t_prop f))
    (t_ty_check t1 (t_ty t1))

(** val t_let :
    (term_node term_o) -> term_bound -> (term_node term_o) errorM **)

let t_let t1 bt = match bt with
| p,t2 ->
  let v,_ = p in (@@) (fun _ ->  (t_let1 t1 bt (t_ty t2))) (vs_check v t1)

(** val t_case :
    (term_node term_o) -> term_branch list -> (term_node term_o) errorM **)

let t_case t0 bl =
  (@@) (fun tty ->
    (@@) (fun bty ->
      let t_check_branch = fun tb ->
        let p0,tbr = tb in
        let p,_ = p0 in
        (@@) (fun _ -> t_ty_check tbr bty) (ty_equal_check tty (pat_ty p))
      in
      (@@) (fun _ ->  (t_case1 t0 bl bty))
        (errorM_list (map t_check_branch bl)))
      (match bl with
       | [] -> raise EmptyCase
       | t1::_ -> let _,tbr = t1 in  (t_ty tbr))) (t_type t0)

(** val t_eps : term_bound -> (term_node term_o) errorM **)

let t_eps bf = match bf with
| p,f -> let v,_ = p in (@@) (fun _ ->  (t_eps1 bf (Some v.vs_ty))) (t_prop f)

(** val t_quant : quant -> term_quant -> (term_node term_o) **)

let t_quant q qf = match qf with
| p,f -> let p0,_ = p in let vl,_ = p0 in if null vl then f else t_quant1 q qf

(** val t_binary :
    binop -> (term_node term_o) -> (term_node term_o) -> (term_node term_o)
    errorM **)

let t_binary op f1 f2 =
  (@@) (fun p1 -> (@@) (fun p2 ->  (t_binary1 op p1 p2)) (t_prop f2))
    (t_prop f1)

(** val t_not : (term_node term_o) -> (term_node term_o) errorM **)

let t_not f =
  (@@) (fun p ->  (t_not1 p)) (t_prop f)

(** val t_forall : term_quant -> (term_node term_o) **)

let t_forall =
  t_quant Tforall

(** val t_exists : term_quant -> (term_node term_o) **)

let t_exists =
  t_quant Texists

(** val t_and :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_and =
  t_binary Tand

(** val t_or :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_or =
  t_binary Tor

(** val t_implies :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_implies =
  t_binary Timplies

(** val t_iff :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_iff =
  t_binary Tiff

(** val t_and_l : (term_node term_o) list -> (term_node term_o) errorM **)

let rec t_and_l = function
| [] ->  t_true
| f::fl ->
  (match fl with
   | [] ->  f
   | _::_ -> (@@) (fun f1 -> t_and f f1) (t_and_l fl))

(** val t_or_l : (term_node term_o) list -> (term_node term_o) errorM **)

let rec t_or_l = function
| [] ->  t_false
| f::fl ->
  (match fl with
   | [] ->  f
   | _::_ -> (@@) (fun f1 -> t_or f f1) (t_or_l fl))

(** val t_quant_close :
    quant -> vsymbol list -> (term_node term_o) list list ->
    (term_node term_o) -> (term_node term_o) errorM **)

let t_quant_close q vl tl f =
  if null vl
  then t_prop f
  else (@@) (fun tq ->  (t_quant q tq)) (t_close_quant vl tl f)

(** val t_forall_close :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    (term_node term_o) errorM **)

let t_forall_close =
  t_quant_close Tforall

(** val t_exists_close :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    (term_node term_o) errorM **)

let t_exists_close =
  t_quant_close Texists

(** val t_let_close :
    vsymbol -> (term_node term_o) -> (term_node term_o) -> (term_node term_o)
    errorM **)

let t_let_close v t1 t2 =
  t_let t1 (t_close_bound v t2)

(** val t_case_close :
    (term_node term_o) -> ((pattern_node pattern_o)*(term_node term_o)) list
    -> (term_node term_o) errorM **)

let t_case_close t0 l =
  t_case t0 (map (fun x -> t_close_branch (fst x) (snd x)) l)

(** val t_eps_close :
    vsymbol -> (term_node term_o) -> (term_node term_o) errorM **)

let t_eps_close v f =
  t_eps (t_close_bound v f)

(** val ps_equ : lsymbol **)

let ps_equ =
  create_psymbol_builtin id_eq (ty_a::(ty_a::[]))

(** val t_equ :
    (term_node term_o) -> (term_node term_o) -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_equ t1 t2 =
  ps_app ps_equ (t1::(t2::[]))

(** val t_neq :
    (term_node term_o) -> (term_node term_o) -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_neq t1 t2 =
  (@@) (fun a ->  (t_not a)) (ps_app ps_equ (t1::(t2::[])))

(** val fs_bool_true : lsymbol **)

let fs_bool_true =
  create_fsymbol_builtin (BigInt.of_int 2) false id_true [] ty_bool

(** val fs_bool_false : lsymbol **)

let fs_bool_false =
  create_fsymbol_builtin (BigInt.of_int 2) false id_false [] ty_bool

(** val t_bool_true : (term_node term_o) **)

let t_bool_true =
  t_app1 fs_bool_true [] (Some ty_bool)

(** val t_bool_false : (term_node term_o) **)

let t_bool_false =
  t_app1 fs_bool_false [] (Some ty_bool)

(** val to_prop :
    (term_node term_o) -> (ty_node_c ty_o hashcons_ty, (term_node term_o))
    errState **)

let to_prop t0 =
  match t_ty t0 with
  | Some _ ->
    if t_equal t0 t_bool_true
    then (fun x -> x) t_true
    else if t_equal t0 t_bool_false
         then (fun x -> x) t_false
         else (@@) (fun t1 -> (fun x -> x) (t_attr_copy t0 t1))
                (t_equ t0 t_bool_true)
  | None -> (fun x -> x) t0

(** val fs_func_app : lsymbol **)

let fs_func_app =
  create_fsymbol_builtin BigInt.zero false id_app (ty_func_ab::(ty_a::[]))
    ty_b

(** val t_func_app :
    (term_node term_o) -> (term_node term_o) -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_func_app fn t0 =
  t_app_infer fs_func_app (fn::(t0::[]))

(** val t_pred_app :
    (term_node term_o) -> (term_node term_o) -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_pred_app pr t0 =
  (@@) (fun t1 -> t_equ t1 t_bool_true) (t_func_app pr t0)

(** val t_func_app_l :
    (term_node term_o) -> (term_node term_o) list -> (ty_node_c ty_o
    hashcons_ty, (term_node term_o)) errState **)

let t_func_app_l fn tl =
  foldl_errst t_func_app tl fn

(** val t_pred_app_l :
    (term_node term_o) -> (term_node term_o) list -> (ty_node_c ty_o
    hashcons_ty, (term_node term_o)) errState **)

let t_pred_app_l pr tl =
  (@@) (fun ta -> t_equ ta t_bool_true) (t_func_app_l pr tl)

(** val pat_gen_fold :
    ('a1 -> ty_node_c ty_o -> 'a1) -> ('a1 -> lsymbol -> 'a1) -> 'a1 ->
    (pattern_node pattern_o) -> 'a1 **)

let rec pat_gen_fold fnT fnL acc pat =
  let fn = fun acc0 p -> pat_gen_fold fnT fnL acc0 p in
  let acc0 = fnT acc (pat_ty pat) in
  (match pat_node pat with
   | Papp (s, pl) -> fold_left fn pl (fnL acc0 s)
   | Por (p, q) -> fn (fn acc0 p) q
   | Pas (p, _) -> fn acc0 p
   | _ -> acc0)

(** val t_gen_fold :
    ('a1 -> ty_node_c ty_o -> 'a1) -> ('a1 -> lsymbol -> 'a1) -> 'a1 ->
    (term_node term_o) -> 'a1 **)

let rec t_gen_fold fnT fnL acc t0 =
  let fn = t_gen_fold fnT fnL in
  let acc0 = opt_fold fnT acc (t_ty t0) in
  (match t_node t0 with
   | Tapp (f, tl) -> fold_left fn tl (fnL acc0 f)
   | Tif (f, t1, t2) -> fn (fn (fn acc0 f) t1) t2
   | Tlet (t1, p) -> let _,t2 = p in fn (fn acc0 t1) t2
   | Tcase (t1, bl) ->
     let branch = fun acc1 x ->
       fn (pat_gen_fold fnT fnL acc1 (fst (fst x))) (snd x)
     in
     fold_left branch bl (fn acc0 t1)
   | Teps p -> let _,f = p in fn acc0 f
   | Tquant (_, p) ->
     let p0,f1 = p in
     let p1,tl = p0 in
     let vl,_ = p1 in
     let acc1 = fold_left (fun a v -> fnT a v.vs_ty) vl acc0 in
     fn (tr_fold fn acc1 tl) f1
   | Tbinop (_, f1, f2) -> fn (fn acc0 f1) f2
   | Tnot f1 -> fn acc0 f1
   | _ -> acc0)

(** val t_s_fold :
    ('a1 -> ty_node_c ty_o -> 'a1) -> ('a1 -> lsymbol -> 'a1) -> 'a1 ->
    (term_node term_o) -> 'a1 **)

let t_s_fold =
  t_gen_fold

(** val t_ty_fold :
    ('a1 -> ty_node_c ty_o -> 'a1) -> 'a1 -> (term_node term_o) -> 'a1 **)

let t_ty_fold fn acc t0 =
  t_s_fold fn (fun x _ -> x) acc t0

(** val t_ty_freevars : Stv.t -> (term_node term_o) -> Stv.t **)

let t_ty_freevars =
  t_ty_fold ty_freevars

(** val t_map_sign_errst_unsafe :
    (bool -> (term_node term_o) -> ('a1, (term_node term_o)) errState) ->
    bool -> (term_node term_o) -> ('a1, (term_node term_o)) errState **)

let t_map_sign_errst_unsafe fn sign f =
  match t_node f with
  | Tif (f1, f2, f3) ->
    if negb (isSome (t_ty f))
    then (@@) (fun f1p ->
           (@@) (fun f1n ->
             (@@) (fun f4 ->
               (@@) (fun f5 ->
                 if t_equal f1p f1n
                 then (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
                        ( (t_if f1p f4 f5))
                 else if sign
                      then (@@) (fun t1 ->
                             (@@) (fun t2 ->
                               (@@) (fun t3 ->
                                 (@@) (fun t4 ->
                                   (fun x -> x) (t_attr_copy f t4))
                                   ( (t_and t1 t3))) ( (t_implies t2 f5)))
                               ( (t_not f1p))) ( (t_implies f1n f4))
                      else (@@) (fun t1 ->
                             (@@) (fun t2 ->
                               (@@) (fun t3 ->
                                 (@@) (fun t4 ->
                                   (fun x -> x) (t_attr_copy f t4))
                                   ( (t_or t1 t3))) ( (t_and t2 f5)))
                               ( (t_not f1n))) ( (t_and f1p f4))) (fn sign f3))
               (fn sign f2)) (fn (negb sign) f1)) (fn sign f1)
    else  (raise (Failure "t_map_sign: cannot determine polarity"))
  | Teps _ ->  (raise (Failure "t_map_sign: cannot determine polarity"))
  | Tbinop (b, f1, f2) ->
    (match b with
     | Timplies ->
       (@@) (fun f1' ->
         (@@) (fun f2' ->
           (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
             ( (t_implies f1' f2'))) (fn sign f2)) (fn (negb sign) f1)
     | Tiff ->
       (@@) (fun f1p ->
         (@@) (fun f1n ->
           (@@) (fun f2p ->
             (@@) (fun f2n ->
               if (&&) (t_equal f1p f1n) (t_equal f2p f2n)
               then (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
                      ( (t_iff f1p f2p))
               else if sign
                    then (@@) (fun t1 ->
                           (@@) (fun t2 ->
                             (@@) (fun t3 -> (fun x -> x) (t_attr_copy f t3))
                               ( (t_and t1 t2))) ( (t_implies f2n f1p)))
                           ( (t_implies f1n f2p))
                    else (@@) (fun t1 ->
                           (@@) (fun t2 ->
                             (@@) (fun t3 -> (fun x -> x) (t_attr_copy f t3))
                               ( (t_implies t1 t2))) ( (t_and f1p f2p)))
                           ( (t_or f1n f2n))) (fn (negb sign) f2))
             (fn sign f2)) (fn (negb sign) f1)) (fn sign f1)
     | _ ->
       (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
         (t_map_errst_unsafe (fn sign) f))
  | Tnot f1 ->
    (@@) (fun f1' ->
      (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1)) ( (t_not f1')))
      (fn (negb sign) f1)
  | _ ->
    (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
      (t_map_errst_unsafe (fn sign) f)

(** val bnd_v_fold : ('a1 -> vsymbol -> 'a1) -> 'a1 -> bind_info -> 'a1 **)

let bnd_v_fold fn acc b =
  Mvs.fold (fun v _ acc0 -> fn acc0 v) b.bv_vars acc

(** val bound_v_fold :
    ('a1 -> vsymbol -> 'a1) -> 'a1 -> (('a2*bind_info)*'a3) -> 'a1 **)

let bound_v_fold fn acc = function
| p,_ -> let _,b = p in bnd_v_fold fn acc b

(** val t_v_fold :
    ('a1 -> vsymbol -> 'a1) -> 'a1 -> (term_node term_o) -> 'a1 **)

let rec t_v_fold fn acc t0 =
  match t_node t0 with
  | Tvar v -> fn acc v
  | Tlet (e, b) -> bound_v_fold fn (t_v_fold fn acc e) b
  | Tcase (e, bl) -> fold_left (bound_v_fold fn) bl (t_v_fold fn acc e)
  | Teps b -> bound_v_fold fn acc b
  | Tquant (_, p) ->
    let p0,_ = p in let p1,_ = p0 in let _,b = p1 in bnd_v_fold fn acc b
  | _ -> t_fold_unsafe (t_v_fold fn) acc t0

(** val t_v_all : (vsymbol -> bool) -> (term_node term_o) -> bool **)

let t_v_all pr t0 =
  t_v_fold (fun x v -> (&&) x (pr v)) true t0

(** val bnd_v_count :
    ('a1 -> vsymbol -> BigInt.t -> 'a1) -> 'a1 -> bind_info -> 'a1 **)

let bnd_v_count fn acc b =
  Mvs.fold (fun v n acc0 -> fn acc0 v n) b.bv_vars acc

(** val t_v_count :
    ('a1 -> vsymbol -> BigInt.t -> 'a1) -> 'a1 -> (term_node term_o) -> 'a1 **)

let rec t_v_count fn acc t0 =
  match t_node t0 with
  | Tvar v -> fn acc v BigInt.one
  | Tlet (e, p) ->
    let p0,_ = p in let _,b = p0 in bnd_v_count fn (t_v_count fn acc e) b
  | Tcase (e, bl) ->
    fold_left (bnd_v_count fn) (map (fun x -> snd (fst x)) bl)
      (t_v_count fn acc e)
  | Teps p -> let p0,_ = p in let _,b = p0 in bnd_v_count fn acc b
  | Tquant (_, p) ->
    let p0,_ = p in let p1,_ = p0 in let _,b = p1 in bnd_v_count fn acc b
  | _ -> t_fold_unsafe (t_v_count fn) acc t0

(** val t_v_occurs : vsymbol -> (term_node term_o) -> BigInt.t **)

let t_v_occurs v t0 =
  t_v_count (fun c u n -> if vs_equal u v then BigInt.add c n else c)
    BigInt.zero t0

(** val t_subst :
    (term_node term_o) Mvs.t -> (term_node term_o) -> (term_node term_o)
    errorM **)

let t_subst m t0 =
  (@@) (fun _ ->  (t_subst_unsafe m t0))
    (iter_err (fun x -> vs_check (fst x) (snd x)) (Mvs.bindings m))

(** val t_subst_single :
    Mvs.key -> (term_node term_o) -> (term_node term_o) -> (term_node term_o)
    errorM **)

let t_subst_single v t1 t0 =
  t_subst (Mvs.singleton v t1) t0

module TermTFAlt =
 struct
  (** val t_select :
      ((term_node term_o) -> 'a1) -> ((term_node term_o) -> 'a1) ->
      (term_node term_o) -> 'a1 **)

  let t_select fnT fnF e =
    if isNone (t_ty e) then fnF e else fnT e

  (** val t_selecti :
      ('a1 -> (term_node term_o) -> 'a2) -> ('a1 -> (term_node term_o) ->
      'a2) -> 'a1 -> (term_node term_o) -> 'a2 **)

  let t_selecti fnT fnF acc e =
    if isNone (t_ty e) then fnF acc e else fnT acc e

  (** val t_map_errst_unsafe :
      ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      (term_node term_o) -> ('a1, (term_node term_o)) errState **)

  let t_map_errst_unsafe fnT fnF =
    t_map_errst_unsafe (t_select fnT fnF)

  (** val t_map_sign_errst_unsafe :
      (bool -> (term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      (bool -> (term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      bool -> (term_node term_o) -> ('a1, (term_node term_o)) errState **)

  let t_map_sign_errst_unsafe fnT fnF =
    t_map_sign_errst_unsafe (t_selecti fnT fnF)

  (** val tr_map_errst :
      ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      ((term_node term_o) -> ('a1, (term_node term_o)) errState) ->
      (term_node term_o) list list -> ('a1, (term_node term_o) list list)
      errState **)

  let tr_map_errst fnT fnF =
    tr_map_errst (t_select fnT fnF)
 end

(** val term_rec :
    (vsymbol -> 'a1) -> (constant -> 'a1) -> (lsymbol -> (term_node term_o)
    list -> 'a1 list -> 'a1) -> ((term_node term_o) -> 'a1 ->
    (term_node term_o) -> 'a1 -> (term_node term_o) -> 'a1 -> 'a1) ->
    ((term_node term_o) -> 'a1 -> vsymbol -> (term_node term_o) -> 'a1 ->
    'a1) -> ((term_node term_o) -> 'a1 ->
    (((pattern_node pattern_o)*(term_node term_o))*'a1) list -> 'a1) ->
    (vsymbol -> (term_node term_o) -> 'a1 -> 'a1) -> (quant -> vsymbol list
    -> (term_node term_o) -> 'a1 -> 'a1) -> (binop -> (term_node term_o) ->
    'a1 -> (term_node term_o) -> 'a1 -> 'a1) -> ((term_node term_o) -> 'a1 ->
    'a1) -> 'a1 -> 'a1 -> (term_node term_o) -> 'a1 **)

let rec term_rec var_case const_case app_case if_case let_case match_case eps_case quant_case binop_case not_case true_case false_case t0 =
  match t_node t0 with
  | Tvar v -> var_case v
  | Tconst c -> const_case c
  | Tapp (l, ts) ->
    app_case l ts
      (map
        (term_rec var_case const_case app_case if_case let_case match_case
          eps_case quant_case binop_case not_case true_case false_case) ts)
  | Tif (t1, t2, t3) ->
    if_case t1
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1) t2
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t2) t3
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t3)
  | Tlet (t1, p) ->
    let p0,t2 = p in
    let v,_ = p0 in
    let_case t1
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1) v t2
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t2)
  | Tcase (t1, ps) ->
    match_case t1
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
      (map (fun x ->
        ((fst (fst x)),(snd x)),(term_rec var_case const_case app_case
                                  if_case let_case match_case eps_case
                                  quant_case binop_case not_case true_case
                                  false_case (snd x))) ps)
  | Teps p ->
    let p0,f = p in
    let v,_ = p0 in
    eps_case v f
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case f)
  | Tquant (q, p) ->
    let p0,f = p in
    let p1,_ = p0 in
    let vs,_ = p1 in
    quant_case q vs f
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case f)
  | Tbinop (b, t1, t2) ->
    binop_case b t1
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1) t2
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case t2)
  | Tnot f ->
    not_case f
      (term_rec var_case const_case app_case if_case let_case match_case
        eps_case quant_case binop_case not_case true_case false_case f)
  | Ttrue -> true_case
  | Tfalse -> false_case

(** val t_not_simp : (term_node term_o) -> (term_node term_o) errorM **)

let t_not_simp f =
  match t_node f with
  | Tnot g ->  (t_attr_copy f g)
  | Ttrue ->  (t_attr_copy f t_false)
  | Tfalse ->  (t_attr_copy f t_true)
  | _ -> t_not f

(** val t_and_simp :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_and_simp f1 f2 =
  match t_node f1 with
  | Ttrue ->  f2
  | Tfalse ->  (t_attr_remove_name "asym_split" f1)
  | _ ->
    (match t_node f2 with
     | Ttrue ->  (t_attr_remove_name "asym_split" f1)
     | Tfalse ->  f2
     | _ -> if t_equal f1 f2 then  f1 else t_and f1 f2)

(** val t_or_simp :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_or_simp f1 f2 =
  match t_node f1 with
  | Ttrue ->  (t_attr_remove_name "asym_split" f1)
  | Tfalse ->  f2
  | _ ->
    (match t_node f2 with
     | Ttrue ->  f2
     | Tfalse ->  (t_attr_remove_name "asym_split" f1)
     | _ -> if t_equal f1 f2 then  f1 else t_or f1 f2)

(** val t_implies_simp :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_implies_simp f1 f2 =
  match t_node f1 with
  | Ttrue ->  f2
  | Tfalse ->
    (match t_node f2 with
     | Ttrue ->  f2
     | _ ->  (t_attr_copy f1 t_true))
  | _ ->
    (match t_node f2 with
     | Ttrue ->  f2
     | Tfalse -> t_not_simp f1
     | _ ->
       if t_equal f1 f2 then  (t_attr_copy f1 t_true) else t_implies f1 f2)

(** val t_iff_simp :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) errorM **)

let t_iff_simp f1 f2 =
  match t_node f1 with
  | Ttrue ->  f2
  | Tfalse -> (match t_node f2 with
               | Ttrue ->  f1
               | _ -> t_not_simp f2)
  | _ ->
    (match t_node f2 with
     | Ttrue ->  f1
     | Tfalse -> t_not_simp f1
     | _ -> if t_equal f1 f2 then  (t_attr_copy f1 t_true) else t_iff f1 f2)

(** val t_quant_close_simp :
    quant -> vsymbol list -> (term_node term_o) list list ->
    (term_node term_o) -> (term_node term_o) errorM **)

let t_quant_close_simp q vl tl f =
  if null vl
  then  f
  else let fvs = t_vars f in
       let check = fun v -> Mvs.mem v fvs in
       if forallb check vl
       then t_quant_close q vl tl f
       else let vl0 = filter check vl in
            if null vl0
            then  f
            else t_quant_close q vl0 (filter (forallb (t_v_all check)) tl) f

(** val t_forall_close_simp :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    (term_node term_o) errorM **)

let t_forall_close_simp =
  t_quant_close_simp Tforall

(** val t_exists_close_simp :
    vsymbol list -> (term_node term_o) list list -> (term_node term_o) ->
    (term_node term_o) errorM **)

let t_exists_close_simp =
  t_quant_close_simp Texists

(** val t_equ_simp :
    (term_node term_o) -> (term_node term_o) -> (ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let t_equ_simp t1 t2 =
  if t_equal t1 t2 then (fun x -> x) t_true else t_equ t1 t2

(** val small : (term_node term_o) -> bool **)

let small t0 =
  match t_node t0 with
  | Tvar _ -> true
  | Tconst _ -> true
  | _ -> false

(** val t_let_close_simp :
    vsymbol -> (term_node term_o) -> (term_node term_o) -> (term_node term_o)
    errorM **)

let t_let_close_simp v e t0 =
  let n = t_v_occurs v t0 in
  if BigInt.is_zero n
  then  t0
  else if (||) (BigInt.eq n BigInt.one) (small e)
       then t_subst_single v e t0
       else t_let_close v e t0

(** val t_quant_simp1 : quant -> term_quant -> (term_node term_o) errorM **)

let t_quant_simp1 q qf = match qf with
| p,f ->
  let p0,_ = p in
  let vl,_ = p0 in
  let fvs = t_vars f in
  let check = fun v -> Mvs.mem v fvs in
  if forallb check vl
  then  (t_quant q qf)
  else let p1,f0 = t_view_quant qf in
       let vl0,tl = p1 in
       let fvs0 = t_vars f0 in
       let check0 = fun v -> Mvs.mem v fvs0 in
       let vl1 = filter check0 vl0 in
       if null vl1
       then  f0
       else t_quant_close q vl1 (filter (forallb (t_v_all check0)) tl) f0







(** val term_traverse :
    ((term_node term_o) -> vsymbol -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> constant -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> 'a2 -> vsymbol ->
    (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> 'a2 -> 'a2 -> 'a2 -> (BigInt.t*'a1, 'a2) errState)
    -> ((term_node term_o) -> lsymbol -> (term_node term_o) list -> 'a2 list
    -> (BigInt.t*'a1, 'a2) errState) -> ((term_node term_o) ->
    (term_node term_o) -> 'a2 ->
    (((pattern_node pattern_o)*(term_node term_o))*'a2) list ->
    (BigInt.t*'a1, 'a2) errState) -> ((term_node term_o) -> vsymbol ->
    (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> quant -> vsymbol list -> (term_node term_o) list
    list -> 'a2 list list -> (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2)
    errState) -> ((term_node term_o) -> binop -> (term_node term_o) ->
    (term_node term_o) -> 'a2 -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2)
    errState) -> ((term_node term_o) -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (BigInt.t*'a1, 'a2) errState) ->
    (term_node term_o) -> (BigInt.t*'a1, 'a2) errState **)

let rec term_traverse var_case const_case let_case if_case app_case match_case eps_case quant_case binop_case not_case true_case false_case tm1 =
  match t_node tm1 with
  | Tvar x -> var_case tm1 x
  | Tconst c -> const_case tm1 c
  | Tapp (l, ts) ->
    (@@) (fun recs -> app_case tm1 l ts recs)
      (errst_list
        (dep_map (fun t1 _ ->
          term_traverse var_case const_case let_case if_case app_case
            match_case eps_case quant_case binop_case not_case true_case
            false_case t1) ts))
  | Tif (t1, t2, t3) ->
    (@@) (fun v1 ->
      (@@) (fun v2 ->
        (@@) (fun v3 -> if_case tm1 t1 t2 t3 v1 v2 v3)
          (term_traverse var_case const_case let_case if_case app_case
            match_case eps_case quant_case binop_case not_case true_case
            false_case t3))
        (term_traverse var_case const_case let_case if_case app_case
          match_case eps_case quant_case binop_case not_case true_case
          false_case t2))
      (term_traverse var_case const_case let_case if_case app_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
  | Tlet (t1, b) ->
    (@@) (fun v1 ->
      (fun x y -> y x () ()) ( ( (t_open_bound b))) (fun y _ _ ->
        (@@) (fun v2 -> let_case tm1 t1 v1 (fst y) (snd y) v2)
          (term_traverse var_case const_case let_case if_case app_case
            match_case eps_case quant_case binop_case not_case true_case
            false_case (snd y))))
      (term_traverse var_case const_case let_case if_case app_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
  | Tcase (t1, tbs) ->
    (@@) (fun r1 ->
      (@@) (fun tbs2 -> match_case tm1 t1 r1 tbs2)
        (errst_list
          (dep_map (fun b _ ->
            (fun x y -> y x () ()) ( ( (t_open_branch b))) (fun y _ _ ->
              (@@) (fun t2 -> (fun x -> x) (y,t2))
                (term_traverse var_case const_case let_case if_case app_case
                  match_case eps_case quant_case binop_case not_case
                  true_case false_case (snd y)))) tbs)))
      (term_traverse var_case const_case let_case if_case app_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
  | Teps b ->
    (fun x y -> y x () ()) ( ( (t_open_bound b))) (fun y _ _ ->
      (@@) (fun v -> eps_case tm1 (fst y) (snd y) v)
        (term_traverse var_case const_case let_case if_case app_case
          match_case eps_case quant_case binop_case not_case true_case
          false_case (snd y)))
  | Tquant (q, tq) ->
    (fun x y -> y x () ()) ( ( (t_open_quant1 tq))) (fun y _ _ ->
      (@@) (fun v ->
        let vs = fst (fst y) in
        let tr = snd (fst y) in
        let t = snd y in
        (@@) (fun v2 -> quant_case tm1 q vs tr v2 t v)
          (errst_list
            (dep_map (fun l1 _ ->
              errst_list
                (dep_map (fun tr1 _ ->
                  term_traverse var_case const_case let_case if_case app_case
                    match_case eps_case quant_case binop_case not_case
                    true_case false_case tr1) l1)) tr)))
        (term_traverse var_case const_case let_case if_case app_case
          match_case eps_case quant_case binop_case not_case true_case
          false_case (snd y)))
  | Tbinop (b, t1, t2) ->
    (@@) (fun r1 ->
      (@@) (fun r2 -> binop_case tm1 b t1 t1 r1 r2)
        (term_traverse var_case const_case let_case if_case app_case
          match_case eps_case quant_case binop_case not_case true_case
          false_case t2))
      (term_traverse var_case const_case let_case if_case app_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
  | Tnot t1 ->
    (@@) (fun r1 -> not_case tm1 t1 r1)
      (term_traverse var_case const_case let_case if_case app_case match_case
        eps_case quant_case binop_case not_case true_case false_case t1)
  | Ttrue -> true_case tm1
  | Tfalse -> false_case tm1

(** val tm_traverse :
    ((term_node term_o) -> vsymbol -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> constant -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> 'a2 -> vsymbol ->
    (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> 'a2 -> 'a2 -> 'a2 -> (BigInt.t*'a1, 'a2) errState)
    -> ((term_node term_o) -> lsymbol -> (term_node term_o) list -> 'a2 list
    -> (BigInt.t*'a1, 'a2) errState) -> ((term_node term_o) ->
    (term_node term_o) -> 'a2 ->
    (((pattern_node pattern_o)*(term_node term_o))*'a2) list ->
    (BigInt.t*'a1, 'a2) errState) -> ((term_node term_o) -> vsymbol ->
    (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> quant -> vsymbol list -> (term_node term_o) list
    list -> 'a2 list list -> (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2)
    errState) -> ((term_node term_o) -> binop -> (term_node term_o) ->
    (term_node term_o) -> 'a2 -> 'a2 -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (term_node term_o) -> 'a2 -> (BigInt.t*'a1, 'a2)
    errState) -> ((term_node term_o) -> (BigInt.t*'a1, 'a2) errState) ->
    ((term_node term_o) -> (BigInt.t*'a1, 'a2) errState) ->
    (term_node term_o) -> (BigInt.t*'a1, 'a2) errState **)

let tm_traverse =
  term_traverse

(** val term_map :
    ((term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    vsymbol -> (term_node term_o) -> (term_node term_o) -> (BigInt.t*'a1,
    (term_node term_o)) errState) -> ((term_node term_o) ->
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (BigInt.t*'a1, (term_node term_o)) errState) -> ((term_node term_o) ->
    lsymbol -> (term_node term_o) list -> (term_node term_o) list ->
    (BigInt.t*'a1, (term_node term_o)) errState) -> ((term_node term_o) ->
    (term_node term_o) -> (term_node term_o) ->
    (((pattern_node pattern_o)*(term_node term_o))*(term_node term_o)) list
    -> (BigInt.t*'a1, (term_node term_o)) errState) -> ((term_node term_o) ->
    vsymbol -> (term_node term_o) -> (term_node term_o) -> (BigInt.t*'a1,
    (term_node term_o)) errState) -> ((term_node term_o) -> quant -> vsymbol
    list -> (term_node term_o) list list -> (term_node term_o) list list ->
    (term_node term_o) -> (term_node term_o) -> (BigInt.t*'a1,
    (term_node term_o)) errState) -> ((term_node term_o) -> binop ->
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> (BigInt.t*'a1, (term_node term_o)) errState) ->
    ((term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (BigInt.t*'a1, (term_node term_o)) errState) -> (term_node term_o) ->
    (BigInt.t*'a1, (term_node term_o)) errState **)

let term_map let_case if_case app_case match_case eps_case quant_case binop_case not_case tm1 =
  tm_traverse (fun tm2 _ -> (fun x -> x) tm2) (fun tm2 _ -> (fun x -> x) tm2)
    let_case if_case app_case match_case eps_case quant_case binop_case
    not_case (fun x -> x) (fun x -> x) tm1

(** val tmap_let_default :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) -> vsymbol
    -> (term_node term_o) -> (term_node term_o) -> (BigInt.t*'a1,
    (term_node term_o)) errState **)

let tmap_let_default _ _ r1 v _ r2 =
   (t_let_close v r1 r2)

(** val tmap_if_default :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (term_node term_o) -> (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_if_default _ _ _ _ r1 r2 r3 =
   (t_if r1 r2 r3)

(** val tmap_app_default :
    (term_node term_o) -> lsymbol -> (term_node term_o) list ->
    (term_node term_o) list -> (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_app_default tm1 l _ rs =
  (fun x -> x) (t_app1 l rs (t_ty tm1))

(** val tmap_match_default :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (((pattern_node pattern_o)*(term_node term_o))*(term_node term_o)) list
    -> (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_match_default _ _ r1 tb =
   (t_case_close r1 (map (fun x -> (fst (fst x)),(snd x)) tb))

(** val tmap_eps_default :
    (term_node term_o) -> vsymbol -> (term_node term_o) -> (term_node term_o)
    -> (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_eps_default _ v _ r =
   (t_eps_close v r)

(** val tmap_quant_default :
    (term_node term_o) -> quant -> vsymbol list -> (term_node term_o) list
    list -> (term_node term_o) list list -> (term_node term_o) ->
    (term_node term_o) -> (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_quant_default _ q vs _ rr _ r =
   (t_quant_close q vs rr r)

(** val tmap_binop_default :
    (term_node term_o) -> binop -> (term_node term_o) -> (term_node term_o)
    -> (term_node term_o) -> (term_node term_o) -> (BigInt.t*'a1,
    (term_node term_o)) errState **)

let tmap_binop_default _ b _ _ r1 r2 =
   (t_binary b r1 r2)

(** val tmap_not_default :
    (term_node term_o) -> (term_node term_o) -> (term_node term_o) ->
    (BigInt.t*'a1, (term_node term_o)) errState **)

let tmap_not_default _ _ r =
   (t_not r)
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





(** Variable symbols *)

(* type vsymbol = {
  vs_name : ident;
  vs_ty   : ty;
} *)

module Vsym2 = MakeMSHW(VsymTag) 
(* (struct
  type t = vsymbol
  let tag vs = vs.vs_name.id_tag
  let equal = (==) (*JOSH TODO equal*)
end) *)

(* module Svs = Vsym.S
module Mvs = Vsym.M *)
module Hvs = Vsym2.H
module Wvs = Vsym2.W

(* let vs_equal : vsymbol -> vsymbol -> bool = (==)
let vs_hash vs = id_hash vs.vs_name
let vs_compare vs1 vs2 = id_compare vs1.vs_name vs2.vs_name *)

(* let create_vsymbol name ty = {
  vs_name = id_register name;
  vs_ty   = ty;
} *)

(** Function and predicate symbols *)

(* type lsymbol = {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
  ls_constr : BigInt.t;
  ls_proj   : bool;
} *)

module Lsym2 = MakeMSHW (LsymTag) 
(* (struct
  type t = lsymbol
  let tag ls = ls.ls_name.id_tag
  let equal = (==) JOSH TODO equal
end) *)

(* module Sls = Lsym.S
module Mls = Lsym.M *)
module Hls = Lsym2.H
module Wls = Lsym2.W

(* let ls_equal : lsymbol -> lsymbol -> bool = (==)
let ls_hash ls = id_hash ls.ls_name
let ls_compare ls1 ls2 = id_compare ls1.ls_name ls2.ls_name *)

(* let check_constr constr _args value =
  if BigInt.is_zero constr || (BigInt.pos constr && value <> None)
  then constr else invalid_arg "Term.create_lsymbol"

let check_proj proj constr args value =
  if not proj || (BigInt.is_zero constr  && value <> None && List.length args = 1)
  then proj else invalid_arg "Term.create_lsymbol" *)

let create_lsymbol ?(constr=BigInt.zero) ?(proj=false) name args value = {
  ls_name   = id_register name;
  ls_args   = args;
  ls_value  = value;
  ls_constr = check_constr constr value;
  ls_proj   = check_proj proj constr args value;
}

let create_fsymbol ?constr ?proj nm al vl =
  create_lsymbol ?constr ?proj nm al (Some vl)

(* let create_psymbol nm al =
  create_lsymbol nm al None *)

(* let ls_ty_freevars ls =
  let acc = oty_freevars Stv.empty ls.ls_value in
  List.fold_left ty_freevars acc ls.ls_args *)

(** Patterns *)

(* type pattern = {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty   : ty;
}

and pattern_node =
  | Pwild (* _ *)
  | Pvar of vsymbol (* newly introduced variables *)
  | Papp of lsymbol * pattern list (* application *)
  | Por  of pattern * pattern (* | *)
  | Pas  of pattern * vsymbol
  (* naming a term recognized by pattern as a variable *)
 *)
(* h-consing constructors for patterns *)

(* let mk_pattern n vs ty = {
  pat_node = n;
  pat_vars = vs;
  pat_ty   = ty;
}

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

let pat_wild ty = mk_pattern Pwild Svs.empty ty
let pat_var v   = mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty

let pat_as p v =
  let s = Svs.add_new (DuplicateVar v) v p.pat_vars in
  mk_pattern (Pas (p,v)) s v.vs_ty

let pat_or p q =
  if Svs.equal p.pat_vars q.pat_vars then
    mk_pattern (Por (p,q)) p.pat_vars p.pat_ty
  else
    let s = Mvs.union (fun _ _ _ -> None) p.pat_vars q.pat_vars in
    raise (UncoveredVar (Svs.choose s))

let pat_app f pl ty =
  let dup v () () = raise (DuplicateVar v) in
  let merge s p = Mvs.union dup s p.pat_vars in
  mk_pattern (Papp (f,pl)) (List.fold_left merge Svs.empty pl) ty *)

(* generic traversal functions *)

(* let pat_map fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app_aux s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as_aux (fn p) v
  | Por (p, q) -> pat_or_aux (fn p) (fn q)

let pat_map fn = pat_map (fun p ->
  let res = fn p in ty_equal_check p.pat_ty res.pat_ty; res)

let pat_fold fn acc pat = match pat.pat_node with
  | Pwild | Pvar _ -> acc
  | Papp (_, pl) -> List.fold_left fn acc pl
  | Pas (p, _) -> fn acc p
  | Por (p, q) -> fn (fn acc p) q

let pat_all pr pat = Util.all pat_fold pr pat
let pat_any pr pat = Util.any pat_fold pr pat

(* smart constructors for patterns *)

exception BadArity of lsymbol * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol *)

(* let pat_app fs pl ty =
  let s = match fs.ls_value with
    | Some vty -> ty_match Mtv.empty vty ty
    | None -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty p = ty_match s ty p.pat_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args pl with
    | Invalid_argument _ -> raise (BadArity (fs, List.length pl)));
  if BigInt.is_zero fs.ls_constr then raise (ConstructorExpected fs);
  pat_app_aux fs pl ty

let pat_as p v =
  ty_equal_check p.pat_ty v.vs_ty;
  pat_as_aux p v

let pat_or p q =
  ty_equal_check p.pat_ty q.pat_ty;
  pat_or_aux p q *)

(* rename all variables in a pattern *)

let rec pat_rename_all m p = match p.pat_node with
  | Pvar v -> pat_var (Mvs.find v m)
  | Pas (p, v) -> pat_as (pat_rename_all m p) (Mvs.find v m)
  | _ -> pat_map (pat_rename_all m) p

(* symbol-wise map/fold *)

let rec pat_gen_map fnT fnL m pat =
  let fn = pat_gen_map fnT fnL m in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (Mvs.find v m)
    | Papp (s, pl) -> pat_app (fnL s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (Mvs.find v m)
    | Por (p, q) -> pat_or (fn p) (fn q)

(* let rec pat_gen_fold fnT fnL acc pat =
  let fn acc p = pat_gen_fold fnT fnL acc p in
  let acc = fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild | Pvar _ -> acc
    | Papp (s, pl) -> List.fold_left fn (fnL acc s) pl
    | Por (p, q) -> fn (fn acc p) q
    | Pas (p, _) -> fn acc p *)

(** Terms and formulas *)

(* type quant =
  | Tforall
  | Texists

type binop =
  | Tand
  | Tor
  | Timplies
  | Tiff

type term = {
  t_node  : term_node;
  t_ty    : ty option;
  t_attrs : Sattr.t;
  t_loc   : Loc.position option;
}

and term_node =
  | Tvar of vsymbol
  | Tconst of Constant.constant
  | Tapp of lsymbol * term list
  | Tif of term * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of term_bound
  | Tquant of quant * term_quant
  | Tbinop of binop * term * term
  | Tnot of term
  | Ttrue
  | Tfalse

and term_bound  = vsymbol * bind_info * term
and term_branch = pattern * bind_info * term
and term_quant  = vsymbol list * bind_info * trigger * term

and trigger = term list list

and bind_info = {
  bv_vars  : BigInt.t Mvs.t;   (* free variables *)
  bv_subst : term Mvs.t   (* deferred substitution *)
} *)

(* term equality modulo alpha-equivalence and location *)

(* exception CompLT
exception CompGT *)

(* type frame = BigInt.t Mvs.t

type term_or_bound =
  | Trm of term (* * frame list*)
  | Bnd of BigInt.t *)


(*lexicographic comparison*)
(* let lex_comp x1 x2 : int =
  if x1 = 0 then x2 else x1

let list_comp l : int =
  List.fold_left lex_comp 0 l

(*Compare variables v1 and v2.
  To be equal, they must either be mapped to each other in each map
  or not in either map and equal*)
let var_compare (m1: BigInt.t Mvs.t) (m2: BigInt.t Mvs.t) (v1: vsymbol) (v2: vsymbol) : int =
  begin match Mvs.find_opt v1 m1, Mvs.find_opt v2 m2 with
    | Some i1, Some i2 ->
      BigInt.compare i1 i2
    | None, None -> vs_compare v1 v2
    | Some _, _ -> -1
    | _, _ -> 1
    end

let quant_compare (q1: quant) (q2: quant) : int =
  match q1, q2 with
  | Tforall, Texists -> -1
  | Texists, Tforall -> 1
  | _, _ -> 0

let binop_compare (b1: binop) (b2: binop) : int =
  match b1, b2 with
  | Tand, Tand -> 0
  | Tor, Tor -> 0
  | Timplies, Timplies -> 0
  | Tiff, Tiff -> 0
  | Tand, _ -> -1
  | _, Tand -> 1
  | Tor, _ -> -1
  | _, Tor -> 1
  | Timplies, _ -> -1
  | _, Timplies -> 1

(*Version of fold_left2 with default values for shorter lists*)
let rec fold_left2_def (f: 'a -> 'b -> 'c -> 'a) (acc: 'a) (l1 : 'b list) (l2: 'c list) (d1: 'a) (d2: 'a) =
  match l1, l2 with
  | [], [] -> acc
  | x1 :: t1, x2 :: t2 -> fold_left2_def f (f acc x1 x2) t1 t2 d1 d2
  | [], _ :: _ -> d1
  | _ :: _, [] -> d2 

let rec or_cmp bv1 bv2 q1 q2 = match q1.pat_node, q2.pat_node with
  | Pwild, Pwild -> 0
  | Pvar v1, Pvar v2 ->
      BigInt.compare (Mvs.find v1 bv1) (Mvs.find v2 bv2)
  | Papp (s1, l1), Papp (s2, l2) ->
      let i1 = ls_compare s1 s2 in
      lex_comp i1 (
        fold_left2_def (fun i p1 p2 ->
          lex_comp i (or_cmp bv1 bv2 p1 p2)
          ) 0 l1 l2 (-1) (1))
  | Por (p1, q1), Por (p2, q2) ->
      let i1 = or_cmp bv1 bv2 p1 p2 in
      lex_comp i1 (
        or_cmp bv1 bv2 q1 q2)
  | Pas (p1, v1), Pas (p2, v2) ->
      let i1 = or_cmp bv1 bv2 p1 p2 in
      lex_comp i1 (
        BigInt.compare (Mvs.find v1 bv1) (Mvs.find v2 bv2))
  | Pwild,  _ -> -1 | _, Pwild  -> 1
  | Pvar _, _ -> -1 | _, Pvar _ -> 1
  | Papp _, _ -> -1 | _, Papp _ -> 1
  | Por _,  _ -> -1 | _, Por _  -> 1

  let rec pat_compare (bnd,bv1,bv2 as state) p1 p2 =
    match p1.pat_node, p2.pat_node with
    | Pwild, Pwild ->
        0, bnd, bv1, bv2
    | Pvar v1, Pvar v2 ->
        0, BigInt.succ bnd, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2 (*equal by fiat*)
    | Papp (s1, l1), Papp (s2, l2) ->
        let i1 = ls_compare s1 s2 in
        let sbnd, sm1, sm2 = state in
        let i2, bnd, bv1, bv2 = fold_left2_def (fun acc p1 p2 ->
            let i, bnd1, m1, m2 = acc in
            let j, bnd2, m1', m2' = pat_compare (bnd1, m1, m2) p1 p2 in
            lex_comp i j, bnd2, m1', m2') (0, sbnd, sm1, sm2) l1 l2 (-1, sbnd, sm1, sm2) (1, sbnd, sm1, sm2) in  (*TODO: are these default right think only value matters anyway*)
        lex_comp i1 i2, bnd, bv1, bv2
    | Por (p1, q1), Por (p2, q2) ->
        let (i1,bnd1,bv1,bv2 as res) = pat_compare state p1 p2 in
        if i1 <> 0 then res
        else
        let i2 = or_cmp bv1 bv2 q1 q2 in
        (i2, bnd1, bv1, bv2)
    | Pas (p1, v1), Pas (p2, v2) ->
        let i1, bnd, bv1, bv2 = pat_compare state p1 p2 in
        i1, BigInt.succ bnd, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2
    | Pwild, _  -> -1, bnd, bv1, bv2 | _, Pwild  -> 1, bnd, bv1, bv2
    | Pvar _, _ -> -1, bnd, bv1, bv2 | _, Pvar _ -> 1, bnd, bv1, bv2
    | Papp _, _ -> -1, bnd, bv1, bv2 | _, Papp _ -> 1, bnd, bv1, bv2
    | Por _, _  -> -1, bnd, bv1, bv2 | _, Por _  -> 1, bnd, bv1, bv2 *)

(* let t_compare ~trigger ~attr ~loc ~const t1 t2 =
  t_compare_full trigger attr loc const t1 t2 *)
  (* let rec t_compare bnd (vml1 : BigInt.t Mvs.t) (vml2 : BigInt.t Mvs.t) t1 t2 : int =
    if t1 != t2 || not (Mvs.is_empty vml1) || not (Mvs.is_empty vml2) then begin
      let i1 = oty_compare t1.t_ty t2.t_ty in
      lex_comp i1 (
      let i2 = if attr then (Sattr.compare t1.t_attrs t2.t_attrs) else 0 in
      lex_comp i2 (
      let i3 = if loc then (Option.compare Loc.compare t1.t_loc t2.t_loc) else 0 in
      lex_comp i3 (
      match t1.t_node, t2.t_node with
      | Tvar v1, Tvar v2 ->
          var_compare vml1 vml2 v1 v2
        | Tconst c1, Tconst c2 ->
            Constant.compare_const ~structural:const c1 c2
        | Tapp (s1,l1), Tapp (s2,l2) ->
          let i1 = ls_compare s1 s2 in
          lex_comp i1 (
            fold_left2_def (fun acc t1 t2 ->
              if acc <> 0 then acc else (t_compare bnd vml1 vml2) t1 t2) (-1) 1 l1 l2 0)
        | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
            let i1 = t_compare bnd vml1 vml2 f1 f2 in
            lex_comp i1 (
            let i2 = t_compare bnd vml1 vml2 t1 t2 in
            lex_comp i2 (
            t_compare bnd vml1 vml2 e1 e2))
        | Tlet (t1,((v1,b1),e1)), Tlet (t2,((v2,b2),e2)) ->
            let i1 = t_compare bnd vml1 vml2 t1 t2 in
            lex_comp i1 (
            let vml1 = Mvs.add v1 bnd vml1 in
            let vml2 = Mvs.add v2 bnd vml2 in
            t_compare (BigInt.succ bnd) vml1 vml2 e1 e2)
        | Tcase (t1,bl1), Tcase (t2,bl2) ->
            let i1 = t_compare bnd vml1 vml2 t1 t2 in
            lex_comp i1 (
            let b_compare ((p1,b1),t1) ((p2,b2),t2) =
              let ((ip, bnd),bv1),bv2 = pat_compare ((bnd,Mvs.empty),Mvs.empty) p1 p2 in
              if ip <> 0 then ip else
              let vml1 = Mvs.union (fun x n1 n2 -> Some n1) bv1 vml1 in
              let vml2 = Mvs.union (fun x n1 n2 -> Some n1) bv2 vml2 in
              t_compare bnd vml1 vml2 t1 t2 in
            Lists.compare b_compare bl1 bl2)
        | Teps ((v1,b1),e1), Teps ((v2,b2),e2) ->
            let vml1 = Mvs.add v1 bnd vml1 in
            let vml2 = Mvs.add v2 bnd vml2 in
            t_compare (BigInt.succ bnd) vml1 vml2 e1 e2
        | Tquant (q1,(((vl1,b1),tr1),f1)), Tquant (q2,(((vl2,b2),tr2),f2)) ->
            let i1 = quant_compare q1 q2 in
            lex_comp i1 (
            let rec add bnd bv1 bv2 vl1 vl2 = match vl1, vl2 with
              | (v1::vl1), (v2::vl2) ->
                  let bv1 = Mvs.add v1 bnd bv1 in
                  let bv2 = Mvs.add v2 bnd bv2 in
                  add (BigInt.succ bnd) bv1 bv2 vl1 vl2
              | [], (_::_) -> -1, bnd, bv1, bv2
              | (_::_), [] -> 1, bnd, bv1, bv2 
              | [], [] -> 0, bnd, bv1, bv2 in
            let i1, bnd, bv1, bv2 = add bnd Mvs.empty Mvs.empty vl1 vl2 in
            if i1 <> 0 then i1 else
            let vml1 = Mvs.union (fun x n1 n2 -> Some n1) bv1 vml1 in
            let vml2 = Mvs.union (fun x n1 n2 -> Some n1) bv2 vml2 in
            let tr_cmp t1 t2 = t_compare bnd vml1 vml2 t1 t2 in
            let i2 = if trigger then (Lists.compare (Lists.compare tr_cmp) tr1 tr2) else 0 in
            if i2 <> 0 then i2 else
            t_compare bnd vml1 vml2 f1 f2)
        | Tbinop (op1,f1,g1), Tbinop (op2,f2,g2) ->
            let i1 = binop_compare op1 op2 in
            lex_comp i1 (
            let i2 = t_compare bnd vml1 vml2 g1 g2 in
            lex_comp i2 (
            t_compare bnd vml1 vml2 f1 f2))
        | Tnot f1, Tnot f2 ->
            t_compare bnd vml1 vml2 f1 f2
        | Ttrue, Ttrue -> 0
        | Tfalse, Tfalse -> 0
        | Tvar _, _   -> -1 | _, Tvar _   -> 1
        | Tconst _, _ -> -1 | _, Tconst _ -> 1
        | Tapp _, _   -> -1 | _, Tapp _   -> 1
        | Tif _, _    -> -1 | _, Tif _    -> 1
        | Tlet _, _   -> -1 | _, Tlet _   -> 1
        | Tcase _, _  -> -1 | _, Tcase _  -> 1
        | Teps _, _   -> -1 | _, Teps _   -> 1
        | Tquant _, _ -> -1 | _, Tquant _ -> 1
        | Tbinop _, _ -> -1 | _, Tbinop _ -> 1
        | Tnot _, _   -> -1 | _, Tnot _   -> 1
        | Ttrue, _    -> -1 | _, Ttrue    -> 1
      ))) end else 0 in
  t_compare BigInt.zero Mvs.empty Mvs.empty t1 t2 *)

(* let t_similar t1 t2 =
  oty_equal t1.t_ty t2.t_ty &&
  match t1.t_node, t2.t_node with
    | Tvar v1, Tvar v2 -> vs_equal v1 v2
    | Tconst c1, Tconst c2 -> Constant.compare_const ~structural:true c1 c2 = 0
    | Tapp (s1,l1), Tapp (s2,l2) -> ls_equal s1 s2 && Lists.equal (==) l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) -> f1 == f2 && t1 == t2 && e1 == e2
    | Tlet (t1,bv1), Tlet (t2,bv2) -> t1 == t2 && bv1 == bv2
    | Tcase (t1,bl1), Tcase (t2,bl2) -> t1 == t2 && Lists.equal (==) bl1 bl2
    | Teps bv1, Teps bv2 -> bv1 == bv2
    | Tquant (q1,bv1), Tquant (q2,bv2) -> q1 = q2 && bv1 == bv2
    | Tbinop (o1,f1,g1), Tbinop (o2,f2,g2) -> o1 = o2 && f1 == f2 && g1 == g2
    | Tnot f1, Tnot f2 -> f1 == f2
    | Ttrue, Ttrue | Tfalse, Tfalse -> true
    | _, _ -> false *)

    (* let rec pat_hash bnd bv p = match p.pat_node with
    | Pwild -> bnd, bv, BigInt.zero
    | Pvar v -> BigInt.succ bnd, Mvs.add v bnd bv, BigInt.succ bnd
    | Papp (s,l) ->
        let hash (bnd,bv,h) p =
          let bnd,bv,hp = pat_hash bnd bv p in
          bnd, bv, Hashcons.combine_big h hp in
        List.fold_left hash (bnd,bv,ls_hash s) l
    | Por (p,q) ->
        let bnd,bv,hp = pat_hash bnd bv p in
        let rec or_hash q = match q.pat_node with
          | Pwild -> BigInt.zero
          | Pvar v -> BigInt.succ (Mvs.find v bv)
          | Papp (s,l) -> Hashcons.combine_big_list or_hash (ls_hash s) l
          | Por (p,q) -> Hashcons.combine_big (or_hash p) (or_hash q)
          | Pas (p,v) -> Hashcons.combine_big (or_hash p) (BigInt.succ (Mvs.find v bv))
        in
        bnd, bv, Hashcons.combine_big hp (or_hash q)
    | Pas (p,v) ->
        let bnd,bv,hp = pat_hash bnd bv p in
        BigInt.succ bnd, Mvs.add v bnd bv, Hashcons.combine_big hp (BigInt.succ bnd) *)

(* let t_hash ~trigger ~attr ~const t =
    t_hash_full trigger attr const t *)
  (*let rec t_hash (bnd : BigInt.t) (vml: (BigInt.t Mvs.t))  t =
    let h = oty_hash t.t_ty in
    let h =
      if attr then
        let comb l h = Hashcons.combine_big (attr_hash l) h in
        Sattr.fold comb t.t_attrs h
      else h
    in
    Hashcons.combine_big h
      begin match t.t_node with
      | Tvar v -> begin match Mvs.find_opt v vml with
                  | Some i -> BigInt.succ i
                  | None -> vs_hash v
                  end
      | Tconst c when const -> BigInt.of_int (Hashtbl.hash c) (*JOSH: make sure*)
      | Tconst (Constant.ConstInt {Number.il_int = c}) -> BigInt.of_int (Hashtbl.hash c)
      | Tconst (Constant.ConstReal {Number.rl_real = c}) -> BigInt.of_int (Hashtbl.hash c)
      | Tconst (Constant.ConstStr c) -> BigInt.of_int (Hashtbl.hash c)
      | Tapp (s,l) ->
          Hashcons.combine_big_list (t_hash bnd vml) (ls_hash s) l
      | Tif (f,t,e) ->
          let hf = t_hash bnd vml f in
          let ht = t_hash bnd vml t in
          let he = t_hash bnd vml e in
          Hashcons.combine2_big hf ht he
      | Tlet (t,((v,b),e)) ->
          let h = t_hash bnd vml t in
          let vml = Mvs.add v bnd vml in
          Hashcons.combine_big h (t_hash (BigInt.succ bnd) vml e)
      | Tcase (t,bl) ->
          let h = t_hash bnd vml t in
          let b_hash ((p,b),t) =
            let (bnd,bv),hp = pat_hash bnd Mvs.empty p in
            let vml = Mvs.union (fun x n1 n2 -> Some n1) bv vml in
            Hashcons.combine_big hp (t_hash bnd vml t) in
          Hashcons.combine_big_list b_hash h bl
      | Teps ((v,b),e) ->
          let vml = Mvs.add v bnd vml in
          t_hash (BigInt.succ bnd) vml e
      | Tquant (q,(((vl,b),tr),f)) ->
          let h = BigInt.of_int (Hashtbl.hash q) in (*JOSH make sure*)
          let rec add bnd bv vl = match vl with
            | v::vl -> add (BigInt.succ bnd) (Mvs.add v bnd bv) vl
            | [] -> bnd, bv in
          let bnd, bv = add bnd Mvs.empty vl in
          let vml = Mvs.union (fun x n1 n2 -> Some n1) bv vml in
          let h =
            if trigger then
              List.fold_left
                (Hashcons.combine_big_list (t_hash bnd vml)) h tr
            else h
          in
          Hashcons.combine_big h (t_hash bnd vml f)
      | Tbinop (op,f,g) ->
          let ho = BigInt.of_int (Hashtbl.hash op) in (*JOSH make sure*)
          let hf = t_hash bnd vml f in
          let hg = t_hash bnd vml g in
          Hashcons.combine2_big ho hf hg
      | Tnot f ->
          Hashcons.combine_big BigInt.one (t_hash bnd vml f)
      | Ttrue -> BigInt.of_int 2
      | Tfalse -> BigInt.of_int 3
      end in
  t_hash BigInt.zero Mvs.empty t *)

let t_hash_generic ~trigger ~attr ~const t =
  t_hash_full trigger attr const t
let t_compare_generic ~trigger ~attr ~loc ~const t1 t2=
  t_compare_full trigger attr loc const t1 t2
let t_equal_generic ~trigger ~attr ~loc ~const t1 t2 =
  t_compare_full trigger attr loc const t1 t2 = 0

let mterm_generic ~trigger ~attr ~loc ~const
    : (module (Extmap.S with type key = term)) =
  (module (Extmap.Make(struct
      type t = term
      let tag t = t_hash_full trigger attr const t (*TODO JOSH hash*)
      (* let compare t1 t2 = t_compare ~trigger ~attr ~loc ~const t1 t2 *)
      let equal x y = (t_compare_full trigger attr loc const x y = 0) (*JOSH TODO equal*)
    end)))

let sterm_generic ~trigger ~attr ~loc ~const
    : (module (Extset.S with type M.key = term)) =
  let module M = (val (mterm_generic ~trigger ~attr ~loc ~const)) in
  (module (Extset.MakeOfMap(M)))

let hterm_generic ~trigger ~attr ~loc ~const
    : (module (Exthtbl.S with type key = term)) =
  (module (Exthtbl.Make(struct
      type t = term
      let hash t = BigInt.hash (t_hash_full trigger attr const t)
      let equal t1 t2 = t_compare_full trigger attr loc const t1 t2 = 0
    end)))

(* let t_hash_strict t =
  t_hash ~trigger:true ~attr:true ~const:true t
let t_equal_strict t1 t2 =
  t_compare ~trigger:true ~attr:true ~loc:true ~const:true t1 t2 = 0
let t_compare_strict t1 t2 =
  t_compare ~trigger:true ~attr:true ~loc:true ~const:true t1 t2 *)

module Mterm_strict =
  (val (mterm_generic ~trigger:true ~attr:true ~loc:true ~const:true))
module Sterm_strict =
  (val (sterm_generic ~trigger:true ~attr:true ~loc:true ~const:true))
module Hterm_strict=
  (val (hterm_generic ~trigger:true ~attr:true ~loc:true ~const:true))

(* let t_hash t =
  t_hash ~trigger:false ~attr:false ~const:false t
let t_equal t1 t2 =
  t_compare ~trigger:false ~attr:false ~loc:false ~const:false t1 t2 = 0
let t_compare t1 t2 =
  t_compare ~trigger:false ~attr:false ~loc:false ~const:false t1 t2 *)

module Mterm =
  (val (mterm_generic ~trigger:false ~attr:false ~loc:false ~const:false))
module Sterm =
  (val (sterm_generic ~trigger:false ~attr:false ~loc:false ~const:false))
module Hterm =
  (val (hterm_generic ~trigger:false ~attr:false ~loc:false ~const:false))

(* type checking *)
(* 
exception TermExpected of term
exception FmlaExpected of term

let t_type t = match t.t_ty with
  | Some ty -> ty
  | None -> raise (TermExpected t)

let t_prop f =
  if f.t_ty = None then f else raise (FmlaExpected f)

let t_ty_check t ty = match ty, t.t_ty with
  | Some l, Some r -> ty_equal_check l r
  | Some _, None -> raise (TermExpected t)
  | None, Some _ -> raise (FmlaExpected t)
  | None, None -> ()

let vs_check v t = ty_equal_check v.vs_ty (t_type t)

(* trigger equality and traversal *)

let tr_equal = Lists.equal (Lists.equal t_equal)

let tr_map fn = List.map (List.map fn)
let tr_fold fn = List.fold_left (List.fold_left fn)
let tr_map_fold fn = Lists.map_fold_left (Lists.map_fold_left fn) *)

(* bind_info equality, hash, and traversal *)

(* let bnd_map fn bv = { bv with bv_subst = Mvs.map fn bv.bv_subst } *)

(* let bnd_fold fn acc bv = Mvs.fold (fun _ t a -> fn a t) bv.bv_subst acc *)

(* let bnd_map_fold fn acc bv =
  let acc,s = Mvs.mapi_fold (fun _ t a -> fn a t) bv.bv_subst acc in
  acc, { bv with bv_subst = s } *)

(* hash-consing for terms and formulas *)

(* let vars_union s1 s2 = Mvs.union (fun _ m n -> Some (BigInt.add m n)) s1 s2

let add_b_vars s ((_,b),_) = vars_union s b.bv_vars

let rec t_vars t = match t.t_node with
  | Tvar v -> Mvs.singleton v BigInt.one
  | Tconst _ -> Mvs.empty
  | Tapp (_,tl) -> List.fold_left add_t_vars Mvs.empty tl
  | Tif (f,t,e) -> add_t_vars (add_t_vars (t_vars f) t) e
  | Tlet (t,bt) -> add_b_vars (t_vars t) bt
  | Tcase (t,bl) -> List.fold_left add_b_vars (t_vars t) bl
  | Teps ((_,b),_) -> b.bv_vars
  | Tquant (_,(((_,b),_),_)) -> b.bv_vars
  | Tbinop (_,f1,f2) -> add_t_vars (t_vars f1) f2
  | Tnot f -> t_vars f
  | Ttrue | Tfalse -> Mvs.empty

and add_t_vars s t = vars_union s (t_vars t)

let add_nt_vars _ n t s = vars_union s
  (if BigInt.eq n BigInt.one then t_vars t else Mvs.map (BigInt.mul n) (t_vars t))

(* hash-consing constructors for terms *)

let mk_term n ty = {
  t_node  = n;
  t_attrs = Sattr.empty;
  t_loc   = None;
  t_ty    = ty;
}

let t_var v         = mk_term (Tvar v) (Some v.vs_ty)
let t_const c ty    = mk_term (Tconst c) (Some ty)
let t_app f tl ty   = mk_term (Tapp (f, tl)) ty
let t_if f t1 t2    = mk_term (Tif (f, t1, t2)) t2.t_ty
let t_let t1 bt ty  = mk_term (Tlet (t1, bt)) ty
let t_case t1 bl ty = mk_term (Tcase (t1, bl)) ty
let t_eps bf ty     = mk_term (Teps bf) ty
let t_quant q qf    = mk_term (Tquant (q, qf)) None
let t_binary op f g = mk_term (Tbinop (op, f, g)) None
let t_not f         = mk_term (Tnot f) None
let t_true          = mk_term (Ttrue) None
let t_false         = mk_term (Tfalse) None*)

let t_attr_set ?loc l t = t_attr_set1 loc l t 
(*{ t with t_attrs = l; t_loc = loc }

let t_attr_add l t = { t with t_attrs = Sattr.add l t.t_attrs }

let t_attr_remove l t = { t with t_attrs = Sattr.remove l t.t_attrs }

let t_attr_copy s t =
  if s == t then s else
  if t_similar s t && Sattr.is_empty t.t_attrs && t.t_loc = None then s else
  let attrs = Sattr.union s.t_attrs t.t_attrs in
  let loc = if t.t_loc = None then s.t_loc else t.t_loc in
  { t with t_attrs = attrs; t_loc = loc }

(* unsafe map *)

let bound_map fn ((u,b),e) = ((u, b), fn e)

let t_map_unsafe fn t = t_attr_copy t (match t.t_node with
  | Tvar _ | Tconst _ -> t
  | Tapp (f,tl) -> t_app f (List.map fn tl) t.t_ty
  | Tif (f,t1,t2) -> t_if (fn f) (fn t1) (fn t2)
  | Tlet (e,b) -> t_let (fn e) (bound_map fn b) t.t_ty
  | Tcase (e,bl) -> t_case (fn e) (List.map (bound_map fn) bl) t.t_ty
  | Teps b -> t_eps (bound_map fn b) t.t_ty
  | Tquant (q,(((vl,b),tl),f)) -> t_quant q (((vl, b), tr_map fn tl), fn f)
  | Tbinop (op,f1,f2) -> t_binary op (fn f1) (fn f2)
  | Tnot f1 -> t_not (fn f1)
  | Ttrue | Tfalse -> t)

(* unsafe fold *)

let bound_fold fn acc ((_,b),e) = fn acc e

let t_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ -> acc
  | Tapp (_,tl) -> List.fold_left fn acc tl
  | Tif (f,t1,t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (e,b) -> fn (bound_fold fn acc b) e
  | Tcase (e,bl) -> List.fold_left (bound_fold fn) (fn acc e) bl
  | Teps b -> bound_fold fn acc b
  | Tquant (_,(((_,b),tl),f1)) -> fn (tr_fold fn acc tl) f1
  | Tbinop (_,f1,f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc *)

(* unsafe map_fold *)

(* let bound_map_fold fn acc ((u,b),e) =
  let acc, e = fn acc e in
  acc, ((u,b),e)

let t_map_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ ->
      acc, t
  | Tapp (f,tl) ->
      let acc,sl = Lists.map_fold_left fn acc tl in
      acc, t_attr_copy t (t_app f sl t.t_ty)
  | Tif (f,t1,t2) ->
      let acc, g  = fn acc f in
      let acc, s1 = fn acc t1 in
      let acc, s2 = fn acc t2 in
      acc, t_attr_copy t (t_if g s1 s2)
  | Tlet (e,b) ->
      let acc, e = fn acc e in
      let acc, b = bound_map_fold fn acc b in
      acc, t_attr_copy t (t_let e b t.t_ty)
  | Tcase (e,bl) ->
      let acc, e = fn acc e in
      let acc, bl = Lists.map_fold_left (bound_map_fold fn) acc bl in
      acc, t_attr_copy t (t_case e bl t.t_ty)
  | Teps b ->
      let acc, b = bound_map_fold fn acc b in
      acc, t_attr_copy t (t_eps b t.t_ty)
  | Tquant (q,(((vl,b),tl),f1)) ->
      let acc, tl = tr_map_fold fn acc tl in
      let acc, f1 = fn acc f1 in
      acc, t_attr_copy t (t_quant q (((vl,b),tl),f1))
  | Tbinop (op,f1,f2) ->
      let acc, g1 = fn acc f1 in
      let acc, g2 = fn acc f2 in
      acc, t_attr_copy t (t_binary op g1 g2)
  | Tnot f1 ->
      let acc, g1 = fn acc f1 in
      acc, t_attr_copy t (t_not g1)
  | Ttrue | Tfalse ->
      acc, t

(* type-unsafe term substitution *)

let fresh_vsymbol v =
  create_vsymbol (id_clone v.vs_name) v.vs_ty

let vs_rename h v =
  let u = fresh_vsymbol v in
  Mvs.add v (t_var u) h, u

let bnd_new s = { bv_vars = s }

let t_close_bound v t = ((v, bnd_new (Mvs.remove v (t_vars t))), t)

let pat_rename h p =
  let add_vs v () = fresh_vsymbol v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_rename_all m p in
  Mvs.union (fun _ _ t -> Some t) h (Mvs.map t_var m), p

let t_close_branch p t = ((p, bnd_new (Mvs.set_diff (t_vars t) p.pat_vars)), t)

let t_close_quant vl tl f =
  let del_v s v = Mvs.remove v s in
  let s = tr_fold add_t_vars (t_vars f) tl in
  let s = List.fold_left del_v s vl in
  (((vl, bnd_new s), tl), t_prop f)

let vl_rename h vl =
  Lists.map_fold_left vs_rename h vl*)

(* let rec t_subst_unsafe m t =
  let t_subst t = t_subst_unsafe m t in
  let t_open_bound v m t (*(v,b,t)*) =
    let m,v = vs_rename m v in
    v, t_subst_unsafe m t in
  let t_open_branch p m t (*(p,b,t)*) =
    let m,p = pat_rename m p in
    p, t_subst_unsafe m t in
  let t_open_quant vl m tl f (*(vl,b,tl,f)*) =
    let m,vl = vl_rename m vl in
    let tl = tr_map (t_subst_unsafe m) tl in
    vl, tl, t_subst_unsafe m f in
  let b_subst ((u,b),e as bv) =
    if Mvs.set_disjoint m b.bv_vars then bv else
      let m1 = Mvs.set_inter m b.bv_vars in
      let v, t1 = t_open_bound u m1 e in
      let ((_, b), _) as x = t_close_bound v t1 in
      x in
  let b_subst1 ((u,b),e as bv) =
    if Mvs.set_disjoint m b.bv_vars then bv else
      let m1 = Mvs.set_inter m b.bv_vars in
      let v, t1 = t_open_branch u m1 e in
      let ((_, b), _) as x = t_close_branch v t1 in
      x in
  let b_subst2 (((vl,b),tl),f1 as bq) =
    if Mvs.set_disjoint m b.bv_vars then bq else
      let m1 = Mvs.set_inter m b.bv_vars in
      let vs, tr, t1 = t_open_quant vl m1 tl f1 in
      let (((_, b), _), _) as x = t_close_quant vs tr t1 in
      x in
  match t.t_node with
  | Tvar u ->
      t_attr_copy t (Mvs.find_def t u m)
  | Tlet (e, bt) ->
      let d = t_subst e in
      t_attr_copy t (t_let d (b_subst bt) t.t_ty)
  | Tcase (e, bl) ->
      let d = t_subst e in
      let bl = List.map b_subst1 bl in
      t_attr_copy t (t_case d bl t.t_ty)
  | Teps bf ->
      t_attr_copy t (t_eps (b_subst bf) t.t_ty)
  | Tquant (q, (((vl,b),tl),f1 as bq)) ->
      t_attr_copy t (t_quant q (b_subst2 bq))
  | _ ->
      t_map_unsafe t_subst t  *)

(* let t_subst_unsafe m t =
  if Mvs.is_empty m then t else t_subst_unsafe m t *)

(* close bindings *)

(* let t_open_bound (v,b,t) = v, t *)

(* let t_open_branch (p, b, t) = p, t

let t_open_quant (vl, b, tl, f) = vl, tl, f *)

(* let  t_open_bound ((v,b),t) =
  let m,v = vs_rename Mvs.empty v in
  v, t_subst_unsafe m t
let t_open_branch ((p,b),t) =
  let m,p = pat_rename Mvs.empty p in
  p, t_subst_unsafe m t*)

(*JOSH: TODO MOVE
  Equal in Coq but not OCaml*)
let coq_to_ocaml_tup3 (x: ('a * 'b) * 'c) : 'a * 'b * 'c =
  let (a, b), c = x in
  a, b, c
let coq_to_ocaml_tup4 (x: (('a * 'b) * 'c) * 'd) : 'a * 'b * 'c * 'd =
  let ((a, b), c), d = x in
  a, b, c, d

let t_open_quant bq =
  coq_to_ocaml_tup3 (t_open_quant1 bq)
  (* let m,vl = vl_rename Mvs.empty vl in
  let tl = tr_map (t_subst_unsafe m) tl in
  vl, tl, t_subst_unsafe m f *)





(* open bindings *)







(* let t_open_bound (v,b,t) =
  let m,v = vs_rename b.bv_subst v in
  v, t_subst_unsafe m t *)

(*let t_open_bound_with e ((v,b),t) =
  vs_check v e;
  let m = Mvs.singleton v e in
  t_subst_unsafe m t *)





let t_clone_bound_id ?loc ?attrs ((v,_),_) =
  id_clone ?loc ?attrs v.vs_name

(** open bindings with optimized closing callbacks *)

let t_open_bound_cb tb =
  coq_to_ocaml_tup3 (t_open_bound_cb1 tb)
  (* let (a, b), c = t_open_bound_cb1 tb in
  a, b, c
  let v, t = t_open_bound tb in
  let close v' t' =
    if t == t' && vs_equal v v' then tb else t_close_bound v' t'
  in
  v, t, close *)

let t_open_branch_cb tbr =
  coq_to_ocaml_tup3 (t_open_branch_cb1 tbr)
  (* let p, t = t_open_branch tbr in
  let close p' t' =
    if t == t' && p == p' then tbr else t_close_branch p' t'
  in
  p, t, close *)

let t_open_quant_cb fq =
  coq_to_ocaml_tup4 (t_open_quant_cb1 fq)
  (* let vl, tl, f = t_open_quant fq in
  let close vl' tl' f' =
    if f == f' &&
      Lists.equal (Lists.equal ((==) : term -> term -> bool)) tl tl' &&
      Lists.equal vs_equal vl vl'
    then fq else t_close_quant vl' tl' f'
  in
  vl, tl, f, close *)

(* retrieve bound identifiers (useful to detect sharing) *)

(* let t_peek_bound ((v,_),_) = v.vs_name

let t_peek_branch ((p,_),_) =
  Svs.fold (fun v a -> Sid.add v.vs_name a) p.pat_vars Sid.empty

let t_peek_quant (((vl,_),_),_) =
  List.map (fun v -> v.vs_name) vl *)

(* constructors with type checking *)

(* let ls_arg_inst ls tl =
  let mtch s ty t = ty_match s ty (t_type t) in
  try List.fold_left2 mtch Mtv.empty ls.ls_args tl with
    | Invalid_argument _ -> raise (BadArity (ls, (BigInt.of_int (List.length tl)))) (*JOSH of_int*)

let ls_app_inst ls tl ty =
  let s = ls_arg_inst ls tl in
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> ty_match s vty ty
    | None, None -> s

let t_app_infer ls tl =
  let s = ls_arg_inst ls tl in
  t_app ls tl (oty_inst s ls.ls_value)

let t_app ls tl ty = ignore (ls_app_inst ls tl ty); t_app ls tl ty

let fs_app fs tl ty = t_app fs tl (Some ty)
let ps_app ps tl    = t_app ps tl None

let t_nat_const n =
  assert (n >= 0);
  t_const (Constant.int_const_of_int n) ty_int

let t_int_const n =
  t_const (Constant.int_const n) Ty.ty_int *)

let t_real_const ?pow2 ?pow5 s =
  t_const (Constant.real_const ?pow2 ?pow5 s) Ty.ty_real

(* let t_string_const s =
  t_const (Constant.string_const s) Ty.ty_str *)

(* exception InvalidIntegerLiteralType of ty
exception InvalidRealLiteralType of ty
exception InvalidStringLiteralType of ty

let check_literal c ty =
  let open Constant in
  let ts = match ty.ty_node, c with
    | Tyapp (ts,[]), _ -> ts
    | _, ConstInt _ -> raise (InvalidIntegerLiteralType ty)
    | _, ConstReal _ -> raise (InvalidRealLiteralType ty)
    | _, ConstStr _ -> raise (InvalidStringLiteralType ty) in
  match c, ts.ts_def with
  | ConstInt _, _ when ts_equal ts ts_int -> ()
  | ConstInt n, Range ir -> Number.check_range n ir
  | ConstInt _, _ -> raise (InvalidIntegerLiteralType ty)
  | ConstReal _, _ when ts_equal ts ts_real -> ()
  | ConstReal x, Float fp -> Number.check_float x fp
  | ConstReal _, _ -> raise (InvalidRealLiteralType ty)
  | ConstStr _, _ when ts_equal ts ts_str -> ()
  | ConstStr _, _ -> raise (InvalidStringLiteralType ty) *)

(* let t_const c ty = check_literal c ty; t_const c ty *)

(* let t_if f t1 t2 =
  t_ty_check t2 t1.t_ty;
  t_if (t_prop f) t1 t2

let t_let t1 (((v,_),t2) as bt) =
  vs_check v t1;
  t_let t1 bt t2.t_ty

exception EmptyCase

let t_case t bl =
  let tty = t_type t in
  let bty = match bl with
    | ((_,_),tbr) :: _ -> tbr.t_ty
    | _ -> raise EmptyCase
  in
  let t_check_branch ((p,_),tbr) =
    ty_equal_check tty p.pat_ty;
    t_ty_check tbr bty
  in
  List.iter t_check_branch bl;
  t_case t bl bty

let t_eps (((v,_),f) as bf) =
  ignore (t_prop f);
  t_eps bf (Some v.vs_ty)

let t_quant q ((((vl,_),_),f) as qf) =
  if vl = [] then f else t_quant q qf

let t_binary op f1 f2 = t_binary op (t_prop f1) (t_prop f2)
let t_not f = t_not (t_prop f)

let t_forall  = t_quant Tforall
let t_exists  = t_quant Texists
let t_and     = t_binary Tand
let t_or      = t_binary Tor
let t_implies = t_binary Timplies
let t_iff     = t_binary Tiff

let rec t_and_l = function
  | [] -> t_true
  | [f] -> f
  | f::fl -> t_and f (t_and_l fl)

let rec t_or_l = function
  | [] -> t_false
  | [f] -> f
  | f::fl -> t_or f (t_or_l fl) *)

let asym_split = create_attribute "asym_split"
let stop_split = create_attribute "stop_split"

let t_and_asym t1 t2 = t_and (t_attr_add asym_split t1) t2
let t_or_asym  t1 t2 = t_or  (t_attr_add asym_split t1) t2

let rec t_and_asym_l = function
  | [] -> t_true
  | [f] -> f
  | f::fl -> t_and_asym f (t_and_asym_l fl)

let rec t_or_asym_l = function
  | [] -> t_false
  | [f] -> f
  | f::fl -> t_or_asym f (t_or_asym_l fl)

(* closing constructors *)

(* let t_quant_close q vl tl f =
  if vl = [] then t_prop f else t_quant q (t_close_quant vl tl f)

let t_forall_close = t_quant_close Tforall
let t_exists_close = t_quant_close Texists

let t_let_close v t1 t2 = t_let t1 (t_close_bound v t2)
let t_case_close t l = t_case t (List.map (fun (p,e) -> t_close_branch p e) l)
let t_eps_close v f = t_eps (t_close_bound v f) *)

(* built-in symbols *)

(* let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh (op_infix "=")) [v; v]*)

let ps_ignore =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "ignore'term") [v]

(*let t_equ t1 t2 = ps_app ps_equ [t1; t2]
let t_neq t1 t2 = t_not (ps_app ps_equ [t1; t2])

let fs_bool_true  = create_fsymbol ~constr:(BigInt.of_int 2) (id_fresh "True")  [] ty_bool
let fs_bool_false = create_fsymbol ~constr:(BigInt.of_int 2) (id_fresh "False") [] ty_bool

let t_bool_true  = fs_app fs_bool_true [] ty_bool
let t_bool_false = fs_app fs_bool_false [] ty_bool

let to_prop t =
  match t.t_ty with
  | Some _ ->
    if t_equal t t_bool_true then t_true
    else if t_equal t t_bool_false then t_false
    else t_attr_copy t (t_equ t t_bool_true)
  | None -> t *)

let fs_tuple_ids = Hid.create 17

let fs_tuple = Hint.memo 17 (fun n ->
  let ts = ts_tuple (BigInt.of_int n) in (*JOSH of_int*)
  let tl = List.map ty_var ts.ts_args in
  let ty = ty_app ts tl in
  let attrs = Sattr.singleton builtin_attr in
  let id = id_fresh ~attrs ("Tuple" ^ string_of_int n) in
  let fs = create_fsymbol ~constr:BigInt.one id tl ty in
  Hid.add fs_tuple_ids fs.ls_name n;
  fs)

let is_fs_tuple fs =
  BigInt.eq fs.ls_constr BigInt.one && Hid.mem fs_tuple_ids fs.ls_name

let is_fs_tuple_id id =
  try Some (Hid.find fs_tuple_ids id) with Not_found -> None

let t_tuple tl =
  let ty = ty_tuple (List.map t_type tl) in
  fs_app (fs_tuple (List.length tl)) tl ty

(* let fs_func_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_b = ty_var (create_tvsymbol (id_fresh "b")) in
  let id = id_fresh (op_infix "@") in
  create_fsymbol id [ty_func ty_a ty_b; ty_a] ty_b *)

(* let t_func_app fn t = t_app_infer fs_func_app [fn; t]
let t_pred_app pr t = t_equ (t_func_app pr t) t_bool_true

let t_func_app_l fn tl = List.fold_left t_func_app fn tl
let t_pred_app_l pr tl = t_equ (t_func_app_l pr tl) t_bool_true *)

let ps_acc =
  let alpha = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_rel = ty_func alpha (ty_pred alpha) in
  create_psymbol (id_fresh "acc") [ty_rel;alpha]

let ps_wf =
  let alpha = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_rel = ty_func alpha (ty_pred alpha) in
  create_psymbol (id_fresh "well_founded") [ty_rel]

(** Term library *)

(* generic map over types, symbols and variables *)

let gen_fresh_vsymbol fnT v =
  let ty = fnT v.vs_ty in
  if ty_equal ty v.vs_ty then v else
  create_vsymbol (id_clone v.vs_name) ty

let gen_vs_rename fnT h v =
  let u = gen_fresh_vsymbol fnT v in
  Mvs.add v u h, u

let gen_vl_rename fnT h vl =
  Lists.map_fold_left (gen_vs_rename fnT) h vl

let gen_pat_rename fnT fnL h p =
  let add_vs v () = gen_fresh_vsymbol fnT v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_gen_map fnT fnL m p in
  Mvs.union (fun _ _ t -> Some t) h m, p

let gen_bnd_rename fnT fnE h b =
  let add_bv v n m = Mvs.add (Mvs.find v h) n m in
  let bvs = Mvs.fold add_bv b.bv_vars Mvs.empty in
  let add_bs v t (nh, m) =
    let nh,v = gen_vs_rename fnT nh v in
    nh, Mvs.add v (fnE t) m
  in
  let h,bsb = Mvs.fold add_bs Mvs.empty (h,Mvs.empty) in
  h, { bv_vars = bvs }

let rec t_gen_map fnT fnL m t =
  let fn = t_gen_map fnT fnL m in
  t_attr_copy t (match t.t_node with
    | Tvar v ->
        let u = Mvs.find_def v v m in
        ty_equal_check (fnT v.vs_ty) u.vs_ty;
        t_var u
    | Tconst c ->
        t_const c (fnT (Option.get t.t_ty))
    | Tapp (fs, tl) ->
        t_app (fnL fs) (List.map fn tl) (Option.map fnT t.t_ty)
    | Tif (f, t1, t2) ->
        t_if (fn f) (fn t1) (fn t2)
    | Tlet (t1, ((u,b),t2)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_let (fn t1) ((u, b), t_gen_map fnT fnL m t2)
    | Tcase (t1, bl) ->
        let fn_br ((p,b),t2) =
          let m,b = gen_bnd_rename fnT fn m b in
          let m,p = gen_pat_rename fnT fnL m p in
          ((p, b), t_gen_map fnT fnL m t2)
        in
        t_case (fn t1) (List.map fn_br bl)
    | Teps ((u,b),f) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_eps ((u, b), t_gen_map fnT fnL m f)
    | Tquant (q, (((vl,b),tl),f)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,vl = gen_vl_rename fnT m vl in
        let fn = t_gen_map fnT fnL m in
        t_quant q (((vl, b), tr_map fn tl), fn f)
    | Tbinop (op, f1, f2) ->
        t_binary op (fn f1) (fn f2)
    | Tnot f1 ->
        t_not (fn f1)
    | Ttrue | Tfalse ->
        t)

let t_gen_map fnT fnL mapV t = t_gen_map (Wty.memoize 17 fnT) fnL mapV t

(* map over type and logic symbols *)

let gen_mapV fnT = Mvs.mapi (fun v _ -> gen_fresh_vsymbol fnT v)

let t_s_map fnT fnL t = t_gen_map fnT fnL (gen_mapV fnT (t_vars t)) t

(* simultaneous substitution into types and terms *)

let t_subst_types mapT mapV t =
  let fnT = ty_inst mapT in
  let m = gen_mapV fnT (t_vars t) in
  let t = t_gen_map fnT (fun ls -> ls) m t in
  let add _ v t m = vs_check v t; Mvs.add v t m in
  let m = Mvs.fold2_inter add m mapV Mvs.empty in
  (m,t)

let t_ty_subst mapT mapV t =
  let m,t = t_subst_types mapT mapV t in
  t_subst_unsafe m t

(* fold over symbols *)

(* let rec t_gen_fold fnT fnL acc t =
  let fn = t_gen_fold fnT fnL in
  let acc = Opt.fold fnT acc t.t_ty in
  match t.t_node with
  | Tconst _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left fn (fnL acc f) tl
  | Tif (f, t1, t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (t1, ((_,b),t2)) -> fn (fn acc t1) t2
  | Tcase (t1, bl) ->
      let branch acc ((p,b),t) =
        fn (pat_gen_fold fnT fnL acc p) t in
      List.fold_left branch (fn acc t1) bl
  | Teps ((_,b),f) -> fn acc f
  | Tquant (_, (((vl,b),tl),f1)) ->
      (* these variables (and their types) may never appear below *)
      let acc = List.fold_left (fun a v -> fnT a v.vs_ty) acc vl in
      fn (tr_fold fn acc tl) f1
  | Tbinop (_, f1, f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc

let t_s_fold = t_gen_fold *)

let t_s_all prT prL t = Util.alld t_s_fold prT prL t
let t_s_any prT prL t = Util.anyd t_s_fold prT prL t

(* map/fold over types in terms and formulas *)

let t_ty_map fn t = t_s_map fn (fun ls -> ls) t

(* let t_ty_fold fn acc t = t_s_fold fn Util.const acc t *)

(* let t_ty_freevars = t_ty_fold ty_freevars *)

(* map/fold over applications in terms and formulas (but not in patterns!) *)

let rec t_app_map fn t =
  let t = t_map_unsafe (t_app_map fn) t in
  match t.t_node with
    | Tapp (ls,tl) ->
        let ls = fn ls (List.map t_type tl) t.t_ty in
        t_attr_copy t (t_app ls tl t.t_ty)
    | _ -> t

let rec t_app_fold fn acc t =
  let acc = t_fold_unsafe (t_app_fold fn) acc t in
  match t.t_node with
    | Tapp (ls,tl) -> fn acc ls (List.map t_type tl) t.t_ty
    | _ -> acc

(* Fold over pattern matching *)

let rec t_case_fold fn acc t =
  let acc = t_fold_unsafe (t_case_fold fn) acc t in
  match t.t_node with
    | Tcase({ t_ty = Some({ty_node = Tyapp (tys, tyl)})}, bl) ->
       let error () = failwith "t_case_fold: compiled pattern matching required." in
       let check_branch = function
         | (({pat_node = Pwild}, _), _) -> ()
         | (({pat_node = Papp (_, args)}, _), _) ->
            List.iter (function {pat_node = Pvar _} -> () | _ -> error ()) args
         | _ -> error ()
       in
       List.iter check_branch bl;
       fn acc tys tyl t.t_ty
    | Tcase(_, _) -> assert false
    | _ -> acc

(* Type- and binding-safe traversal *)

let t_map fn t = match t.t_node with
  | Tlet (t1, b) ->
      let u,t2 = t_open_bound b in
      let s1 = fn t1 and s2 = fn t2 in
      if s2 == t2
        then if s1 == t1 then t
          else t_attr_copy t (t_let s1 b)
        else t_attr_copy t (t_let_close u s1 s2)
  | Tcase (t1, bl) ->
      let s1 = fn t1 in
      let brn same b =
        let p,t = t_open_branch b in
        let s = fn t in
        if s == t then same, b
          else false, t_close_branch p s
      in
      let same, bl = Lists.map_fold_left brn true bl in
      if s1 == t1 && same then t
        else t_attr_copy t (t_case s1 bl)
  | Teps b ->
      let u,t1 = t_open_bound b in
      let s1 = fn t1 in
      if s1 == t1 then t
        else t_attr_copy t (t_eps_close u s1)
  | Tquant (q, b) ->
      let vl,tl,f1 = t_open_quant b in
      let g1 = fn f1 and sl = tr_map fn tl in
      if g1 == f1 && List.for_all2 (List.for_all2 (==)) sl tl then t
        else t_attr_copy t (t_quant_close q vl sl g1)
  | _ ->
      t_map_unsafe fn t

let t_map fn = t_map (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)

(* safe opening fold *)

let t_fold fn acc t = match t.t_node with
  | Tlet (t1, b) ->
      let _,t2 = t_open_bound b in fn (fn acc t1) t2
  | Tcase (t1, bl) ->
      let brn acc b = let _,t = t_open_branch b in fn acc t in
      List.fold_left brn (fn acc t1) bl
  | Teps b ->
      let _,f = t_open_bound b in fn acc f
  | Tquant (_, b) ->
      let _, tl, f1 = t_open_quant b in tr_fold fn (fn acc f1) tl
  | _ -> t_fold_unsafe fn acc t

let t_iter fn t = t_fold (fun () t -> fn t) () t

let t_all pr t = Util.all t_fold pr t
let t_any pr t = Util.any t_fold pr t

(* safe opening map_fold *)

let t_map_fold fn acc t = match t.t_node with
  | Tlet (t1, b) ->
      let acc, s1 = fn acc t1 in
      let u,t2 = t_open_bound b in
      let acc, s2 = fn acc t2 in
      acc, if s2 == t2
        then if s1 == t1 then t
          else t_attr_copy t (t_let s1 b)
        else t_attr_copy t (t_let_close u s1 s2)
  | Tcase (t1, bl) ->
      let acc, s1 = fn acc t1 in
      let brn (acc,same) b =
        let p,t = t_open_branch b in
        let acc, s = fn acc t in
        if s == t then (acc,same), b
          else (acc,false), t_close_branch p s
      in
      let (acc,same), bl = Lists.map_fold_left brn (acc,true) bl in
      acc, if s1 == t1 && same then t
        else t_attr_copy t (t_case s1 bl)
  | Teps b ->
      let u,t1 = t_open_bound b in
      let acc, s1 = fn acc t1 in
      acc, if s1 == t1 then t
        else t_attr_copy t (t_eps_close u s1)
  | Tquant (q, b) ->
      let vl,tl,f1 = t_open_quant b in
      let acc, sl = tr_map_fold fn acc tl in
      let acc, g1 = fn acc f1 in
      acc, if g1 == f1 && List.for_all2 (List.for_all2 (==)) sl tl
        then t else t_attr_copy t (t_quant_close q vl sl g1)
  | _ -> t_map_fold_unsafe fn acc t

let t_map_fold fn = t_map_fold (fun acc t ->
  let res = fn acc t in t_ty_check (snd res) t.t_ty; res)

(* polarity map *)

let t_map_sign fn sign f = t_attr_copy f (match f.t_node with
  | Tbinop (Timplies, f1, f2) ->
      t_implies (fn (not sign) f1) (fn sign f2)
  | Tbinop (Tiff, f1, f2) ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2p = fn sign f2 in let f2n = fn (not sign) f2 in
      if t_equal f1p f1n && t_equal f2p f2n then t_iff f1p f2p
      else if sign
        then t_and (t_implies f1n f2p) (t_implies f2n f1p)
        else t_implies (t_or f1n f2n) (t_and f1p f2p)
  | Tnot f1 ->
      t_not (fn (not sign) f1)
  | Tif (f1, f2, f3) when f.t_ty = None ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2 = fn sign f2 in let f3 = fn sign f3 in
      if t_equal f1p f1n then t_if f1p f2 f3 else if sign
        then t_and (t_implies f1n f2) (t_implies (t_not f1p) f3)
        else t_or (t_and f1p f2) (t_and (t_not f1n) f3)
  | Tif _
  | Teps _ -> failwith "t_map_sign: cannot determine polarity"
  | _ -> t_map (fn sign) f)

(* continuation-passing traversal *)

let rec list_map_cont fnL contL = function
  | e::el ->
      let cont_l e el = contL (e::el) in
      let cont_e e = list_map_cont fnL (cont_l e) el in
      fnL cont_e e
  | [] ->
      contL []

let t_map_cont fn contT t =
  let contT e = contT (t_attr_copy t e) in
  match t.t_node with
  | Tvar _ | Tconst _ -> contT t
  | Tapp (fs, tl) ->
      let cont_app tl = contT (t_app fs tl t.t_ty) in
      list_map_cont fn cont_app tl
  | Tif (f, t1, t2) ->
      let cont_else f t1 t2 = contT (t_if f t1 t2) in
      let cont_then f t1 = fn (cont_else f t1) t2 in
      let cont_if f = fn (cont_then f) t1 in
      fn cont_if f
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let cont_in t1 t2 = contT (t_let t1 (close u t2)) in
      let cont_let t1 = fn (cont_in t1) t2 in
      fn cont_let t1
  | Tcase (t1, bl) ->
      let fnB contB b =
        let pat,t,close = t_open_branch_cb b in
        fn (fun t -> contB (close pat t)) t
      in
      let cont_with t1 bl = contT (t_case t1 bl) in
      let cont_case t1 = list_map_cont fnB (cont_with t1) bl in
      fn cont_case t1
  | Teps b ->
      let u,f,close = t_open_bound_cb b in
      let cont_eps f = contT (t_eps (close u f)) in
      fn cont_eps f
  | Tquant (q, b) ->
      let vl, tl, f1, close = t_open_quant_cb b in
      let cont_dot tl f1 = contT (t_quant q (close vl tl f1)) in
      let cont_quant tl = fn (cont_dot tl) f1 in
      list_map_cont (list_map_cont fn) cont_quant tl
  | Tbinop (op, f1, f2) ->
      let cont_r f1 f2 = contT (t_binary op f1 f2) in
      let cont_l f1 = fn (cont_r f1) f2 in
      fn cont_l f1
  | Tnot f1 ->
      let cont_not f1 = contT (t_not f1) in
      fn cont_not f1
  | Ttrue | Tfalse -> contT t

let t_map_cont fn = t_map_cont (fun cont t ->
  fn (fun e -> t_ty_check e t.t_ty; cont e) t)

(* map/fold over free variables *)

let t_v_map fn t =
  let fn v _ = let res = fn v in vs_check v res; res in
  t_subst_unsafe (Mvs.mapi fn (t_vars t)) t

(* let bnd_v_fold fn acc b = Mvs.fold (fun v _ acc -> fn acc v) b.bv_vars acc

let bound_v_fold fn acc ((_,b),_) = bnd_v_fold fn acc b

let rec t_v_fold fn acc t = match t.t_node with
  | Tvar v -> fn acc v
  | Tlet (e,b) -> bound_v_fold fn (t_v_fold fn acc e) b
  | Tcase (e,bl) -> List.fold_left (bound_v_fold fn) (t_v_fold fn acc e) bl
  | Teps b -> bound_v_fold fn acc b
  | Tquant (_,(((_,b),_),_)) -> bnd_v_fold fn acc b
  | _ -> t_fold_unsafe (t_v_fold fn) acc t *)

(* let t_v_all pr t = Util.all t_v_fold pr t *)
let t_v_any pr t = Util.any t_v_fold pr t

let t_closed t = t_v_all Util.ffalse t

(* let bnd_v_count fn acc b = Mvs.fold (fun v n acc -> fn acc v n) b.bv_vars acc

let bound_v_count fn acc ((_,b),_) = bnd_v_count fn acc b *)

(* let rec t_v_count fn acc t = match t.t_node with
  | Tvar v -> fn acc v BigInt.one
  | Tlet (e,b) -> bound_v_count fn (t_v_count fn acc e) b
  | Tcase (e,bl) -> List.fold_left (bound_v_count fn) (t_v_count fn acc e) bl
  | Teps b -> bound_v_count fn acc b
  | Tquant (_,(((_,b),_),_)) -> bnd_v_count fn acc b
  | _ -> t_fold_unsafe (t_v_count fn) acc t *)

(* let t_v_occurs v t =
  t_v_count (fun c u n -> if vs_equal u v then BigInt.add c n else c) BigInt.zero t *)

(* replaces variables with terms in term [t] using map [m] *)

(* let t_subst m t = Mvs.iter vs_check m; t_subst_unsafe m t

let t_subst_single v t1 t = t_subst (Mvs.singleton v t1) t *)

(* set of free variables *)

let t_freevars = add_t_vars

(* occurrence check *)

let rec t_occurs r t =
  t_equal r t || t_any (t_occurs r) t

(* substitutes term [t2] for term [t1] in term [t] *)

let rec t_replace t1 t2 t =
  if t_equal t t1 then t2 else t_map (t_replace t1 t2) t

let t_replace t1 t2 t =
  t_ty_check t2 t1.t_ty;
  t_replace t1 t2 t

(* lambdas *)

let t_lambda vl trl t =
  let ty = Option.value ~default:ty_bool t.t_ty in
  let add_ty v ty = ty_func v.vs_ty ty in
  let ty = List.fold_right add_ty vl ty in
  let fc = create_vsymbol (id_fresh "fc") ty in
  let copy_loc e = if t.t_loc = None then e
    else t_attr_set ?loc:t.t_loc e.t_attrs e in
  let mk_t_var v = if v.vs_name.id_loc = None then t_var v
    else t_attr_set ?loc:v.vs_name.id_loc Sattr.empty (t_var v) in
  let add_arg h v = copy_loc (t_func_app h (mk_t_var v)) in
  let h = List.fold_left add_arg (mk_t_var fc) vl in
  let f = match t.t_ty with
    | Some _ -> t_equ h t
    | None   -> t_iff (copy_loc (t_equ h t_bool_true)) t in
  t_eps_close fc (copy_loc (t_forall_close vl trl (copy_loc f)))

let t_lambda vl trl t =
  let t = match t.t_node with
    | Tapp (ps,[l;{t_node = Tapp (fs,[])}])
      when ls_equal ps ps_equ && ls_equal fs fs_bool_true ->
        t_attr_copy t l
    | _ -> t in
  if vl <> [] then t_lambda vl trl t
  else if t.t_ty <> None then t
  else t_if t t_bool_true t_bool_false

let t_open_lambda t = match t.t_ty, t.t_node with
  | Some {ty_node = Tyapp (ts,_)}, Teps fb when ts_equal ts ts_func ->
      let fc,f = t_open_bound fb in
      let vl,trl,f = match f.t_node with
        | Tquant (Tforall,fq) -> t_open_quant fq
        | _ -> [], [], t (* fail the next check *) in
      let h,e = match f.t_node with
        | Tapp (ps,[h;e]) when ls_equal ps ps_equ -> h, e
        | Tbinop (Tiff,{t_node = Tapp (ps,[h;{t_node = Tapp (fs,[])}])},e)
          when ls_equal ps ps_equ && ls_equal fs fs_bool_true -> h, e
        | _ -> t, t (* fail the next check *) in
      let rec check h xl = match h.t_node, xl with
        | Tapp (fs,[h;{t_node = Tvar u}]), x::xl
          when ls_equal fs fs_func_app && vs_equal u x -> check h xl
        | Tvar u, [] when vs_equal u fc && BigInt.is_zero (t_v_occurs u e) -> vl, trl, e
        | _ -> [], [], t in
      check h (List.rev vl)
  | _ -> [], [], t

(* it is rather tricky to check if a term is a lambda without properly
   opening the binders. The deferred substitution in the quantifier
   may obscure the closure variable or, on the contrary, introduce it
   on the RHS of the definition, making it recursive. We cannot simply
   reject such deferred substitutions, because the closure variable is
   allowed in the triggers and it can appear there via the deferred
   substitution, why not? Therefore, t_is_lambda is a mere shim around
   t_open_lambda. *)
let t_is_lambda t = let vl,_,_ = t_open_lambda t in vl <> []

let t_open_lambda_cb t =
  let vl, trl, e = t_open_lambda t in
  let close vl' trl' e' =
    if e == e' &&
      Lists.equal (Lists.equal ((==) : term -> term -> bool)) trl trl' &&
      Lists.equal vs_equal vl vl'
    then t else t_lambda vl' trl' e' in
  vl, trl, e, close

let t_closure ls tyl ty =
  let mk_v i ty = create_vsymbol (id_fresh ("y" ^ string_of_int i)) ty in
  let vl = List.mapi mk_v tyl in
  let t = t_app ls (List.map t_var vl) ty in
  t_lambda vl [] t

let t_app_partial ls tl tyl ty =
  if tyl = [] then t_app ls tl ty else
  match tl with
  | [t] when ls_equal ls fs_func_app -> t
  | _ ->
      let cons t tyl = t_type t :: tyl in
      let tyl = List.fold_right cons tl tyl in
      t_func_app_l (t_closure ls tyl ty) tl

let rec t_app_beta_l lam tl =
  if tl = [] then lam else
  let vl, trl, e = t_open_lambda lam in
  if vl = [] then t_func_app_l lam tl else
  let rec add m vl tl = match vl, tl with
    | [], tl ->
        t_app_beta_l (t_subst_unsafe m e) tl
    | vl, [] ->
        let trl = List.map (List.map (t_subst_unsafe m)) trl in
        t_lambda vl trl (t_subst_unsafe m e)
    | v::vl, t::tl ->
        vs_check v t; add (Mvs.add v t m) vl tl in
  add Mvs.empty vl tl

let t_func_app_beta_l lam tl =
  let e = t_app_beta_l lam tl in
  if e.t_ty = None then t_if e t_bool_true t_bool_false else e

let t_pred_app_beta_l lam tl =
  let e = t_app_beta_l lam tl in
  if e.t_ty = None then e else t_equ e t_bool_true

let t_func_app_beta lam t = t_func_app_beta_l lam [t]
let t_pred_app_beta lam t = t_pred_app_beta_l lam [t]

(* constructors with propositional simplification *)

(* let t_not_simp f = match f.t_node with
  | Ttrue  -> t_attr_copy f t_false
  | Tfalse -> t_attr_copy f t_true
  | Tnot g -> t_attr_copy f g
  | _      -> t_not f *)

(* let t_and_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> t_attr_remove asym_split f1
  | Tfalse, _ -> t_attr_remove asym_split f1
  | _, Tfalse -> f2
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_and f1 f2 *)

let t_and_simp_l l = List.fold_right t_and_simp l t_true

(* let t_or_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> t_attr_remove asym_split f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> t_attr_remove asym_split f1
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_or f1 f2 *)

let t_or_simp_l l = List.fold_right t_or_simp l t_false

let t_and_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> t_attr_remove asym_split f1
  | Tfalse, _ -> t_attr_remove asym_split f1
  | _, Tfalse -> f2
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_and_asym f1 f2

let t_and_asym_simp_l l = List.fold_right t_and_asym_simp l t_true

let t_or_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> t_attr_remove asym_split f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> t_attr_remove asym_split f1
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_or_asym f1 f2

let t_or_asym_simp_l l = List.fold_right t_or_asym_simp l t_false

(* let t_implies_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f2
  | Tfalse, _ -> t_attr_copy f1 t_true
  | _, Tfalse -> t_not_simp f1
  | _, _ when t_equal f1 f2 -> t_attr_copy f1 t_true
  | _, _ -> t_implies f1 f2 *)

(* let t_iff_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f1
  | Tfalse, _ -> t_not_simp f2
  | _, Tfalse -> t_not_simp f1
  | _, _ when t_equal f1 f2 -> t_attr_copy f1 t_true
  | _, _ -> t_iff f1 f2 *)

let t_binary_simp op = match op with
  | Tand     -> t_and_simp
  | Tor      -> t_or_simp
  | Timplies -> t_implies_simp
  | Tiff     -> t_iff_simp

let t_if_simp f1 f2 f3 = match f1.t_node, f2.t_node, f3.t_node with
  | Ttrue, _, _  -> f2
  | Tfalse, _, _ -> f3
  | _, Ttrue, _  -> t_implies_simp (t_not_simp f1) f3
  | _, Tfalse, _ -> t_and_asym_simp (t_not_simp f1) f3
  | _, _, Ttrue  -> t_implies_simp f1 f2
  | _, _, Tfalse -> t_and_asym_simp f1 f2
  | _, _, _ when t_equal f2 f3 -> f2
  | _, _, _ -> t_if f1 f2 f3


(* let small t = match t.t_node with
  | Tvar _ | Tconst _ -> true
(* NOTE: shouldn't we allow this?
  | Tapp (_,[]) -> true
*)
  | _ -> false *)

let v_copy_unused v =
  let id = v.vs_name in
  if Sattr.mem Ident.unused_attr id.id_attrs then v else
  let attrs = Sattr.singleton Ident.unused_attr in
  let attrs =
    try
      ignore (get_model_trace_attr ~attrs:id.id_attrs); attrs
    with Not_found ->
      Sattr.add (create_model_trace_attr id.id_string) attrs
  in
  let id' = id_derive ~attrs (id.id_string ^ unused_suffix) id in
  create_vsymbol id' v.vs_ty

let t_let_simp_keep_var ~keep e (((v,b),t) as bt) =
  let n = t_v_occurs v t in
  if BigInt.is_zero n then
    if keep then t_let_close (v_copy_unused v) e t else t
  else
  if BigInt.eq n BigInt.one || small e then begin
    vs_check v e;
    let t = t_subst_unsafe (Mvs.singleton v e) t in
    if keep then t_let_close (v_copy_unused v) e t else t
  end else
    t_let e bt

let t_let_simp = t_let_simp_keep_var ~keep:false

let t_let_close_simp_keep_var ~keep v e t =
  let n = t_v_occurs v t in
  if BigInt.is_zero n then
    if keep then t_let_close (v_copy_unused v) e t else t
  else
  if BigInt.eq n BigInt.one || small e then
    let t = t_subst_single v e t in
    if keep then t_let_close (v_copy_unused v) e t else t
  else
    t_let_close v e t

(* let t_let_close_simp = t_let_close_simp_keep_var ~keep:false *)

let t_case_simp t bl =
  let e0,tl = match bl with
    | [] -> raise EmptyCase
    | ((_,_),e0)::tl -> e0,tl in
  let e0_true = match e0.t_node with
    | Ttrue -> true | _ -> false in
  let e0_false = match e0.t_node with
    | Tfalse -> true | _ -> false in
  let is_e0 ((_,_),e) = match e.t_node with
    | Ttrue -> e0_true
    | Tfalse -> e0_false
    | _ -> t_equal e e0 in
  if t_closed e0 && List.for_all is_e0 tl then e0
  else t_case t bl

let t_case_close_simp t bl =
  let e0,tl = match bl with
    | [] -> raise EmptyCase
    | (_,e0)::tl -> e0,tl in
  let e0_true = match e0.t_node with
    | Ttrue -> true | _ -> false in
  let e0_false = match e0.t_node with
    | Tfalse -> true | _ -> false in
  let is_e0 (_,e) = match e.t_node with
    | Ttrue -> e0_true
    | Tfalse -> e0_false
    | _ -> t_equal e e0 in
  if t_closed e0 && List.for_all is_e0 tl then e0
  else t_case_close t bl

let t_quant_simp q ((((vl,_),_),f) as qf) =
  let fvs = t_vars f in
  let check v = Mvs.mem v fvs in
  if List.for_all check vl then
    t_quant q qf
  else
    let vl,tl,f = t_open_quant qf in
    let fvs = t_vars f in
    let check v = Mvs.mem v fvs in
    let vl = List.filter check vl in
    if vl = [] then f
    else t_quant_close q vl (List.filter (List.for_all (t_v_all check)) tl) f

(* let t_quant_close_simp q vl tl f =
  if vl = [] then f else
  let fvs = t_vars f in
  let check v = Mvs.mem v fvs in
  if List.for_all check vl then
    t_quant_close q vl tl f
  else
    let vl = List.filter check vl in
    if vl = [] then f
    else t_quant_close q vl (List.filter (List.for_all (t_v_all check)) tl) f *)

let t_forall_simp = t_quant_simp Tforall
let t_exists_simp = t_quant_simp Texists

(* let t_forall_close_simp = t_quant_close_simp Tforall
let t_exists_close_simp = t_quant_close_simp Texists *)

(* let t_equ_simp t1 t2 =
  if t_equal t1 t2 then t_true  else t_equ t1 t2 *)

let t_neq_simp t1 t2 =
  if t_equal t1 t2 then t_false else t_neq t1 t2

let t_forall_close_merge vs f = match f.t_node with
  | Tquant (Tforall, fq) ->
      let vs', trs, f = t_open_quant fq in
      t_forall_close (vs@vs') trs f
  | _ -> t_forall_close vs [] f

let t_exists_close_merge vs f = match f.t_node with
  | Tquant (Texists, fq) ->
      let vs', trs, f = t_open_quant fq in
      t_exists_close (vs@vs') trs f
  | _ -> t_exists_close vs [] f

let t_map_simp fn f = t_attr_copy f (match f.t_node with
  | Tapp (p, [t1;t2]) when ls_equal p ps_equ ->
      t_equ_simp (fn t1) (fn t2)
  | Tif (f1, f2, f3) ->
      t_if_simp (fn f1) (fn f2) (fn f3)
  | Tlet (t, b) ->
      let u,t2,close = t_open_bound_cb b in
      t_let_simp (fn t) (close u (fn t2))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      t_quant_simp q (close vl (tr_map fn tl) (fn f1))
  | Tbinop (op, f1, f2) ->
      t_binary_simp op (fn f1) (fn f2)
  | Tnot f1 ->
      t_not_simp (fn f1)
  | _ -> t_map fn f)


let t_map_simp fn = t_map_simp (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)


(** Traversal with separate functions for value-typed and prop-typed terms *)

module TermTF = struct
  let t_select fnT fnF e =
    if e.t_ty = None then fnF e else fnT e

  let t_selecti fnT fnF acc e =
    if e.t_ty = None then fnF acc e else fnT acc e

  let t_map fnT fnF = t_map (t_select fnT fnF)
  let t_fold fnT fnF = t_fold (t_selecti fnT fnF)
  let t_map_fold fnT fnF = t_map_fold (t_selecti fnT fnF)
  let t_all prT prF = t_all (t_select prT prF)
  let t_any prT prF = t_any (t_select prT prF)
  let t_map_simp fnT fnF = t_map_simp (t_select fnT fnF)
  let t_map_sign fnT fnF = t_map_sign (t_selecti fnT fnF)
  let t_map_cont fnT fnF = t_map_cont (t_selecti fnT fnF)
  let tr_map fnT fnF = tr_map (t_select fnT fnF)
  let tr_fold fnT fnF = tr_fold (t_selecti fnT fnF)
  let tr_map_fold fnT fnF = tr_map_fold (t_selecti fnT fnF)
end


let term_size t =
  let rec aux acc t =
    let acc' = BigInt.succ acc in
    assert (acc' > acc); (* to avoid integer overflow *) (*JOSH - don't need*)
    t_fold_unsafe aux acc' t
  in aux BigInt.zero t

let term_branch_size ((_,_),t) = term_size t



let rec remove_unused_in_term polarity t =
  t_attr_copy t (match t.t_node with
  | Tbinop (Timplies, t1, t2) ->
      t_implies_simp
        (remove_unused_in_term (not polarity) t1)
        (remove_unused_in_term polarity t2)
  | Tbinop (Tiff, t1, t2) ->
      let t1p = remove_unused_in_term polarity t1 in
      let t1n = remove_unused_in_term (not polarity) t1 in
      let t2p = remove_unused_in_term polarity t2 in
      let t2n = remove_unused_in_term (not polarity) t2 in
      if t_equal t1p t1n && t_equal t2p t2n then t_iff_simp t1p t2p
      else if polarity
        then t_and_simp (t_implies_simp t1n t2p) (t_implies_simp t2n t1p)
        else t_implies_simp (t_or_simp t1n t2n) (t_and_simp t1p t2p)
  | Tnot t1 ->
      t_not_simp (remove_unused_in_term (not polarity) t1)
  | Tlet(t,fb) ->
      let vs, t1, cb = t_open_bound_cb fb in
      let t1 = t_map_simp (remove_unused_in_term polarity) t1 in
      if Sattr.mem unused_attr vs.vs_name.id_attrs then t1
      else
        t_let_simp_keep_var ~keep:true t (cb vs t1)
  | (Tapp(ls,[{t_node=Tvar {vs_name = id; _ }; _ } ;_])
    | Tapp(ls,[{t_node=Tapp({ls_name = id;_} ,[]); _ };_]))
    when ls_equal ls ps_equ &&
         Sattr.mem unused_attr id.id_attrs ->
      if polarity then t_false else t_true
  | Tif (t1, t2, t3) when t.t_ty = None ->
      let t1p = remove_unused_in_term polarity t1 in
      let t1n = remove_unused_in_term (not polarity) t1 in
      let t2 = remove_unused_in_term polarity t2 in
      let t3 = remove_unused_in_term polarity t3 in
      if t_equal t1p t1n then t_if_simp t1p t2 t3 else
      if polarity
        then t_and_simp (t_implies_simp t1n t2) (t_implies_simp (t_not_simp t1p) t3)
        else t_or_simp (t_and_simp t1p t2) (t_and_simp (t_not_simp t1n) t3)
  | Tif _ | Teps _ -> t
  | _ -> t_map_simp (remove_unused_in_term polarity) t)
