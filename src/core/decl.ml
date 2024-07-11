open BinNums
open Common
open CoqHashtbl
open CoqUtil
open Weakhtbl
open Wstdlib
open Datatypes
open Ident
open Monads
open Specif
open State
open Term

open Ty
open Hashcons
open Pmap
open Zmap

type hack = tysymbol

type constructor = lsymbol * lsymbol option list

type data_decl = (ty_node_c ty_o) tysymbol_o * constructor list

type ls_defn = (lsymbol * (term_node term_o)) * BigInt.t list

type logic_decl = lsymbol * ls_defn

type prsymbol = { pr_name : ident }

(** val pr_name : prsymbol -> ident **)

let pr_name p =
  p.pr_name

(** val prsymbol_eqb : prsymbol -> prsymbol -> bool **)

let prsymbol_eqb p1 p2 =
  id_equal p1.pr_name p2.pr_name

module PropTag =
 struct
  type t = prsymbol

  (** val tag : prsymbol -> tag **)

  let tag pr =
    pr.pr_name.id_tag

  (** val equal : prsymbol -> prsymbol -> bool **)

  let equal =
    prsymbol_eqb
 end

module Prop1 = MakeMSWeak(PropTag)

module Spr = Prop1.S

module Mpr = Prop1.M

(** val pr_equal : prsymbol -> prsymbol -> bool **)

let pr_equal =
  prsymbol_eqb

(** val pr_hash : prsymbol -> BigInt.t **)

let pr_hash pr =
  id_hash pr.pr_name

(** val create_prsymbol : preid -> (BigInt.t, prsymbol) st **)

let create_prsymbol n =
  (@@) (fun i -> (fun x -> x) { pr_name = i }) (id_register n)

type ind_decl = lsymbol * (prsymbol * (term_node term_o)) list

type ind_sign =
| Ind
| Coind

type ind_list = ind_sign * ind_decl list

type prop_kind =
| Plemma
| Paxiom
| Pgoal

type prop_decl = (prop_kind, prsymbol, (term_node term_o)) ocaml_tup3

type decl_node =
| Dtype of (ty_node_c ty_o) tysymbol_o
| Ddata of data_decl list
| Dparam of lsymbol
| Dlogic of logic_decl list
| Dind of ind_list
| Dprop of prop_decl

type decl = { d_node : decl_node; d_news : Sid.t; d_tag : tag }

(** val d_node : decl -> decl_node **)

let d_node d =
  d.d_node

(** val d_news : decl -> Sid.t **)

let d_news d =
  d.d_news

(** val d_tag : decl -> tag **)

let d_tag d =
  d.d_tag

(** val constructor_eqb : constructor -> constructor -> bool **)

let constructor_eqb =
  tuple_eqb ls_equal (list_eqb (option_eqb ls_equal))

(** val data_decl_eqb : data_decl -> data_decl -> bool **)

let data_decl_eqb =
  tuple_eqb ts_equal (list_eqb constructor_eqb)

(** val ind_sign_beq : ind_sign -> ind_sign -> bool **)

let ind_sign_beq x y =
  match x with
  | Ind -> (match y with
            | Ind -> true
            | Coind -> false)
  | Coind -> (match y with
              | Ind -> false
              | Coind -> true)

(** val ind_sign_eq_dec : ind_sign -> ind_sign -> bool **)

let ind_sign_eq_dec x y =
  let b = ind_sign_beq x y in if b then true else false

(** val prop_kind_beq : prop_kind -> prop_kind -> bool **)

let prop_kind_beq x y =
  match x with
  | Plemma -> (match y with
               | Plemma -> true
               | _ -> false)
  | Paxiom -> (match y with
               | Paxiom -> true
               | _ -> false)
  | Pgoal -> (match y with
              | Pgoal -> true
              | _ -> false)

(** val prop_kind_eq_dec : prop_kind -> prop_kind -> bool **)

let prop_kind_eq_dec x y =
  let b = prop_kind_beq x y in if b then true else false

(** val ind_sign_eqb : ind_sign -> ind_sign -> bool **)

let ind_sign_eqb =
  ind_sign_beq

(** val prop_kind_eqb : prop_kind -> prop_kind -> bool **)

let prop_kind_eqb =
  prop_kind_beq

(** val ls_defn_eqb : ls_defn -> ls_defn -> bool **)

let ls_defn_eqb =
  tuple_eqb (tuple_eqb ls_equal term_eqb) (list_eqb BigInt.eq)

(** val logic_decl_eqb : logic_decl -> logic_decl -> bool **)

let logic_decl_eqb =
  tuple_eqb ls_equal ls_defn_eqb

(** val ind_decl_eqb : ind_decl -> ind_decl -> bool **)

let ind_decl_eqb =
  tuple_eqb ls_equal (list_eqb (tuple_eqb prsymbol_eqb term_eqb))

(** val decl_node_eqb : decl_node -> decl_node -> bool **)

let decl_node_eqb d1 d2 =
  match d1 with
  | Dtype s1 -> (match d2 with
                 | Dtype s2 -> ts_equal s1 s2
                 | _ -> false)
  | Ddata l1 ->
    (match d2 with
     | Ddata l2 -> list_eqb data_decl_eqb l1 l2
     | _ -> false)
  | Dparam s1 -> (match d2 with
                  | Dparam s2 -> ls_equal s1 s2
                  | _ -> false)
  | Dlogic l1 ->
    (match d2 with
     | Dlogic l2 -> list_eqb logic_decl_eqb l1 l2
     | _ -> false)
  | Dind i ->
    let (s1, l1) = i in
    (match d2 with
     | Dind i0 ->
       let (s2, l2) = i0 in
       (&&) (ind_sign_eqb s1 s2) (list_eqb ind_decl_eqb l1 l2)
     | _ -> false)
  | Dprop p1 ->
    (match d2 with
     | Dprop p2 ->
       let (p, f1) = (fun (x, y, z) -> ((x, y), z)) p1 in
       let (k1, pr1) = p in
       let (p0, f2) = (fun (x, y, z) -> ((x, y), z)) p2 in
       let (k2, pr2) = p0 in
       (&&) ((&&) (prop_kind_eqb k1 k2) (pr_equal pr1 pr2)) (term_eqb f1 f2)
     | _ -> false)

(** val decl_eqb : decl -> decl -> bool **)

let decl_eqb d1 d2 =
  (&&)
    ((&&) (decl_node_eqb d1.d_node d2.d_node) (Sid.equal d1.d_news d2.d_news))
    (tag_equal d1.d_tag d2.d_tag)

module DeclHash =
 struct
  type t = decl

  (** val eq_ld : logic_decl -> logic_decl -> bool **)

  let eq_ld x1 x2 =
    (&&) (ls_equal (fst x1) (fst x2))
      (t_equal_strict (snd (fst (snd x1))) (snd (fst (snd x2))))

  (** val eq_iax :
      (prsymbol * (term_node term_o)) -> (prsymbol * (term_node term_o)) ->
      bool **)

  let eq_iax =
    tuple_eqb pr_equal t_equal_strict

  (** val eq_ind1 : ind_decl -> ind_decl -> bool **)

  let eq_ind1 =
    tuple_eqb ls_equal (list_eqb eq_iax)

  (** val equal : decl -> decl -> bool **)

  let equal d1 d2 =
    match d1.d_node with
    | Dtype s1 ->
      (match d2.d_node with
       | Dtype s2 -> ts_equal s1 s2
       | _ -> false)
    | Ddata l1 ->
      (match d2.d_node with
       | Ddata l2 -> list_eqb data_decl_eqb l1 l2
       | _ -> false)
    | Dparam s1 ->
      (match d2.d_node with
       | Dparam s2 -> ls_equal s1 s2
       | _ -> false)
    | Dlogic l1 ->
      (match d2.d_node with
       | Dlogic l2 -> list_eqb eq_ld l1 l2
       | _ -> false)
    | Dind i ->
      let (s1, l1) = i in
      (match d2.d_node with
       | Dind i0 ->
         let (s2, l2) = i0 in
         (&&) (ind_sign_eqb s1 s2) (list_eqb eq_ind1 l1 l2)
       | _ -> false)
    | Dprop p1 ->
      (match d2.d_node with
       | Dprop p2 ->
         let (p, f1) = (fun (x, y, z) -> ((x, y), z)) p1 in
         let (k1, pr1) = p in
         let (p0, f2) = (fun (x, y, z) -> ((x, y), z)) p2 in
         let (k2, pr2) = p0 in
         (&&) ((&&) (prop_kind_eqb k1 k2) (pr_equal pr1 pr2))
           (t_equal_strict f1 f2)
       | _ -> false)

  (** val cs_hash : constructor -> BigInt.t **)

  let cs_hash x =
    combine_big_list (combine_big_option ls_hash) (ls_hash (fst x)) (snd x)

  (** val hs_td : data_decl -> BigInt.t **)

  let hs_td x =
    combine_big_list cs_hash (ts_hash (fst x)) (snd x)

  (** val hs_ld : logic_decl -> BigInt.t **)

  let hs_ld x =
    combine_big (ls_hash (fst x)) (t_hash_strict (snd (fst (snd x))))

  (** val hs_prop : (prsymbol * (term_node term_o)) -> BigInt.t **)

  let hs_prop x =
    combine_big (pr_hash (fst x)) (t_hash_strict (snd x))

  (** val hs_ind : ind_decl -> BigInt.t **)

  let hs_ind x =
    combine_big_list hs_prop (ls_hash (fst x)) (snd x)

  (** val hs_kind : prop_kind -> BigInt.t **)

  let hs_kind = function
  | Plemma -> (BigInt.of_int 11)
  | Paxiom -> (BigInt.of_int 13)
  | Pgoal -> (BigInt.of_int 17)

  (** val hash : decl -> BigInt.t **)

  let hash d =
    match d.d_node with
    | Dtype s -> ts_hash s
    | Ddata l -> combine_big_list hs_td (BigInt.of_int 3) l
    | Dparam s -> ls_hash s
    | Dlogic l -> combine_big_list hs_ld (BigInt.of_int 5) l
    | Dind i -> let (_, l) = i in combine_big_list hs_ind (BigInt.of_int 7) l
    | Dprop y ->
      let (p, f) = (fun (x, y, z) -> ((x, y), z)) y in
      let (k, pr) = p in combine_big (hs_kind k) (hs_prop (pr, f))

  (** val tag : tag -> decl -> decl **)

  let tag n d =
    { d_node = d.d_node; d_news = d.d_news; d_tag = (create_tag n) }
 end

module Hsdecl = Make(DeclHash)

module DeclTag =
 struct
  type t = decl

  (** val tag : decl -> tag **)

  let tag d =
    d.d_tag

  (** val equal : decl -> decl -> bool **)

  let equal =
    decl_eqb
 end

module Decl1 = MakeMSWeak(DeclTag)

module Sdecl = Decl1.S

module Mdecl = Decl1.M

(** val d_equal : decl -> decl -> bool **)

let d_equal =
  decl_eqb

(** val d_hash : decl -> tag **)

let d_hash d =
  tag_hash d.d_tag

(** val mk_decl : decl_node -> Sid.t -> (decl hashcons_ty, decl) st **)

let mk_decl node news =
  let d = { d_node = node; d_news = news; d_tag = dummy_tag } in
  (match node with
   | Dprop p ->
     let (p0, _) = (fun (x, y, z) -> ((x, y), z)) p in
     let (x, _) = p0 in
     (match x with
      | Pgoal -> Hsdecl.unique d
      | _ -> Hsdecl.hashcons d)
   | _ -> Hsdecl.hashcons d)
exception UnboundVar of vsymbol
exception UnexpectedProjOrConstr of lsymbol
exception NoTerminationProof of lsymbol

exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadLogicDecl of lsymbol * lsymbol
exception BadConstructor of lsymbol

exception BadRecordField of lsymbol
exception RecordFieldMissing of lsymbol
exception DuplicateRecordField of lsymbol

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

exception NonPositiveTypeDecl of tysymbol * lsymbol * ty

exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident

exception NonFoundedTypeDecl of tysymbol
open Common
open CoqUtil
open Weakhtbl
open Datatypes

open Ident
open IntFuncs
open List0
open Monads
open Term

open Ty


(** val check_fvs : (term_node term_o) -> (term_node term_o) errorM **)

let check_fvs f =
  (@@) (fun _ -> t_prop f)
    (match t_v_fold (fun _ vs -> Some vs) None f with
     | Some v -> raise (UnboundVar v)
     | None ->  ())

(** val check_vl : ty_node_c ty_o -> vsymbol -> unit errorM **)

let check_vl t0 v =
  ty_equal_check t0 v.vs_ty

(** val map2_opt :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list option **)

let rec map2_opt f l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some []
           | _ :: _ -> None)
  | x1 :: t1 ->
    (match l2 with
     | [] -> None
     | x2 :: t2 ->
       (match map2_opt f t1 t2 with
        | Some l3 -> Some ((f x1 x2) :: l3)
        | None -> None))

(** val list_iter2 :
    ('a1 -> 'a2 -> unit errorM) -> 'a1 list -> 'a2 list -> unit errorM **)

let rec list_iter2 f l1 l2 =
  match l1 with
  | [] ->
    (match l2 with
     | [] ->  ()
     | _ :: _ -> raise (Invalid_argument "iter2"))
  | x1 :: t1 ->
    (match l2 with
     | [] -> raise (Invalid_argument "iter2")
     | x2 :: t2 -> (@@) (fun _ -> list_iter2 f t1 t2) (f x1 x2))

(** val make_ls_defn :
    lsymbol -> vsymbol list -> (term_node term_o) -> (ty_node_c ty_o
    hashcons_ty, lsymbol * ls_defn) errState **)

let make_ls_defn ls vl t0 =
  if (||) (negb (BigInt.is_zero ls.ls_constr)) ls.ls_proj
  then  (raise (UnexpectedProjOrConstr ls))
  else let add_v = fun s v -> Svs.add_new_opt v s in
       (@@) (fun _ ->
         (@@) (fun hd ->
           (@@) (fun bd ->
             (@@) (fun tforall ->
               (@@) (fun fd ->
                 (@@) (fun _ ->
                   (@@) (fun _ ->  (ls, ((ls, fd), [])))
                     ( (t_ty_check t0 ls.ls_value)))
                   ( (list_iter2 check_vl ls.ls_args vl)))
                 ( (check_fvs tforall))) ( (t_forall_close vl [] bd)))
             (TermTFAlt.t_selecti t_equ (fun x y ->  (t_iff x y)) hd t0))
           (t_app ls (map t_var vl) (t_ty t0)))
         (
           (fold_left (fun acc x ->
             (@@) (fun s ->
               match add_v s x with
               | Some s' ->  s'
               | None -> raise (DuplicateVar x)) acc) vl ( Svs.empty)))

(** val open_ls_defn_aux :
    ls_defn -> (vsymbol list * (term_node term_o)) option **)

let open_ls_defn_aux = function
| (p, _) ->
  let (_, f) = p in
  let s =
    match t_node f with
    | Tvar _ -> (([], []), f)
    | Tconst _ -> (([], []), f)
    | Tapp (_, _) -> (([], []), f)
    | Tif (_, _, _) -> (([], []), f)
    | Tlet (_, _) -> (([], []), f)
    | Tcase (_, _) -> (([], []), f)
    | Teps _ -> (([], []), f)
    | Tquant (q, b) ->
      (match q with
       | Tforall -> t_view_quant b
       | Texists -> (([], []), f))
    | _ -> (([], []), f)
  in
  let (p0, f0) = s in
  let (vl, _) = p0 in
  (match t_node f0 with
   | Tapp (_, l1) ->
     (match l1 with
      | [] -> None
      | _ :: l2 ->
        (match l2 with
         | [] -> None
         | f1 :: l3 -> (match l3 with
                        | [] -> Some (vl, f1)
                        | _ :: _ -> None)))
   | Tbinop (_, _, f1) -> Some (vl, f1)
   | _ -> None)

(** val open_ls_defn :
    ls_defn -> (vsymbol list * (term_node term_o)) errorM **)

let open_ls_defn l =
  match open_ls_defn_aux l with
  | Some p ->  p
  | None -> assert_false "open_ls_defn"

type mut_adt = data_decl list

type mut_info = mut_adt list * mut_adt Mts.t

(** val mut_adt_eqb : mut_adt -> mut_adt -> bool **)

let mut_adt_eqb =
  list_eqb data_decl_eqb

(** val get_ctx_tys : decl Mid.t -> mut_info **)

let get_ctx_tys kn =
  Mid.fold (fun _ d acc ->
    match d.d_node with
    | Ddata m ->
      let (ms, mp) = acc in
      ((m :: ms), (fold_right (fun t0 ts -> Mts.add t0 m ts) mp (map fst m)))
    | _ -> acc) kn ([], Mts.empty)

(** val is_vty_adt :
    mut_info -> ty_node_c ty_o ->
    ((mut_adt * (ty_node_c ty_o) tysymbol_o) * ty_node_c ty_o list) option **)

let is_vty_adt ctx t0 =
  match ty_node t0 with
  | Tyvar _ -> None
  | Tyapp (ts, tys) ->
    option_bind (Mts.find_opt ts (snd ctx)) (fun m -> Some ((m, ts), tys))

(** val ts_in_mut : (ty_node_c ty_o) tysymbol_o -> mut_adt -> bool **)

let ts_in_mut ts m =
  isSome (list_find_opt (fun a -> ts_equal (fst a) ts) m)

(** val vty_in_m :
    mut_adt -> ty_node_c ty_o list -> ty_node_c ty_o -> bool **)

let vty_in_m m vs v =
  match ty_node v with
  | Tyvar _ -> false
  | Tyapp (ts, vs') -> (&&) (ts_in_mut ts m) (list_eqb ty_equal vs vs')

(** val vty_in_m' : mut_adt -> ty_node_c ty_o -> bool **)

let vty_in_m' m v =
  match ty_node v with
  | Tyvar _ -> false
  | Tyapp (ts, _) -> ts_in_mut ts m

(** val add_union : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let add_union eq x l =
  if existsb (fun y -> eq x y) l then l else x :: l

(** val get_adts_present :
    mut_info -> vsymbol list -> (mut_adt * ty_node_c ty_o list) list **)

let get_adts_present ctx l =
  fold_right (fun v acc ->
    match is_vty_adt ctx v.vs_ty with
    | Some p ->
      let (p0, vs) = p in
      let (m, _) = p0 in
      add_union (tuple_eqb mut_adt_eqb (list_eqb ty_eqb)) (m, vs) acc
    | None -> acc) [] l

(** val get_idx_lists_aux :
    decl Mid.t -> (vsymbol list * (term_node term_o)) Mls.t ->
    ((mut_adt * ty_node_c ty_o list) * BigInt.t list list) list **)

let get_idx_lists_aux kn funs =
  let syms = Mls.fold (fun _ x y -> (fst x) :: y) funs [] in
  map (fun pat ->
    let (m, vs) = pat in
    let l =
      map (fun args ->
        map fst
          (filter (fun it -> vty_in_m m vs (snd it))
            (combine (iota2 (int_length args)) (map (fun v -> v.vs_ty) args))))
        syms
    in
    ((m, vs), (if existsb null l then [] else l)))
    (get_adts_present (get_ctx_tys kn) (concat syms))

(** val get_idx_lists :
    decl Mid.t -> (vsymbol list * (term_node term_o)) Mls.t ->
    ((mut_adt * ty_node_c ty_o list) * BigInt.t list list) list **)

let get_idx_lists kn funs =
  filter (fun pat -> let (_, x) = pat in negb (null x))
    (get_idx_lists_aux kn funs)

(** val get_possible_index_lists : 'a1 list list -> 'a1 list list **)

let rec get_possible_index_lists = function
| [] -> [] :: []
| l1 :: rest ->
  let r = get_possible_index_lists rest in
  concat (map (fun x -> map (fun y -> x :: y) r) l1)

(** val check_unif_map : ty_node_c ty_o Mtv.t -> bool **)

let check_unif_map m =
  Mtv.for_all (fun v t0 ->
    match ty_node t0 with
    | Tyvar v1 -> tv_equal v v1
    | Tyapp (_, _) -> false) m

(** val vsym_in_m : mut_adt -> ty_node_c ty_o list -> vsymbol -> bool **)

let vsym_in_m m vs x =
  vty_in_m m vs x.vs_ty

(** val constr_in_m : lsymbol -> mut_adt -> bool **)

let constr_in_m l m =
  existsb (fun d -> existsb (fun c -> ls_equal (fst c) l) (snd d)) m

(** val pat_constr_vars_inner :
    mut_adt -> ty_node_c ty_o list -> (pattern_node pattern_o) -> Svs.t **)

let rec pat_constr_vars_inner m vs p =
  match pat_node p with
  | Pwild -> Svs.empty
  | Pvar x -> if vsym_in_m m vs x then Svs.singleton x else Svs.empty
  | Papp (f, ps) ->
    if constr_in_m f m
    then fold_right Svs.union Svs.empty
           (map2 (fun p0 x ->
             if vty_in_m' m x
             then pat_constr_vars_inner m vs p0
             else Svs.empty) ps f.ls_args)
    else Svs.empty
  | Por (p1, p2) ->
    Svs.inter (pat_constr_vars_inner m vs p1) (pat_constr_vars_inner m vs p2)
  | Pas (p', y) ->
    Svs.union (if vsym_in_m m vs y then Svs.singleton y else Svs.empty)
      (pat_constr_vars_inner m vs p')

(** val pat_constr_vars :
    mut_adt -> ty_node_c ty_o list -> (pattern_node pattern_o) -> Svs.t **)

let rec pat_constr_vars m vs p =
  match pat_node p with
  | Papp (_, _) -> pat_constr_vars_inner m vs p
  | Por (p1, p2) ->
    Svs.inter (pat_constr_vars m vs p1) (pat_constr_vars m vs p2)
  | Pas (p0, _) -> pat_constr_vars m vs p0
  | _ -> Svs.empty

(** val upd_option : vsymbol option -> vsymbol -> vsymbol option **)

let upd_option hd x =
  match hd with
  | Some y -> if vs_equal x y then None else hd
  | None -> None

(** val upd_option_iter : vsymbol option -> Svs.t -> vsymbol option **)

let upd_option_iter x xs =
  Svs.fold (fun v o -> upd_option o v) xs x

(** val check_var_case : unit Svs.M.t -> vsymbol option -> vsymbol -> bool **)

let check_var_case small hd v =
  (||) (option_eqb vs_equal hd (Some v)) (Svs.mem v small)

(** val tm_var_case :
    Svs.t -> vsymbol option -> (term_node term_o) -> bool **)

let tm_var_case small hd t0 =
  match t_node t0 with
  | Tvar v -> check_var_case small hd v
  | _ -> false

(** val get_constr_smaller :
    Svs.t -> vsymbol option -> mut_adt -> ty_node_c ty_o list -> lsymbol ->
    (term_node term_o) list -> (pattern_node pattern_o) -> Svs.t **)

let get_constr_smaller small hd m vs f tms p =
  match pat_node p with
  | Papp (f1, ps) ->
    if ls_equal f f1
    then fold_right Svs.union Svs.empty
           (map2 (fun t0 p0 ->
             if tm_var_case small hd t0
             then pat_constr_vars m vs p0
             else Svs.empty) tms ps)
    else Svs.empty
  | _ -> Svs.empty

(** val svs_remove_all : vsymbol list -> Svs.t -> Svs.t **)

let svs_remove_all l s =
  fold_right Svs.remove s l

(** val rem_opt_list : 'a1 option list -> 'a1 list **)

let rem_opt_list l =
  fold_right (fun x acc -> match x with
                           | Some y -> y :: acc
                           | None -> acc) [] l

(** val check_decrease_fun :
    (lsymbol * BigInt.t) list -> Svs.t -> vsymbol option -> mut_adt ->
    ty_node_c ty_o list -> (term_node term_o) -> bool **)

let check_decrease_fun funs small hd m vs t0 =
  term_rec (fun _ _ _ -> true) (fun _ _ _ -> true)
    (fun f ts recs small0 hd0 ->
    match list_find_opt (fun y -> ls_equal f (fst y)) funs with
    | Some p ->
      let (_, i) = p in
      (match big_nth ts i with
       | Some tm ->
         (match t_node tm with
          | Tvar x ->
            (&&)
              ((&&) (Svs.contains small0 x)
                (list_eqb ty_equal f.ls_args (rem_opt_list (map t_ty ts))))
              (forallb (fun x0 -> x0) (map (fun x0 -> x0 small0 hd0) recs))
          | _ -> false)
       | None -> false)
    | None -> forallb (fun x -> x) (map (fun x -> x small0 hd0) recs))
    (fun _ rec1 _ rec2 _ rec3 small0 hd0 ->
    (&&) ((&&) (rec1 small0 hd0) (rec2 small0 hd0)) (rec3 small0 hd0))
    (fun _ rec1 x _ rec2 small0 hd0 ->
    (&&) (rec1 small0 hd0) (rec2 (Svs.remove x small0) (upd_option hd0 x)))
    (fun t1 rec1 recps small0 hd0 ->
    let r2 =
      map (fun y ->
        let (y0, rec0) = y in
        let (p, _) = y0 in
        let toadd =
          match t_node t1 with
          | Tvar mvar ->
            if check_var_case small0 hd0 mvar
            then pat_constr_vars m vs p
            else Svs.empty
          | Tapp (c, tms) -> get_constr_smaller small0 hd0 m vs c tms p
          | _ -> Svs.empty
        in
        let newsmall = Svs.union toadd (Svs.diff small0 (pat_vars p)) in
        rec0 newsmall (upd_option_iter hd0 (pat_vars p))) recps
    in
    (&&) (rec1 small0 hd0) (forallb (fun x -> x) r2))
    (fun v _ rec0 small0 hd0 ->
    rec0 (Svs.remove v small0) (upd_option hd0 v))
    (fun _ vars _ rec0 small0 hd0 ->
    rec0 (svs_remove_all vars small0) (upd_option_iter hd0 (Svs.of_list vars)))
    (fun _ _ rec1 _ rec2 small0 hd0 ->
    (&&) (rec1 small0 hd0) (rec2 small0 hd0)) (fun _ rec0 -> rec0)
    (fun _ _ -> true) (fun _ _ -> true) t0 small hd

(** val find_idx_list :
    (lsymbol * (vsymbol list * (term_node term_o))) list -> mut_adt ->
    ty_node_c ty_o list -> BigInt.t list list -> BigInt.t list option **)

let find_idx_list l m vs candidates =
  list_find_opt (fun il ->
    forallb (fun y ->
      let (y0, i) = y in
      let (_, y1) = y0 in
      let (vars, t0) = y1 in
      (match big_nth vars i with
       | Some x ->
         check_decrease_fun (combine (map fst l) il) Svs.empty (Some x) m vs
           t0
       | None -> false)) (combine l il)) candidates

(** val list_inb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let list_inb eq x l =
  existsb (fun y -> eq x y) l

(** val mut_in_ctx : mut_adt -> decl Mid.t -> bool **)

let mut_in_ctx m kn =
  list_inb mut_adt_eqb m (fst (get_ctx_tys kn))

(** val find_elt : ('a1 -> 'a2 option) -> 'a1 list -> ('a1 * 'a2) option **)

let find_elt f l =
  fold_right (fun x acc ->
    match f x with
    | Some y -> Some (x, y)
    | None -> acc) None l

(** val check_termination_aux :
    decl Mid.t -> (vsymbol list * (term_node term_o)) Mls.t -> BigInt.t Mls.t
    option **)

let check_termination_aux kn funs =
  if Mls.is_empty funs
  then None
  else let l = Mls.bindings funs in
       let idxs = get_idx_lists kn funs in
       option_bind
         (find_elt (fun y ->
           let (y0, cands) = y in
           let (m, vs) = y0 in
           if mut_in_ctx m kn
           then find_idx_list l m vs (get_possible_index_lists cands)
           else None) idxs) (fun y ->
         let (_, idxs0) = y in
         Some
         (fold_right (fun x acc -> Mls.add (fst x) (snd x) acc) Mls.empty
           (combine (map fst l) idxs0)))

(** val ls_in_tm : lsymbol -> (term_node term_o) -> bool **)

let ls_in_tm l t0 =
  term_rec (fun _ -> false) (fun _ -> false) (fun f _ recs ->
    (||) (ls_equal f l) (existsb (fun x -> x) recs)) (fun _ r1 _ r2 _ r3 ->
    (||) ((||) r1 r2) r3) (fun _ r1 _ _ r2 -> (||) r1 r2) (fun _ r1 recs ->
    (||) r1 (existsb snd recs)) (fun _ _ r -> r) (fun _ _ _ r -> r)
    (fun _ _ r1 _ r2 -> (||) r1 r2) (fun _ r -> r) false false t0

(** val build_decl : decl_node -> Sid.t -> tag -> decl **)

let build_decl node news tag0 =
  { d_node = node; d_news = news; d_tag = tag0 }

(** val get_logic_defs :
    logic_decl list -> (vsymbol list * (term_node term_o)) Mls.t option **)

let get_logic_defs ld =
  fold_left (fun acc y ->
    let (ls, ld0) = y in
    (match acc with
     | Some m ->
       (match open_ls_defn_aux ld0 with
        | Some ld' -> Some (Mls.add ls ld' m)
        | None -> None)
     | None -> None)) ld (Some Mls.empty)

(** val check_termination_strict : decl Mid.t -> decl -> decl errorM **)

let check_termination_strict kn d =
  match d.d_node with
  | Dlogic l0 ->
    (match l0 with
     | [] ->  d
     | l :: ls ->
       let ld = l :: ls in
       (match get_logic_defs ld with
        | Some syms ->
          let binds = Mls.bindings syms in
          if forallb (fun t0 ->
               forallb (fun l1 -> negb (ls_in_tm l1 t0)) (map fst binds))
               (map (fun x -> snd (snd x)) binds)
          then  d
          else (match check_termination_aux kn syms with
                | Some idxs ->
                  let ldl =
                    map (fun y ->
                      let (ls0, l1) = y in
                      let (p, _) = l1 in
                      let (_, f) = p in
                      (ls0, ((ls0, f),
                      ((match Mls.find_opt ls0 idxs with
                        | Some i -> i
                        | None -> (BigInt.of_int (-1))) :: [])))) ld
                  in
                   (build_decl (Dlogic ldl) d.d_news d.d_tag)
                | None -> raise (NoTerminationProof (fst l)))
        | None -> assert_false "open_ls_defn"))
  | _ ->  d

(** val news_id : Sid.t -> ident -> Sid.t errorM **)

let news_id s i =
  Sid.add_new (ClashIdent i) i s

(** val create_ty_decl :
    (ty_node_c ty_o) tysymbol_o -> (decl hashcons_ty, decl) st **)

let create_ty_decl t0 =
  mk_decl (Dtype t0) (Sid.singleton (ts_name t0))

(** val is_nodef : 'a1 type_def -> bool **)

let is_nodef = function
| NoDef -> true
| _ -> false

(** val foldl_errst :
    ('a1 -> 'a2 -> ('a3, 'a1) errState) -> 'a2 list -> 'a1 -> ('a3, 'a1)
    errState **)

let rec foldl_errst f l x =
  match l with
  | [] ->  x
  | h :: t0 -> (@@) (fun j -> foldl_errst f t0 j) (f x h)

(** val foldl_err :
    ('a1 -> 'a2 -> 'a1 errorM) -> 'a2 list -> 'a1 -> 'a1 errorM **)

let rec foldl_err f l x =
  match l with
  | [] ->  x
  | h :: t0 -> (@@) (fun j -> foldl_err f t0 j) (f x h)

(** val iter_err : ('a1 -> unit errorM) -> 'a1 list -> unit errorM **)

let iter_err f l =
  foldl_err (fun _ -> f) l ()

(** val fold_left2_err :
    ('a3 -> 'a1 -> 'a2 -> 'a3 errorM) -> 'a3 -> 'a1 list -> 'a2 list -> 'a3
    option errorM **)

let rec fold_left2_err f accu l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] ->  (Some accu)
           | _ :: _ ->  None)
  | a1 :: l3 ->
    (match l2 with
     | [] ->  None
     | a2 :: l4 -> (@@) (fun x -> fold_left2_err f x l3 l4) (f accu a1 a2))

(** val opt_get_exn : exn -> 'a1 option -> 'a1 errorM **)

let opt_get_exn e = function
| Some y ->  y
| None -> raise e

(** val create_data_decl :
    data_decl list -> (ty_node_c ty_o hashcons_ty * decl hashcons_ty, decl)
    errState **)

let create_data_decl tdl =
  if null tdl
  then  (raise EmptyDecl)
  else let tss = fold_left (fun s x -> Sts.add (fst x) s) tdl Sts.empty in
       let check_proj = fun tyv s tya ls ->
         match ls with
         | Some ls1 ->
           (match ls1.ls_args with
            | [] -> raise (BadRecordField ls1)
            | ptyv :: l ->
              (match l with
               | [] ->
                 (match ls1.ls_value with
                  | Some ptya ->
                    if ls1.ls_proj
                    then if BigInt.is_zero ls1.ls_constr
                         then (@@) (fun _ ->
                                (@@) (fun _ ->
                                  Sls.add_new (DuplicateRecordField ls1) ls1 s)
                                  (ty_equal_check tya ptya))
                                (ty_equal_check tyv ptyv)
                         else raise (BadRecordField ls1)
                    else raise (BadRecordField ls1)
                  | None -> raise (BadRecordField ls1))
               | _ :: _ -> raise (BadRecordField ls1)))
         | None ->  s
       in
       let check_constr = fun tys ty cll pjs news c ->
         let (fs, pl) = c in
         (@@) (fun ty1 ->
           (@@) (fun _ ->
             (@@) (fun o ->
               match o with
               | Some fs_pjs ->
                 if negb (Sls.equal pjs fs_pjs)
                 then (@@) (fun x -> raise (RecordFieldMissing x))
                        (Sls.choose (Sls.diff pjs fs_pjs))
                 else if negb (BigInt.eq fs.ls_constr cll)
                      then raise (BadConstructor fs)
                      else let vs = ty_freevars Stv.empty ty in
                           let check =
                             let rec check seen ty0 =
                               match ty_node ty0 with
                               | Tyvar v ->
                                 if Stv.mem v vs
                                 then  ()
                                 else raise (UnboundTypeVar v)
                               | Tyapp (ts, tl) ->
                                 let now1 = Sts.mem ts tss in
                                 if (&&) seen now1
                                 then raise
                                        ((fun ((x, y), z) -> NonPositiveTypeDecl(x, y, z))
                                          ((tys, fs), ty0))
                                 else iter_err (check ((||) seen now1)) tl
                             in check
                           in
                           (@@) (fun _ -> news_id news fs.ls_name)
                             (iter_err (check false) fs.ls_args)
               | None -> raise (BadConstructor fs))
               (fold_left2_err (check_proj ty) Sls.empty fs.ls_args pl))
             (ty_equal_check ty ty1))
           (opt_get_exn (BadConstructor fs) fs.ls_value)
       in
       let check_decl = fun news d ->
         let (ts, cl) = d in
         let cll = int_length cl in
         if null cl
         then  (raise (EmptyAlgDecl ts))
         else if negb (is_nodef (ts_def ts))
              then  (raise (IllegalTypeAlias ts))
              else (@@) (fun news1 ->
                     let pjs =
                       fold_left (fun s y ->
                         let pl = snd y in
                         fold_left (CoqUtil.opt_fold Sls.add_left) pl s) cl
                         Sls.empty
                     in
                     (match Sls.fold (fun pj s ->
                              match s with
                              | Coq_inl s1 ->
                                let ls = pj.ls_name in
                                if Sid.contains s1 ls
                                then Coq_inr ls
                                else Coq_inl (Sid.add ls s1)
                              | Coq_inr err -> Coq_inr err) pjs (Coq_inl
                              news1) with
                      | Coq_inl news2 ->
                        (@@) (fun l1 ->
                          (@@) (fun ty ->
                             (foldl_err (check_constr ts ty cll pjs) cl news2))
                            (ty_app ts l1))
                          ( (st_list (map ty_var (ts_args ts))))
                      | Coq_inr l ->  (raise (ClashIdent l))))
                     ( (news_id news (ts_name ts)))
       in
       (@@) (fun news ->  ( (mk_decl (Ddata tdl) news)))
         ( (foldl_errst check_decl tdl Sid.empty))

(** val create_param_decl : lsymbol -> (decl hashcons_ty, decl) errState **)

let create_param_decl ls =
  if (||) (negb (BigInt.is_zero ls.ls_constr)) ls.ls_proj
  then  (raise (UnexpectedProjOrConstr ls))
  else let news = Sid.singleton ls.ls_name in  (mk_decl (Dparam ls) news)

(** val create_logic_decl_nocheck :
    logic_decl list -> (decl hashcons_ty, decl) errState **)

let create_logic_decl_nocheck ldl =
  if null ldl
  then  (raise EmptyDecl)
  else let check_decl = fun news x ->
         let (ls, l) = x in
         let (p, _) = l in
         let (s, _) = p in
         if negb (ls_equal s ls)
         then raise (BadLogicDecl (ls, s))
         else if (||) (negb (BigInt.is_zero ls.ls_constr)) ls.ls_proj
              then raise (UnexpectedProjOrConstr ls)
              else news_id news ls.ls_name
       in
       (@@) (fun news ->  (mk_decl (Dlogic ldl) news))
         ( (foldl_err check_decl ldl Sid.empty))

(** val lsyms_notin_tm : Sls.t -> (term_node term_o) -> bool **)

let lsyms_notin_tm p t0 =
  Sls.for_all (fun x -> negb (ls_in_tm x t0)) p

(** val ind_strict_pos : Sls.t -> (term_node term_o) -> bool **)

let rec ind_strict_pos sps f =
  (||) (lsyms_notin_tm sps f)
    (match t_node f with
     | Tapp (p, tms) ->
       (&&) (Sls.mem p sps) (forallb (lsyms_notin_tm sps) tms)
     | Tif (f1, f2, f3) ->
       (&&) ((&&) (lsyms_notin_tm sps f1) (ind_strict_pos sps f2))
         (ind_strict_pos sps f3)
     | Tlet (t0, tb) ->
       let (_, t2) = t_view_bound tb in
       (&&) (ind_strict_pos sps t2) (lsyms_notin_tm sps t0)
     | Tcase (t0, pats) ->
       (&&) (lsyms_notin_tm sps t0)
         (forallb (fun x ->
           let (_, t1) = t_view_branch x in ind_strict_pos sps t1) pats)
     | Tquant (_, tq) ->
       let (_, f0) = t_view_quant tq in ind_strict_pos sps f0
     | Tbinop (b, f1, f2) ->
       (match b with
        | Timplies -> (&&) (ind_strict_pos sps f2) (lsyms_notin_tm sps f1)
        | _ ->
          (match b with
           | Tiff -> false
           | _ -> (&&) (ind_strict_pos sps f1) (ind_strict_pos sps f2)))
     | _ -> false)

(** val ind_pos : Sls.t -> (term_node term_o) -> bool **)

let rec ind_pos sps f =
  match t_node f with
  | Tapp (p, ts) -> (&&) (Sls.mem p sps) (forallb (lsyms_notin_tm sps) ts)
  | Tlet (t0, tb) ->
    (&&) (lsyms_notin_tm sps t0) (ind_pos sps (snd (t_view_bound tb)))
  | Tquant (q, tq) ->
    (match q with
     | Tforall -> ind_pos sps (snd (t_view_quant tq))
     | Texists -> false)
  | Tbinop (b, f1, f2) ->
    (match b with
     | Timplies -> (&&) (ind_strict_pos sps f1) (ind_pos sps f2)
     | _ -> false)
  | _ -> false

(** val valid_ind_form :
    lsymbol -> (term_node term_o) -> (term_node term_o) option **)

let rec valid_ind_form ps f =
  match t_node f with
  | Tapp (p, ts) ->
    if (&&) (ls_equal p ps)
         (list_eqb ty_equal p.ls_args (rem_opt_list (map t_ty ts)))
    then Some f
    else None
  | Tlet (_, tb) -> valid_ind_form ps (snd (t_view_bound tb))
  | Tquant (q, tq) ->
    (match q with
     | Tforall -> valid_ind_form ps (snd (t_view_quant tq))
     | Texists -> None)
  | Tbinop (b, _, f2) ->
    (match b with
     | Timplies -> valid_ind_form ps f2
     | _ -> None)
  | _ -> None

(** val create_ind_decl :
    ind_sign -> ind_decl list -> (decl hashcons_ty, decl) errState **)

let create_ind_decl s idl =
  if null idl
  then  (raise EmptyDecl)
  else let sps = fold_left (fun acc x -> Sls.add (fst x) acc) idl Sls.empty in
       let check_ax = fun ps news x ->
         let (pr, f) = x in
         (@@) (fun f0 ->
           if negb (ind_pos sps f0)
           then raise
                  ((fun ((x, y), z) -> NonPositiveIndDecl(x, y, z)) ((ps,
                    pr), ps))
           else (match valid_ind_form ps f0 with
                 | Some g ->
                   let gtv = t_ty_freevars Stv.empty g in
                   let ftv = t_ty_freevars Stv.empty f0 in
                   if negb (Stv.subset ftv ftv)
                   then (@@) (fun y -> raise (UnboundTypeVar y))
                          (Stv.choose (Stv.diff ftv gtv))
                   else news_id news pr.pr_name
                 | None -> raise (InvalidIndDecl (ps, pr)))) (check_fvs f)
       in
       let check_decl = fun news x ->
         let (ps, al) = x in
         if null al
         then raise (EmptyIndDecl ps)
         else if isSome ps.ls_value
              then raise (PredicateSymbolExpected ps)
              else (@@) (fun news0 -> foldl_err (check_ax ps) al news0)
                     (news_id news ps.ls_name)
       in
       (@@) (fun news ->  (mk_decl (Dind (s, idl)) news))
         ( (foldl_err check_decl idl Sid.empty))

(** val create_prop_decl :
    prop_kind -> prsymbol -> (term_node term_o) -> (decl hashcons_ty, decl)
    errState **)

let create_prop_decl k p f =
  (@@) (fun news ->
    (@@) (fun f0 ->
       (mk_decl (Dprop ((fun ((x, y), z) -> (x, y, z)) ((k, p), f0))) news))
      ( (check_fvs f))) ( (news_id Sid.empty p.pr_name))

(** val syms_ts : Sid.t -> (ty_node_c ty_o) tysymbol_o -> unit Sid.M.t **)

let syms_ts s ts =
  Sid.add (ts_name ts) s

(** val syms_ls : Sid.t -> lsymbol -> unit Sid.M.t **)

let syms_ls s ls =
  Sid.add ls.ls_name s

(** val syms_ty : Sid.t -> ty_node_c ty_o -> Sid.t **)

let syms_ty s ty =
  ty_s_fold syms_ts s ty

(** val syms_term : Sid.t -> (term_node term_o) -> Sid.t **)

let syms_term s t0 =
  t_s_fold syms_ty syms_ls s t0

(** val syms_ty_decl : (ty_node_c ty_o) tysymbol_o -> Sid.t **)

let syms_ty_decl ts =
  type_def_fold syms_ty Sid.empty (ts_def ts)

(** val syms_data_decl : data_decl list -> Sid.t **)

let syms_data_decl tdl =
  let syms_constr = fun syms pat ->
    let (fs, _) = pat in fold_left syms_ty fs.ls_args syms
  in
  let syms_decl = fun syms pat ->
    let (_, cl) = pat in fold_left syms_constr cl syms
  in
  fold_left syms_decl tdl Sid.empty

(** val syms_param_decl : lsymbol -> Sid.t **)

let syms_param_decl ls =
  let syms = CoqUtil.opt_fold syms_ty Sid.empty ls.ls_value in
  fold_left syms_ty ls.ls_args syms

(** val syms_logic_decl : logic_decl list -> Sid.t **)

let syms_logic_decl ldl =
  let syms_decl = fun syms pat ->
    let (ls, ld) = pat in
    (match open_ls_defn_aux ld with
     | Some p ->
       let (_, e) = p in
       let syms0 = fold_left syms_ty ls.ls_args syms in syms_term syms0 e
     | None -> syms)
  in
  fold_left syms_decl ldl Sid.empty

(** val syms_ind_decl : ind_decl list -> Sid.t **)

let syms_ind_decl idl =
  let syms_ax = fun syms pat -> let (_, f) = pat in syms_term syms f in
  let syms_decl = fun syms pat ->
    let (_, al) = pat in fold_left syms_ax al syms
  in
  fold_left syms_decl idl Sid.empty

(** val syms_prop_decl : (term_node term_o) -> Sid.t **)

let syms_prop_decl f =
  syms_term Sid.empty f

(** val get_used_syms_ty : ty_node_c ty_o -> Sid.t **)

let get_used_syms_ty ty =
  syms_ty Sid.empty ty

(** val get_used_syms_decl : decl -> Sid.t **)

let get_used_syms_decl d =
  match d.d_node with
  | Dtype ts -> syms_ty_decl ts
  | Ddata dl -> syms_data_decl dl
  | Dparam ls -> syms_param_decl ls
  | Dlogic ldl -> syms_logic_decl ldl
  | Dind i -> let (_, idl) = i in syms_ind_decl idl
  | Dprop x ->
    let (_, f) = (fun (x, y, z) -> ((x, y), z)) x in syms_prop_decl f

type known_map = decl Mid.t

(** val known_id : known_map -> ident -> unit errorM **)

let known_id kn i =
  if negb (Mid.mem i kn) then raise (UnknownIdent i) else  ()

(** val known_add_decl_aux : known_map -> decl -> known_map errorM **)

let known_add_decl_aux kn0 d =
  let kn = Mid.map (fun _ -> d) d.d_news in
  let inter0 = Mid.set_inter kn0 kn in
  if negb (Mid.is_empty inter0)
  then (@@) (fun x ->
         let (i, d1) = x in
         if d_equal d1 d
         then raise (KnownIdent i)
         else raise (RedeclaredIdent i)) (Mid.choose inter0)
  else let kn1 = Mid.set_union kn0 kn in
       let unk = Mid.set_diff (get_used_syms_decl d) kn1 in
       if Sid.is_empty unk
       then  kn1
       else (@@) (fun j -> raise (UnknownIdent j)) (Sid.choose unk)

(** val list_assoc :
    ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> 'a2 option **)

let list_assoc eq x l =
  fold_right (fun y acc -> if eq x (fst y) then Some (snd y) else acc) None l

(** val list_mem_assoc :
    ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> bool **)

let list_mem_assoc eq x l =
  isSome (list_assoc eq x l)

(** val list_of_opt : 'a1 list option -> 'a1 list **)

let list_of_opt = function
| Some y -> y
| None -> []

(** val find_constructors :
    known_map -> (ty_node_c ty_o) tysymbol_o -> constructor list **)

let find_constructors kn ts =
  list_of_opt
    (option_bind (Mid.find_opt (ts_name ts) kn) (fun d ->
      match d.d_node with
      | Ddata dl -> list_assoc ts_equal ts dl
      | _ -> None))

(** val find_inductive_cases :
    known_map -> lsymbol -> (prsymbol * (term_node term_o)) list **)

let find_inductive_cases kn ps =
  list_of_opt
    (option_bind (Mid.find_opt ps.ls_name kn) (fun d ->
      match d.d_node with
      | Dind i -> let (_, dl) = i in list_assoc ls_equal ps dl
      | _ -> None))

(** val find_logic_definition : known_map -> lsymbol -> ls_defn option **)

let find_logic_definition kn ls =
  option_bind (Mid.find_opt ls.ls_name kn) (fun d ->
    match d.d_node with
    | Dlogic dl -> list_assoc ls_equal ls dl
    | _ -> None)

(** val find_prop : known_map -> prsymbol -> (term_node term_o) **)

let find_prop kn pr =
  match option_bind (Mid.find_opt pr.pr_name kn) (fun d ->
          match d.d_node with
          | Dtype _ -> None
          | Ddata _ -> None
          | Dparam _ -> None
          | Dlogic _ -> None
          | Dind i ->
            let (_, dl) = i in
            option_bind
              (list_find_opt (fun x -> list_mem_assoc pr_equal pr (snd x)) dl)
              (fun l1 -> list_assoc pr_equal pr (snd l1))
          | Dprop x -> let (_, f) = (fun (x, y, z) -> ((x, y), z)) x in Some f) with
  | Some tm -> tm
  | None -> t_false

(** val find_prop_decl :
    known_map -> prsymbol -> (prop_kind * (term_node term_o)) errorM **)

let find_prop_decl kn pr =
  (@@) (fun d ->
    match d.d_node with
    | Dind i ->
      let (_, dl) = i in
      (match list_find_opt (fun x -> list_mem_assoc pr_equal pr (snd x)) dl with
       | Some l1 ->
         (match list_assoc pr_equal pr (snd l1) with
          | Some f ->  (Paxiom, f)
          | None -> raise Not_found)
       | None -> raise Not_found)
    | Dprop p ->
      let (p0, f) = (fun (x, y, z) -> ((x, y), z)) p in
      let (k, _) = p0 in  (k, f)
    | _ -> assert_false "find_prop_decl") (Mid.find pr.pr_name kn)

(** val all_tysymbols : known_map -> Sts.t **)

let all_tysymbols kn =
  Mid.fold (fun _ d acc ->
    match d.d_node with
    | Dtype ts -> Sts.add ts acc
    | Ddata ld -> fold_right Sts.add acc (map fst ld)
    | _ -> acc) kn Sts.empty

(** val is_abstract_type :
    known_map -> (ty_node_c ty_o) tysymbol_o -> bool **)

let is_abstract_type kn ts =
  Mid.exists_ (fun _ d ->
    match d.d_node with
    | Dtype ts' -> ts_equal ts ts'
    | _ -> false) kn

(** val check_ts :
    known_map -> Sts.t -> Stv.t -> (ty_node_c ty_o) tysymbol_o -> BigInt.t ->
    bool **)

let check_ts kn tss tvs ts z =
  int_rect (fun _ _ _ -> false) (fun _ -> false) (fun _ _ _ rec0 x ->
    let (p, ts0) = x in
    let (p0, tvs0) = p in
    let (kn0, tss0) = p0 in
    if Sts.mem ts0 tss0
    then false
    else if is_abstract_type kn0 ts0
         then Stv.is_empty tvs0
         else let cl = find_constructors kn0 ts0 in
              let tss1 = Sts.add ts0 tss0 in
              existsb (fun y ->
                let (ls, _) = y in
                forallb (fun t0 ->
                  let rec check_type ty =
                    match ty_node ty with
                    | Tyvar tv -> negb (Stv.mem tv tvs0)
                    | Tyapp (ts1, tl) ->
                      (match fold_left2 (fun acc ty0 tv ->
                               if check_type ty0 then acc else Stv.add tv acc)
                               tl (ts_args ts1) Stv.empty with
                       | Some tvs1 -> rec0 (((kn0, tss1), tvs1), ts1)
                       | None -> false)
                  in check_type t0) ls.ls_args) cl) z (((kn, tss), tvs), ts)

(** val check_foundness : known_map -> decl -> unit errorM **)

let check_foundness kn d =
  match d.d_node with
  | Ddata tdl ->
    foldl_err (fun _ x ->
      if check_ts kn Sts.empty Stv.empty (fst x)
           (Sts.cardinal (all_tysymbols kn))
      then  ()
      else raise (NonFoundedTypeDecl (fst x))) tdl ()
  | _ ->  ()

(** val get_opt_def : 'a1 option -> 'a1 -> 'a1 **)

let get_opt_def x d =
  match x with
  | Some y -> y
  | None -> d

(** val ts_extract_pos_aux :
    known_map -> Sts.t -> (ty_node_c ty_o) tysymbol_o -> BigInt.t -> bool
    list option **)

let ts_extract_pos_aux kn sts ts z =
  int_rect (fun _ _ _ -> None) (fun _ -> None) (fun _ _ _ rec0 x ->
    let (p, ts0) = x in
    let (kn0, sts0) = p in
    if is_alias_type_def (ts_def ts0)
    then None
    else if ts_equal ts0 ts_func
         then Some (false :: (true :: []))
         else if Sts.mem ts0 sts0
              then Some (map (fun _ -> true) (ts_args ts0))
              else (match find_constructors kn0 ts0 with
                    | [] -> Some (map (fun _ -> false) (ts_args ts0))
                    | c :: l ->
                      let sts1 = Sts.add ts0 sts0 in
                      let get_ty =
                        let rec get_ty ty stv =
                          match ty_node ty with
                          | Tyvar _ -> stv
                          | Tyapp (ts1, tl) ->
                            (match rec0 ((kn0, sts1), ts1) with
                             | Some l0 ->
                               let get = fun acc t0 pos ->
                                 if pos
                                 then get_ty t0 acc
                                 else ty_freevars acc t0
                               in
                               get_opt_def (fold_left2 get tl l0 stv)
                                 Stv.empty
                             | None -> Stv.empty)
                        in get_ty
                      in
                      let negs =
                        fold_left (fun acc x0 ->
                          let (ls, _) = x0 in
                          fold_left (fun x1 y -> get_ty y x1) ls.ls_args acc)
                          (c :: l) Stv.empty
                      in
                      Some
                      (map (fun v -> negb (Stv.mem v negs)) (ts_args ts0))))
    z ((kn, sts), ts)

(** val ts_extract_pos :
    known_map -> Sts.t -> (ty_node_c ty_o) tysymbol_o -> bool list errorM **)

let ts_extract_pos kn sts ts =
  match ts_extract_pos_aux kn sts ts (Sts.cardinal (all_tysymbols kn)) with
  | Some l ->  l
  | None -> assert_false "ts_extract_pos"

(** val check_positivity : known_map -> decl -> unit errorM **)

let check_positivity kn d =
  match d.d_node with
  | Ddata tdl ->
    let tss = fold_left (fun acc x -> Sts.add (fst x) acc) tdl Sts.empty in
    let check_constr = fun tys x ->
      let (cs, _) = x in
      let check_ty =
        let rec check_ty ty =
          match ty_node ty with
          | Tyvar _ ->  ()
          | Tyapp (ts, tl) ->
            let check = fun ty0 pos ->
              if pos
              then check_ty ty0
              else if ty_s_any (Sts.contains tss) ty0
                   then raise
                          ((fun ((x, y), z) -> NonPositiveTypeDecl(x, y, z))
                            ((tys, cs), ty0))
                   else  ()
            in
            (@@) (fun l1 -> list_iter2 check tl l1)
              (ts_extract_pos kn Sts.empty ts)
        in check_ty
      in
      iter_err check_ty cs.ls_args
    in
    iter_err (fun x -> iter_err (check_constr (fst x)) (snd x)) tdl
  | _ ->  ()

(** val known_add_decl : known_map -> decl -> (decl * decl Mid.t) errorM **)

let known_add_decl kn d =
  (@@) (fun kn0 ->
    (@@) (fun _ ->
      (@@) (fun _ ->
        (@@) (fun d0 ->  (d0, kn0)) (check_termination_strict kn0 d))
        (check_foundness kn0 d)) (check_positivity kn0 d))
    (known_add_decl_aux kn d)
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

open Wstdlib
open Ident
open Ty
open Term

let sexp_of_ind_sign (x: ind_sign) : Sexplib0.Sexp.t =
  match x with Ind -> Sexplib0.Sexp.Atom "Ind" | Coind -> Sexplib0.Sexp.Atom "Coind"

let ind_sign_of_sexp (x: Sexplib0.Sexp.t) : ind_sign =
  match x with
  | Sexplib0.Sexp.Atom "Ind" -> Ind
  | Sexplib0.Sexp.Atom "Coind"  -> Coind 
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "ind_sign_of_sexp" x 


let sexp_of_prop_kind (x: prop_kind) : Sexplib0.Sexp.t =
   match x with Plemma -> Sexplib0.Sexp.Atom "Plemma" | Paxiom -> Sexplib0.Sexp.Atom "Paxiom" | Pgoal -> Sexplib0.Sexp.Atom "Pgoal"


let prop_kind_of_sexp (x: Sexplib0.Sexp.t) : prop_kind =
  match x with
  | Sexplib0.Sexp.Atom "Plemma" -> Plemma
  | Sexplib0.Sexp.Atom "Paxiom"  -> Paxiom 
  | Sexplib0.Sexp.Atom "Pgoal"  -> Pgoal 
  | _ -> Sexplib0.Sexp_conv.of_sexp_error "prop_kind_of_sexp" x 

(*  (*Type declaration*)

type constructor = lsymbol * lsymbol option list
(** constructor symbol with the list of projections *)

type data_decl = tysymbol * constructor list

(** Logic declaration *)

type ls_defn = lsymbol * term * int list

type logic_decl = lsymbol * ls_defn

exception UnboundVar of vsymbol
exception UnexpectedProjOrConstr of lsymbol

let check_fvs f =
  t_v_fold (fun _ vs -> raise (UnboundVar vs)) () f;
  t_prop f

let check_vl ty v = ty_equal_check ty v.vs_ty*)
let check_tl ty t = ty_equal_check ty (t_type t)

(*let make_ls_defn ls vl t =
  (* check ls *)
  if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
  (* check for duplicate arguments *)
  let add_v s v = Svs.add_new (DuplicateVar v) v s in
  ignore (List.fold_left add_v Svs.empty vl);
  (* build the definition axiom *)
  let hd = t_app ls (List.map t_var vl) t.t_ty in
  let bd = TermTF.t_selecti t_equ t_iff hd t in
  let fd = check_fvs (t_forall_close vl [] bd) in
  (* check for unbound type variables *)
  let htv = t_ty_freevars Stv.empty hd in
  let ttv = t_ty_freevars Stv.empty t in
  if not (Stv.subset ttv htv) then
    raise (UnboundTypeVar (Stv.choose (Stv.diff ttv htv)));
  (* check correspondence with the type signature of ls *)
  List.iter2 check_vl ls.ls_args vl;
  t_ty_check t ls.ls_value;
  (* return the definition *)
  ls, (ls, fd, []) *)

(*JOSH - TODO hack*)
(* let make_ls_defn ls vl t =
  let l, ((l1, t), l2) = make_ls_defn ls vl t in
  l, (l1, t, l2) *)

(* let open_ls_defn ((_,f),_) =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  match f.t_node with
    | Tapp (_, [_; f])
    | Tbinop (_, _, f) -> vl,f
    | _ -> assert false *)

let open_ls_defn_cb ld =
  let (ls,_),_ = ld in
  let vl,t = open_ls_defn ld in
  let close ls' vl' t' =
    if t_equal_strict t t' && Lists.equal vs_equal vl vl' && ls_equal ls ls'
    then ls,ld else make_ls_defn ls' vl' t'
  in
  vl,t,close

  let ls_defn_decrease ((_,_),l) = List.map BigInt.to_int l (*JOSH to_int*)

let ls_defn_axiom ((_,f),_) = f

let ls_defn_of_axiom f =
  let _,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  let hd,e = match f.t_node with
    | Tapp (ls, [hd; t]) when ls_equal ls ps_equ -> hd,t
    | Tbinop (Tiff, hd, f) -> hd,f
    | _ -> raise Exit in
  let ls,tl = match hd.t_node with
    | Tapp (ls,tl) -> ls,tl
    | _ -> raise Exit in
  let vs_of_t t = match t.t_node with
    | Tvar v -> v
    | _ -> raise Exit in
  let vl = List.map vs_of_t tl in
  make_ls_defn ls vl e

let ls_defn_of_axiom f =
  try Some (ls_defn_of_axiom f) with
    | Exit | UnboundVar _ | UnboundTypeVar _
    | DuplicateVar _ | TypeMismatch _ | UnexpectedProjOrConstr _ -> None

(** Termination checking for mutually recursive logic declarations *)

type descent =
  | Less of int
  | Equal of int
  | Unknown

type call_set = (ident * descent array) Hid.t
type vs_graph = descent Mvs.t list

let create_call_set () = Hid.create 5

let create_vs_graph vl =
  let i = ref (-1) in
  let add vm v = incr i; Mvs.add v (Equal !i) vm in
  [List.fold_left add Mvs.empty vl]

(* TODO: can we handle projections somehow? *)
let register_call cgr caller vsg callee tl =
  let call vm =
    let describe t = match t.t_node with
      | Tvar v -> Mvs.find_def Unknown v vm
      | _ -> Unknown in
    let dl = List.map describe tl in
    Hid.add cgr callee (caller, Array.of_list dl) in
  List.iter call vsg

let vs_graph_drop vsg u = List.rev_map (Mvs.remove u) vsg

(* TODO: can we handle projections somehow? *)
let vs_graph_let vsg t u = match t.t_node with
  | Tvar v ->
      let add vm = try Mvs.add u (Mvs.find v vm) vm
                  with Not_found -> Mvs.remove u vm in
      List.rev_map add vsg
  | _ ->
      vs_graph_drop vsg u

let rec match_var link acc p = match p.pat_node with
  | Pwild -> acc
  | Pvar u -> List.rev_map (Mvs.add u link) acc
  | Pas (p,u) -> List.rev_map (Mvs.add u link) (match_var link acc p)
  | Por (p1,p2) ->
      List.rev_append (match_var link acc p1) (match_var link acc p2)
  | Papp _ ->
      let link = match link with
        | Unknown -> Unknown
        | Equal i -> Less i
        | Less i  -> Less i in
      let join u = Mvs.add u link in
      List.rev_map (Svs.fold join p.pat_vars) acc

let rec match_term vm t acc p = match t.t_node, p.pat_node with
  | _, Pwild -> acc
  | Tvar v, _ when Mvs.mem v vm ->
      match_var (Mvs.find v vm) acc p
  | Tapp _, Pvar u ->
      vs_graph_drop acc u
  | Tapp _, Pas (p,u) ->
      match_term vm t (vs_graph_drop acc u) p
  | Tapp _, Por (p1,p2) ->
      List.rev_append (match_term vm t acc p1) (match_term vm t acc p2)
  | Tapp (c1,tl), Papp (c2,pl) when ls_equal c1 c2 ->
      let down l t p = match_term vm t l p in
      List.fold_left2 down acc tl pl
  | _,_ ->
      List.rev_map (fun vm -> Mvs.set_diff vm p.pat_vars) acc

let vs_graph_pat vsg t p =
  let add acc vm = List.rev_append (match_term vm t [vm] p) acc in
  List.fold_left add [] vsg

let build_call_graph cgr syms ls (vl,e) =
  let rec term vm () t = match t.t_node with
    | Tapp (s,tl) when Mls.mem s syms ->
        t_fold (term vm) () t;
        register_call cgr ls.ls_name vm s.ls_name tl
    | Tlet (t,b) ->
        term vm () t;
        let u,e = t_open_bound b in
        term (vs_graph_let vm t u) () e
    | Tcase (t,bl) ->
        term vm () t;
        List.iter (fun b ->
          let p,e = t_open_branch b in
          term (vs_graph_pat vm t p) () e) bl
    | Tquant (_,b) -> (* ignore triggers *)
        let _,_,f = t_open_quant b in term vm () f
    | _ ->
        t_fold (term vm) () t
  in
  term (create_vs_graph vl) () e

let build_call_list cgr id =
  let htb = Hid.create 5 in
  let local v = Array.mapi (fun i -> function
    | (Less j) as d when i = j -> d
    | (Equal j) as d when i = j -> d
    | _ -> Unknown) v
  in
  let subsumes v1 v2 =
    let sbs d1 d2 = match d1,d2 with
      | _, Unknown -> ()
      | Equal u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Less  u2 when u1 = u2 -> ()
      | _,_ -> raise Not_found
    in
    let test i d1 = sbs d1 (Array.get v2 i) in
    try Array.iteri test v1; true with Not_found -> false
  in
  let subsumed s c =
    List.exists (subsumes c) (Hid.find_all htb s)
  in
  let multiply v1 v2 =
    let to_less = function
      | Unknown -> Unknown
      | Equal i -> Less i
      | Less i  -> Less i
    in
    Array.map (function
      | Unknown -> Unknown
      | Equal i -> Array.get v2 i
      | Less i -> to_less (Array.get v2 i)) v1
  in
  let resolve s c =
    Hid.add htb s c;
    let mult (s,v) = (s, multiply c v) in
    List.rev_map mult (Hid.find_all cgr s)
  in
  let rec add_call lc = function
    | [] -> lc
    | (s,c)::r when id_equal id s -> add_call (local c :: lc) r
    | (s,c)::r when subsumed s c -> add_call lc r
    | (s,c)::r -> add_call lc (List.rev_append (resolve s c) r)
  in
  add_call [] (Hid.find_all cgr id)

let find_variant exn cgr id =
  let cl = build_call_list cgr id in
  let add d1 d2 = match d1, d2 with
    | Unknown, _ -> d1
    | _, Unknown -> d2
    | Less _, _  -> d1
    | _, Less _  -> d2
    | _, _ -> d1
  in
  let add v1 v2 =
    Array.mapi (fun i d1 -> add d1 (Array.get v2 i)) v1
  in
  let rec check acc mx = match mx with
    | [] -> List.rev acc
    | a :: r ->
        (* calculate the bitwise minimum of all call vectors *)
        let p = List.fold_left add a r in
        (* find the decreasing argument positions *)
        let find l = function Less i -> i :: l | _ -> l in
        let res = Array.fold_left find [] p in
        (* eliminate the decreasing calls *)
        if res = [] then raise exn;
        let test a =
          List.for_all (fun i -> Array.get a i <> Less i) res
        in
        check (List.rev_append res acc) (List.filter test mx)
  in
  check [] cl

(* exception NoTerminationProof of lsymbol *)

let check_termination ldl =
  let cgr = create_call_set () in
  let add acc (ls,ld) = Mls.add ls (open_ls_defn ld) acc in
let syms = List.fold_left add Mls.empty ldl in
  Mls.iter (build_call_graph cgr syms) syms;
  let check ls _ =
    find_variant (NoTerminationProof ls) cgr ls.ls_name in
  let res = Mls.mapi check syms in
  List.map (fun (ls,((_,f),_)) -> (ls,((ls,f),(List.map BigInt.of_int (Mls.find ls res))))) ldl 

(** Inductive predicate declaration *)

(* type prsymbol = {
  pr_name : ident;
} *)

module Prop = MakeMSHW (PropTag) 
(*struct
  type t = prsymbol
  let tag pr = pr.pr_name.id_tag
  let equal = (==) (*JOSH TODO equal*)
end)*)

(* module Spr = Prop.S
module Mpr = Prop.M *)
module Hpr = Prop.H
module Wpr = Prop.W

(* let pr_equal : prsymbol -> prsymbol -> bool = (==)

let pr_hash pr = id_hash pr.pr_name

let create_prsymbol n = { pr_name = id_register n } *)

(* type ind_decl = lsymbol * (prsymbol * term) list *)

(* type ind_sign = Ind | Coind
[@@deriving sexp]

type ind_list = ind_sign * ind_decl list *)

(** Proposition declaration *)

(* type prop_kind =
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal     (* prove, do not use as a premise *)
[@@deriving sexp]

type prop_decl = prop_kind * prsymbol * term *)

(** Declaration type *)

(*type decl = {
  d_node : decl_node;
  d_news : Sid.t;         (* idents introduced in declaration *)
  d_tag  : Weakhtbl.tag;  (* unique magical tag *)
}

and decl_node =
  | Dtype  of tysymbol          (* abstract types and aliases *)
  | Ddata  of data_decl list    (* recursive algebraic types *)
  | Dparam of lsymbol           (* abstract functions and predicates *)
  | Dlogic of logic_decl list   (* recursive functions and predicates *)
  | Dind   of ind_list          (* (co)inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)
*)
(** Declarations *)

(* module Hsdecl = Hashcons.Make (struct

  type t = decl

  let cs_equal (cs1,pl1) (cs2,pl2) =
    ls_equal cs1 cs2 && Lists.equal (Option.equal ls_equal) pl1 pl2

  let eq_td (ts1,td1) (ts2,td2) =
    ts_equal ts1 ts2 && Lists.equal cs_equal td1 td2

  let eq_ld (ls1,((_,f1),_)) (ls2,((_,f2),_)) =
    ls_equal ls1 ls2 && t_equal_strict f1 f2

  let eq_iax (pr1,fr1) (pr2,fr2) =
    pr_equal pr1 pr2 && t_equal_strict fr1 fr2

  let eq_ind (ps1,al1) (ps2,al2) =
    ls_equal ps1 ps2 && Lists.equal eq_iax al1 al2

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  s1, Dtype  s2 -> ts_equal s1 s2
    | Ddata  l1, Ddata  l2 -> Lists.equal eq_td l1 l2
    | Dparam s1, Dparam s2 -> ls_equal s1 s2
    | Dlogic l1, Dlogic l2 -> Lists.equal eq_ld l1 l2
    | Dind   (s1,l1), Dind (s2,l2) -> s1 = s2 && Lists.equal eq_ind l1 l2
    | Dprop (k1,pr1,f1), Dprop (k2,pr2,f2) ->
        k1 = k2 && pr_equal pr1 pr2 && t_equal_strict f1 f2
    | _,_ -> false

  let cs_hash (cs,pl) =
    (Hashcons.combine_big_list (Hashcons.combine_big_option ls_hash) (ls_hash cs) pl) 

  let hs_td (ts,td) = Hashcons.combine_big_list cs_hash (ts_hash ts) td

  let hs_ld (ls,((_,f),_)) = Hashcons.combine_big (ls_hash ls) (t_hash_strict f)

  let hs_prop (pr,f) = Hashcons.combine_big (pr_hash pr)(t_hash_strict f)

  let hs_ind (ps,al) = Hashcons.combine_big_list hs_prop (ls_hash ps) al

  let hs_kind = function
    | Plemma -> BigInt.of_int 11 | Paxiom -> BigInt.of_int 13 | Pgoal -> BigInt.of_int 17

  let hash d =  (match d.d_node with
    | Dtype  s -> ts_hash s
    | Ddata  l -> Hashcons.combine_big_list hs_td (BigInt.of_int 3) l
    | Dparam s -> ls_hash s
    | Dlogic l -> Hashcons.combine_big_list hs_ld (BigInt.of_int 5) l
    | Dind (_,l) -> Hashcons.combine_big_list hs_ind (BigInt.of_int 7) l
    | Dprop (k,pr,f) -> Hashcons.combine_big (hs_kind k) (hs_prop (pr,f)))

  let tag n d = { d with d_tag = Weakhtbl.create_tag n }

end) *)

module Decl = MakeMSHW (DeclTag)
(*struct
  type t = decl
  let tag d = d.d_tag
  let equal = (==) (*JOSH TODO equal*)
end)

module Sdecl = Decl.S
module Mdecl = Decl.M*)
module Wdecl = Decl.W
module Hdecl = Decl.H

(* let d_equal : decl -> decl -> bool = (==)

let d_hash d = Weakhtbl.tag_hash d.d_tag *)

(** Declaration constructors *)

(* let mk_decl node news =
  let d = {
      d_node = node;
      d_news = news;
      d_tag  = Weakhtbl.dummy_tag;
    } in
  match node with
  | Dprop (Pgoal,_,_) -> Hsdecl.unique d
  | _ -> Hsdecl.hashcons d *)


(* exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident *)
(* exception BadLogicDecl of lsymbol * lsymbol *)
(* exception BadConstructor of lsymbol *)

(* exception BadRecordField of lsymbol *)
exception BadRecordType of lsymbol * tysymbol
exception BadRecordUnnamed of lsymbol * tysymbol
exception BadRecordCons of lsymbol * tysymbol
(* exception RecordFieldMissing of lsymbol *)
(* exception DuplicateRecordField of lsymbol *)

(* exception EmptyDecl *)
(* exception EmptyAlgDecl of tysymbol *)
(* exception EmptyIndDecl of lsymbol *)

(* exception NonPositiveTypeDecl of tysymbol * lsymbol * ty *)

(* let news_id s id = Sid.add_new (ClashIdent id) id s *)

(* let syms_ts s ts = Sid.add ts.ts_name s
let syms_ls s ls = Sid.add ls.ls_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ty syms_ls s t *)

(* let syms_ty_decl ts =
  type_def_fold syms_ty Sid.empty ts.ts_def *)

(* let create_ty_decl ts =
  let news = Sid.singleton ts.ts_name in
  mk_decl (Dtype ts) news *)

(* let syms_data_decl tdl =
  let syms_constr syms (fs,_) =
    List.fold_left syms_ty syms fs.ls_args in
  let syms_decl syms (_,cl) =
    List.fold_left syms_constr syms cl in
  List.fold_left syms_decl Sid.empty tdl *)

(* let create_data_decl tdl =
  if tdl = [] then raise EmptyDecl;
  let add s (ts,_) = Sts.add ts s in
  let tss = List.fold_left add Sts.empty tdl in
  let check_proj tyv s tya ls = match ls with
    | None -> s
    | Some ({ls_args = [ptyv]; ls_value = Some ptya; ls_constr = b; ls_proj=true} as ls) ->
        if BigInt.is_zero b then
        (ty_equal_check tyv ptyv;
        ty_equal_check tya ptya;
        Sls.add_new (DuplicateRecordField ls) ls s)
        else raise (BadRecordField ls)
    | Some ls -> raise (BadRecordField ls)
  in
  let check_constr tys ty cll pjs news (fs,pl) =
    ty_equal_check ty (Opt.get_exn (BadConstructor fs) fs.ls_value);
    let fs_pjs =
      try List.fold_left2 (check_proj ty) Sls.empty fs.ls_args pl
      with Invalid_argument _ -> raise (BadConstructor fs) in
    if not (Sls.equal pjs fs_pjs) then
      raise (RecordFieldMissing (Sls.choose (Sls.diff pjs fs_pjs)));
    if not (BigInt.eq fs.ls_constr cll) then raise (BadConstructor fs);
    let vs = ty_freevars Stv.empty ty in
    let rec check seen ty = match ty.ty_node with
      | Tyvar v when Stv.mem v vs -> ()
      | Tyvar v -> raise (UnboundTypeVar v)
      | Tyapp (ts,tl) ->
          let now = Sts.mem ts tss in
          if seen && now
            then raise (NonPositiveTypeDecl (tys,fs,ty))
            else List.iter (check (seen || now)) tl
    in
    List.iter (check false) fs.ls_args;
    news_id news fs.ls_name
  in
  let check_decl news (ts,cl) =
    let cll = BigInt.of_int (List.length cl) in
    if cl = [] then raise (EmptyAlgDecl ts);
    if ts.ts_def <> NoDef then raise (IllegalTypeAlias ts);
    let news = news_id news ts.ts_name in
    let pjs = List.fold_left (fun s (_,pl) ->
      List.fold_left (Opt.fold Sls.add_left) s pl) Sls.empty cl in
    let news = Sls.fold (fun pj s -> news_id s pj.ls_name) pjs news in
    let ty = ty_app ts (List.map ty_var ts.ts_args) in
    List.fold_left (check_constr ts ty cll pjs) news cl
  in
  let news = List.fold_left check_decl Sid.empty tdl in
  mk_decl (Ddata tdl) news *)

(* let syms_param_decl ls =
  let syms = Opt.fold syms_ty Sid.empty ls.ls_value in
  List.fold_left syms_ty syms ls.ls_args

let create_param_decl ls =
  if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
  let news = Sid.singleton ls.ls_name in
  mk_decl (Dparam ls) news

let syms_logic_decl ldl =
  let syms_decl syms (ls,ld) =
    let _, e = open_ls_defn ld in
    let syms = List.fold_left syms_ty syms ls.ls_args in
    syms_term syms e
  in
  List.fold_left syms_decl Sid.empty ldl

(*JOSH: TODO hack*)
let lsym_ocaml_to_coq (x, (y, z, w)) =
  (x, ((y, z), w)) *)

let create_logic_decl ldl =
  if ldl = [] then raise EmptyDecl;
  let check_decl news (ls,((s,_),_)) =
    if not (ls_equal s ls) then raise (BadLogicDecl (ls, s));
    if not (BigInt.is_zero ls.ls_constr) || ls.ls_proj then raise (UnexpectedProjOrConstr ls);
    news_id news ls.ls_name
  in
  let news = List.fold_left check_decl Sid.empty ldl in
  let ldl = check_termination ldl in
  (*JOSH: TODO hack*)
  (* let ldl = List.map lsym_ocaml_to_coq ldl in *)
  mk_decl (Dlogic ldl) news

(* exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol *)

(* exception Found of lsymbol *)
(* let ls_mem s sps = if Sls.mem s sps then raise (Found s) else false *)
(* let t_pos_ps sps = t_s_all (fun _ -> true) (fun s -> not (ls_mem s sps))

let rec f_pos_ps sps pol f = match f.t_node, pol with
  | Tapp (s, _), Some false when ls_mem s sps -> false
  | Tapp (s, _), None when ls_mem s sps -> false
  | Tbinop (Tiff, f, g), _ ->
      f_pos_ps sps None f && f_pos_ps sps None g
  | Tbinop (Timplies, f, g), _ ->
      f_pos_ps sps (Option.map not pol) f && f_pos_ps sps pol g
  | Tnot f, _ ->
      f_pos_ps sps (Option.map not pol) f
  | Tif (f,g,h), _ ->
      f_pos_ps sps None f && f_pos_ps sps pol g && f_pos_ps sps pol h
  | _ -> TermTF.t_all (t_pos_ps sps) (f_pos_ps sps pol) f *)

  (* let lsyms_notin_tm (p: Sls.t) (t: term) : bool =
    Sls.for_all (fun x -> not (ls_in_tm x t)) p
  
  (*JOSH: different positivity check for now*)
  let rec ind_strict_pos (sps: Sls.t) (f: term) : bool =
    lsyms_notin_tm sps f ||
    match f.t_node with
  | Tapp (p, tms) -> Sls.mem p sps &&
    List.for_all (lsyms_notin_tm sps) tms
  | Tbinop (Timplies, f1, f2) -> ind_strict_pos sps f2 && lsyms_notin_tm sps f1
  | Tquant(q, tq) -> let ((_, _), f) = t_view_quant tq in ind_strict_pos sps f
  | Tbinop(Tand, f1, f2) | Tbinop(Tor, f1, f2) -> ind_strict_pos sps f1 && ind_strict_pos sps f2
  (*TODO: too restrictive?*)
  | Tlet(t, tb) -> let (_, t2) = t_view_bound tb in
    ind_strict_pos sps t2 && lsyms_notin_tm sps t
  | Tif(f1, f2, f3) ->
    lsyms_notin_tm sps f1 && ind_strict_pos sps f2 && ind_strict_pos sps f3
  | Tcase(t, pats) ->
      (*Maybe too restrictive*)
    lsyms_notin_tm sps t &&
    List.for_all (fun x -> let (_, t) = t_view_branch x in ind_strict_pos sps t) pats
  | _ -> false
  
  let rec ind_pos (sps: Sls.t) (f: term) : bool =
    match f.t_node with
    | Tapp(p, ts) -> Sls.mem p sps && List.for_all (lsyms_notin_tm sps) ts
    | Tquant(Tforall, tq) -> let (_, f) = t_view_quant tq in ind_pos sps f
    | Tlet(t, tb) -> (*TODO: too restrictive?*) lsyms_notin_tm sps t &&
      let (_, f) = t_view_bound tb in ind_pos sps f
    | Tbinop(Timplies, f1, f2) -> ind_strict_pos sps f1 && ind_pos sps f2
    | _ -> false
  
  (*Inductive predicates have a certain shape*)
  let rec valid_ind_form (ps: lsymbol) (f: term) : term option =
    match f.t_node with
    | Tapp(p, ts) -> if ls_equal p ps && (p.ls_args = rem_opt_list (List.map (fun x -> x.t_ty) ts)) then Some f else None (*TODO: do we need this check?*)
      (*NOTE: ignore length, implied by typing*)
    | Tbinop(Timplies, f1, f2) -> valid_ind_form ps f2
    | Tquant(Tforall, tq) -> let (_, f) = t_view_quant tq in valid_ind_form ps f
    | Tlet(t, tb) -> let (_, f) = t_view_bound tb in valid_ind_form ps f
    | _ -> None *)
  
  
(* let syms_ind_decl idl =
  let syms_ax syms (_,f) =
    syms_term syms f in
  let syms_decl syms (_,al) =
    List.fold_left syms_ax syms al in
  List.fold_left syms_decl Sid.empty idl *)
  
(* let create_ind_decl s idl =
  if idl = [] then raise EmptyDecl;
  let add acc (ps,_) = Sls.add ps acc in
  let sps = List.fold_left add Sls.empty idl in
  let check_ax ps news (pr,f) =
    (*JOSH - alt*)
    (*First, check for positivity*)
    (if not(ind_pos sps f) then raise (NonPositiveIndDecl(ps, pr, ps))); (*TODO: not ps*)
    match (valid_ind_form ps f) with
    | Some g ->
      (*Need g to check for freevars*)
      let gtv = t_ty_freevars Stv.empty g in
      let ftv = t_ty_freevars Stv.empty f in
      if not (Stv.subset ftv gtv) then
        raise (UnboundTypeVar (Stv.choose (Stv.diff ftv gtv)));
        news_id news pr.pr_name
    | None -> raise (InvalidIndDecl (ps, pr))
    in

    (* (*This does the transformation I proved correct (but less) - 
      transforms into lists of implications followed by main formula*)
    let rec clause acc f = match f.t_node with
      | Tquant (Tforall, f) ->
          let _,_,f = t_open_quant f in clause acc f
      | Tbinop (Timplies, g, f) -> clause (g::acc) f
      | Tlet (t, bf) ->
          let v, f = t_open_bound bf in
          clause (t_equ (t_var v) t :: acc) f
      | _ -> (acc, f)
    in
    let cls, g = clause [] (check_fvs f) in
    match g.t_node with
      | Tapp (s, tl) when ls_equal s ps ->
          List.iter2 check_tl ps.ls_args tl;
          (if not(ind_pos sps f) then raise (NonPositiveIndDecl(ps, pr, s))); (*TODO: not s*)
          (*(try ignore (ind_strict_pos sps f) (*(List.for_all (ind_strict_pos sps) (*(f_pos_ps sps (Some true))*) (g::cls))*)
          with Found ls -> raise (NonPositiveIndDecl (ps, pr, ls)));*)
          (* check for unbound type variables *)
          let gtv = t_ty_freevars Stv.empty g in
          let ftv = t_ty_freevars Stv.empty f in
          if not (Stv.subset ftv gtv) then
            raise (UnboundTypeVar (Stv.choose (Stv.diff ftv gtv)));
          news_id news pr.pr_name
      | _ -> raise (InvalidIndDecl (ps, pr))
  in *)
  let check_decl news (ps,al) =
    if al = [] then raise (EmptyIndDecl ps);
    if ps.ls_value <> None then raise (Term.PredicateSymbolExpected ps);
    let news = news_id news ps.ls_name in
    List.fold_left (check_ax ps) news al
  in
  let news = List.fold_left check_decl Sid.empty idl in
  mk_decl (Dind (s, idl)) news *)

(* let syms_prop_decl f =
  syms_term Sid.empty f *)

(* let create_prop_decl k p f =
  let news = news_id Sid.empty p.pr_name in
  mk_decl (Dprop (k,p,check_fvs f)) news *)

(* let get_used_syms_ty ty = syms_ty Sid.empty ty

let get_used_syms_decl d =
  match d.d_node with
  | Dtype ts -> syms_ty_decl ts
  | Ddata dl -> syms_data_decl dl
  | Dparam ls -> syms_param_decl ls
  | Dlogic ldl -> syms_logic_decl ldl
  | Dind (_, idl) -> syms_ind_decl idl
  | Dprop (_,_,f) -> syms_prop_decl f *)

(** Utilities *)

let decl_map fn d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> d
  | Dlogic l ->
      let fn (ls,ld) =
        let vl,e,close = open_ls_defn_cb ld in
        close ls vl (fn e)
      in
      create_logic_decl (List.map fn l)
  | Dind (s, l) ->
      let fn (pr,f) = pr, fn f in
      let fn (ps,l) = ps, List.map fn l in
      create_ind_decl s (List.map fn l)
  | Dprop (k,pr,f) ->
      create_prop_decl k pr (fn f)

let decl_fold fn acc d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> acc
  | Dlogic l ->
      let fn acc (_,ld) =
        let _,e = open_ls_defn ld in
        fn acc e
      in
      List.fold_left fn acc l
  | Dind (_, l) ->
      let fn acc (_,f) = fn acc f in
      let fn acc (_,l) = List.fold_left fn acc l in
      List.fold_left fn acc l
  | Dprop (_,_,f) ->
      fn acc f

let list_rpair_map_fold fn =
  let fn acc (x1,x2) =
    let acc,x2 = fn acc x2 in acc,(x1,x2) in
  Lists.map_fold_left fn

let decl_map_fold fn acc d = match d.d_node with
  | Dtype _ | Ddata _ | Dparam _ -> acc, d
  | Dlogic l ->
      let fn acc (ls,ld) =
        let vl,e,close = open_ls_defn_cb ld in
        let acc,e = fn acc e in
        acc, close ls vl e
      in
      let acc,l = Lists.map_fold_left fn acc l in
      acc, create_logic_decl l
  | Dind (s, l) ->
      let acc, l = list_rpair_map_fold (list_rpair_map_fold fn) acc l in
      acc, create_ind_decl s l
  | Dprop (k,pr,f) ->
      let acc, f = fn acc f in
      acc, create_prop_decl k pr f

module DeclTF = struct
  let decl_map fnT fnF = decl_map (TermTF.t_select fnT fnF)
  let decl_fold fnT fnF = decl_fold (TermTF.t_selecti fnT fnF)
  let decl_map_fold fnT fnF = decl_map_fold (TermTF.t_selecti fnT fnF)
end

(** Known identifiers *)

(* exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident *)

(* type known_map = decl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id) *)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if d_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id)
  in
  Mid.union check_known kn1 kn2

(* let known_add_decl kn0 decl =
  let kn = Mid.map (Util.const decl) decl.d_news in
  let check id decl0 _ =
    if d_equal decl0 decl
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id)
  in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff (get_used_syms_decl decl) kn in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk)) *)

(* let find_constructors kn ts =
  match (Mid.find ts.ts_name kn).d_node with
  | Dtype _ -> []
  | Ddata dl -> List.assq ts dl
  | Dparam _ | Dlogic _ | Dind _ | Dprop _ -> assert false

let find_inductive_cases kn ps =
  match (Mid.find ps.ls_name kn).d_node with
  | Dind (_, dl) -> List.assq ps dl
  | Dlogic _ | Dparam _ | Ddata _ -> []
  | Dtype _ | Dprop _ -> assert false

let find_logic_definition kn ls =
  match (Mid.find ls.ls_name kn).d_node with
  | Dlogic dl -> Some (List.assq ls dl)
  | Dparam _ | Dind _ | Ddata _ -> None
  | Dtype _ | Dprop _ -> assert false

let find_prop kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind (_, dl) ->
      let test (_,l) = List.mem_assq pr l in
      List.assq pr (snd (List.find test dl))
  | Dprop (_,_,f) -> f
  | Dtype _ | Ddata _ | Dparam _ | Dlogic _ -> assert false

let find_prop_decl kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind (_, dl) ->
      let test (_,l) = List.mem_assq pr l in
      Paxiom, List.assq pr (snd (List.find test dl))
  | Dprop (k,_,f) -> k,f
  | Dtype _ | Ddata _ | Dparam _ | Dlogic _ -> assert false *)

let check_match kn d =
  let rec check () t = match t.t_node with
    | Tcase (t1,bl) ->
        let get_constructors ts = List.map fst (find_constructors kn ts) in
        let pl = List.map (fun b -> let p,_ = t_open_branch b in [p]) bl in
        Loc.try2 ?loc:t.t_loc (Pattern.check_compile ~get_constructors) [t1] pl;
        t_fold check () t
    | _ -> t_fold check () t
  in
  decl_fold check () d
(* 
exception NonFoundedTypeDecl of tysymbol

let check_foundness kn d =
  let rec check_ts tss tvs ts =
    (* recursive data type, abandon *)
    if Sts.mem ts tss then false else
    let cl = find_constructors kn ts in
    (* an abstract type is inhabited iff
       all its type arguments are inhabited *)
    if cl == [] then Stv.is_empty tvs else
    (* an algebraic type is inhabited iff
       we can build a value of this type *)
    let tss = Sts.add ts tss in
    List.exists (check_constr tss tvs) cl
  and check_constr tss tvs (ls,_) =
    (* we can construct a value iff every
       argument is of an inhabited type *)
    List.for_all (check_type tss tvs) ls.ls_args
  and check_type tss tvs ty = match ty.ty_node with
    | Tyvar tv ->
        not (Stv.mem tv tvs)
    | Tyapp (ts,tl) ->
        let check acc tv ty =
          if check_type tss tvs ty then acc else Stv.add tv acc in
        let tvs = List.fold_left2 check Stv.empty ts.ts_args tl in
        check_ts tss tvs ts
  in
  match d.d_node with
  | Ddata tdl ->
      let check () (ts,_) =
        if check_ts Sts.empty Stv.empty ts
        then () else raise (NonFoundedTypeDecl ts)
      in
      List.fold_left check () tdl
  | _ -> () *)

(* let rec ts_extract_pos kn sts ts =
  assert (not (is_alias_type_def ts.ts_def));
  if ts_equal ts ts_func then [false;true] else
  if Sts.mem ts sts then List.map Util.ttrue ts.ts_args else
  match find_constructors kn ts with
    | [] ->
        List.map Util.ffalse ts.ts_args
    | csl ->
        let sts = Sts.add ts sts in
        let rec get_ty stv ty = match ty.ty_node with
          | Tyvar _ -> stv
          | Tyapp (ts,tl) ->
              let get acc pos =
                if pos then get_ty acc else ty_freevars acc in
              List.fold_left2 get stv (ts_extract_pos kn sts ts) tl
        in
        let get_cs acc (ls,_) = List.fold_left get_ty acc ls.ls_args in
        let negs = List.fold_left get_cs Stv.empty csl in
        List.map (fun v -> not (Stv.mem v negs)) ts.ts_args

let check_positivity kn d = match d.d_node with
  | Ddata tdl ->
      let add s (ts,_) = Sts.add ts s in
      let tss = List.fold_left add Sts.empty tdl in
      let check_constr tys (cs,_) =
        let rec check_ty ty = match ty.ty_node with
          | Tyvar _ -> ()
          | Tyapp (ts,tl) ->
              let check pos ty =
                if pos then check_ty ty else
                if ty_s_any (Sts.contains tss) ty then
                  raise (NonPositiveTypeDecl (tys,cs,ty)) in
              List.iter2 check (ts_extract_pos kn Sts.empty ts) tl
        in
        List.iter check_ty cs.ls_args
      in
      let check_decl (ts,cl) = List.iter (check_constr ts) cl in
      List.iter check_decl tdl
  | _ -> () *)

(* let known_add_decl kn d =
  let kn = known_add_decl kn d in
  check_positivity kn d;
  check_foundness kn d;
  check_match kn d;
  let d = check_termination_strict kn d in
  (d, kn) *)

(** Records *)

exception EmptyRecord

let parse_record kn fll =
  let fs = match fll with
    | [] -> raise EmptyRecord
    | (fs,_)::_ -> fs in
  let ts = match fs.ls_args with
    | [{ ty_node = Tyapp (ts,_) }] -> ts
    | _ -> raise (BadRecordField fs) in
  let cs, pjl = match find_constructors kn ts with
    | [cs,pjl] -> cs, List.map (Opt.get_exn (BadRecordUnnamed (fs, ts))) pjl
    | _hd1 :: _hd2 :: _ -> raise (BadRecordCons (fs, ts))
    | _ -> raise (BadRecordType (fs, ts)) in
  let pjs = Sls.of_list pjl in
  let flm = List.fold_left (fun m (pj,v) ->
    if not (Sls.mem pj pjs) then raise (BadRecordField pj) else
    Mls.add_new (DuplicateRecordField pj) pj v m) Mls.empty fll in
  cs,pjl,flm

let make_record kn fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let get_arg pj = Mls.find_exn (RecordFieldMissing pj) pj flm in
  fs_app cs (List.map get_arg pjl) ty

let make_record_update kn t fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let get_arg pj = match Mls.find_opt pj flm with
    | Some v -> v
    | None -> t_app_infer pj [t] in
  fs_app cs (List.map get_arg pjl) ty

let make_record_pattern kn fll ty =
  let cs,pjl,flm = parse_record kn fll in
  let s = ty_match Mtv.empty (Option.get cs.ls_value) ty in
  let get_arg pj = match Mls.find_opt pj flm with
    | Some v -> v
    | None -> pat_wild (ty_inst s (Option.get pj.ls_value))
  in
  pat_app cs (List.map get_arg pjl) ty
