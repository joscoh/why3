open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Pattern
open List0
open Trans
open Monads
open Datatypes
open CoqUtil


















(** val rewriteT :
    (term_node term_o) -> (BigInt.t*ty_node_c ty_o hashcons_ty,
    (term_node term_o)) errState **)

let rewriteT t0 =
  term_map tmap_let_default tmap_if_default tmap_app_default
    (fun _ _ r1 tb ->
    (@@) (fun res -> (fun x -> x) (t_attr_copy t0 res))
      (compile_bare_aux t_case_close t_let_close_simp (r1::[])
        (map (fun x -> ((fst (fst x))::[]),(snd x)) tb))) tmap_eps_default
    tmap_quant_default tmap_binop_default tmap_not_default t0

(** val compile_match : task -> (BigInt.t*hashcons_full, task) errState **)

let compile_match =
  decl_errst (fun d ->
    (@@) (fun x -> x)
      ( ( ( (errst_list ((decl_map (fun t0 ->  (rewriteT t0)) d)::[]))))))
    None

type state = { mt_map : lsymbol Mts.t; cc_map : lsymbol Mls.t;
               cp_map : lsymbol list Mls.t; pp_map : lsymbol Mls.t;
               kept_m : Sty.t Mts.t; tp_map : (decl*theory) Mid.t;
               inf_ts : Sts.t; ma_map : bool list Mts.t; keep_e : bool;
               keep_r : bool; keep_m : bool; no_ind : bool; no_inv : 
               bool; no_sel : bool }

(** val mt_map : state -> lsymbol Mts.t **)

let mt_map s =
  s.mt_map

(** val cc_map : state -> lsymbol Mls.t **)

let cc_map s =
  s.cc_map

(** val cp_map : state -> lsymbol list Mls.t **)

let cp_map s =
  s.cp_map

(** val pp_map : state -> lsymbol Mls.t **)

let pp_map s =
  s.pp_map

(** val kept_m : state -> Sty.t Mts.t **)

let kept_m s =
  s.kept_m

(** val tp_map : state -> (decl*theory) Mid.t **)

let tp_map s =
  s.tp_map

(** val inf_ts : state -> Sts.t **)

let inf_ts s =
  s.inf_ts

(** val ma_map : state -> bool list Mts.t **)

let ma_map s =
  s.ma_map

(** val keep_e : state -> bool **)

let keep_e s =
  s.keep_e

(** val keep_r : state -> bool **)

let keep_r s =
  s.keep_r

(** val keep_m : state -> bool **)

let keep_m s =
  s.keep_m

(** val no_ind : state -> bool **)

let no_ind s =
  s.no_ind

(** val no_inv : state -> bool **)

let no_inv s =
  s.no_inv

(** val no_sel : state -> bool **)

let no_sel s =
  s.no_sel

(** val state_with_mt_mat : state -> lsymbol Mts.t -> state **)

let state_with_mt_mat s mt_map0 =
  { mt_map = mt_map0; cc_map = s.cc_map; cp_map = s.cp_map; pp_map =
    s.pp_map; kept_m = s.kept_m; tp_map = s.tp_map; inf_ts = s.inf_ts;
    ma_map = s.ma_map; keep_e = s.keep_e; keep_r = s.keep_r; keep_m =
    s.keep_m; no_ind = s.no_ind; no_inv = s.no_inv; no_sel = s.no_sel }

(** val enc_ty : state -> ty_node_c ty_o option -> bool **)

let enc_ty s = function
| Some ty ->
  (match ty_node ty with
   | Tyvar _ -> false
   | Tyapp (ts, _) -> negb (Sty.mem ty (Mts.find_def Sty.empty ts s.kept_m)))
| None -> false

(** val uncompiled : string **)

let uncompiled =
  "eliminate_algebraic: compile_match required"

(** val option_get : 'a1 option -> 'a1 errorM **)

let option_get = function
| Some x ->  x
| None -> raise (Invalid_argument "option is None")

(** val is_forall : quant -> bool **)

let is_forall = function
| Tforall -> true
| Texists -> false

(** val is_exists : quant -> bool **)

let is_exists q =
  negb (is_forall q)

(** val is_and : binop -> bool **)

let is_and = function
| Tand -> true
| _ -> false

(** val is_or : binop -> bool **)

let is_or = function
| Tor -> true
| _ -> false

(** val rewriteT' :
    known_map -> state -> (term_node term_o) -> (BigInt.t*ty_node_c ty_o
    hashcons_ty, (term_node term_o)) errState **)

let rec rewriteT' kn s t0 =
  match t_node t0 with
  | Tapp (ls, args) ->
    if (&&) (BigInt.pos ls.ls_constr) (enc_ty s (t_ty t0))
    then (@@) (fun args0 ->
           (@@) (fun cc ->
             (@@) (fun t1 -> (fun x -> x) (t_attr_copy t0 t1))
               ( (t_app cc args0 (t_ty t0)))) ( (Mls.find ls s.cc_map)))
           (errst_list (map (rewriteT' kn s) args))
    else (match args with
          | [] ->
            TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)
              (rewriteF' kn s Svs.empty true) t0
          | arg::l ->
            (match l with
             | [] ->
               if (&&) ls.ls_proj (enc_ty s (t_ty t0))
               then (@@) (fun arg0 ->
                      (@@) (fun pp ->
                        (@@) (fun t1 -> (fun x -> x) (t_attr_copy t0 t1))
                          ( (t_app pp (arg0::[]) (t_ty t0))))
                        ( (Mls.find ls s.pp_map))) (rewriteT' kn s arg)
               else TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)
                      (rewriteF' kn s Svs.empty true) t0
             | _::_ ->
               TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)
                 (rewriteF' kn s Svs.empty true) t0))
  | Tcase (t1, bl) ->
    if negb (enc_ty s (t_ty t1))
    then TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)
           (rewriteF' kn s Svs.empty true) t0
    else (@@) (fun t2 ->
           let mk_br = fun x br ->
             let w,m = x in
             let b1 = t_view_branch br in
             let p = fst b1 in
             let e = snd b1 in
             (@@) (fun e0 ->
               match pat_node p with
               | Pwild -> (fun x -> x) ((Some e0),m)
               | Papp (cs, pl) ->
                 let add_var = fun e1 p0 pj ->
                   match pat_node p0 with
                   | Pvar v ->
                     (@@) (fun a1 ->  (t_let_close_simp v a1 e1))
                       ( (fs_app pj (t2::[]) v.vs_ty))
                   | _ ->  (raise (Printer.UnsupportedTerm (t0,uncompiled)))
                 in
                 (@@) (fun pjl ->
                   (@@) (fun e1 ->
                     match e1 with
                     | Some e2 -> (fun x -> x) (w,(Mls.add cs e2 m))
                     | None ->  (raise (Invalid_argument "List.fold_left2")))
                     (fold_left2_errst add_var e0 pl pjl))
                   ( (Mls.find cs s.cp_map))
               | _ ->  (raise (Printer.UnsupportedTerm (t0,uncompiled))))
               (rewriteT' kn s e)
           in
           (@@) (fun wm ->
             let w,m = wm in
             let find0 = fun x ->
               match Mls.find_opt (fst x) m with
               | Some y ->  y
               | None -> option_get w
             in
             (@@) (fun ts ->
               (@@) (fun res -> (fun x -> x) (t_attr_copy t0 res))
                 ((@@) (fun l ->
                   match l with
                   | [] ->
                     (@@) (fun l0 ->  (t_app l0 (t2::l) (t_ty t0)))
                       ( (Mts.find ts s.mt_map))
                   | t3::l0 ->
                     (match l0 with
                      | [] -> (fun x -> x) t3
                      | _::_ ->
                        (@@) (fun l1 ->  (t_app l1 (t2::l) (t_ty t0)))
                          ( (Mts.find ts s.mt_map))))
                   ( (errorM_list (map find0 (find_constructors kn ts))))))
               (match t_ty t2 with
                | Some ty ->
                  (match ty_node ty with
                   | Tyvar _ ->
                      (raise (Printer.UnsupportedTerm (t0,uncompiled)))
                   | Tyapp (ts, _) -> (fun x -> x) ts)
                | None ->  (raise (Printer.UnsupportedTerm (t0,uncompiled)))))
             (foldl_errst mk_br bl (None,Mls.empty))) (rewriteT' kn s t1)
  | _ ->
    TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)
      (rewriteF' kn s Svs.empty true) t0

(** val rewriteF' :
    known_map -> state -> Svs.t -> bool -> (term_node term_o) ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, (term_node term_o)) errState **)

and rewriteF' kn s av sign f =
  match t_node f with
  | Tlet (t1, _) ->
    let av0 = Mvs.set_diff av (t_vars t1) in
    TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
      (rewriteF' kn s av0) sign f
  | Tcase (t1, bl) ->
    if negb (enc_ty s (t_ty t1))
    then TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
           (rewriteF' kn s av) sign f
    else (@@) (fun t2 ->
           let av' = Mvs.set_diff av (t_vars t2) in
           let mk_br = fun x br ->
             let w,m = x in
             let b1 = t_view_branch br in
             let p = fst b1 in
             let e = snd b1 in
             (@@) (fun e0 ->
               match pat_node p with
               | Pwild -> (fun x -> x) ((Some e0),m)
               | Papp (cs, pl) ->
                 let get_var = fun p0 ->
                   match pat_node p0 with
                   | Pvar v ->  v
                   | _ -> raise (Printer.UnsupportedTerm (f,uncompiled))
                 in
                 (@@) (fun vs -> (fun x -> x) (w,(Mls.add cs (vs,e0) m)))
                   ( (errorM_list (map get_var pl)))
               | _ ->  (raise (Printer.UnsupportedTerm (f,uncompiled))))
               (rewriteF' kn s av' sign e)
           in
           (@@) (fun wm ->
             let w,m = wm in
             let find0 = fun x ->
               let cs = fst x in
               (@@) (fun vle ->
                 let vl,e = vle in
                 (@@) (fun ls ->
                   (@@) (fun hd ->
                     match t_node t2 with
                     | Tvar v ->
                       if Svs.mem v av
                       then 
                              ((@@) (fun hd0 ->
                                if sign
                                then t_forall_close_simp vl [] hd0
                                else t_exists_close_simp vl [] hd0)
                                (t_let_close_simp v hd e))
                       else (@@) (fun hd0 ->
                              
                                (if sign
                                 then (@@) (fun t3 ->
                                        t_forall_close_simp vl [] t3)
                                        (t_implies_simp hd0 e)
                                 else (@@) (fun t3 ->
                                        t_exists_close_simp vl [] t3)
                                        (t_and_simp hd0 e))) ( (t_equ t2 hd))
                     | _ ->
                       (@@) (fun hd0 ->
                         
                           (if sign
                            then (@@) (fun t3 ->
                                   t_forall_close_simp vl [] t3)
                                   (t_implies_simp hd0 e)
                            else (@@) (fun t3 ->
                                   t_exists_close_simp vl [] t3)
                                   (t_and_simp hd0 e))) ( (t_equ t2 hd)))
                     ( (t_app ls (map t_var vl) (t_ty t2))))
                   ( (Mls.find cs s.cc_map)))
                 (match Mls.find_opt cs m with
                  | Some x0 -> (fun x -> x) x0
                  | None ->
                    let get_var = fun pj ->
                      (@@) (fun t3 ->
                        (@@) (fun ty ->
                           ( (create_vsymbol (id_fresh1 "w") ty)))
                          ( (t_type t3))) ( (t_app_infer pj (t2::[])))
                    in
                    (@@) (fun vs ->
                      (@@) (fun l ->
                        (@@) (fun w1 -> (fun x -> x) (l,w1)) ( (option_get w)))
                        (errst_list (map get_var vs)))
                      ( (Mls.find cs s.cp_map)))
             in
             (@@) (fun ts ->
               let op = if sign then t_and_simp else t_or_simp in
               (@@) (fun res -> (fun x -> x) (t_attr_copy f res))
                 (map_join_left_errst t_true find0 (fun x y ->  (op x y))
                   (find_constructors kn ts)))
               (
                 (match t_ty t2 with
                  | Some ty ->
                    (match ty_node ty with
                     | Tyvar _ ->
                       raise (Printer.UnsupportedTerm (f,uncompiled))
                     | Tyapp (ts, _) ->  ts)
                  | None -> raise (Printer.UnsupportedTerm (f,uncompiled)))))
             (foldl_errst mk_br bl (None,Mls.empty))) (rewriteT' kn s t1)
  | Tquant (q, bf) ->
    if (||) ((&&) (is_forall q) sign) ((&&) (is_exists q) (negb sign))
    then let p,close = t_view_quant_cb bf in
         let p0,f1 = p in
         let vl,tr = p0 in
         (@@) (fun tr0 ->
           let av0 = fold_right Svs.add av vl in
           (@@) (fun f2 ->
             (@@) (fun c ->
               (@@) (fun t1 -> (fun x -> x) (t_attr_copy f t1))
                 ( (t_quant_simp1 q c))) ( (close vl tr0 f2)))
             (rewriteF' kn s av0 sign f1))
           (TermTFAlt.tr_map_errst (rewriteT' kn s)
             (rewriteF' kn s Svs.empty sign) tr)
    else TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
           (rewriteF' kn s Svs.empty) sign f
  | Tbinop (o, _, _) ->
    if (||) ((&&) (is_and o) sign) ((&&) (is_or o) (negb sign))
    then TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
           (rewriteF' kn s av) sign f
    else TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
           (rewriteF' kn s Svs.empty) sign f
  | _ ->
    TermTFAlt.t_map_sign_errst_unsafe (fun _ -> rewriteT' kn s)
      (rewriteF' kn s Svs.empty) sign f

(** val add_selector :
    (state*task) -> (ty_node_c ty_o) tysymbol_o -> ty_node_c ty_o ->
    (lsymbol*'a1) list -> (BigInt.t*hashcons_full, state*task) errState **)

let add_selector st ts ty csl =
  let s = fst st in
  let tsk = snd st in
  if s.no_sel
  then (fun x -> x) st
  else let mt_id =
         id_derive1 ((^) "match_" (ts_name ts).id_string) (ts_name ts)
       in
       (@@) (fun v ->
         (@@) (fun mt_ty ->
           let mt_al = ty::(rev_map (fun _ -> mt_ty) csl) in
           (@@) (fun mt_ls ->
             let mt_map0 = Mts.add ts mt_ls s.mt_map in
             (@@) (fun task0 ->
               let mt_vs = fun _ -> create_vsymbol (id_fresh1 "z") mt_ty in
               (@@) (fun mt_vl ->
                 let mt_tl = rev_map t_var mt_vl in
                 let mt_add = fun tsk0 x t0 ->
                   let cs = fst x in
                   let id =
                     (^) mt_ls.ls_name.id_string
                       ((^) "_" cs.ls_name.id_string)
                   in
                   (@@) (fun pr ->
                     (@@) (fun vl ->
                       (@@) (fun newcs ->
                         (@@) (fun v0 ->
                           (@@) (fun hd ->
                             (@@) (fun hd0 ->
                               let vl0 = rev_append mt_vl (rev vl) in
                               (@@) (fun e ->
                                 (@@) (fun ax ->
                                   add_prop_decl tsk0 Paxiom pr ax)
                                   ( (t_forall_close vl0 [] e)))
                                 ( ( (t_equ hd0 t0))))
                               ( ( (fs_app mt_ls (hd::mt_tl) mt_ty))))
                             ( ( (fs_app newcs (rev_map t_var vl) v0))))
                           ( (option_get cs.ls_value)))
                         ( (Mls.find cs s.cc_map)))
                       (
                         (
                           (st_list
                             (rev_map (create_vsymbol (id_fresh1 "u"))
                               cs.ls_args)))))
                     ( ( (create_prsymbol (id_derive1 id cs.ls_name))))
                 in
                 (@@) (fun task1 ->
                   (fun x -> x) ((state_with_mt_mat s mt_map0),task1))
                   (fold_left2_errst' mt_add task0 csl mt_tl))
                 ( ( (st_list (rev_map mt_vs csl)))))
               (add_param_decl tsk mt_ls))
             ( ( (create_fsymbol1 mt_id mt_al mt_ty)))) ( ( ( (ty_var v)))))
         ( ( (create_tvsymbol (id_fresh1 "a"))))
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



(* a type constructor generates an infinite type if either it is tagged by
   meta_infinite or one of its "material" arguments is an infinite type *)

let meta_infinite = register_meta "infinite_type" [MTtysymbol]
  ~desc:"Specify@ that@ the@ given@ type@ has@ always@ an@ infinite@ \
         cardinality."

let meta_material = register_meta "material_type_arg" [MTtysymbol;MTint]
  ~desc:"If@ the@ given@ type@ argument@ is@ instantiated@ by@ an@ infinite@ \
         type@ then@ the@ associated@ type@ constructor@ is@ infinite"

let meta_alg_kept = register_meta "algebraic:kept" [MTty]
  ~desc:"Keep@ primitive@ operations@ over@ this@ algebraic@ type."

let get_material_args matl =
  let add_arg acc = function
    | [MAts ts; MAint i] ->
        let acc, mat = try acc, Mts.find ts acc with Not_found ->
          let mat = Array.make (List.length ts.ts_args) false in
          Mts.add ts mat acc, mat in
        Array.set mat i true;
        acc
    | _ -> assert false
  in
  Mts.map Array.to_list (List.fold_left add_arg Mts.empty matl)

let is_infinite_ty inf_ts ma_map =
  let rec inf_ty ty = match ty.ty_node with
    | Tyapp (ts,[_;ty]) when ts_equal ts ts_func -> inf_ty ty
    | Tyapp (ts,_) when Mts.mem ts inf_ts -> true
    | Tyapp (ts,_) when not (Mts.mem ts ma_map) -> false
    | Tyapp (ts,l) ->
        let mat = Mts.find ts ma_map in
        List.exists2 (fun mat ty -> mat && inf_ty ty) mat l
    | _ -> false (* FIXME? can we have non-ground types here? *)
  in
  inf_ty

(** Compile match patterns *)

(* let rec rewriteT t0 = match t0.t_node with
  | Tcase (t,bl) ->
      let t = rewriteT t in
      let mk_b b = let p,t = t_open_branch b in [p], rewriteT t in
      let mk_case = t_case_close and mk_let = t_let_close_simp in
      let res = Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl) in
      t_attr_copy t0 res
  | _ -> t_map rewriteT t0 *)

(* let compile_match = Trans.decl (fun d -> [decl_map rewriteT d]) None *)

(** Eliminate algebraic types and match statements *)

(* type state = {
  mt_map : lsymbol Mts.t;       (* from type symbols to selector functions *)
  cc_map : lsymbol Mls.t;       (* from old constructors to new constructors *)
  cp_map : lsymbol list Mls.t;  (* from old constructors to new projections *)
  pp_map : lsymbol Mls.t;       (* from old projections to new projections *)
  kept_m : Sty.t Mts.t;         (* should we keep constructors/projections/Tcase for this type? *)
  tp_map : (decl*theory) Mid.t; (* skipped tuple symbols *)
  inf_ts : Sts.t;               (* infinite types *)
  ma_map : bool list Mts.t;     (* material type arguments *)
  keep_e : bool;                (* keep monomorphic enumeration types *)
  keep_r : bool;                (* keep non-recursive records *)
  keep_m : bool;                (* keep monomorphic data types *)
  no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                (* do not generate selector *)
}

let enc_ty state = function
  | Some({ ty_node = Tyapp (ts,_) } as ty) ->
    not (Sty.mem ty (Mts.find_def Sty.empty ts state.kept_m))
  | _ -> assert false *)

(* let uncompiled = "eliminate_algebraic: compile_match required" *)

let rewriteT = rewriteT'
let rewriteF = rewriteF'

(* let rec rewriteT kn state t = match t.t_node with
  | Tcase (t1,bl) when enc_ty state t1.t_ty ->
      let t1 = rewriteT kn state t1 in
      let mk_br (w,m) br =
        let (p,e) = t_open_branch br in
        let e = rewriteT kn state e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let add_var e p pj = match p.pat_node with
              | Pvar v -> t_let_close_simp v (fs_app pj [t1] v.vs_ty) e
              | _ -> Printer.unsupportedTerm t uncompiled
            in
            let pjl = Mls.find cs state.cp_map in
            let e = List.fold_left2 add_var e pl pjl in
            w, Mls.add cs e m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find (cs,_) = try Mls.find cs m with Not_found -> Option.get w in
      let ts = match t1.t_ty with
        | Some { ty_node = Tyapp (ts,_) } -> ts
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      let res =
        begin match List.map find (find_constructors kn ts) with
        | [t] -> t
        | tl  -> t_app (Mts.find ts state.mt_map) (t1::tl) t.t_ty
        end
      in
      (* Preserve attributes and location of t *)
      t_attr_copy t res
  | Tapp (ls, args) when BigInt.pos ls.ls_constr && enc_ty state t.t_ty ->
      let args = List.map (rewriteT kn state) args in
      t_attr_copy t (t_app (Mls.find ls state.cc_map) args t.t_ty)
  | Tapp (ls, [arg]) when ls.ls_proj && enc_ty state arg.t_ty ->
      let arg = rewriteT kn state arg in
      t_attr_copy t (t_app (Mls.find ls state.pp_map) [arg] t.t_ty)
  | _ ->
      TermTF.t_map (rewriteT kn state) (rewriteF kn state Svs.empty true) t

and rewriteF kn state av sign f =
  match f.t_node with
  | Tcase (t1,bl) when enc_ty state t1.t_ty ->
      let t1 = rewriteT kn state t1 in
      let av' = Mvs.set_diff av (t_vars t1) in
      let mk_br (w,m) br =
        let (p,e) = t_open_branch br in
        let e = rewriteF kn state av' sign e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let get_var p = match p.pat_node with
              | Pvar v -> v
              | _ -> Printer.unsupportedTerm f uncompiled
            in
            w, Mls.add cs (List.map get_var pl, e) m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedTerm f uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find (cs,_) =
        let vl,e = try Mls.find cs m with Not_found ->
          let var = create_vsymbol (id_fresh "w") in
          let get_var pj = var (t_type (t_app_infer pj [t1])) in
          List.map get_var (Mls.find cs state.cp_map), Option.get w
        in
        let hd = t_app (Mls.find cs state.cc_map) (List.map t_var vl) t1.t_ty in
        match t1.t_node with
        | Tvar v when Svs.mem v av ->
            let hd = t_let_close_simp v hd e in if sign
            then t_forall_close_simp vl [] hd
            else t_exists_close_simp vl [] hd
        | _ ->
            let hd = t_equ t1 hd in if sign
            then t_forall_close_simp vl [] (t_implies_simp hd e)
            else t_exists_close_simp vl [] (t_and_simp     hd e)
      in
      let ts = match t1.t_ty with
        | Some { ty_node = Tyapp (ts,_) } -> ts
        | _ -> Printer.unsupportedTerm f uncompiled
      in
      let op = if sign then t_and_simp else t_or_simp in
      let res = Lists.map_join_left find op (find_constructors kn ts) in
      (* Preserve attributes and location of f *)
      t_attr_copy f res
  | Tquant (q, bf) when (q = Tforall && sign) || (q = Texists && not sign) ->
      let vl, tr, f1, close = t_open_quant_cb bf in
      let tr = TermTF.tr_map (rewriteT kn state)
                      (rewriteF kn state Svs.empty sign) tr in
      let av = List.fold_right Svs.add vl av in
      let f1 = rewriteF kn state av sign f1 in
      (* Preserve attributes and location of f *)
      t_attr_copy f (t_quant_simp q (close vl tr f1))
  | Tbinop (o, _, _) when (o = Tand && sign) || (o = Tor && not sign) ->
      TermTF.t_map_sign (Util.const (rewriteT kn state))
        (rewriteF kn state av) sign f
  | Tlet (t1, _) ->
      let av = Mvs.set_diff av (t_vars t1) in
      TermTF.t_map_sign (Util.const (rewriteT kn state))
        (rewriteF kn state av) sign f
  | _ ->
      TermTF.t_map_sign (Util.const (rewriteT kn state))
        (rewriteF kn state Svs.empty) sign f *)

(* let add_selector (state,task) ts ty csl =
  if state.no_sel then state, task else
  (* declare the selector function *)
  let mt_id = id_derive ("match_" ^ ts.ts_name.id_string) ts.ts_name in
  let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in
  let mt_al = ty :: List.rev_map (fun _ -> mt_ty) csl in
  let mt_ls = create_fsymbol mt_id mt_al mt_ty in
  let mt_map = Mts.add ts mt_ls state.mt_map in
  let task  = add_param_decl task mt_ls in
  (* define the selector function *)
  let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in
  let mt_vl = List.rev_map mt_vs csl in
  let mt_tl = List.rev_map t_var mt_vl in
  let mt_add tsk (cs,_) t =
    let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let newcs = Mls.find cs state.cc_map in
    let hd = fs_app newcs (List.rev_map t_var vl) (Option.get cs.ls_value) in
    let hd = fs_app mt_ls (hd::mt_tl) mt_ty in
    let vl = List.rev_append mt_vl (List.rev vl) in
    let ax = t_forall_close vl [] (t_equ hd t) in
    add_prop_decl tsk Paxiom pr ax
  in
  let task = List.fold_left2 mt_add task csl mt_tl in
  { state with mt_map }, task *)

let add_selector acc ts ty = function
  | [_] -> acc
  | csl -> add_selector acc ts ty csl

let add_indexer (state,task) ts ty csl =
  (* declare the indexer function *)
  let mt_id = id_derive ("index_" ^ ts.ts_name.id_string) ts.ts_name in
  let mt_ls = create_fsymbol mt_id [ty] ty_int in
  let task  = add_param_decl task mt_ls in
  (* define the indexer function *)
  let index = ref (-1) in
  let mt_add tsk (cs,_) =
    incr index;
    let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let newcs = Mls.find cs state.cc_map in
    let hd = fs_app newcs (List.rev_map t_var vl) (Option.get cs.ls_value) in
    let ax = t_equ (fs_app mt_ls [hd] ty_int) (t_nat_const !index) in
    let ax = t_forall_close (List.rev vl) [[hd]] ax in
    add_prop_decl tsk Paxiom pr ax
  in
  let task = List.fold_left mt_add task csl in
  state, task

let add_discriminator (state,task) ts ty csl =
  let d_add (c1,_) task (c2,_) =
    let id = c1.ls_name.id_string ^ "_" ^ c2.ls_name.id_string in
    let pr = create_prsymbol (id_derive id ts.ts_name) in
    let ul = List.rev_map (create_vsymbol (id_fresh "u")) c1.ls_args in
    let vl = List.rev_map (create_vsymbol (id_fresh "v")) c2.ls_args in
    let newc1 = Mls.find c1 state.cc_map in
    let newc2 = Mls.find c2 state.cc_map in
    let t1 = fs_app newc1 (List.rev_map t_var ul) ty in
    let t2 = fs_app newc2 (List.rev_map t_var vl) ty in
    let ax = t_neq t1 t2 in
    let ax = t_forall_close (List.rev vl) [[t2]] ax in
    let ax = t_forall_close (List.rev ul) [[t1]] ax in
    add_prop_decl task Paxiom pr ax
  in
  let rec dl_add task = function
    | c :: cl -> dl_add (List.fold_left (d_add c) task cl) cl
    | _ -> task
  in
  state, dl_add task csl

let add_indexer acc ts ty = function
  | [_] -> acc
  | csl when not (fst acc).no_ind -> add_indexer acc ts ty csl
  | csl when List.length csl <= 16 -> add_discriminator acc ts ty csl
  | _ -> acc

let complete_projections csl =
  let conv_c (c, pjl) =
    let conv_p i = function
      | (None, ty) ->
         let id = Printf.sprintf "%s_proj_%d" c.ls_name.id_string (i+1) in
         let id = id_derive id c.ls_name in
         Some (create_fsymbol ~proj:true id [Option.get c.ls_value] ty)
      | (pj, _) -> pj
    in
    (c, List.mapi conv_p (List.combine pjl c.ls_args))
  in
  List.map conv_c csl

(* Adding meta so that counterexamples consider this new projection as a
   counterexample projection. This allow counterexamples to appear for
   these values.
*)
let add_meta_model_projection tsk ls =
  add_meta tsk meta_model_projection [MAls ls]

let add_projections (state,task) _ts _ty csl =
  (* declare and define the projection functions *)
  let pj_add (cp_map,pp_map,tsk) (cs,pl) =
    let vl = List.map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let tl = List.map t_var vl in
    let hd = fs_app (Mls.find cs state.cc_map) tl (Option.get cs.ls_value) in
    let add (pjl,pp_map,tsk) t pj =
      let pj = Option.get pj in
      let ls,pp_map =
        match Mls.find pj pp_map with
        | pj -> pj,pp_map
        | exception Not_found ->
          let id = id_clone pj.ls_name in
          let ls = create_lsymbol id pj.ls_args pj.ls_value in
          ls,Mls.add pj ls pp_map
      in
      let tsk = add_param_decl tsk ls in
      let id = id_derive (ls.ls_name.id_string ^ "'def") ls.ls_name in
      let pr = create_prsymbol id in
      let hh = t_app ls [hd] t.t_ty in
      let ax = t_forall_close vl [] (t_equ hh t) in
      let tsk = add_prop_decl tsk Paxiom pr ax in
      let tsk = add_meta_model_projection tsk ls in
      ls::pjl,pp_map,tsk
    in
    let pjl,pp_map,tsk = List.fold_left2 add ([],pp_map,tsk) tl pl in
    Mls.add cs (List.rev pjl) cp_map, pp_map, tsk
  in
  let csl = complete_projections csl in
  let cp_map, pp_map, task =
    List.fold_left pj_add (state.cp_map, state.pp_map, task) csl
  in
  { state with cp_map; pp_map }, task

let add_inversion (state,task) ts ty csl =
  if state.no_inv then state, task else
  (* add the inversion axiom *)
  let ax_id = ts.ts_name.id_string ^ "_inversion" in
  let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in
  let ax_vs = create_vsymbol (id_fresh "u") ty in
  let ax_hd = t_var ax_vs in
  let mk_cs (cs,_) =
    let pjl = Mls.find cs state.cp_map in
    let app pj = t_app_infer pj [ax_hd] in
    let cs = Mls.find cs state.cc_map in
    t_equ ax_hd (fs_app cs (List.map app pjl) ty) in
  let ax_f = Lists.map_join_left mk_cs t_or csl in
  let ax_f = t_forall_close [ax_vs] [] ax_f in
  state, add_prop_decl task Paxiom ax_pr ax_f

let kept_no_case used state = function
  | ts, [_,_::_] -> state.keep_r && not (Sid.mem ts.ts_name used)
  | { ts_args = [] } as ts, csl ->
     state.keep_e && List.for_all (fun (_,l) -> l = []) csl &&
       not (Mts.mem ts state.kept_m)
  | _ -> false

let add_axioms used (state,task) ((ts,csl) as d) =
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  if kept_no_case used state d then
    (* for kept enums and records, we still use the selector function, but
       always use the non-encoded projections and constructors *)
    let state =
      let fold_c state (c, pjs) =
        let pjs = List.map Option.get pjs in
        let cc_map = Mls.add c c state.cc_map in
        let cp_map = Mls.add c pjs state.cp_map in
        let fold_pj pp_map pj = Mls.add pj pj pp_map in
        let pp_map = List.fold_left fold_pj state.pp_map pjs in
        { state with cc_map; cp_map; pp_map }
      in
      List.fold_left fold_c state csl
    in
    add_selector (state, task) ts ty csl
  else if ts.ts_args <> [] || not (Mts.mem ts state.kept_m) then
    (* declare constructors as abstract functions *)
    let cs_add (state,task) (cs,_) =
      let id = id_clone cs.ls_name in
      let ls = create_lsymbol id cs.ls_args cs.ls_value in
      { state with cc_map = Mls.add cs ls state.cc_map },add_param_decl task ls
    in
    let state,task = List.fold_left cs_add (state,task) csl in
    (* add selector, projections, and inversion axiom *)
    let state,task = add_selector (state,task) ts ty csl in
    let state,task = add_indexer (state,task) ts ty csl in
    let state,task = add_projections (state,task) ts ty csl in
    let state,task = add_inversion (state,task) ts ty csl in
    state, task
  else state,task

let add_tags mts (state,task) (ts,csl) =
  let rec mat_ts sts ts csl =
    let sts = Sts.add ts sts in
    let add s (ls,_) = List.fold_left (mat_ty sts) s ls.ls_args in
    let stv = List.fold_left add Stv.empty csl in
    List.map (Stv.contains stv) ts.ts_args
  and mat_ty sts stv ty = match ty.ty_node with
    | Tyvar tv -> Stv.add tv stv
    | Tyapp (ts,tl) ->
        if Sts.mem ts sts then raise Exit; (* infinite type *)
        let matl = try Mts.find ts state.ma_map with
          Not_found -> mat_ts sts ts (Mts.find_def [] ts mts) in
        let add s mat ty = if mat then mat_ty sts s ty else s in
        List.fold_left2 add stv matl tl
  in try
    let matl = mat_ts state.inf_ts ts csl in
    let state = { state with ma_map = Mts.add ts matl state.ma_map } in
    let c = ref (-1) in
    let add_material task m =
      incr c;
      if m then add_meta task meta_material [MAts ts; MAint !c] else task
    in
    state, List.fold_left add_material task matl
  with Exit ->
    let state = { state with inf_ts = Sts.add ts state.inf_ts } in
    state, add_meta task meta_infinite [MAts ts]

let has_nested_use sts csl =
  let check_c (c, _) =
    let check_arg ty = match ty.ty_node with
    | Tyapp (_, tl) -> List.exists (ty_s_any (Fun.flip Sts.mem sts)) tl
    | Tyvar _ -> false
    in
    List.exists check_arg c.ls_args
  in
  List.exists check_c csl

let comp t (state,task) = match t.task_decl.td_node with
  | Decl ({ d_node = Ddata dl } as d) ->
      let used = get_used_syms_decl d in
      let sts = List.fold_left (fun acc (ts, _) -> Sts.add ts acc) Sts.empty dl in
      let fold_kept_m state (ts,csl as d) =
          if has_nested_use sts csl then { state with kept_m = Mts.remove ts state.kept_m }
          else if ts.ts_args = [] && state.keep_m && not (kept_no_case used state d) then
            { state with kept_m = Mts.add ts (Sty.singleton (ty_app ts [])) state.kept_m }
          else state
      in
      let state = List.fold_left fold_kept_m state dl in
      (* add projections to records with keep_recs *)
      let conv_t ((ts, csl) as d) =
        (* complete_projections can only be called on records or enums, so it
           won't introduced ill-formed projections *)
        if kept_no_case used state d then (ts, complete_projections csl) else d
      in
      let dl = List.map conv_t dl in
      (* add type declarations *)
      let concrete d = Mts.mem (fst d) state.kept_m || kept_no_case used state d in
      let dl_concr, dl_abs = List.partition concrete dl in
      let task = List.fold_left (fun t (ts,_) -> add_ty_decl t ts) task dl_abs in
      let task = if dl_concr = [] then task else add_data_decl task dl_concr in
      (* add needed functions and axioms *)
      let state, task = List.fold_left (add_axioms used) (state,task) dl in
      (* add the tags for infinite types and material arguments *)
      let mts = List.fold_right (fun (t,l) -> Mts.add t l) dl Mts.empty in
      let state, task = List.fold_left (add_tags mts) (state,task) dl in
      (* return the updated state and task *)
      state, task
  | Decl d ->
      let fnT = rewriteT t.task_known state in
      let fnF = rewriteF t.task_known state Svs.empty true in
      state, add_decl task (DeclTF.decl_map fnT fnF d)
  | _ ->
      state, add_tdecl task t.task_decl

let comp t (state,task) = match t.task_decl.td_node with
  | Use {th_decls = [{td_node = Decl ({d_node = Ddata [ts,_]})}]}
    when is_ts_tuple ts ->
      state, task
  | Decl ({ d_node = Ddata [ts,_] } as d) when is_ts_tuple ts ->
      let th = tuple_theory (List.length ts.ts_args) in
      let tp_map = Mid.add ts.ts_name (d,th) state.tp_map in
      { state with tp_map = tp_map }, task
  | Decl d ->
      let rstate,rtask = ref state, ref task in
      let add _ (d,th) () =
        let t = Option.get (add_decl None d) in
        let state,task = comp t (!rstate,!rtask) in
        let task = add_tdecl task (create_use th) in
        rstate := state ; rtask := task ; None
      in
      let tp_map = Mid.diff add state.tp_map (get_used_syms_decl d) in
      comp t ({ !rstate with tp_map = tp_map }, !rtask)
  | _ ->
      comp t (state,task)

let fold_comp st =
  let init = Task.add_meta None meta_infinite [MAts ts_int] in
  let init = Task.add_meta init meta_infinite [MAts ts_real] in
  let init = Task.add_meta init meta_infinite [MAts ts_str] in
  let init = Task.add_param_decl init ps_equ in
  Trans.fold comp (st,init)

let on_empty_state t =
  Trans.on_tagged_ts meta_infinite (fun inf_ts ->
  Trans.on_meta meta_material (fun ml ->
    let inf_ts = Sts.union inf_ts (Sts.of_list [ts_real; ts_int; ts_str]) in
    let fold ma_map = function
      | [MAts ts; MAint i] ->
        let ma = match Mts.find ts ma_map with
        | l -> Array.of_list l
        | exception Not_found -> Array.make (List.length ts.ts_args) false
        in
        ma.(i) <- true;
        Mts.add ts (Array.to_list ma) ma_map
      | _ -> assert false
    in
    let ma_map = List.fold_left fold Mts.empty ml in
    let empty_state = {
      mt_map = Mts.empty; cc_map = Mls.empty; cp_map = Mls.empty;
      pp_map = Mls.empty; kept_m = Mts.empty; tp_map = Mid.empty;
      inf_ts; ma_map; keep_e = false; keep_r = false; keep_m = false;
      no_ind = false; no_inv = false; no_sel = false
    } in t empty_state))

(* We need to rewrite metas *after* the main pass, because we need to know the
   final state. Some metas may mention symbols declared after the meta. *)
let fold_rewrite_metas state t task = match t.task_decl.td_node with
  | Meta (m, mal) ->
    let map_arg ma = match ma with
    | MAls ({ ls_value = Some({ty_node = Tyapp(ts, _)}) } as ls)
        when BigInt.pos ls.ls_constr && not (Mts.mem ts state.kept_m) ->
      MAls (Mls.find_def ls ls state.cc_map)
    | MAls ({ ls_proj = true; ls_args = [{ty_node = Tyapp(ts, _)}] } as ls)
        when not (Mts.mem ts state.kept_m) ->
      MAls (Mls.find_def ls ls state.pp_map)
    | _ -> ma
    in
    add_meta task m (List.map map_arg mal)
  | _ ->
    add_tdecl task t.task_decl

let rewrite_metas st = Trans.fold (fold_rewrite_metas st) None

let eliminate_match =
  Trans.bind (Trans.compose compile_match (on_empty_state fold_comp))
             (fun (state, task) -> Trans.seq [Trans.return task; rewrite_metas state])
let meta_elim = register_meta "eliminate_algebraic" [MTstring]
  ~desc:"@[<hov 2>Configure the 'eliminate_algebraic' transformation:@\n\
    - keep_enums:   @[keep monomorphic enumeration types (do not use with polymorphism encoding)@]@\n\
    - keep_recs:    @[keep non-recursive records (do not use with polymorphism encoding)@]@\n\
    - keep_mono:    @[keep monomorphic algebraic datatypes@]@\n\
    - no_index:     @[do not generate indexing functions@]@\n\
    - no_inversion: @[do not generate inversion axioms@]@\n\
    - no_selector:  @[do not generate selector@]@]"

let eliminate_algebraic =
  Trans.on_meta meta_elim (fun ml ->
  Trans.on_tagged_ty meta_alg_kept (fun kept ->
  on_empty_state (fun st ->
  let check st = function
    | [MAstr "keep_enums"] -> { st with keep_e = true }
    | [MAstr "keep_recs"]  -> { st with keep_r = true }
    | [MAstr "keep_mono"]  -> { st with keep_m = true }
    | [MAstr "no_index"]   -> { st with no_ind = true }
    | [MAstr "no_inversion"] -> { st with no_inv = true }
    | [MAstr "no_selector"]  -> { st with no_sel = true }
    | [MAstr s] ->
        raise (
            Invalid_argument (
                "meta eliminate_algebraic, arg = \"" ^ s ^ "\""))
    | l ->
        raise (
            Invalid_argument (
                "meta eliminate_algebraic, nb arg = " ^
                  string_of_int (List.length l) ^ ""))
  in
  let st = List.fold_left check st ml in
  let kept_fold ty m =
    match ty with
    | { ty_node=Tyapp(ts, _) } as ty ->
        let s = Mts.find_def Sty.empty ts m in
        Mts.add ts (Sty.add ty s) m
    | _ -> m
  in
  let st = { st with kept_m = Sty.fold kept_fold kept Mts.empty } in
  let add ty decls = create_meta Libencoding.meta_kept [MAty ty] :: decls in
  let add_meta_decls kept_m =
    Trans.add_tdecls (Mts.fold (fun _ -> Sty.fold add) kept_m [])
  in
  Trans.bind (Trans.compose compile_match (fold_comp st))
             (fun (state, task) ->
              Trans.seq [Trans.return task;
                         rewrite_metas state;
                         add_meta_decls state.kept_m]))))

(** Eliminate user-supplied projection functions *)

let rec rewrite map t = match t.t_node with
  | Tapp (ls, [arg]) when ls.ls_proj ->
      let arg = rewrite map arg in
      t_attr_copy t (t_app (Mls.find_def ls ls map) [arg] t.t_ty)
  | _ -> t_map (rewrite map) t

let elim_proj keep_rec t (map,task) = match t.task_decl.td_node with
  | Decl { d_node = Ddata dl } ->
    (* add type declarations *)
    let conv (cs,pjl) = cs, List.map (fun _ -> None) pjl in
    let conv (ts,csl) = match csl with
      | [_] when keep_rec -> ts,csl
      | _ -> ts,List.map conv csl
    in
    let task = add_data_decl task (List.map conv dl) in
    (* add projection definitions *)
    let add vs csl (map,task) pj =
      let mk_b (cs,pjl) =
        let mk_v = create_vsymbol (id_fresh "x") in
        let vl = List.map mk_v cs.ls_args in
        let p = pat_app cs (List.map pat_var vl) vs.vs_ty in
        let find acc v = function
          | Some ls when ls_equal ls pj -> t_var v
          | _ -> acc in
        let t = List.fold_left2 find t_true(*dummy*) vl pjl in
        t_close_branch p t in
      let bl = List.map mk_b csl in
      let f = t_case (t_var vs) bl in
      let id = id_clone pj.ls_name in
      let pj_new = create_lsymbol id pj.ls_args pj.ls_value in
      let def = make_ls_defn pj_new [vs] f in
      Mls.add pj pj_new map,add_logic_decl task [def]
    in
    let add (map,task) (_,csl) =
      match csl with
      | [_] when keep_rec -> (map,task)
      | _ ->
         let (cs,pjl) = List.hd csl in
         let ty = Option.get cs.ls_value in
         let vs = create_vsymbol (id_fresh "v") ty in
         let pjl = List.filter_map Fun.id pjl in
         List.fold_left (add vs csl) (map,task) pjl
    in
    List.fold_left add (map,task) dl
  | Decl d -> map, add_decl task (Decl.decl_map (rewrite map) d)
  | Meta (m, args) ->
     let conv = function
       | MAls p when p.ls_proj -> MAls (Mls.find_def p p map)
       | m -> m
     in
     map, add_meta task m (List.map conv args)
  | _ -> map, add_tdecl task t.task_decl

let eliminate_projections = Trans.fold_map (elim_proj false) Mls.empty None

let eliminate_projections_sums = Trans.fold_map (elim_proj true) Mls.empty None

let () =
  Trans.register_transform "compile_match" compile_match
    ~desc:"Transform@ pattern-matching@ with@ nested@ patterns@ \
      into@ nested@ pattern-matching@ with@ flat@ patterns.";
  Trans.register_transform "eliminate_match" eliminate_match
    ~desc:"Eliminate@ all@ pattern-matching@ expressions.";
  Trans.register_transform "eliminate_algebraic" eliminate_algebraic
    ~desc:"Replace@ algebraic@ data@ types@ by@ first-order@ definitions.";
  Trans.register_transform "eliminate_projections" eliminate_projections
    ~desc:"Define@ algebraic@ projection@ symbols@ separately.";
  Trans.register_transform "eliminate_projections_sums" eliminate_projections_sums
    ~desc:"Like@ eliminate@_projections,@ but@ only@ projections@ on@ types@ \
      with@ more@ than@ one@ constructor."

(** conditional transformations, only applied when polymorphic types occur *)

let eliminate_algebraic_if_poly =
  Trans.on_meta Detect_polymorphism.meta_monomorphic_types_only
    (function
    | [] -> eliminate_algebraic
    | _ -> Trans.compose compile_match eliminate_projections_sums)

let () =
  Trans.register_transform "eliminate_algebraic_if_poly"
    eliminate_algebraic_if_poly
    ~desc:"Same@ as@ eliminate_algebraic@ but@ only@ if@ polymorphism@ appear."
