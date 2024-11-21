open Ident
open Ty
open Term
open Monads
open List0 (*fold_left*)
open Datatypes (*app*)
open CoqUtil
exception ConstructorExpected of lsymbol * ty
exception NonExhaustive of pattern list










(** val hd : 'a1 list -> 'a1 errorM **)

let hd = function
| [] -> raise (Failure "hd")
| x::_ ->  x

(** val tl : 'a1 list -> 'a1 list errorM **)

let tl = function
| [] -> raise (Failure "tl")
| _::xs ->  xs

(** val populate :
    (lsymbol -> bool) -> ty_node_c ty_o -> ((pattern_node pattern_o) list
    Mls.t*(lsymbol*(pattern_node pattern_o) list) list) ->
    (pattern_node pattern_o) -> ((pattern_node pattern_o) list
    Mls.t*(lsymbol*(pattern_node pattern_o) list) list) errorM **)

let rec populate is_constr ty acc p =
  match pat_node p with
  | Papp (fs, pl) ->
    if is_constr fs
    then if Mls.mem fs (fst acc)
         then  acc
         else  ((Mls.add fs pl (fst acc)),((fs,pl)::(snd acc)))
    else raise (ConstructorExpected (fs,ty))
  | Por (p0, q) ->
    (@@) (fun p1 -> populate is_constr ty p1 q) (populate is_constr ty acc p0)
  | Pas (p0, _) -> populate is_constr ty acc p0
  | _ ->  acc

(** val populate_all :
    (lsymbol -> bool) -> ty_node_c ty_o -> ((pattern_node pattern_o)
    list*'a1) list -> ((pattern_node pattern_o) list
    Mls.t*(lsymbol*(pattern_node pattern_o) list) list) errorM **)

let populate_all is_constr ty rl =
  let populate0 = fun acc x ->
    (@@) (fun p -> populate is_constr ty acc p) (hd (fst x))
  in
  foldl_err populate0 rl (Mls.empty,[])

(** val add_case :
    lsymbol -> (pattern_node pattern_o) list -> 'a1 ->
    ((pattern_node pattern_o) list*'a1) list Mls.t ->
    ((pattern_node pattern_o) list*'a1) list Mls.t **)

let add_case fs pl a cases =
  Mls.change (fun x ->
    match x with
    | Some rl -> Some ((pl,a)::rl)
    | None -> Some ((pl,a)::[])) fs cases

(** val union_cases :
    (pattern_node pattern_o) list -> 'a1 -> (pattern_node pattern_o) list
    Mls.t -> ((pattern_node pattern_o) list*'a1) list Mls.t ->
    ((pattern_node pattern_o) list*'a1) list Mls.t **)

let union_cases pl a types cases =
  let add0 = fun pl0 q -> (pat_wild (pat_ty q))::pl0 in
  let wild = fun ql -> ((fold_left add0 ql pl),a)::[] in
  let join = fun _ wl rl -> Some (app wl rl) in
  Mls.union join (Mls.map wild types) cases

(** val dispatch_aux :
    (vsymbol -> (term_node term_o) -> 'a1 -> 'a1 errorM) ->
    (term_node term_o) -> (pattern_node pattern_o) list Mls.t ->
    ((pattern_node pattern_o) list*'a1) -> (((pattern_node pattern_o)
    list*'a1) list Mls.t*((pattern_node pattern_o) list*'a1) list) ->
    (((pattern_node pattern_o) list*'a1) list Mls.t*((pattern_node pattern_o)
    list*'a1) list) errorM **)

let rec dispatch_aux mk_let t0 types pla casewild =
  match fst pla with
  | [] -> raise (Failure "hd")
  | p::pl ->
    let cases = fst casewild in
    let wilds = snd casewild in
    let a = snd pla in
    (match pat_node p with
     | Pwild ->  ((union_cases pl a types cases),((pl,a)::wilds))
     | Pvar x ->
       (@@) (fun a0 ->  ((union_cases pl a0 types cases),((pl,a0)::wilds)))
         (mk_let x t0 a)
     | Papp (fs, pl') ->  ((add_case fs (rev_append pl' pl) a cases),wilds)
     | Por (p1, q1) ->
       (@@) (fun d1 -> dispatch_aux mk_let t0 types ((p1::pl),a) d1)
         (dispatch_aux mk_let t0 types ((q1::pl),a) (cases,wilds))
     | Pas (p0, x) ->
       (@@) (fun a0 ->
         dispatch_aux mk_let t0 types ((p0::pl),a0) (cases,wilds))
         (mk_let x t0 a))

(** val dispatch_aux' :
    (vsymbol -> (term_node term_o) -> 'a1 -> 'a1 errorM) ->
    (term_node term_o) -> (pattern_node pattern_o) list Mls.t ->
    ((pattern_node pattern_o) list*'a1) -> (((pattern_node pattern_o)
    list*'a1) list Mls.t*((pattern_node pattern_o) list*'a1) list) ->
    (((pattern_node pattern_o) list*'a1) list Mls.t*((pattern_node pattern_o)
    list*'a1) list) errorM **)

let dispatch_aux' =
  dispatch_aux

(** val dispatch :
    (vsymbol -> (term_node term_o) -> 'a1 -> 'a1 errorM) ->
    (term_node term_o) -> (pattern_node pattern_o) list Mls.t ->
    ((pattern_node pattern_o) list*'a1) list -> (((pattern_node pattern_o)
    list*'a1) list Mls.t*((pattern_node pattern_o) list*'a1) list) errorM **)

let dispatch mk_let t0 types rl =
  foldr_err (fun x y -> dispatch_aux' mk_let t0 types y x) rl (Mls.empty,[])

type 'a compile_result =
| Succ of 'a
| NonExh of (pattern_node pattern_o) list

(** val compile_exn : 'a1 compile_result errorM -> 'a1 errorM **)

let compile_exn e =
  (@@) (fun x ->
    match x with
    | Succ y ->  y
    | NonExh ps -> raise (NonExhaustive ps)) e

(** val comp_cases :
    ((term_node term_o) list -> (pattern list*'a2) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState) ->
    (pattern list*'a2) list Mls.t -> (term_node term_o) list ->
    ty_node_c ty_o -> lsymbol -> (term_node term_o) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState **)

let comp_cases compile cases tl0 ty cs al =
  (@@) (fun r ->
    (@@) (fun c ->
      match c with
      | Succ a -> (fun x -> x) (Succ a)
      | NonExh pl ->
        let cont =
          let rec cont acc vl pl0 =
            match vl with
            | [] ->
              (@@) (fun p1 -> (fun x -> x) (p1::pl0)) ( (pat_app cs acc ty))
            | _::vl0 ->
              (match pl0 with
               | [] ->  (assert_false "comp_cases failed")
               | p::pl1 -> cont (p::acc) vl0 pl1)
          in cont
        in
        (@@) (fun c0 ->  (raise (NonExhaustive c0))) (cont [] cs.ls_args pl))
      (compile (rev_append al tl0) r)) ( (Mls.find cs cases))

(** val opt_get : 'a1 option -> 'a1 errorM **)

let opt_get = function
| Some x ->  x
| None -> raise (Invalid_argument "option is None")

(** val comp_wilds :
    ((term_node term_o) list -> (pattern list*'a1) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState) ->
    (pattern_node pattern_o) list Mls.t -> (term_node term_o) list ->
    (pattern list*'a1) list -> unit Sls.M.t -> ty_node_c ty_o -> unit ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState **)

let comp_wilds compile types tl0 wilds css ty _ =
  (@@) (fun c ->
    
      (match c with
       | Succ x -> (fun x -> x) (Succ x)
       | NonExh pl ->
         let find_cs = fun cs ->
           if Mls.mem cs types
           then (fun x -> x) ()
           else (@@) (fun v ->
                  (@@) (fun tm ->
                    let wild = fun ty0 -> pat_wild (ty_inst_unsafe tm ty0) in
                    (@@) (fun pw ->  (raise (NonExhaustive (pw::pl))))
                      (pat_app cs (map wild cs.ls_args) ty))
                    (ty_match Mtv.empty v ty)) ( (opt_get cs.ls_value))
         in
         (@@) (fun _ ->  (raise (NonExhaustive ((pat_wild ty)::pl))))
           (iter_errst find_cs (Sls.elements css)))) (compile tl0 wilds)

(** val comp_full :
    ((term_node term_o) -> ((pattern_node pattern_o)*'a1) list -> 'a1 errorM)
    -> bool -> (unit -> (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1
    compile_result) errState) -> (lsymbol -> (term_node term_o) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState) ->
    (pattern_node pattern_o) list Mls.t -> Sls.t ->
    (lsymbol*(pattern_node pattern_o) list) list -> (term_node term_o) ->
    ty_node_c ty_o -> unit -> (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1
    compile_result) errState **)

let comp_full mk_case bare comp_wilds0 comp_cases0 types css cslist t0 ty _ =
  (@@) (fun no_wilds ->
    (@@) (fun base ->
      let add0 = fun acc x ->
        let cs,ql = x in
        let get_vs = fun q -> create_vsymbol (id_fresh1 "x") (pat_ty q) in
        (@@) (fun vl ->
          let pl = rev_map pat_var vl in
          let al = rev_map t_var vl in
          (@@) (fun c ->
            match c with
            | Succ x0 ->
              (@@) (fun p -> (fun x -> x) ((p,x0)::acc)) ( (pat_app cs pl ty))
            | NonExh pl0 ->  (raise (NonExhaustive pl0))) (comp_cases0 cs al))
          ( ( (st_list (rev_map get_vs ql))))
      in
      (@@) (fun l -> (@@) (fun c -> (fun x -> x) (Succ c)) ( (mk_case t0 l)))
        (foldl_errst add0 cslist base))
      (if no_wilds
       then (fun x -> x) []
       else (@@) (fun c ->
              match c with
              | Succ x -> (fun x -> x) (((pat_wild ty),x)::[])
              | NonExh pl ->  (raise (NonExhaustive pl))) (comp_wilds0 ())))
    (if bare
     then (@@) (fun t1 ->
            let cs = fst t1 in
            (fun x -> x) (BigInt.eq (Mls.cardinal types) cs.ls_constr))
            ( (Mls.choose types))
     else (fun x -> x) (Mls.set_submap css types))

(** val compile_aux :
    ((ty_node_c ty_o) tysymbol_o -> lsymbol list) -> ((term_node term_o) ->
    ((pattern_node pattern_o)*'a1) list -> 'a1 errorM) -> (vsymbol ->
    (term_node term_o) -> 'a1 -> 'a1 errorM) -> bool -> bool ->
    (term_node term_o) list -> ((pattern_node pattern_o) list*'a1) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1 compile_result) errState **)

let rec compile_aux get_constructors mk_case mk_let bare simpl_constr tl0 rl =
  match tl0 with
  | [] ->
    (match rl with
     | [] ->
       (@@) (fun pl -> (fun x -> x) (NonExh pl))
         (errst_list
           (map (fun t0 ->
             (@@) (fun ty -> (fun x -> x) (pat_wild ty)) ( (t_type t0))) tl0))
     | p::_ -> let _,a = p in (fun x -> x) (Succ a))
  | t0::tl1 ->
    (match rl with
     | [] ->
       (@@) (fun pl -> (fun x -> x) (NonExh pl))
         (errst_list
           (map (fun t1 ->
             (@@) (fun ty -> (fun x -> x) (pat_wild ty)) ( (t_type t1))) tl0))
     | _::_ ->
       (@@) (fun ty ->
         match ty_node ty with
         | Tyvar _ ->
           let bare0 = false in
           let is_constr = fun fs ->
             (&&) (BigInt.pos fs.ls_constr)
               ((||) bare0 (Sls.mem fs Sls.empty))
           in
           (@@) (fun types_cslist ->
             let types = fst types_cslist in
             let cslist = snd types_cslist in
             (@@) (fun casewild ->
               let cases = fst casewild in
               let wilds = snd casewild in
               let comp_wilds0 = fun _ ->
                 (@@) (fun c ->
                   
                     (match c with
                      | Succ x -> (fun x -> x) (Succ x)
                      | NonExh pl ->
                        let find_cs = fun cs ->
                          if Mls.mem cs types
                          then (fun x -> x) ()
                          else (@@) (fun v ->
                                 (@@) (fun tm ->
                                   let wild = fun ty0 ->
                                     pat_wild (ty_inst_unsafe tm ty0)
                                   in
                                   (@@) (fun pw ->
                                      (raise (NonExhaustive (pw::pl))))
                                     (pat_app cs (map wild cs.ls_args) ty))
                                   (ty_match Mtv.empty v ty))
                                 ( (opt_get cs.ls_value))
                        in
                        (@@) (fun _ ->
                           (raise (NonExhaustive ((pat_wild ty)::pl))))
                          (iter_errst find_cs (Sls.elements Sls.empty))))
                   (compile_aux get_constructors mk_case mk_let bare
                     simpl_constr tl1 wilds)
               in
               let comp_cases0 = fun cs al ->
                 (@@) (fun r ->
                   (@@) (fun c ->
                     match c with
                     | Succ a -> (fun x -> x) (Succ a)
                     | NonExh pl ->
                       let cont =
                         let rec cont acc vl pl0 =
                           match vl with
                           | [] ->
                             (@@) (fun p1 -> (fun x -> x) (p1::pl0))
                               ( (pat_app cs acc ty))
                           | _::vl0 ->
                             (match pl0 with
                              | [] ->  (assert_false "comp_cases failed")
                              | p::pl1 -> cont (p::acc) vl0 pl1)
                         in cont
                       in
                       (@@) (fun c0 ->  (raise (NonExhaustive c0)))
                         (cont [] cs.ls_args pl))
                     (compile_aux get_constructors mk_case mk_let bare
                       simpl_constr (rev_append al tl1) r))
                   ( (Mls.find cs cases))
               in
               if Mls.is_empty types
               then comp_wilds0 ()
               else if simpl_constr
                    then (match t_node t0 with
                          | Tapp (cs, al) ->
                            if is_constr cs
                            then if Mls.mem cs types
                                 then comp_cases0 cs al
                                 else comp_wilds0 ()
                            else comp_full mk_case bare comp_wilds0
                                   comp_cases0 types Sls.empty cslist t0 ty ()
                          | _ ->
                            comp_full mk_case bare comp_wilds0 comp_cases0
                              types Sls.empty cslist t0 ty ())
                    else comp_full mk_case bare comp_wilds0 comp_cases0 types
                           Sls.empty cslist t0 ty ())
               ( (dispatch mk_let t0 types rl)))
             ( (populate_all is_constr ty rl))
         | Tyapp (ts, _) ->
           if bare
           then let bare0 = true in
                let is_constr = fun fs ->
                  (&&) (BigInt.pos fs.ls_constr)
                    ((||) bare0 (Sls.mem fs Sls.empty))
                in
                (@@) (fun types_cslist ->
                  let types = fst types_cslist in
                  let cslist = snd types_cslist in
                  (@@) (fun casewild ->
                    let cases = fst casewild in
                    let wilds = snd casewild in
                    let comp_wilds0 = fun _ ->
                      (@@) (fun c ->
                        
                          (match c with
                           | Succ x -> (fun x -> x) (Succ x)
                           | NonExh pl ->
                             let find_cs = fun cs ->
                               if Mls.mem cs types
                               then (fun x -> x) ()
                               else (@@) (fun v ->
                                      (@@) (fun tm ->
                                        let wild = fun ty0 ->
                                          pat_wild (ty_inst_unsafe tm ty0)
                                        in
                                        (@@) (fun pw ->
                                           (raise (NonExhaustive (pw::pl))))
                                          (pat_app cs (map wild cs.ls_args)
                                            ty)) (ty_match Mtv.empty v ty))
                                      ( (opt_get cs.ls_value))
                             in
                             (@@) (fun _ ->
                                (raise (NonExhaustive ((pat_wild ty)::pl))))
                               (iter_errst find_cs (Sls.elements Sls.empty))))
                        (compile_aux get_constructors mk_case mk_let bare
                          simpl_constr tl1 wilds)
                    in
                    let comp_cases0 = fun cs al ->
                      (@@) (fun r ->
                        (@@) (fun c ->
                          match c with
                          | Succ a -> (fun x -> x) (Succ a)
                          | NonExh pl ->
                            let cont =
                              let rec cont acc vl pl0 =
                                match vl with
                                | [] ->
                                  (@@) (fun p1 -> (fun x -> x) (p1::pl0))
                                    ( (pat_app cs acc ty))
                                | _::vl0 ->
                                  (match pl0 with
                                   | [] ->  (assert_false "comp_cases failed")
                                   | p::pl1 -> cont (p::acc) vl0 pl1)
                              in cont
                            in
                            (@@) (fun c0 ->  (raise (NonExhaustive c0)))
                              (cont [] cs.ls_args pl))
                          (compile_aux get_constructors mk_case mk_let bare
                            simpl_constr (rev_append al tl1) r))
                        ( (Mls.find cs cases))
                    in
                    if Mls.is_empty types
                    then comp_wilds0 ()
                    else if simpl_constr
                         then (match t_node t0 with
                               | Tapp (cs, al) ->
                                 if is_constr cs
                                 then if Mls.mem cs types
                                      then comp_cases0 cs al
                                      else comp_wilds0 ()
                                 else comp_full mk_case bare comp_wilds0
                                        comp_cases0 types Sls.empty cslist t0
                                        ty ()
                               | _ ->
                                 comp_full mk_case bare comp_wilds0
                                   comp_cases0 types Sls.empty cslist t0 ty ())
                         else comp_full mk_case bare comp_wilds0 comp_cases0
                                types Sls.empty cslist t0 ty ())
                    ( (dispatch mk_let t0 types rl)))
                  ( (populate_all is_constr ty rl))
           else let bare0 = false in
                let css = Sls.of_list (get_constructors ts) in
                let is_constr = fun fs ->
                  (&&) (BigInt.pos fs.ls_constr) ((||) bare0 (Sls.mem fs css))
                in
                (@@) (fun types_cslist ->
                  let types = fst types_cslist in
                  let cslist = snd types_cslist in
                  (@@) (fun casewild ->
                    let cases = fst casewild in
                    let wilds = snd casewild in
                    let comp_wilds0 = fun _ ->
                      (@@) (fun c ->
                        
                          (match c with
                           | Succ x -> (fun x -> x) (Succ x)
                           | NonExh pl ->
                             let find_cs = fun cs ->
                               if Mls.mem cs types
                               then (fun x -> x) ()
                               else (@@) (fun v ->
                                      (@@) (fun tm ->
                                        let wild = fun ty0 ->
                                          pat_wild (ty_inst_unsafe tm ty0)
                                        in
                                        (@@) (fun pw ->
                                           (raise (NonExhaustive (pw::pl))))
                                          (pat_app cs (map wild cs.ls_args)
                                            ty)) (ty_match Mtv.empty v ty))
                                      ( (opt_get cs.ls_value))
                             in
                             (@@) (fun _ ->
                                (raise (NonExhaustive ((pat_wild ty)::pl))))
                               (iter_errst find_cs (Sls.elements css))))
                        (compile_aux get_constructors mk_case mk_let bare
                          simpl_constr tl1 wilds)
                    in
                    let comp_cases0 = fun cs al ->
                      (@@) (fun r ->
                        (@@) (fun c ->
                          match c with
                          | Succ a -> (fun x -> x) (Succ a)
                          | NonExh pl ->
                            let cont =
                              let rec cont acc vl pl0 =
                                match vl with
                                | [] ->
                                  (@@) (fun p1 -> (fun x -> x) (p1::pl0))
                                    ( (pat_app cs acc ty))
                                | _::vl0 ->
                                  (match pl0 with
                                   | [] ->  (assert_false "comp_cases failed")
                                   | p::pl1 -> cont (p::acc) vl0 pl1)
                              in cont
                            in
                            (@@) (fun c0 ->  (raise (NonExhaustive c0)))
                              (cont [] cs.ls_args pl))
                          (compile_aux get_constructors mk_case mk_let bare
                            simpl_constr (rev_append al tl1) r))
                        ( (Mls.find cs cases))
                    in
                    if Mls.is_empty types
                    then comp_wilds0 ()
                    else if simpl_constr
                         then (match t_node t0 with
                               | Tapp (cs, al) ->
                                 if is_constr cs
                                 then if Mls.mem cs types
                                      then comp_cases0 cs al
                                      else comp_wilds0 ()
                                 else comp_full mk_case bare comp_wilds0
                                        comp_cases0 types css cslist t0 ty ()
                               | _ ->
                                 comp_full mk_case bare comp_wilds0
                                   comp_cases0 types css cslist t0 ty ())
                         else comp_full mk_case bare comp_wilds0 comp_cases0
                                types css cslist t0 ty ())
                    ( (dispatch mk_let t0 types rl)))
                  ( (populate_all is_constr ty rl))) ( (t_type t0)))

(** val compile_aux' :
    ((ty_node_c ty_o) tysymbol_o -> lsymbol list) -> ((term_node term_o) ->
    ((pattern_node pattern_o)*'a1) list -> 'a1 errorM) -> (vsymbol ->
    (term_node term_o) -> 'a1 -> 'a1 errorM) -> bool -> bool ->
    (term_node term_o) list -> ((pattern_node pattern_o) list*'a1) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1) errState **)

let compile_aux' get_constructors mk_case mk_let bare simpl_constr tl0 rl =
  (@@) (fun x ->
    match x with
    | Succ x0 -> (fun x -> x) x0
    | NonExh pl ->  (raise (NonExhaustive pl)))
    (compile_aux get_constructors mk_case mk_let bare simpl_constr tl0 rl)

(** val compile_bare_aux :
    ((term_node term_o) -> ((pattern_node pattern_o)*'a1) list -> 'a1 errorM)
    -> (vsymbol -> (term_node term_o) -> 'a1 -> 'a1 errorM) ->
    (term_node term_o) list -> ((pattern_node pattern_o) list*'a1) list ->
    (BigInt.t*ty_node_c ty_o hashcons_ty, 'a1) errState **)

let compile_bare_aux mk_case mk_let tl0 rl =
  let get_constructors = fun _ -> [] in
  (@@) (fun x ->
    match x with
    | Succ x0 -> (fun x -> x) x0
    | NonExh _ ->  (raise (NonExhaustive [])))
    (compile_aux get_constructors mk_case mk_let true true tl0 rl)

(** val check_compile_aux :
    ((ty_node_c ty_o) tysymbol_o -> lsymbol list) -> (term_node term_o) list
    -> (pattern_node pattern_o) list list -> (BigInt.t*ty_node_c ty_o
    hashcons_ty, unit) errState **)

let check_compile_aux get_constructors tl0 ps = match ps with
| [] ->
  (@@) (fun pl ->  (raise (NonExhaustive pl)))
    (errst_list
      (map (fun t0 ->
        (@@) (fun ty -> (fun x -> x) (pat_wild ty)) ( (t_type t0))) tl0))
| pl::_ ->
  let mkt = fun p ->
    (@@) (fun i -> (fun x -> x) (t_var i))
      ( (create_vsymbol (id_fresh1 "_") (pat_ty p)))
  in
  (@@) (fun tl1 ->
    let rl = map (fun pl0 -> pl0,t_true) ps in
    (@@) (fun _ -> (fun x -> x) ())
      (compile_aux get_constructors t_case_close t_let_close_simp false false
        tl1 rl))
    (if null tl0 then  (errst_list (map mkt pl)) else (fun x -> x) tl0)
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

(* exception Bare *)

(* let rec populate (is_constr: lsymbol -> bool) (ty: ty) (css,csl as acc) p = match p.pat_node with
  | Pwild | Pvar _ -> acc
  | Pas (p,_) -> populate is_constr ty acc p
  | Por (p,q) -> populate is_constr ty (populate is_constr ty acc p) q
  | Papp (fs,pl) when is_constr fs ->
      if Mls.mem fs css then acc else
      Mls.add fs pl css, (fs,pl) :: csl
  | Papp (fs,_) -> raise (ConstructorExpected (fs,ty))

let populate_all (is_constr: lsymbol -> bool) (ty: ty) rl =
  let populate acc (pl,_) = populate is_constr ty acc (List.hd pl) in
  List.fold_left populate (Mls.empty,[]) rl *)

(* let dispatch mk_let t types rl = 
  let add_case fs pl a cases =
    Mls.change (function
      | None -> Some [pl,a]
      | Some rl -> Some ((pl,a)::rl)) fs cases
  in
  let union_cases pl a types cases =
    let add pl q = pat_wild q.pat_ty :: pl in
    let wild ql = [List.fold_left add pl ql, a] in
    let join _ wl rl = Some (List.append wl rl) in
    Mls.union join (Mls.map wild types) cases
  in
  let rec dispatch (pl,a) (cases,wilds) =
    let p = List.hd pl in let pl = List.tl pl in
    match p.pat_node with
      | Papp (fs,pl') ->
          add_case fs (List.rev_append pl' pl) a cases, wilds
      | Por (p,q) ->
          dispatch (p::pl, a) (dispatch (q::pl, a) (cases,wilds))
      | Pas (p,x) ->
          dispatch (p::pl, mk_let x t a) (cases,wilds)
      | Pvar x ->
          let a = mk_let x t a in
          union_cases pl a types cases, (pl,a)::wilds
      | Pwild ->
          union_cases pl a types cases, (pl,a)::wilds
  in
  List.fold_right dispatch rl (Mls.empty,[]) *)

(* let comp_cases compile cases tl ty cs al =
  try compile (List.rev_append al tl) (Mls.find cs cases)
  with NonExhaustive pl ->
    let rec cont acc vl pl = match vl,pl with
      | (_::vl), (p::pl) -> cont (p::acc) vl pl
      | [], pl -> pat_app cs acc ty :: pl
      | _, _ -> assert false
    in
    raise (NonExhaustive (cont [] cs.ls_args pl)) *)

(* let comp_wilds compile types tl wilds css ty () =
  match (compile tl wilds) with
  | Succ x -> Succ x
  | NonExh pl ->
    let find_cs cs =
      if Mls.mem cs types then () else
      let tm = ty_match Mtv.empty (Option.get cs.ls_value) ty in
      let wild ty = pat_wild (ty_inst tm ty) in
      let pw = pat_app cs (List.map wild cs.ls_args) ty in
      raise (NonExhaustive (pw :: pl))
    in
    Sls.iter find_cs css;
    raise (NonExhaustive (pat_wild ty :: pl)) *)

  (* try compile tl wilds
  with NonExhaustive pl ->
    let find_cs cs =
      if Mls.mem cs types then () else
      let tm = ty_match Mtv.empty (Option.get cs.ls_value) ty in
      let wild ty = pat_wild (ty_inst tm ty) in
      let pw = pat_app cs (List.map wild cs.ls_args) ty in
      raise (NonExhaustive (pw :: pl))
    in
    Sls.iter find_cs css;
    raise (NonExhaustive (pat_wild ty :: pl)) *)

(*TODO: maybe put this back in*)
(* let comp_full mk_case compile bare types tl cases wilds css cslist t ty () =
  let no_wilds =
    if bare then
      let cs,_ = Mls.choose types in
      BigInt.eq (Mls.cardinal types) (cs.ls_constr)
    else
      Mls.set_submap css types
  in
  let base = if no_wilds then []
    else 
      begin match comp_wilds compile types tl wilds css ty () with
      | NonExh pl -> raise (NonExhaustive pl)
      | Succ x ->
      
          [pat_wild ty,x ]
      end
  in
  let add acc (cs,ql) =
    let get_vs q = create_vsymbol (id_fresh "x") q.pat_ty in
    let vl = List.rev_map get_vs ql in
    let pl = List.rev_map pat_var vl in
    let al = List.rev_map t_var vl in
    begin match comp_cases compile cases tl ty cs al with
    | NonExh pl -> raise (NonExhaustive pl)
    | Succ x ->
        (pat_app cs pl ty, x) :: acc
    end
  in
  Succ (mk_case t (List.fold_left add base cslist)) *)

(* let compile ~get_constructors ~mk_case ~mk_let (bare: bool) (simpl_constr: bool) tl rl =
  compile_aux' get_constructors mk_case mk_let bare simpl_constr tl rl *)
  (* let rec compile tl rl = match tl,rl with
    | _, [] -> (* no actions *)
        let pl = List.map (fun t -> pat_wild (t_type t)) tl in
        NonExh pl  (*(NonExhaustive pl)*)
    | [], (_,a) :: _ -> (* no terms, at least one action *)
        Succ a
    | t :: tl, _ -> (* process the leftmost column *)
        let ty = t_type t in
        (* extract the set of constructors *)
        let bare,css = match ty.ty_node with
          | Tyapp (ts,_) -> if bare then (true, Sls.empty) else (false, Sls.of_list (get_constructors ts))
              (* begin try false, Sls.of_list (get_constructors ts)
              with Bare -> true, Sls.empty end *)
          | Tyvar _ -> false, Sls.empty
        in
        (* if bare, only check fs.ls_constr *)
        let is_constr fs =
          BigInt.pos fs.ls_constr && (bare || Sls.mem fs css)
        in
        (* map every constructor occurring at the head
         * of the pattern list to the list of its args *)
        let types, cslist = populate_all is_constr ty rl
        in
        (* dispatch every case to a primitive constructor/wild case *)
        let cases,wilds = dispatch mk_let t types rl in
        (* how to proceed if [t] is [Tapp(cs,al)] and [cs] is in [cases] *)
        
        (* how to proceed if [t] is not covered by [cases] *)
        
        

        (* assemble the primitive case statement *)
        if Mls.is_empty types then
          comp_wilds compile types tl wilds css ty ()
        else if simpl_constr then
          begin match t.t_node with
          (* | _ when Mls.is_empty types ->
              comp_wilds () *)
          | Tapp (cs,al) when is_constr cs ->
              if Mls.mem cs types then comp_cases compile cases tl ty cs al else comp_wilds compile types tl wilds css ty ()
          | _ -> comp_full mk_case compile bare types tl cases wilds css cslist t ty ()
              
            end
          else comp_full mk_case compile bare types tl cases wilds css cslist t ty ()
  in
  compile tl rl *)

let compile ~get_constructors ~mk_case ~mk_let (bare: bool) (simpl_constr: bool) tl rl =
  compile_aux' get_constructors mk_case mk_let bare simpl_constr tl rl

let compile_bare ~mk_case ~mk_let tl rl =
  compile_bare_aux mk_case mk_let tl rl
  (* let get_constructors _ = [] in
  try compile ~get_constructors ~mk_case ~mk_let true true tl rl
  with NonExhaustive _ -> raise (NonExhaustive []) *)

let check_compile ~get_constructors tl ps =
  check_compile_aux get_constructors tl ps
  (* function
  | [] ->
      let pl = List.map (fun t -> pat_wild (t_type t)) tl in
      raise (NonExhaustive pl)
  | (pl::_) as ppl ->
      let mkt p = t_var (create_vsymbol (id_fresh "_") p.pat_ty) in
      let tl = if tl = [] then List.map mkt pl else tl in
      let rl = List.map (fun pl -> pl, ()) ppl in
      let mk_case _ _ = () and mk_let _ _ _ = () in
      compile ~get_constructors ~mk_case ~mk_let false false tl rl *)

let is_exhaustive tl = function
  | [] -> false
  | (pl::_) as ppl ->
      let mkt p = t_var (create_vsymbol (id_fresh "_") p.pat_ty) in
      let tl = if tl = [] then List.map mkt pl else tl in
      let rl = List.map (fun pl -> pl, true) ppl in
      let get_constructors _ = [] in
      let mk_case _ _ = true and mk_let _ _ _ = true in
      try compile ~get_constructors ~mk_case ~mk_let true false tl rl
      with NonExhaustive _ -> false
