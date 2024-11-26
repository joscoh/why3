open List0
open Monads
open Ident
open Term
open Decl
open Trans










(** val log :
    decl list -> (lsymbol*'a1) -> (decl hashcons_ty, decl list) errState **)

let log acc = function
| ps,_ -> (@@) (fun p1 -> (fun x -> x) (p1::acc)) (create_param_decl ps)

(** val axm :
    decl list -> (prsymbol*(term_node term_o)) -> (decl hashcons_ty, decl
    list) errState **)

let axm acc = function
| pr,f ->
  (@@) (fun p1 -> (fun x -> x) (p1::acc)) (create_prop_decl Paxiom pr f)

(** val imp :
    decl list -> ('a1*(prsymbol*(term_node term_o)) list) -> (decl
    hashcons_ty, decl list) errState **)

let imp acc = function
| _,al -> foldl_errst axm al acc

(** val exi :
    (term_node term_o) list -> ('a1*(term_node term_o)) -> (ty_node_c ty_o
    hashcons_ty, (term_node term_o)) errState **)

let exi vl x =
  let rec descend f =
    match t_node f with
    | Tapp (_, tl) ->
      let marry = fun acc v t ->
        (@@) (fun t1 ->  (t_and_simp acc t1)) (t_equ v t)
      in
      (@@) (fun o ->
        match o with
        | Some x0 -> (fun x -> x) x0
        | None -> (fun x -> x) f) (fold_left2_errst marry t_true vl tl)
    | Tlet (t, tb) ->
      let v,f0 = t_view_bound tb in
      (@@) (fun d -> (@@) (fun x -> x) ( (t_let_close v t d))) (descend f0)
    | Tquant (q, f0) ->
      (match q with
       | Tforall ->
         let p,f1 = t_view_quant f0 in
         let vl0,tl = p in
         (@@) (fun d ->  (t_exists_close vl0 tl d)) (descend f1)
       | Texists -> (fun x -> x) f)
    | Tbinop (b, g, f0) ->
      (match b with
       | Timplies -> (@@) (fun d ->  (t_and g d)) (descend f0)
       | _ -> (fun x -> x) f)
    | _ -> (fun x -> x) f
  in descend (snd x)

(** val inv :
    decl list -> (lsymbol*('a1*(term_node term_o)) list) ->
    (BigInt.t*(ty_node_c ty_o hashcons_ty*decl hashcons_ty), decl list)
    errState **)

let inv acc = function
| ps,al ->
  (@@) (fun vl ->
    let tl = map t_var vl in
    (@@) (fun hd ->
      (@@) (fun dj ->
        (@@) (fun hsdj ->
          (@@) (fun ax ->
            let nm =
              id_derive1 ((^) ps.ls_name.id_string "_inversion") ps.ls_name
            in
            (@@) (fun p ->
              (@@) (fun pd -> (fun x -> x) (pd::acc))
                ( ( (create_prop_decl Paxiom p ax))))
              ( ( (create_prsymbol nm)))) ( (t_forall_close vl [] hsdj)))
          ( (t_implies hd dj)))
        (
          (
            (map_join_left_errst t_true (exi tl) (fun t1 t2 ->  (t_or t1 t2))
              al)))) ( ( (ps_app ps tl))))
    ( ( (st_list (map (create_vsymbol (id_fresh1 "z")) ps.ls_args))))

(** val elim :
    decl -> (BigInt.t*(ty_node_c ty_o hashcons_ty*decl hashcons_ty), decl
    list) errState **)

let elim d =
  match d.d_node with
  | Dind x ->
    let il = snd x in
    (@@) (fun dl ->
      (@@) (fun dl0 ->
        (@@) (fun dl1 -> (fun x -> x) (rev dl1)) (foldl_errst inv il dl0))
        ( ( (foldl_errst imp il dl)))) ( ( (foldl_errst log il [])))
  | _ -> (fun x -> x) (d::[])

(** val elim_lift : decl -> (BigInt.t*unit, decl list) errState **)

let elim_lift d =
    (elim d)

(** val eliminate_inductive : task -> (BigInt.t*unit, task) errState **)

let eliminate_inductive =
  decl_errst elim_lift None
let () = Trans.register_transform "eliminate_inductive" eliminate_inductive
  ~desc:"Replace@ inductive@ predicates@ by@ (incomplete)@ axiomatic@ \
         definitions,@ i.e.@ construction@ axioms@ and@ an@ inversion@ axiom."
