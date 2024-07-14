open BinNums
open Datatypes
open Base
open Countable
open Numbers

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a gmap_dep_ne =
| GNode001 of 'a gmap_dep_ne
| GNode010 of 'a
| GNode011 of 'a * 'a gmap_dep_ne
| GNode100 of 'a gmap_dep_ne
| GNode101 of 'a gmap_dep_ne * 'a gmap_dep_ne
| GNode110 of 'a gmap_dep_ne * 'a
| GNode111 of 'a gmap_dep_ne * 'a * 'a gmap_dep_ne

type 'a gmap_dep =
| GEmpty
| GNodes of 'a gmap_dep_ne

type ('k, 'a) gmap = { gmap_car : 'a gmap_dep }

(** val gmap_dep_ne_case :
    'a1 gmap_dep_ne -> ('a1 gmap_dep -> (__*'a1) option -> 'a1 gmap_dep ->
    'a2) -> 'a2 **)

let gmap_dep_ne_case t f =
  match t with
  | GNode001 r -> f GEmpty None (GNodes r)
  | GNode010 x -> f GEmpty (Some (__,x)) GEmpty
  | GNode011 (x, r) -> f GEmpty (Some (__,x)) (GNodes r)
  | GNode100 l -> f (GNodes l) None GEmpty
  | GNode101 (l, r) -> f (GNodes l) None (GNodes r)
  | GNode110 (l, x) -> f (GNodes l) (Some (__,x)) GEmpty
  | GNode111 (l, x, r) -> f (GNodes l) (Some (__,x)) (GNodes r)

(** val gmap_empty :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2) gmap
    coq_Empty **)

let gmap_empty _ _ =
  { gmap_car = GEmpty }

(** val gmap_dep_ne_singleton : positive -> 'a1 -> 'a1 gmap_dep_ne **)

let rec gmap_dep_ne_singleton i x =
  match i with
  | Coq_xI i0 -> GNode001 (gmap_dep_ne_singleton i0 x)
  | Coq_xO i0 -> GNode100 (gmap_dep_ne_singleton i0 x)
  | Coq_xH -> GNode010 x

(** val gmap_partial_alter_aux :
    (positive -> __ -> 'a1 gmap_dep_ne -> 'a1 gmap_dep) -> ('a1 option -> 'a1
    option) -> positive -> 'a1 gmap_dep -> 'a1 gmap_dep **)

let gmap_partial_alter_aux go f i = function
| GEmpty ->
  (match f None with
   | Some x -> GNodes (gmap_dep_ne_singleton i x)
   | None -> GEmpty)
| GNodes t -> go i __ t

(** val gmap_dep_ne_partial_alter :
    ('a1 option -> 'a1 option) -> positive -> 'a1 gmap_dep_ne -> 'a1 gmap_dep **)

let rec gmap_dep_ne_partial_alter f i = function
| GNode001 r ->
  (match i with
   | Coq_xI i0 ->
     (match gmap_dep_ne_partial_alter f i0 r with
      | GEmpty -> GEmpty
      | GNodes r0 -> GNodes (GNode001 r0))
   | Coq_xO i0 ->
     (match f None with
      | Some x0 ->
        let l = gmap_dep_ne_singleton i0 x0 in GNodes (GNode101 (l, r))
      | None -> GNodes (GNode001 r))
   | Coq_xH ->
     (match f None with
      | Some a -> let p0 = __,a in let _,x0 = p0 in GNodes (GNode011 (x0, r))
      | None -> GNodes (GNode001 r)))
| GNode010 x0 ->
  (match i with
   | Coq_xI i0 ->
     (match f None with
      | Some x1 ->
        let r = gmap_dep_ne_singleton i0 x1 in GNodes (GNode011 (x0, r))
      | None -> GNodes (GNode010 x0))
   | Coq_xO i0 ->
     (match f None with
      | Some x1 ->
        let l = gmap_dep_ne_singleton i0 x1 in GNodes (GNode110 (l, x0))
      | None -> GNodes (GNode010 x0))
   | Coq_xH ->
     (match f (Some x0) with
      | Some a -> let p0 = __,a in let _,x1 = p0 in GNodes (GNode010 x1)
      | None -> GEmpty))
| GNode011 (x0, r) ->
  (match i with
   | Coq_xI i0 ->
     (match gmap_dep_ne_partial_alter f i0 r with
      | GEmpty -> GNodes (GNode010 x0)
      | GNodes r0 -> GNodes (GNode011 (x0, r0)))
   | Coq_xO i0 ->
     (match f None with
      | Some x1 ->
        let l = gmap_dep_ne_singleton i0 x1 in GNodes (GNode111 (l, x0, r))
      | None -> GNodes (GNode011 (x0, r)))
   | Coq_xH ->
     (match f (Some x0) with
      | Some a -> let p0 = __,a in let _,x1 = p0 in GNodes (GNode011 (x1, r))
      | None -> GNodes (GNode001 r)))
| GNode100 l ->
  (match i with
   | Coq_xI i0 ->
     (match f None with
      | Some x0 ->
        let r = gmap_dep_ne_singleton i0 x0 in GNodes (GNode101 (l, r))
      | None -> GNodes (GNode100 l))
   | Coq_xO i0 ->
     (match gmap_dep_ne_partial_alter f i0 l with
      | GEmpty -> GEmpty
      | GNodes l0 -> GNodes (GNode100 l0))
   | Coq_xH ->
     (match f None with
      | Some a -> let p0 = __,a in let _,x0 = p0 in GNodes (GNode110 (l, x0))
      | None -> GNodes (GNode100 l)))
| GNode101 (l, r) ->
  (match i with
   | Coq_xI i0 ->
     (match gmap_dep_ne_partial_alter f i0 r with
      | GEmpty -> GNodes (GNode100 l)
      | GNodes r0 -> GNodes (GNode101 (l, r0)))
   | Coq_xO i0 ->
     (match gmap_dep_ne_partial_alter f i0 l with
      | GEmpty -> GNodes (GNode001 r)
      | GNodes l0 -> GNodes (GNode101 (l0, r)))
   | Coq_xH ->
     (match f None with
      | Some a ->
        let p0 = __,a in let _,x0 = p0 in GNodes (GNode111 (l, x0, r))
      | None -> GNodes (GNode101 (l, r))))
| GNode110 (l, x0) ->
  (match i with
   | Coq_xI i0 ->
     (match f None with
      | Some x1 ->
        let r = gmap_dep_ne_singleton i0 x1 in GNodes (GNode111 (l, x0, r))
      | None -> GNodes (GNode110 (l, x0)))
   | Coq_xO i0 ->
     (match gmap_dep_ne_partial_alter f i0 l with
      | GEmpty -> GNodes (GNode010 x0)
      | GNodes l0 -> GNodes (GNode110 (l0, x0)))
   | Coq_xH ->
     (match f (Some x0) with
      | Some a -> let p0 = __,a in let _,x1 = p0 in GNodes (GNode110 (l, x1))
      | None -> GNodes (GNode100 l)))
| GNode111 (l, x0, r) ->
  (match i with
   | Coq_xI i0 ->
     (match gmap_dep_ne_partial_alter f i0 r with
      | GEmpty -> GNodes (GNode110 (l, x0))
      | GNodes r0 -> GNodes (GNode111 (l, x0, r0)))
   | Coq_xO i0 ->
     (match gmap_dep_ne_partial_alter f i0 l with
      | GEmpty -> GNodes (GNode011 (x0, r))
      | GNodes l0 -> GNodes (GNode111 (l0, x0, r)))
   | Coq_xH ->
     (match f (Some x0) with
      | Some a ->
        let p0 = __,a in let _,x1 = p0 in GNodes (GNode111 (l, x1, r))
      | None -> GNodes (GNode101 (l, r))))

(** val gmap_dep_partial_alter :
    ('a1 option -> 'a1 option) -> positive -> 'a1 gmap_dep -> 'a1 gmap_dep **)

let gmap_dep_partial_alter f i x =
  gmap_partial_alter_aux (fun x0 _ -> gmap_dep_ne_partial_alter f x0) f i x

(** val gmap_partial_alter :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
    gmap) coq_PartialAlter **)

let gmap_partial_alter _ h f k pat =
  let { gmap_car = mt } = pat in
  { gmap_car = (gmap_dep_partial_alter f (h.encode k) mt) }

(** val gmap_fold_aux :
    (positive -> 'a2 -> 'a1 gmap_dep_ne -> 'a2) -> positive -> 'a2 -> 'a1
    gmap_dep -> 'a2 **)

let gmap_fold_aux go i y = function
| GEmpty -> y
| GNodes t -> go i y t

(** val gmap_dep_ne_fold :
    (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 gmap_dep_ne ->
    'a2 **)

let rec gmap_dep_ne_fold f x x0 x1 =
  gmap_dep_ne_case x1 (fun ml mx mr ->
    gmap_fold_aux (fun x2 x3 x4 -> gmap_dep_ne_fold f x2 x3 x4) (Coq_xI x)
      (gmap_fold_aux (fun x2 x3 x4 -> gmap_dep_ne_fold f x2 x3 x4) (Coq_xO x)
        (match mx with
         | Some p0 -> let _,x2 = p0 in f (Pos.reverse x) x2 x0
         | None -> x0) ml) mr)

(** val gmap_dep_fold :
    (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 gmap_dep -> 'a2 **)

let gmap_dep_fold f =
  gmap_fold_aux (gmap_dep_ne_fold f)

(** val gmap_fold :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 -> 'a2 -> __ ->
    __) -> __ -> ('a1, 'a2) gmap -> __ **)

let gmap_fold _ h f y pat =
  let { gmap_car = mt } = pat in
  gmap_dep_fold (fun i x ->
    match h.decode i with
    | Some k -> f k x
    | None -> id) Coq_xH y mt
