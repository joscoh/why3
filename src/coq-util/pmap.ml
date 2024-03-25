open BinNums
open Base
open Fin_maps
open Numbers
open Option0

type __ = Obj.t

type 'a coq_Pmap_ne =
| PNode001 of 'a coq_Pmap_ne
| PNode010 of 'a
| PNode011 of 'a * 'a coq_Pmap_ne
| PNode100 of 'a coq_Pmap_ne
| PNode101 of 'a coq_Pmap_ne * 'a coq_Pmap_ne
| PNode110 of 'a coq_Pmap_ne * 'a
| PNode111 of 'a coq_Pmap_ne * 'a * 'a coq_Pmap_ne

type 'a coq_Pmap =
| PEmpty
| PNodes of 'a coq_Pmap_ne

(** val coq_Pmap_ne_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 coq_Pmap_ne, 'a1 coq_Pmap_ne)
    coq_RelDecision **)

let rec coq_Pmap_ne_eq_dec eqDecision0 x y =
  match x with
  | PNode001 p ->
    (match y with
     | PNode001 p0 -> coq_Pmap_ne_eq_dec eqDecision0 p p0
     | _ -> false)
  | PNode010 y0 ->
    (match y with
     | PNode010 a -> decide_rel eqDecision0 y0 a
     | _ -> false)
  | PNode011 (y0, p) ->
    (match y with
     | PNode011 (a, p0) ->
       if decide_rel eqDecision0 y0 a
       then coq_Pmap_ne_eq_dec eqDecision0 p p0
       else false
     | _ -> false)
  | PNode100 p ->
    (match y with
     | PNode100 p0 -> coq_Pmap_ne_eq_dec eqDecision0 p p0
     | _ -> false)
  | PNode101 (p, p0) ->
    (match y with
     | PNode101 (p1, p2) ->
       if coq_Pmap_ne_eq_dec eqDecision0 p p1
       then coq_Pmap_ne_eq_dec eqDecision0 p0 p2
       else false
     | _ -> false)
  | PNode110 (p, y0) ->
    (match y with
     | PNode110 (p0, a) ->
       if coq_Pmap_ne_eq_dec eqDecision0 p p0
       then decide_rel eqDecision0 y0 a
       else false
     | _ -> false)
  | PNode111 (p, y0, p0) ->
    (match y with
     | PNode111 (p1, a, p2) ->
       if coq_Pmap_ne_eq_dec eqDecision0 p p1
       then if decide_rel eqDecision0 y0 a
            then coq_Pmap_ne_eq_dec eqDecision0 p0 p2
            else false
       else false
     | _ -> false)

(** val coq_Pmap_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 coq_Pmap, 'a1 coq_Pmap) coq_RelDecision **)

let coq_Pmap_eq_dec eqDecision0 x y =
  match x with
  | PEmpty -> (match y with
               | PEmpty -> true
               | PNodes _ -> false)
  | PNodes p ->
    (match y with
     | PEmpty -> false
     | PNodes p0 -> decide_rel (coq_Pmap_ne_eq_dec eqDecision0) p p0)

(** val coq_PNode :
    'a1 coq_Pmap -> 'a1 option -> 'a1 coq_Pmap -> 'a1 coq_Pmap **)

let coq_PNode ml mx mr =
  match ml with
  | PEmpty ->
    (match mx with
     | Some x ->
       (match mr with
        | PEmpty -> PNodes (PNode010 x)
        | PNodes r -> PNodes (PNode011 (x, r)))
     | None ->
       (match mr with
        | PEmpty -> PEmpty
        | PNodes r -> PNodes (PNode001 r)))
  | PNodes l ->
    (match mx with
     | Some x ->
       (match mr with
        | PEmpty -> PNodes (PNode110 (l, x))
        | PNodes r -> PNodes (PNode111 (l, x, r)))
     | None ->
       (match mr with
        | PEmpty -> PNodes (PNode100 l)
        | PNodes r -> PNodes (PNode101 (l, r))))

(** val coq_Pmap_ne_case :
    'a1 coq_Pmap_ne -> ('a1 coq_Pmap -> 'a1 option -> 'a1 coq_Pmap -> 'a2) ->
    'a2 **)

let coq_Pmap_ne_case t f =
  match t with
  | PNode001 r -> f PEmpty None (PNodes r)
  | PNode010 x -> f PEmpty (Some x) PEmpty
  | PNode011 (x, r) -> f PEmpty (Some x) (PNodes r)
  | PNode100 l -> f (PNodes l) None PEmpty
  | PNode101 (l, r) -> f (PNodes l) None (PNodes r)
  | PNode110 (l, x) -> f (PNodes l) (Some x) PEmpty
  | PNode111 (l, x, r) -> f (PNodes l) (Some x) (PNodes r)

(** val coq_Pmap_ne_lookup : (positive, 'a1, 'a1 coq_Pmap_ne) coq_Lookup **)

let rec coq_Pmap_ne_lookup i = function
| PNode001 r ->
  (match i with
   | Coq_xI i0 -> lookup coq_Pmap_ne_lookup i0 r
   | _ -> None)
| PNode010 x -> (match i with
                 | Coq_xH -> Some x
                 | _ -> None)
| PNode011 (x, r) ->
  (match i with
   | Coq_xI i0 -> lookup coq_Pmap_ne_lookup i0 r
   | Coq_xO _ -> None
   | Coq_xH -> Some x)
| PNode100 l ->
  (match i with
   | Coq_xO i0 -> lookup coq_Pmap_ne_lookup i0 l
   | _ -> None)
| PNode101 (l, r) ->
  (match i with
   | Coq_xI i0 -> lookup coq_Pmap_ne_lookup i0 r
   | Coq_xO i0 -> lookup coq_Pmap_ne_lookup i0 l
   | Coq_xH -> None)
| PNode110 (l, x) ->
  (match i with
   | Coq_xI _ -> None
   | Coq_xO i0 -> lookup coq_Pmap_ne_lookup i0 l
   | Coq_xH -> Some x)
| PNode111 (l, x, r) ->
  (match i with
   | Coq_xI i0 -> lookup coq_Pmap_ne_lookup i0 r
   | Coq_xO i0 -> lookup coq_Pmap_ne_lookup i0 l
   | Coq_xH -> Some x)

(** val coq_Pmap_lookup : (positive, 'a1, 'a1 coq_Pmap) coq_Lookup **)

let coq_Pmap_lookup i = function
| PEmpty -> None
| PNodes t -> lookup coq_Pmap_ne_lookup i t

(** val coq_Pmap_empty : 'a1 coq_Pmap coq_Empty **)

let coq_Pmap_empty =
  PEmpty

(** val coq_Pmap_ne_singleton : positive -> 'a1 -> 'a1 coq_Pmap_ne **)

let rec coq_Pmap_ne_singleton i x =
  match i with
  | Coq_xI i0 -> PNode001 (coq_Pmap_ne_singleton i0 x)
  | Coq_xO i0 -> PNode100 (coq_Pmap_ne_singleton i0 x)
  | Coq_xH -> PNode010 x

(** val coq_Pmap_partial_alter_aux :
    (positive -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap) -> ('a1 option -> 'a1
    option) -> positive -> 'a1 coq_Pmap -> 'a1 coq_Pmap **)

let coq_Pmap_partial_alter_aux go f i = function
| PEmpty ->
  (match f None with
   | Some x -> PNodes (coq_Pmap_ne_singleton i x)
   | None -> PEmpty)
| PNodes t -> go i t

(** val coq_Pmap_ne_partial_alter :
    ('a1 option -> 'a1 option) -> positive -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap **)

let rec coq_Pmap_ne_partial_alter f i t =
  coq_Pmap_ne_case t (fun ml mx mr ->
    match i with
    | Coq_xI i0 ->
      coq_PNode ml mx
        (coq_Pmap_partial_alter_aux (coq_Pmap_ne_partial_alter f) f i0 mr)
    | Coq_xO i0 ->
      coq_PNode
        (coq_Pmap_partial_alter_aux (coq_Pmap_ne_partial_alter f) f i0 ml) mx
        mr
    | Coq_xH -> coq_PNode ml (f mx) mr)

(** val coq_Pmap_partial_alter :
    (positive, 'a1, 'a1 coq_Pmap) coq_PartialAlter **)

let coq_Pmap_partial_alter f =
  coq_Pmap_partial_alter_aux (coq_Pmap_ne_partial_alter f) f

(** val coq_Pmap_ne_fmap :
    ('a1 -> 'a2) -> 'a1 coq_Pmap_ne -> 'a2 coq_Pmap_ne **)

let rec coq_Pmap_ne_fmap f = function
| PNode001 r -> PNode001 (coq_Pmap_ne_fmap f r)
| PNode010 x -> PNode010 (f x)
| PNode011 (x, r) -> PNode011 ((f x), (coq_Pmap_ne_fmap f r))
| PNode100 l -> PNode100 (coq_Pmap_ne_fmap f l)
| PNode101 (l, r) -> PNode101 ((coq_Pmap_ne_fmap f l), (coq_Pmap_ne_fmap f r))
| PNode110 (l, x) -> PNode110 ((coq_Pmap_ne_fmap f l), (f x))
| PNode111 (l, x, r) ->
  PNode111 ((coq_Pmap_ne_fmap f l), (f x), (coq_Pmap_ne_fmap f r))

(** val coq_Pmap_fmap : (__ -> __) -> __ coq_Pmap -> __ coq_Pmap **)

let coq_Pmap_fmap f = function
| PEmpty -> PEmpty
| PNodes t -> PNodes (coq_Pmap_ne_fmap f t)

(** val coq_Pmap_omap_aux :
    ('a1 coq_Pmap_ne -> 'a2 coq_Pmap) -> 'a1 coq_Pmap -> 'a2 coq_Pmap **)

let coq_Pmap_omap_aux go = function
| PEmpty -> PEmpty
| PNodes t' -> go t'

(** val coq_Pmap_ne_omap :
    ('a1 -> 'a2 option) -> 'a1 coq_Pmap_ne -> 'a2 coq_Pmap **)

let rec coq_Pmap_ne_omap f t =
  coq_Pmap_ne_case t (fun ml mx mr ->
    coq_PNode (coq_Pmap_omap_aux (coq_Pmap_ne_omap f) ml)
      (mbind (Obj.magic (fun _ _ -> option_bind)) f (Obj.magic mx))
      (coq_Pmap_omap_aux (coq_Pmap_ne_omap f) mr))

(** val coq_Pmap_merge_aux :
    ('a1 coq_Pmap_ne -> 'a2 coq_Pmap_ne -> 'a3 coq_Pmap) -> ('a1 option ->
    'a2 option -> 'a3 option) -> 'a1 coq_Pmap -> 'a2 coq_Pmap -> 'a3 coq_Pmap **)

let coq_Pmap_merge_aux go f mt1 mt2 =
  match mt1 with
  | PEmpty ->
    (match mt2 with
     | PEmpty -> PEmpty
     | PNodes t2' -> coq_Pmap_ne_omap (fun x -> f None (Some x)) t2')
  | PNodes t1' ->
    (match mt2 with
     | PEmpty -> coq_Pmap_ne_omap (fun x -> f (Some x) None) t1'
     | PNodes t2' -> go t1' t2')

(** val coq_Pmap_ne_merge :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 coq_Pmap_ne -> 'a2
    coq_Pmap_ne -> 'a3 coq_Pmap **)

let rec coq_Pmap_ne_merge f t1 t2 =
  coq_Pmap_ne_case t1 (fun ml1 mx1 mr1 ->
    coq_Pmap_ne_case t2 (fun ml2 mx2 mr2 ->
      coq_PNode (coq_Pmap_merge_aux (coq_Pmap_ne_merge f) f ml1 ml2)
        (diag_None f mx1 mx2)
        (coq_Pmap_merge_aux (coq_Pmap_ne_merge f) f mr1 mr2)))

(** val coq_Pmap_merge :
    (__ option -> __ option -> __ option) -> __ coq_Pmap -> __ coq_Pmap -> __
    coq_Pmap **)

let coq_Pmap_merge f =
  coq_Pmap_merge_aux (coq_Pmap_ne_merge f) f

(** val coq_Pmap_fold_aux :
    (positive -> 'a2 -> 'a1 coq_Pmap_ne -> 'a2) -> positive -> 'a2 -> 'a1
    coq_Pmap -> 'a2 **)

let coq_Pmap_fold_aux go i y = function
| PEmpty -> y
| PNodes t -> go i y t

(** val coq_Pmap_ne_fold :
    (positive -> 'a1 -> 'a2 -> 'a2) -> positive -> 'a2 -> 'a1 coq_Pmap_ne ->
    'a2 **)

let rec coq_Pmap_ne_fold f i y t =
  coq_Pmap_ne_case t (fun ml mx mr ->
    coq_Pmap_fold_aux (coq_Pmap_ne_fold f) (Coq_xI i)
      (coq_Pmap_fold_aux (coq_Pmap_ne_fold f) (Coq_xO i)
        (match mx with
         | Some x -> f (Pos.reverse i) x y
         | None -> y) ml) mr)

(** val coq_Pmap_fold :
    (positive -> 'a1 -> __ -> __) -> __ -> 'a1 coq_Pmap -> __ **)

let coq_Pmap_fold f =
  coq_Pmap_fold_aux (coq_Pmap_ne_fold f) Coq_xH
