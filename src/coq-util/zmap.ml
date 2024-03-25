open Basics
open BinNums
open Base
open Fin_maps
open Option0
open Pmap

type __ = Obj.t

type 'a coq_Zmap = { coq_Zmap_0 : 'a option; coq_Zmap_pos : 'a coq_Pmap;
                     coq_Zmap_neg : 'a coq_Pmap }

(** val coq_Zmap_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 coq_Zmap, 'a1 coq_Zmap) coq_RelDecision **)

let coq_Zmap_eq_dec eqDecision0 t1 t2 =
  let { coq_Zmap_0 = x; coq_Zmap_pos = t3; coq_Zmap_neg = t1' } = t1 in
  let { coq_Zmap_0 = y; coq_Zmap_pos = t4; coq_Zmap_neg = t2' } = t2 in
  if decide (decide_rel (option_eq_dec eqDecision0) x y)
  then if decide (decide_rel (coq_Pmap_eq_dec eqDecision0) t3 t4)
       then decide (decide_rel (coq_Pmap_eq_dec eqDecision0) t1' t2')
       else false
  else false

(** val coq_Zmap_empty : 'a1 coq_Zmap coq_Empty **)

let coq_Zmap_empty =
  { coq_Zmap_0 = None; coq_Zmap_pos = (empty coq_Pmap_empty); coq_Zmap_neg =
    (empty coq_Pmap_empty) }

(** val coq_Zmap_lookup : (coq_Z, 'a1, 'a1 coq_Zmap) coq_Lookup **)

let coq_Zmap_lookup i t =
  match i with
  | Z0 -> t.coq_Zmap_0
  | Zpos p -> lookup coq_Pmap_lookup p t.coq_Zmap_pos
  | Zneg p -> lookup coq_Pmap_lookup p t.coq_Zmap_neg

(** val coq_Zmap_partial_alter :
    (coq_Z, 'a1, 'a1 coq_Zmap) coq_PartialAlter **)

let coq_Zmap_partial_alter f i t =
  match i with
  | Z0 ->
    let { coq_Zmap_0 = o; coq_Zmap_pos = t0; coq_Zmap_neg = t' } = t in
    { coq_Zmap_0 = (f o); coq_Zmap_pos = t0; coq_Zmap_neg = t' }
  | Zpos p ->
    let { coq_Zmap_0 = o; coq_Zmap_pos = t0; coq_Zmap_neg = t' } = t in
    { coq_Zmap_0 = o; coq_Zmap_pos =
    (partial_alter coq_Pmap_partial_alter f p t0); coq_Zmap_neg = t' }
  | Zneg p ->
    let { coq_Zmap_0 = o; coq_Zmap_pos = t0; coq_Zmap_neg = t' } = t in
    { coq_Zmap_0 = o; coq_Zmap_pos = t0; coq_Zmap_neg =
    (partial_alter coq_Pmap_partial_alter f p t') }

(** val coq_Zmap_fmap : (__ -> __) -> __ coq_Zmap -> __ coq_Zmap **)

let coq_Zmap_fmap f t =
  let { coq_Zmap_0 = o; coq_Zmap_pos = t0; coq_Zmap_neg = t' } = t in
  { coq_Zmap_0 = (fmap (fun _ _ -> option_fmap) f o); coq_Zmap_pos =
  (fmap (fun _ _ -> coq_Pmap_fmap) f t0); coq_Zmap_neg =
  (fmap (fun _ _ -> coq_Pmap_fmap) f t') }

(** val coq_Zmap_merge :
    (__ option -> __ option -> __ option) -> __ coq_Zmap -> __ coq_Zmap -> __
    coq_Zmap **)

let coq_Zmap_merge f t1 t2 =
  let { coq_Zmap_0 = o1; coq_Zmap_pos = t3; coq_Zmap_neg = t1' } = t1 in
  let { coq_Zmap_0 = o2; coq_Zmap_pos = t4; coq_Zmap_neg = t2' } = t2 in
  { coq_Zmap_0 = (diag_None f o1 o2); coq_Zmap_pos =
  (merge (fun _ _ _ -> coq_Pmap_merge) f t3 t4); coq_Zmap_neg =
  (merge (fun _ _ _ -> coq_Pmap_merge) f t1' t2') }

(** val coq_Zmap_fold :
    (coq_Z -> 'a1 -> __ -> __) -> __ -> 'a1 coq_Zmap -> __ **)

let coq_Zmap_fold f d t =
  let { coq_Zmap_0 = mx; coq_Zmap_pos = t0; coq_Zmap_neg = t' } = t in
  map_fold (fun _ -> coq_Pmap_fold) (compose f (fun x -> Zpos x))
    (map_fold (fun _ -> coq_Pmap_fold) (compose f (fun x -> Zneg x))
      (match mx with
       | Some x -> f Z0 x d
       | None -> d) t') t0
