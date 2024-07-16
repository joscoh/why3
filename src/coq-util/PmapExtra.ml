open CoqUtil
open Pmap
open Zmap

(** val pmap_ne_eqb :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_Pmap_ne -> 'a1 coq_Pmap_ne -> bool **)

let rec pmap_ne_eqb eqb p1 p2 =
  match p1 with
  | PNode001 p3 ->
    (match p2 with
     | PNode001 p4 -> pmap_ne_eqb eqb p3 p4
     | _ -> false)
  | PNode010 x1 -> (match p2 with
                    | PNode010 x2 -> eqb x1 x2
                    | _ -> false)
  | PNode011 (x1, p3) ->
    (match p2 with
     | PNode011 (x2, p4) -> (&&) (eqb x1 x2) (pmap_ne_eqb eqb p3 p4)
     | _ -> false)
  | PNode100 p3 ->
    (match p2 with
     | PNode100 p4 -> pmap_ne_eqb eqb p3 p4
     | _ -> false)
  | PNode101 (p3, p4) ->
    (match p2 with
     | PNode101 (p5, p6) ->
       (&&) (pmap_ne_eqb eqb p3 p5) (pmap_ne_eqb eqb p4 p6)
     | _ -> false)
  | PNode110 (p3, x1) ->
    (match p2 with
     | PNode110 (p4, x2) -> (&&) (eqb x1 x2) (pmap_ne_eqb eqb p3 p4)
     | _ -> false)
  | PNode111 (p3, x1, p4) ->
    (match p2 with
     | PNode111 (p5, x2, p6) ->
       (&&) ((&&) (eqb x1 x2) (pmap_ne_eqb eqb p3 p5)) (pmap_ne_eqb eqb p4 p6)
     | _ -> false)

(** val pmap_eqb :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_Pmap -> 'a1 coq_Pmap -> bool **)

let pmap_eqb eqb p1 p2 =
  match p1 with
  | PEmpty -> (match p2 with
               | PEmpty -> true
               | PNodes _ -> false)
  | PNodes p3 ->
    (match p2 with
     | PEmpty -> false
     | PNodes p4 -> pmap_ne_eqb eqb p3 p4)

(** val zmap_eqb :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_Zmap -> 'a1 coq_Zmap -> bool **)

let zmap_eqb eqb z1 z2 =
  (&&)
    ((&&) (option_eqb eqb z1.coq_Zmap_0 z2.coq_Zmap_0)
      (pmap_eqb eqb z1.coq_Zmap_pos z2.coq_Zmap_pos))
    (pmap_eqb eqb z1.coq_Zmap_neg z2.coq_Zmap_neg)
