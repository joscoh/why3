open Base

(** val unit_eq_dec : (unit, unit) coq_RelDecision **)

let unit_eq_dec _ _ =
  true

(** val prod_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a2, 'a2) coq_RelDecision -> ('a1 * 'a2,
    'a1 * 'a2) coq_RelDecision **)

let prod_eq_dec eqDecision0 eqDecision1 x y =
  let (a, b) = x in
  let (a0, b0) = y in
  if decide_rel eqDecision0 a a0 then decide_rel eqDecision1 b b0 else false
