open Base

val unit_eq_dec : (unit, unit) coq_RelDecision

val prod_eq_dec :
  ('a1, 'a1) coq_RelDecision -> ('a2, 'a2) coq_RelDecision -> ('a1 * 'a2,
  'a1 * 'a2) coq_RelDecision
