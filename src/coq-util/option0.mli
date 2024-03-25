open Datatypes
open Base

type __ = Obj.t

val option_eq_dec :
  ('a1, 'a1) coq_RelDecision -> ('a1 option, 'a1 option) coq_RelDecision

val option_bind : (__ -> __ option) -> __ option -> __ option

val option_fmap : (__ -> __) -> __ option -> __ option
