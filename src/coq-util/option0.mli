open Datatypes

type __ = Obj.t

val option_bind : (__ -> __ option) -> __ option -> __ option

val option_fmap : (__ -> __) -> __ option -> __ option
