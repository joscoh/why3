open Datatypes

type __ = Obj.t

type coq_Decision = bool

val decide : coq_Decision -> bool

type ('a, 'b) coq_RelDecision = 'a -> 'b -> coq_Decision

val decide_rel : ('a1, 'a2) coq_RelDecision -> 'a1 -> 'a2 -> coq_Decision

type 'a coq_Empty = 'a

val empty : 'a1 coq_Empty -> 'a1

type 'm coq_MBind = __ -> __ -> (__ -> 'm) -> 'm -> 'm

val mbind : 'a1 coq_MBind -> ('a2 -> 'a1) -> 'a1 -> 'a1

type 'm coq_FMap = __ -> __ -> (__ -> __) -> 'm -> 'm

val fmap : 'a1 coq_FMap -> ('a2 -> 'a3) -> 'a1 -> 'a1

type ('k, 'a, 'm) coq_Lookup = 'k -> 'm -> 'a option

val lookup : ('a1, 'a2, 'a3) coq_Lookup -> 'a1 -> 'a3 -> 'a2 option

type ('k, 'a, 'm) coq_SingletonM = 'k -> 'a -> 'm

val singletonM : ('a1, 'a2, 'a3) coq_SingletonM -> 'a1 -> 'a2 -> 'a3

type ('k, 'a, 'm) coq_Insert = 'k -> 'a -> 'm -> 'm

val insert : ('a1, 'a2, 'a3) coq_Insert -> 'a1 -> 'a2 -> 'a3 -> 'a3

type ('k, 'm) coq_Delete = 'k -> 'm -> 'm

val delete : ('a1, 'a2) coq_Delete -> 'a1 -> 'a2 -> 'a2

type ('k, 'a, 'm) coq_PartialAlter =
  ('a option -> 'a option) -> 'k -> 'm -> 'm

val partial_alter :
  ('a1, 'a2, 'a3) coq_PartialAlter -> ('a2 option -> 'a2 option) -> 'a1 ->
  'a3 -> 'a3

type 'm coq_Merge =
  __ -> __ -> __ -> (__ option -> __ option -> __ option) -> 'm -> 'm -> 'm

val merge :
  'a1 coq_Merge -> ('a2 option -> 'a3 option -> 'a4 option) -> 'a1 -> 'a1 ->
  'a1

type 'c coq_Size = 'c -> nat
