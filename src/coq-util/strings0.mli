open BinNums
open Base
open Countable

val ascii_eq_dec : (char, char) coq_RelDecision

val string_eq_dec : (string, string) coq_RelDecision

val bool_cons_pos : bool -> positive -> positive

val ascii_cons_pos : char -> positive -> positive

val string_to_pos : string -> positive

val pos_to_string : positive -> string

val string_countable : string coq_Countable
