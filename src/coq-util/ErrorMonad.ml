
type __ = Obj.t

type 'a errorM = 'a

(** val ignore : 'a1 errorM -> unit errorM **)

let ignore x =
  (@@) (fun _ ->  ()) x
