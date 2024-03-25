open BinNums

module Pos =
 struct
  (** val reverse_go : positive -> positive -> positive **)

  let rec reverse_go p1 = function
  | Coq_xI p3 -> reverse_go (Coq_xI p1) p3
  | Coq_xO p3 -> reverse_go (Coq_xO p1) p3
  | Coq_xH -> p1

  (** val reverse : positive -> positive **)

  let reverse =
    reverse_go Coq_xH
 end
