open BinNums

(** val bool_cons_pos : bool -> positive -> positive **)

let bool_cons_pos b p =
  if b then Coq_xI p else Coq_xO p

(** val ascii_cons_pos : char -> positive -> positive **)

let ascii_cons_pos c p =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    bool_cons_pos b0
      (bool_cons_pos b1
        (bool_cons_pos b2
          (bool_cons_pos b3
            (bool_cons_pos b4
              (bool_cons_pos b5 (bool_cons_pos b6 (bool_cons_pos b7 p))))))))
    c

(** val string_to_pos : string -> positive **)

let rec string_to_pos s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> Coq_xH)
    (fun c s0 -> ascii_cons_pos c (string_to_pos s0))
    s
