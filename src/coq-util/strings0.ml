open BinNums
open Base
open Countable

(** val ascii_eq_dec : (char, char) coq_RelDecision **)

let ascii_eq_dec =
  (=)

(** val string_eq_dec : (string, string) coq_RelDecision **)

let rec string_eq_dec s x0 =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> true)
      (fun _ _ -> false)
      x0)
    (fun a s0 ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> false)
      (fun a0 s1 ->
      if decide_rel ascii_eq_dec a a0 then string_eq_dec s0 s1 else false)
      x0)
    s

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

(** val pos_to_string : positive -> string **)

let rec pos_to_string = function
| Coq_xI p0 ->
  (match p0 with
   | Coq_xI p1 ->
     (match p1 with
      | Coq_xI p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\255', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\127', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\191', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('?', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\223', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('_', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\159', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\031', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\239', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('o', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\175', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('/', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\207', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('O', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\143', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\015', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\247', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('w', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\183', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('7', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\215', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('W', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\151', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\023', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\231', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('g', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\167', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\'', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\199', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('G', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\135', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\007', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xO p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\251', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('{', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\187', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (';', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\219', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('[', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\155', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\027', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\235', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('k', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\171', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('+', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\203', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('K', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\139', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\011', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\243', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('s', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\179', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('3', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\211', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('S', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\147', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\019', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\227', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('c', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\163', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('#', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\195', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('C', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\131', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\003', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xH -> "")
   | Coq_xO p1 ->
     (match p1 with
      | Coq_xI p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\253', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('}', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\189', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('=', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\221', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (']', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\157', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\029', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\237', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('m', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\173', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('-', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\205', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('M', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\141', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\r', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\245', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('u', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\181', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('5', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\213', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('U', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\149', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\021', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\229', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('e', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\165', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('%', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\197', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('E', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\133', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\005', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xO p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\249', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('y', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\185', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('9', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\217', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('Y', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\153', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\025', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\233', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('i', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\169', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (')', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\201', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('I', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\137', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\t', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\241', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('q', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\177', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('1', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\209', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('Q', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\145', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\017', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\225', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('a', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\161', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('!', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\193', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('A', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\129', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\001', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xH -> "")
   | Coq_xH -> "")
| Coq_xO p0 ->
  (match p0 with
   | Coq_xI p1 ->
     (match p1 with
      | Coq_xI p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\254', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('~', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\190', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('>', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\222', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('^', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\158', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\030', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\238', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('n', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\174', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('.', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\206', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('N', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\142', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\014', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\246', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('v', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\182', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('6', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\214', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('V', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\150', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\022', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\230', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('f', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\166', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('&', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\198', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('F', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\134', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\006', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xO p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\250', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('z', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\186', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (':', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\218', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('Z', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\154', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\026', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\234', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('j', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\170', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('*', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\202', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('J', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\138', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\n', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\242', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('r', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\178', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('2', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\210', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('R', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\146', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\018', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\226', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('b', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\162', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('"', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\194', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('B', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\130', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\002', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xH -> "")
   | Coq_xO p1 ->
     (match p1 with
      | Coq_xI p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\252', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('|', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\188', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('<', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\220', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\\', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\156', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\028', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\236', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('l', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\172', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (',', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\204', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('L', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\140', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\012', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\244', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('t', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\180', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('4', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\212', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('T', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\148', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\020', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\228', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('d', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\164', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('$', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\196', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('D', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\132', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\004', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xO p2 ->
        (match p2 with
         | Coq_xI p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\248', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('x', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\184', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('8', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\216', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('X', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\152', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\024', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\232', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('h', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\168', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('(', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\200', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('H', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\136', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\b', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xO p3 ->
           (match p3 with
            | Coq_xI p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\240', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('p', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\176', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('0', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\208', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('P', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\144', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\016', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xO p4 ->
              (match p4 with
               | Coq_xI p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\224', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('`', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\160', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         (' ', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xO p5 ->
                 (match p5 with
                  | Coq_xI p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\192', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('@', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xO p6 ->
                    (match p6 with
                     | Coq_xI p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\128', (pos_to_string p7))
                     | Coq_xO p7 ->
                       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                         ('\000', (pos_to_string p7))
                     | Coq_xH -> "")
                  | Coq_xH -> "")
               | Coq_xH -> "")
            | Coq_xH -> "")
         | Coq_xH -> "")
      | Coq_xH -> "")
   | Coq_xH -> "")
| Coq_xH -> ""

(** val string_countable : string coq_Countable **)

let string_countable =
  { encode = string_to_pos; decode = (fun p -> Some (pos_to_string p)) }
