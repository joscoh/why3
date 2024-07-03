type 'b0 nl_symbol =
  | NLFVar_symbol of 'b0
  | NLBruijn_symbol of (Z.t)

type ('b0, 'b3) nl_fo_term_list =
  | NL_FONil
  | NL_FOCons of (('b0, 'b3) nl_fo_term) * (('b0, 'b3) nl_fo_term_list)
and ('b0, 'b3) nl_fo_term =
  | NLFVar_fo_term of 'b3
  | NLBruijn_fo_term of (Z.t)
  | NL_App of ('b0 nl_symbol) * (('b0, 'b3) nl_fo_term_list)

type ('b0, 'b1) nl_fo_formula =
  | NL_Forall of (('b0, 'b1) nl_fo_formula)
  | NL_Exists of (('b0, 'b1) nl_fo_formula)
  | NL_And of (('b0, 'b1) nl_fo_formula) * (('b0, 'b1) nl_fo_formula)
  | NL_Or of (('b0, 'b1) nl_fo_formula) * (('b0, 'b1) nl_fo_formula)
  | NL_Not of (('b0, 'b1) nl_fo_formula)
  | NL_FTrue
  | NL_FFalse
  | NL_PApp of ('b0 nl_symbol) * (('b0, 'b1) nl_fo_term_list)

type nlimpl_fo_formula = {
  nlrepr_fo_formula_field: (Z.t, Z.t) nl_fo_formula;
  nlfree_var_symbol_set_abstraction_fo_formula_field: Z.t;
  nlfree_var_fo_term_set_abstraction_fo_formula_field: Z.t;
  }

type nlimpl_symbol = {
  nlrepr_symbol_field: (Z.t) nl_symbol;
  nlfree_var_symbol_set_abstraction_symbol_field: Z.t;
  }

type nlimpl_fo_term_list = {
  nlrepr_fo_term_list_field: (Z.t, Z.t) nl_fo_term_list;
  nlfree_var_symbol_set_abstraction_fo_term_list_field: Z.t;
  nlfree_var_fo_term_set_abstraction_fo_term_list_field: Z.t;
  }

type cons_fo_formula =
  | NLC_Forall of (Z.t) * nlimpl_fo_formula
  | NLC_Exists of (Z.t) * nlimpl_fo_formula
  | NLC_And of nlimpl_fo_formula * nlimpl_fo_formula
  | NLC_Or of nlimpl_fo_formula * nlimpl_fo_formula
  | NLC_Not of nlimpl_fo_formula
  | NLC_FTrue
  | NLC_FFalse
  | NLC_PApp of nlimpl_symbol * nlimpl_fo_term_list

let rec bind_var_symbol_in_symbol (t: (Z.t) nl_symbol) (x: Z.t) (i: Z.t) :
  (Z.t) nl_symbol =
  match t with
  | NLFVar_symbol v0 ->
    if Z.equal v0 x then NLBruijn_symbol i else NLFVar_symbol v0
  | NLBruijn_symbol v0 -> NLBruijn_symbol v0

let rec bind_var_symbol_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list)
                                        (x: Z.t) (i: Z.t) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (bind_var_symbol_in_fo_term v0 x (Z.add i Z.zero),
    bind_var_symbol_in_fo_term_list v1 x (Z.add i Z.zero))
and bind_var_fo_term_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list) 
                                     (x: Z.t) (i: Z.t) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (bind_var_fo_term_in_fo_term v0 x (Z.add i Z.zero),
    bind_var_fo_term_in_fo_term_list v1 x (Z.add i Z.zero))
and bind_var_symbol_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (x: Z.t) (i: Z.t) :
  (Z.t, Z.t) nl_fo_term =
  match t with
  | NLFVar_fo_term v0 -> NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> NLBruijn_fo_term v0
  | NL_App (v0,
    v1) ->
    NL_App (bind_var_symbol_in_symbol v0 x (Z.add i Z.zero),
    bind_var_symbol_in_fo_term_list v1 x (Z.add i Z.zero))
and bind_var_fo_term_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (x: Z.t) (i: Z.t) :
  (Z.t, Z.t) nl_fo_term =
  match t with
  | NLFVar_fo_term v0 ->
    if Z.equal v0 x then NLBruijn_fo_term i else NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> NLBruijn_fo_term v0
  | NL_App (v0,
    v1) ->
    NL_App (v0, bind_var_fo_term_in_fo_term_list v1 x (Z.add i Z.zero))

let rec bind_var_symbol_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula) (x: Z.t)
                                      (i: Z.t) : (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 ->
    NL_Forall (bind_var_symbol_in_fo_formula v0 x (Z.add i Z.zero))
  | NL_Exists v0 ->
    NL_Exists (bind_var_symbol_in_fo_formula v0 x (Z.add i Z.zero))
  | NL_And (v0,
    v1) ->
    NL_And (bind_var_symbol_in_fo_formula v0 x (Z.add i Z.zero),
    bind_var_symbol_in_fo_formula v1 x (Z.add i Z.zero))
  | NL_Or (v0,
    v1) ->
    NL_Or (bind_var_symbol_in_fo_formula v0 x (Z.add i Z.zero),
    bind_var_symbol_in_fo_formula v1 x (Z.add i Z.zero))
  | NL_Not v0 -> NL_Not (bind_var_symbol_in_fo_formula v0 x (Z.add i Z.zero))
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (bind_var_symbol_in_symbol v0 x (Z.add i Z.zero),
    bind_var_symbol_in_fo_term_list v1 x (Z.add i Z.zero))
and bind_var_fo_term_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula) (x: Z.t)
                                   (i: Z.t) : (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 ->
    NL_Forall (bind_var_fo_term_in_fo_formula v0 x (Z.add i Z.one))
  | NL_Exists v0 ->
    NL_Exists (bind_var_fo_term_in_fo_formula v0 x (Z.add i Z.one))
  | NL_And (v0,
    v1) ->
    NL_And (bind_var_fo_term_in_fo_formula v0 x (Z.add i Z.zero),
    bind_var_fo_term_in_fo_formula v1 x (Z.add i Z.zero))
  | NL_Or (v0,
    v1) ->
    NL_Or (bind_var_fo_term_in_fo_formula v0 x (Z.add i Z.zero),
    bind_var_fo_term_in_fo_formula v1 x (Z.add i Z.zero))
  | NL_Not v0 ->
    NL_Not (bind_var_fo_term_in_fo_formula v0 x (Z.add i Z.zero))
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (v0, bind_var_fo_term_in_fo_term_list v1 x (Z.add i Z.zero))

let construct_fo_formula (c: cons_fo_formula) : nlimpl_fo_formula =
  match c with
  | NLC_Forall (v0,
    v1) ->
    { nlrepr_fo_formula_field =
      NL_Forall (let v11 = v1.nlrepr_fo_formula_field in
                 bind_var_fo_term_in_fo_formula v11 v0 Z.zero);
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      v1.nlfree_var_symbol_set_abstraction_fo_formula_field;
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      v1.nlfree_var_fo_term_set_abstraction_fo_formula_field }
  | NLC_Exists (v0,
    v1) ->
    { nlrepr_fo_formula_field =
      NL_Exists (let v11 = v1.nlrepr_fo_formula_field in
                 bind_var_fo_term_in_fo_formula v11 v0 Z.zero);
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      v1.nlfree_var_symbol_set_abstraction_fo_formula_field;
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      v1.nlfree_var_fo_term_set_abstraction_fo_formula_field }
  | NLC_And (v0,
    v1) ->
    { nlrepr_fo_formula_field =
      NL_And (v0.nlrepr_fo_formula_field, v1.nlrepr_fo_formula_field);
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      (let aux (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux v0.nlfree_var_symbol_set_abstraction_fo_formula_field
       v1.nlfree_var_symbol_set_abstraction_fo_formula_field);
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      (let aux1 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux1 v0.nlfree_var_fo_term_set_abstraction_fo_formula_field
       v1.nlfree_var_fo_term_set_abstraction_fo_formula_field) }
  | NLC_Or (v0,
    v1) ->
    { nlrepr_fo_formula_field =
      NL_Or (v0.nlrepr_fo_formula_field, v1.nlrepr_fo_formula_field);
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      (let aux2 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux2 v0.nlfree_var_symbol_set_abstraction_fo_formula_field
       v1.nlfree_var_symbol_set_abstraction_fo_formula_field);
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      (let aux3 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux3 v0.nlfree_var_fo_term_set_abstraction_fo_formula_field
       v1.nlfree_var_fo_term_set_abstraction_fo_formula_field) }
  | NLC_Not v0 ->
    { nlrepr_fo_formula_field = NL_Not v0.nlrepr_fo_formula_field;
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      v0.nlfree_var_symbol_set_abstraction_fo_formula_field;
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      v0.nlfree_var_fo_term_set_abstraction_fo_formula_field }
  | NLC_FTrue ->
    { nlrepr_fo_formula_field = NL_FTrue;
      nlfree_var_symbol_set_abstraction_fo_formula_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_fo_formula_field = Z.zero }
  | NLC_FFalse ->
    { nlrepr_fo_formula_field = NL_FFalse;
      nlfree_var_symbol_set_abstraction_fo_formula_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_fo_formula_field = Z.zero }
  | NLC_PApp (v0,
    v1) ->
    { nlrepr_fo_formula_field =
      NL_PApp (v0.nlrepr_symbol_field, v1.nlrepr_fo_term_list_field);
      nlfree_var_symbol_set_abstraction_fo_formula_field =
      (let aux4 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux4 v0.nlfree_var_symbol_set_abstraction_symbol_field
       v1.nlfree_var_symbol_set_abstraction_fo_term_list_field);
      nlfree_var_fo_term_set_abstraction_fo_formula_field =
      v1.nlfree_var_fo_term_set_abstraction_fo_term_list_field }

let imply (a: nlimpl_fo_formula) (b: nlimpl_fo_formula) : nlimpl_fo_formula =
  construct_fo_formula (NLC_Or (construct_fo_formula (NLC_Not a), b))

let equiv (a: nlimpl_fo_formula) (b: nlimpl_fo_formula) : nlimpl_fo_formula =
  construct_fo_formula (NLC_And (imply a b, imply b a))

type ('b0, 'b1) nl_fo_formula_list =
  | NL_FOFNil
  | NL_FOFCons of (('b0, 'b1) nl_fo_formula) *
      (('b0, 'b1) nl_fo_formula_list)

type nlimpl_fo_formula_list = {
  nlrepr_fo_formula_list_field: (Z.t, Z.t) nl_fo_formula_list;
  nlfree_var_symbol_set_abstraction_fo_formula_list_field: Z.t;
  nlfree_var_fo_term_set_abstraction_fo_formula_list_field: Z.t;
  }

type cons_fo_formula_list =
  | NLC_FOFNil
  | NLC_FOFCons of nlimpl_fo_formula * nlimpl_fo_formula_list

let construct_fo_formula_list (c: cons_fo_formula_list) :
  nlimpl_fo_formula_list =
  match c with
  | NLC_FOFNil ->
    { nlrepr_fo_formula_list_field = NL_FOFNil;
      nlfree_var_symbol_set_abstraction_fo_formula_list_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_fo_formula_list_field = Z.zero }
  | NLC_FOFCons (v0,
    v1) ->
    { nlrepr_fo_formula_list_field =
      NL_FOFCons (v0.nlrepr_fo_formula_field,
      v1.nlrepr_fo_formula_list_field);
      nlfree_var_symbol_set_abstraction_fo_formula_list_field =
      (let aux5 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux5 v0.nlfree_var_symbol_set_abstraction_fo_formula_field
       v1.nlfree_var_symbol_set_abstraction_fo_formula_list_field);
      nlfree_var_fo_term_set_abstraction_fo_formula_list_field =
      (let aux6 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux6 v0.nlfree_var_fo_term_set_abstraction_fo_formula_field
       v1.nlfree_var_fo_term_set_abstraction_fo_formula_list_field) }

type nlimpl_fo_term = {
  nlrepr_fo_term_field: (Z.t, Z.t) nl_fo_term;
  nlfree_var_symbol_set_abstraction_fo_term_field: Z.t;
  nlfree_var_fo_term_set_abstraction_fo_term_field: Z.t;
  }

type cons_fo_term_list =
  | NLC_FONil
  | NLC_FOCons of nlimpl_fo_term * nlimpl_fo_term_list

let construct_fo_term_list (c: cons_fo_term_list) : nlimpl_fo_term_list =
  match c with
  | NLC_FONil ->
    { nlrepr_fo_term_list_field = NL_FONil;
      nlfree_var_symbol_set_abstraction_fo_term_list_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_fo_term_list_field = Z.zero }
  | NLC_FOCons (v0,
    v1) ->
    { nlrepr_fo_term_list_field =
      NL_FOCons (v0.nlrepr_fo_term_field, v1.nlrepr_fo_term_list_field);
      nlfree_var_symbol_set_abstraction_fo_term_list_field =
      (let aux7 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux7 v0.nlfree_var_symbol_set_abstraction_fo_term_field
       v1.nlfree_var_symbol_set_abstraction_fo_term_list_field);
      nlfree_var_fo_term_set_abstraction_fo_term_list_field =
      (let aux8 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux8 v0.nlfree_var_fo_term_set_abstraction_fo_term_field
       v1.nlfree_var_fo_term_set_abstraction_fo_term_list_field) }

type cons_symbol = Z.t

let construct_symbol (c: cons_symbol) : nlimpl_symbol =
  let v0 = c in
  { nlrepr_symbol_field = NLFVar_symbol v0;
    nlfree_var_symbol_set_abstraction_symbol_field = Z.add Z.one v0 }

type cons_fo_term =
  | NLCVar_fo_term of (Z.t)
  | NLC_App of nlimpl_symbol * nlimpl_fo_term_list

let construct_fo_term (c: cons_fo_term) : nlimpl_fo_term =
  match c with
  | NLCVar_fo_term v0 ->
    { nlrepr_fo_term_field = NLFVar_fo_term v0;
      nlfree_var_symbol_set_abstraction_fo_term_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_fo_term_field = Z.add Z.one v0 }
  | NLC_App (v0,
    v1) ->
    { nlrepr_fo_term_field =
      NL_App (v0.nlrepr_symbol_field, v1.nlrepr_fo_term_list_field);
      nlfree_var_symbol_set_abstraction_fo_term_field =
      (let aux9 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux9 v0.nlfree_var_symbol_set_abstraction_symbol_field
       v1.nlfree_var_symbol_set_abstraction_fo_term_list_field);
      nlfree_var_fo_term_set_abstraction_fo_term_field =
      v1.nlfree_var_fo_term_set_abstraction_fo_term_list_field }

let drinker (_: unit) : nlimpl_fo_formula_list =
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let fotnil = construct_fo_term_list NLC_FONil in
  let c0 = construct_symbol Z.zero in
  let v0 = construct_fo_term (NLCVar_fo_term Z.zero) in
  let l0 = construct_fo_term_list (NLC_FOCons (v0, fotnil)) in
  let phip = construct_fo_formula (NLC_PApp (c0, l0)) in
  let phi0 = construct_fo_formula (NLC_Forall (Z.zero, phip)) in
  let phi1 = construct_fo_formula (NLC_Not phip) in
  let phi2 = construct_fo_formula (NLC_Or (phi1, phi0)) in
  let phi3 = construct_fo_formula (NLC_Exists (Z.zero, phi2)) in
  let phi4 = construct_fo_formula (NLC_Not phi3) in
  construct_fo_formula_list (NLC_FOFCons (phi4, fonil))

let group (_: unit) : nlimpl_fo_formula_list =
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let fotnil = construct_fo_term_list NLC_FONil in
  let c0 = construct_symbol Z.zero in
  let c1 = construct_symbol Z.one in
  let neutral = construct_fo_term (NLC_App (c1, fotnil)) in
  let aux10 (v1: nlimpl_fo_term) (v2: nlimpl_fo_term) (v3: nlimpl_fo_term) :
    nlimpl_fo_formula =
    let l = construct_fo_term_list (NLC_FOCons (v3, fotnil)) in
    let l1 = construct_fo_term_list (NLC_FOCons (v2, l)) in
    let l2 = construct_fo_term_list (NLC_FOCons (v1, l1)) in
    construct_fo_formula (NLC_PApp (c0, l2)) in
  let v0 = construct_fo_term (NLCVar_fo_term Z.zero) in
  let v1 = construct_fo_term (NLCVar_fo_term Z.one) in
  let v2 = construct_fo_term (NLCVar_fo_term (Z.of_string "2")) in
  let v3 = construct_fo_term (NLCVar_fo_term (Z.of_string "3")) in
  let v4 = construct_fo_term (NLCVar_fo_term (Z.of_string "4")) in
  let v5 = construct_fo_term (NLCVar_fo_term (Z.of_string "5")) in
  let phimul = aux10 v0 v1 v2 in
  let phimul1 = construct_fo_formula (NLC_Exists (Z.of_string "2", phimul)) in
  let phimul2 = construct_fo_formula (NLC_Forall (Z.one, phimul1)) in
  let phimul3 = construct_fo_formula (NLC_Forall (Z.zero, phimul2)) in
  let phi0ass = aux10 v0 v1 v3 in
  let phi1ass = aux10 v1 v2 v5 in
  let phi0ass1 = construct_fo_formula (NLC_And (phi0ass, phi1ass)) in
  let phi1ass1 = aux10 v3 v2 v4 in
  let phi2ass = aux10 v0 v5 v4 in
  let phicass = equiv phi1ass1 phi2ass in
  let phiass = imply phi0ass1 phicass in
  let phiass1 = construct_fo_formula (NLC_Forall (Z.of_string "5", phiass)) in
  let phiass2 = construct_fo_formula (NLC_Forall (Z.of_string "4", phiass1)) in
  let phiass3 = construct_fo_formula (NLC_Forall (Z.of_string "3", phiass2)) in
  let phiass4 = construct_fo_formula (NLC_Forall (Z.of_string "2", phiass3)) in
  let phiass5 = construct_fo_formula (NLC_Forall (Z.one, phiass4)) in
  let phiass6 = construct_fo_formula (NLC_Forall (Z.zero, phiass5)) in
  let phin0 = aux10 neutral v0 v0 in
  let phin1 = aux10 v0 neutral v0 in
  let phin = construct_fo_formula (NLC_And (phin0, phin1)) in
  let phin2 = construct_fo_formula (NLC_Forall (Z.zero, phin)) in
  let phi2 = aux10 v0 v0 neutral in
  let phi21 = construct_fo_formula (NLC_Forall (Z.zero, phi2)) in
  let phigh = aux10 v0 v1 v2 in
  let phig = aux10 v1 v0 v2 in
  let phig1 = imply phigh phig in
  let phig2 = construct_fo_formula (NLC_Forall (Z.of_string "2", phig1)) in
  let phig3 = construct_fo_formula (NLC_Forall (Z.one, phig2)) in
  let phig4 = construct_fo_formula (NLC_Forall (Z.zero, phig3)) in
  let phig5 = construct_fo_formula (NLC_Not phig4) in
  let l = construct_fo_formula_list (NLC_FOFCons (phimul3, fonil)) in
  let l1 = construct_fo_formula_list (NLC_FOFCons (phiass6, l)) in
  let l2 = construct_fo_formula_list (NLC_FOFCons (phin2, l1)) in
  let l3 = construct_fo_formula_list (NLC_FOFCons (phi21, l2)) in
  construct_fo_formula_list (NLC_FOFCons (phig5, l3))

let bidon1 (_: unit) : nlimpl_fo_formula_list =
  let a = construct_symbol Z.zero in
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let r = construct_fo_formula (NLC_Not (imply a1 a1)) in
  construct_fo_formula_list (NLC_FOFCons (r, fonil))

let bidon2 (_: unit) : nlimpl_fo_formula_list =
  let a = construct_symbol Z.zero in
  let b = construct_symbol Z.one in
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let b1 = construct_fo_formula (NLC_PApp (b, fotnil)) in
  let o = construct_fo_formula (NLC_Or (a1, b1)) in
  let a2 = construct_fo_formula (NLC_And (a1, b1)) in
  let r = construct_fo_formula (NLC_Not (imply a2 o)) in
  construct_fo_formula_list (NLC_FOFCons (r, fonil))

let bidon3 (_: unit) : nlimpl_fo_formula_list =
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let fotnil = construct_fo_term_list NLC_FONil in
  let a = construct_symbol Z.zero in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let b = construct_symbol Z.one in
  let b1 = construct_fo_formula (NLC_PApp (b, fotnil)) in
  let c = construct_symbol (Z.of_string "2") in
  let c1 = construct_fo_formula (NLC_PApp (c, fotnil)) in
  let r = imply (imply a1 (imply b1 c1)) (imply (imply a1 b1) (imply a1 c1)) in
  let r1 = construct_fo_formula (NLC_Not r) in
  construct_fo_formula_list (NLC_FOFCons (r1, fonil))

let bidon4 (_: unit) : nlimpl_fo_formula_list =
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let fotnil = construct_fo_term_list NLC_FONil in
  let a = construct_symbol Z.zero in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let b = construct_symbol Z.one in
  let b1 = construct_fo_formula (NLC_PApp (b, fotnil)) in
  let c = construct_symbol (Z.of_string "2") in
  let c1 = construct_fo_formula (NLC_PApp (c, fotnil)) in
  let r = imply (imply a1 (imply b1 c1)) (imply b1 (imply a1 c1)) in
  let r1 = construct_fo_formula (NLC_Not r) in
  construct_fo_formula_list (NLC_FOFCons (r1, fonil))

let pierce (_: unit) : nlimpl_fo_formula_list =
  let a = construct_symbol Z.zero in
  let b = construct_symbol Z.one in
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let b1 = construct_fo_formula (NLC_PApp (b, fotnil)) in
  let r = imply (imply (imply a1 b1) a1) a1 in
  let r1 = construct_fo_formula (NLC_Not r) in
  construct_fo_formula_list (NLC_FOFCons (r1, fonil))

let generate (n: Z.t) : nlimpl_fo_formula_list =
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let rec aux11 (m: Z.t) : nlimpl_fo_formula =
    let symb = construct_symbol m in
    let symb1 = construct_fo_formula (NLC_PApp (symb, fotnil)) in
    if Z.equal m Z.zero
    then equiv symb1 (aux0 n)
    else equiv symb1 (aux11 (Z.sub m Z.one))
  and aux0 (m: Z.t) : nlimpl_fo_formula =
    let symb = construct_symbol m in
    let symb1 = construct_fo_formula (NLC_PApp (symb, fotnil)) in
    if Z.equal m Z.zero then symb1 else equiv symb1 (aux0 (Z.sub m Z.one)) in
  let r = construct_fo_formula (NLC_Not (aux11 n)) in
  construct_fo_formula_list (NLC_FOFCons (r, fonil))

let zenon5 (_: unit) : nlimpl_fo_formula_list =
  let a = construct_symbol Z.zero in
  let b = construct_symbol Z.one in
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let a1 = construct_fo_formula (NLC_PApp (a, fotnil)) in
  let v = construct_fo_term (NLCVar_fo_term Z.zero) in
  let v1 = construct_fo_term_list (NLC_FOCons (v, fotnil)) in
  let bv = construct_fo_formula (NLC_PApp (b, v1)) in
  let e1 = construct_fo_formula (NLC_Exists (Z.zero, imply a1 bv)) in
  let e2 = construct_fo_formula (NLC_Exists (Z.zero, imply bv a1)) in
  let g = construct_fo_formula (NLC_Exists (Z.zero, equiv a1 bv)) in
  let ng = construct_fo_formula (NLC_Not g) in
  let l = construct_fo_formula_list (NLC_FOFCons (e1, fonil)) in
  let l1 = construct_fo_formula_list (NLC_FOFCons (e2, l)) in
  construct_fo_formula_list (NLC_FOFCons (ng, l1))

let zenon6 (_: unit) : nlimpl_fo_formula_list =
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let p = construct_symbol Z.zero in
  let q = construct_symbol Z.one in
  let r = construct_symbol (Z.of_string "2") in
  let s = construct_symbol (Z.of_string "3") in
  let x = construct_fo_term (NLCVar_fo_term Z.zero) in
  let x1 = construct_fo_term_list (NLC_FOCons (x, fotnil)) in
  let px = construct_fo_formula (NLC_PApp (p, x1)) in
  let qx = construct_fo_formula (NLC_PApp (q, x1)) in
  let rx = construct_fo_formula (NLC_PApp (r, x1)) in
  let sx = construct_fo_formula (NLC_PApp (s, x1)) in
  let h1 = construct_fo_formula (NLC_And (sx, qx)) in
  let h11 = construct_fo_formula (NLC_Exists (Z.zero, h1)) in
  let h12 = construct_fo_formula (NLC_Not h11) in
  let h2 = construct_fo_formula (NLC_Exists (Z.zero, px)) in
  let h21 = construct_fo_formula (NLC_Not h2) in
  let h2_ = construct_fo_formula (NLC_Exists (Z.zero, qx)) in
  let h22 = imply h21 h2_ in
  let h3 = construct_fo_formula (NLC_Or (qx, rx)) in
  let h31 = imply h3 sx in
  let h32 = construct_fo_formula (NLC_Forall (Z.zero, h31)) in
  let h4 = construct_fo_formula (NLC_Or (qx, rx)) in
  let h41 = imply px h4 in
  let h42 = construct_fo_formula (NLC_Forall (Z.zero, h41)) in
  let g = construct_fo_formula (NLC_And (px, rx)) in
  let g1 = construct_fo_formula (NLC_Exists (Z.zero, g)) in
  let g2 = construct_fo_formula (NLC_Not g1) in
  let l = construct_fo_formula_list (NLC_FOFCons (h12, fonil)) in
  let l1 = construct_fo_formula_list (NLC_FOFCons (h22, l)) in
  let l2 = construct_fo_formula_list (NLC_FOFCons (h32, l1)) in
  let l3 = construct_fo_formula_list (NLC_FOFCons (h42, l2)) in
  construct_fo_formula_list (NLC_FOFCons (g2, l3))

let zenon10 (n: Z.t) : nlimpl_fo_formula_list =
  let fotnil = construct_fo_term_list NLC_FONil in
  let fonil = construct_fo_formula_list NLC_FOFNil in
  let r = construct_symbol Z.zero in
  let f = construct_symbol Z.one in
  let x = construct_fo_term (NLCVar_fo_term Z.zero) in
  let x1 = construct_fo_term_list (NLC_FOCons (x, fotnil)) in
  let rec aux12 (n0: Z.t) : nlimpl_fo_term_list =
    if Z.equal n0 Z.zero
    then x1
    else
      begin
        let t = aux12 (Z.sub n0 Z.one) in
        let fx = construct_fo_term (NLC_App (f, t)) in
        construct_fo_term_list (NLC_FOCons (fx, fotnil)) end in
  let rx = construct_fo_formula (NLC_PApp (r, x1)) in
  let rfx = construct_fo_formula (NLC_PApp (r, aux12 Z.one)) in
  let rfnx = construct_fo_formula (NLC_PApp (r, aux12 n)) in
  let h = construct_fo_formula (NLC_Or (rx, rfx)) in
  let h1 = construct_fo_formula (NLC_Forall (Z.zero, h)) in
  let g = construct_fo_formula (NLC_And (rx, rfnx)) in
  let g1 = construct_fo_formula (NLC_Exists (Z.zero, g)) in
  let g2 = construct_fo_formula (NLC_Not g1) in
  let l = construct_fo_formula_list (NLC_FOFCons (h1, fonil)) in
  construct_fo_formula_list (NLC_FOFCons (g2, l))

type ('b0, 'b1) nl_tableau =
  | NL_Root
  | NL_Node of (('b0, 'b1) nl_tableau) * (('b0, 'b1) nl_fo_formula) *
      (('b0, 'b1) nl_fo_formula_list)

type nlimpl_tableau = {
  nlrepr_tableau_field: (Z.t, Z.t) nl_tableau;
  nlfree_var_symbol_set_abstraction_tableau_field: Z.t;
  nlfree_var_fo_term_set_abstraction_tableau_field: Z.t;
  }

type cons_tableau =
  | NLC_Root
  | NLC_Node of nlimpl_tableau * nlimpl_fo_formula * nlimpl_fo_formula_list

let construct_tableau (c: cons_tableau) : nlimpl_tableau =
  match c with
  | NLC_Root ->
    { nlrepr_tableau_field = NL_Root;
      nlfree_var_symbol_set_abstraction_tableau_field = Z.zero;
      nlfree_var_fo_term_set_abstraction_tableau_field = Z.zero }
  | NLC_Node (v0,
    v1,
    v2) ->
    { nlrepr_tableau_field =
      NL_Node (v0.nlrepr_tableau_field,
      v1.nlrepr_fo_formula_field,
      v2.nlrepr_fo_formula_list_field);
      nlfree_var_symbol_set_abstraction_tableau_field =
      (let aux13 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux13 (let aux14 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
              aux14 v0.nlfree_var_symbol_set_abstraction_tableau_field
              v1.nlfree_var_symbol_set_abstraction_fo_formula_field)
       v2.nlfree_var_symbol_set_abstraction_fo_formula_list_field);
      nlfree_var_fo_term_set_abstraction_tableau_field =
      (let aux15 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux15 (let aux16 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
              aux16 v0.nlfree_var_fo_term_set_abstraction_tableau_field
              v1.nlfree_var_fo_term_set_abstraction_fo_formula_field)
       v2.nlfree_var_fo_term_set_abstraction_fo_formula_list_field) }

type 'st preprocessing_return = {
  preprocessed: nlimpl_fo_formula_list;
  final_goals_number: Z.t;
  }

let destruct_fo_formula_list (t: nlimpl_fo_formula_list) :
  cons_fo_formula_list =
  let fv0 = t.nlfree_var_symbol_set_abstraction_fo_formula_list_field in
  let fv1 = t.nlfree_var_fo_term_set_abstraction_fo_formula_list_field in
  match t.nlrepr_fo_formula_list_field with
  | NL_FOFNil -> NLC_FOFNil
  | NL_FOFCons (v0,
    v1) ->
    (let resv0 =
       { nlrepr_fo_formula_field = v0;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     let resv1 =
       { nlrepr_fo_formula_list_field = v1;
         nlfree_var_symbol_set_abstraction_fo_formula_list_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_list_field = fv1 } in
     NLC_FOFCons (resv0, resv1))

let rec unbind_var_symbol_in_symbol (t: (Z.t) nl_symbol) (i: Z.t)
                                    (x: (Z.t) nl_symbol) : (Z.t) nl_symbol =
  match t with
  | NLFVar_symbol v0 -> NLFVar_symbol v0
  | NLBruijn_symbol v0 -> if Z.equal v0 i then x else NLBruijn_symbol v0

let rec unbind_var_symbol_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list)
                                          (i: Z.t) (x: (Z.t) nl_symbol) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (unbind_var_symbol_in_fo_term v0 (Z.add i Z.zero) x,
    unbind_var_symbol_in_fo_term_list v1 (Z.add i Z.zero) x)
and unbind_var_fo_term_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list)
                                       (i: Z.t) (x: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (unbind_var_fo_term_in_fo_term v0 (Z.add i Z.zero) x,
    unbind_var_fo_term_in_fo_term_list v1 (Z.add i Z.zero) x)
and unbind_var_symbol_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (i: Z.t)
                                 (x: (Z.t) nl_symbol) : (Z.t, Z.t) nl_fo_term
  =
  match t with
  | NLFVar_fo_term v0 -> NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> NLBruijn_fo_term v0
  | NL_App (v0,
    v1) ->
    NL_App (unbind_var_symbol_in_symbol v0 (Z.add i Z.zero) x,
    unbind_var_symbol_in_fo_term_list v1 (Z.add i Z.zero) x)
and unbind_var_fo_term_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (i: Z.t)
                                  (x: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_term =
  match t with
  | NLFVar_fo_term v0 -> NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> if Z.equal v0 i then x else NLBruijn_fo_term v0
  | NL_App (v0,
    v1) ->
    NL_App (v0, unbind_var_fo_term_in_fo_term_list v1 (Z.add i Z.zero) x)

let rec unbind_var_symbol_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula)
                                        (i: Z.t) (x: (Z.t) nl_symbol) :
  (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 ->
    NL_Forall (unbind_var_symbol_in_fo_formula v0 (Z.add i Z.zero) x)
  | NL_Exists v0 ->
    NL_Exists (unbind_var_symbol_in_fo_formula v0 (Z.add i Z.zero) x)
  | NL_And (v0,
    v1) ->
    NL_And (unbind_var_symbol_in_fo_formula v0 (Z.add i Z.zero) x,
    unbind_var_symbol_in_fo_formula v1 (Z.add i Z.zero) x)
  | NL_Or (v0,
    v1) ->
    NL_Or (unbind_var_symbol_in_fo_formula v0 (Z.add i Z.zero) x,
    unbind_var_symbol_in_fo_formula v1 (Z.add i Z.zero) x)
  | NL_Not v0 ->
    NL_Not (unbind_var_symbol_in_fo_formula v0 (Z.add i Z.zero) x)
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (unbind_var_symbol_in_symbol v0 (Z.add i Z.zero) x,
    unbind_var_symbol_in_fo_term_list v1 (Z.add i Z.zero) x)
and unbind_var_fo_term_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula) (i: Z.t)
                                     (x: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 ->
    NL_Forall (unbind_var_fo_term_in_fo_formula v0 (Z.add i Z.one) x)
  | NL_Exists v0 ->
    NL_Exists (unbind_var_fo_term_in_fo_formula v0 (Z.add i Z.one) x)
  | NL_And (v0,
    v1) ->
    NL_And (unbind_var_fo_term_in_fo_formula v0 (Z.add i Z.zero) x,
    unbind_var_fo_term_in_fo_formula v1 (Z.add i Z.zero) x)
  | NL_Or (v0,
    v1) ->
    NL_Or (unbind_var_fo_term_in_fo_formula v0 (Z.add i Z.zero) x,
    unbind_var_fo_term_in_fo_formula v1 (Z.add i Z.zero) x)
  | NL_Not v0 ->
    NL_Not (unbind_var_fo_term_in_fo_formula v0 (Z.add i Z.zero) x)
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (v0, unbind_var_fo_term_in_fo_term_list v1 (Z.add i Z.zero) x)

let destruct_fo_formula (t: nlimpl_fo_formula) : cons_fo_formula =
  let fv0 = t.nlfree_var_symbol_set_abstraction_fo_formula_field in
  let fv1 = t.nlfree_var_fo_term_set_abstraction_fo_formula_field in
  match t.nlrepr_fo_formula_field with
  | NL_Forall v0 ->
    (let w0 = fv1 in
     let fv11 =
       let aux17 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux17 (Z.add Z.one w0) fv1 in
     let v01 = unbind_var_fo_term_in_fo_formula v0 Z.zero (NLFVar_fo_term w0) in
     let resv0 =
       { nlrepr_fo_formula_field = v01;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv11 } in
     NLC_Forall (w0, resv0))
  | NL_Exists v0 ->
    (let w0 = fv1 in
     let fv11 =
       let aux18 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
       aux18 (Z.add Z.one w0) fv1 in
     let v01 = unbind_var_fo_term_in_fo_formula v0 Z.zero (NLFVar_fo_term w0) in
     let resv0 =
       { nlrepr_fo_formula_field = v01;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv11 } in
     NLC_Exists (w0, resv0))
  | NL_And (v0,
    v1) ->
    (let resv0 =
       { nlrepr_fo_formula_field = v0;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     let resv1 =
       { nlrepr_fo_formula_field = v1;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     NLC_And (resv0, resv1))
  | NL_Or (v0,
    v1) ->
    (let resv0 =
       { nlrepr_fo_formula_field = v0;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     let resv1 =
       { nlrepr_fo_formula_field = v1;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     NLC_Or (resv0, resv1))
  | NL_Not v0 ->
    (let resv0 =
       { nlrepr_fo_formula_field = v0;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     NLC_Not resv0)
  | NL_FTrue -> NLC_FTrue
  | NL_FFalse -> NLC_FFalse
  | NL_PApp (v0,
    v1) ->
    (let resv0 =
       { nlrepr_symbol_field = v0;
         nlfree_var_symbol_set_abstraction_symbol_field = fv0 } in
     let resv1 =
       { nlrepr_fo_term_list_field = v1;
         nlfree_var_symbol_set_abstraction_fo_term_list_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_term_list_field = fv1 } in
     NLC_PApp (resv0, resv1))

let destruct_fo_term (t: nlimpl_fo_term) : cons_fo_term =
  let fv0 = t.nlfree_var_symbol_set_abstraction_fo_term_field in
  let fv3 = t.nlfree_var_fo_term_set_abstraction_fo_term_field in
  match t.nlrepr_fo_term_field with
  | NLFVar_fo_term v0 -> NLCVar_fo_term v0
  | NLBruijn_fo_term v0 -> assert false (* absurd *)
  | NL_App (v0,
    v1) ->
    (let resv0 =
       { nlrepr_symbol_field = v0;
         nlfree_var_symbol_set_abstraction_symbol_field = fv0 } in
     let resv1 =
       { nlrepr_fo_term_list_field = v1;
         nlfree_var_symbol_set_abstraction_fo_term_list_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_term_list_field = fv3 } in
     NLC_App (resv0, resv1))

type fvr = (Z.t) list

let destruct_fo_term_list (t: nlimpl_fo_term_list) : cons_fo_term_list =
  let fv0 = t.nlfree_var_symbol_set_abstraction_fo_term_list_field in
  let fv3 = t.nlfree_var_fo_term_set_abstraction_fo_term_list_field in
  match t.nlrepr_fo_term_list_field with
  | NL_FONil -> NLC_FONil
  | NL_FOCons (v0,
    v1) ->
    (let resv0 =
       { nlrepr_fo_term_field = v0;
         nlfree_var_symbol_set_abstraction_fo_term_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_term_field = fv3 } in
     let resv1 =
       { nlrepr_fo_term_list_field = v1;
         nlfree_var_symbol_set_abstraction_fo_term_list_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_term_list_field = fv3 } in
     NLC_FOCons (resv0, resv1))

let rec merge (l1: (Z.t) list) (l2: (Z.t) list) : (Z.t) list =
  match l1 with
  | [] -> l2
  | x :: q1 ->
    begin match l2 with
    | [] -> l1
    | y :: q2 ->
      if Z.lt x y
      then x :: merge q1 l2
      else begin if Z.gt x y then y :: merge l1 q2 else x :: merge q1 q2 end
    end

let rec term_free_vars_noghost (t: nlimpl_fo_term) : fvr =
  match destruct_fo_term t with
  | NLCVar_fo_term x -> x :: [] 
  | NLC_App (_, l) -> term_list_free_vars_noghost l
and term_list_free_vars_noghost (l: nlimpl_fo_term_list) : fvr =
  match destruct_fo_term_list l with
  | NLC_FONil -> [] 
  | NLC_FOCons (t,
    q) ->
    (let r1 = term_free_vars_noghost t in
     let r2 = term_list_free_vars_noghost q in merge r1 r2)

let rec remove (x: Z.t) (l: (Z.t) list) : (Z.t) list =
  match l with
  | [] -> [] 
  | y :: q -> if Z.equal y x then remove x q else y :: remove x q

let rec collect_free_var_formula (phi: nlimpl_fo_formula) : fvr =
  match destruct_fo_formula phi with
  | NLC_PApp (p, l) -> term_list_free_vars_noghost l
  | NLC_Not phi0 -> collect_free_var_formula phi0
  | NLC_And (phi1,
    phi2) ->
    (let r1 = collect_free_var_formula phi1 in
     let r2 = collect_free_var_formula phi2 in merge r1 r2)
  | NLC_Or (phi1,
    phi2) ->
    (let r1 = collect_free_var_formula phi1 in
     let r2 = collect_free_var_formula phi2 in merge r1 r2)
  | NLC_FTrue -> [] 
  | NLC_FFalse -> [] 
  | NLC_Forall (x,
    phi0) ->
    (let r = collect_free_var_formula phi0 in remove x r)
  | NLC_Exists (x,
    phi0) ->
    (let r = collect_free_var_formula phi0 in remove x r)

let rec collect_free_var_formula_list (phil: nlimpl_fo_formula_list) : fvr =
  match destruct_fo_formula_list phil with
  | NLC_FOFNil -> [] 
  | NLC_FOFCons (phi0,
    q) ->
    (let fvr1 = collect_free_var_formula phi0 in
     let fvr2 = collect_free_var_formula_list q in merge fvr1 fvr2)

let smart_and (phi1: nlimpl_fo_formula) (phi2: nlimpl_fo_formula) :
  nlimpl_fo_formula =
  match destruct_fo_formula phi1 with
  | NLC_FFalse -> phi1
  | NLC_FTrue -> phi2
  | _ ->
    begin match destruct_fo_formula phi2 with
    | NLC_FFalse -> phi2
    | NLC_FTrue -> phi1
    | _ -> construct_fo_formula (NLC_And (phi1, phi2))
    end

let smart_or (phi1: nlimpl_fo_formula) (phi2: nlimpl_fo_formula) :
  nlimpl_fo_formula =
  match destruct_fo_formula phi1 with
  | NLC_FTrue -> phi1
  | NLC_FFalse -> phi2
  | _ ->
    begin match destruct_fo_formula phi2 with
    | NLC_FTrue -> phi2
    | NLC_FFalse -> phi1
    | _ -> construct_fo_formula (NLC_Or (phi1, phi2))
    end

let smart_forall (x: Z.t) (phi: nlimpl_fo_formula) : nlimpl_fo_formula =
  match destruct_fo_formula phi with
  | NLC_FFalse -> phi
  | NLC_FTrue -> phi
  | _ -> construct_fo_formula (NLC_Forall (x, phi))

let smart_exists (x: Z.t) (phi: nlimpl_fo_formula) : nlimpl_fo_formula =
  match destruct_fo_formula phi with
  | NLC_FFalse -> phi
  | NLC_FTrue -> phi
  | _ -> construct_fo_formula (NLC_Exists (x, phi))

let rec nnf_simpl (phi: nlimpl_fo_formula) : nlimpl_fo_formula =
  match destruct_fo_formula phi with
  | NLC_PApp (p, l) -> phi
  | NLC_Not phi' -> nnf_neg_simpl phi'
  | NLC_And (phi1,
    phi2) ->
    (let phi'1 = nnf_simpl phi1 in let phi'2 = nnf_simpl phi2 in
     smart_and phi'1 phi'2)
  | NLC_Or (phi1,
    phi2) ->
    (let phi'1 = nnf_simpl phi1 in let phi'2 = nnf_simpl phi2 in
     smart_or phi'1 phi'2)
  | NLC_FTrue -> phi
  | NLC_FFalse -> phi
  | NLC_Forall (x,
    phi0) ->
    (let phi' = nnf_simpl phi0 in smart_forall x phi')
  | NLC_Exists (x,
    phi0) ->
    (let phi' = nnf_simpl phi0 in smart_exists x phi')
and nnf_neg_simpl (phi: nlimpl_fo_formula) : nlimpl_fo_formula =
  match destruct_fo_formula phi with
  | NLC_PApp (p, l) -> construct_fo_formula (NLC_Not phi)
  | NLC_Not phi' -> nnf_simpl phi'
  | NLC_And (phi1,
    phi2) ->
    (let phi'1 = nnf_neg_simpl phi1 in let phi'2 = nnf_neg_simpl phi2 in
     smart_or phi'1 phi'2)
  | NLC_Or (phi1,
    phi2) ->
    (let phi'1 = nnf_neg_simpl phi1 in let phi'2 = nnf_neg_simpl phi2 in
     smart_and phi'1 phi'2)
  | NLC_FTrue -> construct_fo_formula NLC_FFalse
  | NLC_FFalse -> construct_fo_formula NLC_FTrue
  | NLC_Forall (x,
    phi0) ->
    (let phi' = nnf_neg_simpl phi0 in smart_exists x phi')
  | NLC_Exists (x,
    phi0) ->
    (let phi' = nnf_neg_simpl phi0 in smart_forall x phi')

exception Unsat

let rec nnf_simpl_list (phis: nlimpl_fo_formula_list) (gnum: Z.t) :
  nlimpl_fo_formula_list * (Z.t) =
  match destruct_fo_formula_list phis with
  | NLC_FOFNil -> (phis, gnum)
  | NLC_FOFCons (phi,
    q) ->
    (let (q', gnum') = nnf_simpl_list q (Z.sub gnum Z.one) in
     let phi' = nnf_simpl phi in
     match destruct_fo_formula phi' with
     | NLC_FTrue ->
       (q', (if Z.gt gnum Z.zero then gnum' else Z.add gnum' Z.one))
     | NLC_FFalse -> raise Unsat
     | _ ->
       (let res = construct_fo_formula_list (NLC_FOFCons (phi', q')) in
        (res, Z.add gnum' Z.one)))

exception Sat

type comb_ret = {
  form: nlimpl_fo_formula;
  llen: Z.t;
  }

let rec combine_with (l: nlimpl_fo_formula_list) (phi0: nlimpl_fo_formula) :
  comb_ret =
  match destruct_fo_formula_list l with
  | NLC_FOFNil -> { form = phi0; llen = Z.one }
  | NLC_FOFCons (x,
    q) ->
    (let cr = combine_with q x in let phi' = cr.form in
     let phir = construct_fo_formula (NLC_And (phi0, phi')) in
     { form = phir; llen = Z.add cr.llen Z.one })

let rec exists_quantify (l: (Z.t) list) (phi: nlimpl_fo_formula) :
  nlimpl_fo_formula =
  match l with
  | [] -> phi
  | x :: q ->
    (let phi' = construct_fo_formula (NLC_Exists (x, phi)) in
     exists_quantify q phi')

let rec term_free_vars (t: nlimpl_fo_term) : (Z.t) list =
  match destruct_fo_term t with
  | NLCVar_fo_term x -> x :: [] 
  | NLC_App (_, l) -> term_list_free_vars l
and term_list_free_vars (l: nlimpl_fo_term_list) : (Z.t) list =
  match destruct_fo_term_list l with
  | NLC_FONil -> [] 
  | NLC_FOCons (t, q) -> merge (term_free_vars t) (term_list_free_vars q)

type 'st skolemization_return = {
  skolemized: nlimpl_fo_formula;
  skolem_bound: Z.t;
  free_var_list: (Z.t) list;
  }

type 'st skolemization_env_return = nlimpl_fo_term_list

let rec skolem_parameters :
  type st. ((Z.t) list) -> (st skolemization_env_return) -> 
           (st skolemization_env_return) =
  fun l acc -> match l with
    | [] -> acc
    | x :: q ->
      (let accl = acc in let varx = construct_fo_term (NLCVar_fo_term x) in
       let accl' = construct_fo_term_list (NLC_FOCons (varx, accl)) in
       let acc' = accl' in skolem_parameters q acc')

let rec subst_base_symbol_in_symbol (t: (Z.t) nl_symbol) (x: Z.t)
                                    (u: (Z.t) nl_symbol) : (Z.t) nl_symbol =
  match t with
  | NLFVar_symbol v0 -> if Z.equal v0 x then u else NLFVar_symbol v0
  | NLBruijn_symbol v0 -> NLBruijn_symbol v0

let rec subst_base_symbol_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list)
                                          (x: Z.t) (u: (Z.t) nl_symbol) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (subst_base_symbol_in_fo_term v0 x u,
    subst_base_symbol_in_fo_term_list v1 x u)
and subst_base_fo_term_in_fo_term_list (t: (Z.t, Z.t) nl_fo_term_list)
                                       (x: Z.t) (u: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_term_list =
  match t with
  | NL_FONil -> NL_FONil
  | NL_FOCons (v0,
    v1) ->
    NL_FOCons (subst_base_fo_term_in_fo_term v0 x u,
    subst_base_fo_term_in_fo_term_list v1 x u)
and subst_base_symbol_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (x: Z.t)
                                 (u: (Z.t) nl_symbol) : (Z.t, Z.t) nl_fo_term
  =
  match t with
  | NLFVar_fo_term v0 -> NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> NLBruijn_fo_term v0
  | NL_App (v0,
    v1) ->
    NL_App (subst_base_symbol_in_symbol v0 x u,
    subst_base_symbol_in_fo_term_list v1 x u)
and subst_base_fo_term_in_fo_term (t: (Z.t, Z.t) nl_fo_term) (x: Z.t)
                                  (u: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_term =
  match t with
  | NLFVar_fo_term v0 -> if Z.equal v0 x then u else NLFVar_fo_term v0
  | NLBruijn_fo_term v0 -> NLBruijn_fo_term v0
  | NL_App (v0, v1) -> NL_App (v0, subst_base_fo_term_in_fo_term_list v1 x u)

let rec subst_base_symbol_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula)
                                        (x: Z.t) (u: (Z.t) nl_symbol) :
  (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 -> NL_Forall (subst_base_symbol_in_fo_formula v0 x u)
  | NL_Exists v0 -> NL_Exists (subst_base_symbol_in_fo_formula v0 x u)
  | NL_And (v0,
    v1) ->
    NL_And (subst_base_symbol_in_fo_formula v0 x u,
    subst_base_symbol_in_fo_formula v1 x u)
  | NL_Or (v0,
    v1) ->
    NL_Or (subst_base_symbol_in_fo_formula v0 x u,
    subst_base_symbol_in_fo_formula v1 x u)
  | NL_Not v0 -> NL_Not (subst_base_symbol_in_fo_formula v0 x u)
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (subst_base_symbol_in_symbol v0 x u,
    subst_base_symbol_in_fo_term_list v1 x u)
and subst_base_fo_term_in_fo_formula (t: (Z.t, Z.t) nl_fo_formula) (x: Z.t)
                                     (u: (Z.t, Z.t) nl_fo_term) :
  (Z.t, Z.t) nl_fo_formula =
  match t with
  | NL_Forall v0 -> NL_Forall (subst_base_fo_term_in_fo_formula v0 x u)
  | NL_Exists v0 -> NL_Exists (subst_base_fo_term_in_fo_formula v0 x u)
  | NL_And (v0,
    v1) ->
    NL_And (subst_base_fo_term_in_fo_formula v0 x u,
    subst_base_fo_term_in_fo_formula v1 x u)
  | NL_Or (v0,
    v1) ->
    NL_Or (subst_base_fo_term_in_fo_formula v0 x u,
    subst_base_fo_term_in_fo_formula v1 x u)
  | NL_Not v0 -> NL_Not (subst_base_fo_term_in_fo_formula v0 x u)
  | NL_FTrue -> NL_FTrue
  | NL_FFalse -> NL_FFalse
  | NL_PApp (v0,
    v1) ->
    NL_PApp (v0, subst_base_fo_term_in_fo_term_list v1 x u)

let nlsubst_fo_term_in_fo_formula (t: nlimpl_fo_formula) (x: Z.t)
                                  (u: nlimpl_fo_term) : nlimpl_fo_formula =
  { nlrepr_fo_formula_field =
    subst_base_fo_term_in_fo_formula t.nlrepr_fo_formula_field
    x
    u.nlrepr_fo_term_field;
    nlfree_var_symbol_set_abstraction_fo_formula_field =
    (let aux19 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
     aux19 t.nlfree_var_symbol_set_abstraction_fo_formula_field
     u.nlfree_var_symbol_set_abstraction_fo_term_field);
    nlfree_var_fo_term_set_abstraction_fo_formula_field =
    (let aux20 (a: Z.t) (b: Z.t) : Z.t = if Z.lt a b then b else a in
     aux20 t.nlfree_var_fo_term_set_abstraction_fo_formula_field
     u.nlfree_var_fo_term_set_abstraction_fo_term_field) }

let rec skolemize :
  type st. nlimpl_fo_formula -> (Z.t) -> (bool) ->  (st skolemization_return) =
  fun phi skb b -> match destruct_fo_formula phi with
    | NLC_PApp (_,
      l) ->
      { skolemized = phi; skolem_bound = skb; free_var_list =
        if b then term_list_free_vars l else []  }
    | NLC_Not phi' ->
      { skolemized = phi; skolem_bound = skb; free_var_list =
        if b
        then
          match destruct_fo_formula phi' with
          | NLC_PApp (_, l) -> term_list_free_vars l
          | _ -> assert false (* absurd *)
        else []  }
    | NLC_And (phi1,
      phi2) ->
      (let res1 = skolemize phi1 skb b in
       let res2 = skolemize phi2 res1.skolem_bound b in
       let skr =
         construct_fo_formula (NLC_And (res1.skolemized, res2.skolemized)) in
       let fvlist = merge res1.free_var_list res2.free_var_list in
       { skolemized = skr; skolem_bound = res2.skolem_bound; free_var_list =
         fvlist })
    | NLC_Or (phi1,
      phi2) ->
      (let res1 = skolemize phi1 skb b in
       let res2 = skolemize phi2 res1.skolem_bound b in
       let skr =
         construct_fo_formula (NLC_Or (res1.skolemized, res2.skolemized)) in
       let fvlist = merge res1.free_var_list res2.free_var_list in
       { skolemized = skr; skolem_bound = res2.skolem_bound; free_var_list =
         fvlist })
    | NLC_FTrue -> assert false (* absurd *)
    | NLC_FFalse -> assert false (* absurd *)
    | NLC_Forall (x,
      phi0) ->
      (let res = skolemize phi0 skb b in
       let skr = construct_fo_formula (NLC_Forall (x, res.skolemized)) in
       let fvl = remove x res.free_var_list in
       { skolemized = skr; skolem_bound = res.skolem_bound; free_var_list =
         fvl })
    | NLC_Exists (x,
      phi0) ->
      (let res = skolemize phi0 skb true in let fvl = res.free_var_list in
       let fvl1 = remove x fvl in let skb' = res.skolem_bound in
       let fonil = construct_fo_term_list NLC_FONil in
       let skenv = skolem_parameters fvl1 fonil in let skparams = skenv in
       let symb = construct_symbol skb' in
       let skolemf = construct_fo_term (NLC_App (symb, skparams)) in
       let phir = nlsubst_fo_term_in_fo_formula res.skolemized x skolemf in
       { skolemized = phir; skolem_bound = Z.add skb' Z.one; free_var_list =
         fvl1 })

type split_ret = {
  forms: nlimpl_fo_formula_list;
  total_goals: Z.t;
  }

let rec split (phi: nlimpl_fo_formula) (l: nlimpl_fo_formula_list)
              (lnum: Z.t) (gnum: Z.t) : split_ret =
  match destruct_fo_formula phi with
  | NLC_And (phi1,
    phi2) ->
    (let gnumcall =
       if Z.equal lnum Z.one
       then
         if not (Z.equal gnum Z.zero)
         then Z.of_string "-1"
         else Z.sub gnum Z.one
       else Z.sub gnum Z.one in
     let r0 = split phi2 l (Z.sub lnum Z.one) gnumcall in
     let l0 = r0.forms in let r1 = split phi1 l0 Z.zero (Z.of_string "-1") in
     let l1 = r1.forms in
     { forms = l1; total_goals =
       if not (Z.equal gnum Z.zero)
       then Z.add r0.total_goals r1.total_goals
       else Z.zero })
  | _ ->
    (let lr = construct_fo_formula_list (NLC_FOFCons (phi, l)) in
     { forms = lr; total_goals =
       if not (Z.equal gnum Z.zero) then Z.one else Z.zero })

let preprocessing :
  type st. nlimpl_fo_formula_list -> (Z.t) ->  (st preprocessing_return) =
  fun phil gnum -> let s = collect_free_var_formula_list phil in
                   let (phisimpl,
                   gnum1) =
                   nnf_simpl_list phil gnum in
                   match destruct_fo_formula_list phisimpl with
                   | NLC_FOFNil -> raise Sat
                   | NLC_FOFCons (phi0,
                     q) ->
                     (let cb = combine_with q phi0 in let len = cb.llen in
                      let phicb = cb.form in
                      let phiex = exists_quantify s phicb in
                      let skr =
                        skolemize phiex
                        phiex.nlfree_var_symbol_set_abstraction_fo_formula_field
                        false in
                      let phisk = skr.skolemized in
                      let fonil = construct_fo_formula_list NLC_FOFNil in
                      let spl = split phisk fonil len gnum1 in
                      { preprocessed = spl.forms; final_goals_number =
                        spl.total_goals })

type 'a t = {
  mutable history: (Z.t) list;
  mutable current_time: Z.t;
  mutable buffer: ('a list) array;
  }

let zero : Z.t = Z.zero

let one : Z.t = Z.one

let create : type a. unit ->  (a t) =
  fun _ -> { history = [] ; current_time = zero; buffer =
             Array.make (Z.to_int one) ([] ) }

type sdata =
  | PConflict of nlimpl_fo_term_list * nlimpl_fo_term_list
  | Assign of nlimpl_fo_term

type 'a timestamp = {
  time: Z.t;
  size: Z.t;
  }

let stamp : type a. (a t) ->  (a timestamp) =
  fun tb -> { time = tb.current_time; size =
              Z.of_int (Array.length tb.buffer) }

exception Failure

let mone : Z.t = Z.of_string "-1"

let backtrack : type a. (a timestamp) -> (a t) ->  unit =
  fun t1 tb -> let final_size = t1.size in
               let rec unroll (delta: Z.t) : unit =
                 if not (Z.equal delta zero)
                 then begin match tb.history with
                 | [] -> assert false (* absurd *)
                 | x :: q ->
                   tb.history <- q;
                   if Z.equal x mone
                   then unroll (Z.sub delta one)
                   else
                     begin
                       if Z.lt x final_size
                       then
                         let h = (tb.buffer).(Z.to_int x) in
                         match h with
                         | [] -> assert false (* absurd *)
                         | _ :: q1 ->
                           tb.buffer.(Z.to_int x) <- q1;
                           unroll (Z.sub delta one)
                       else unroll (Z.sub delta one) end
                 end in
               if Z.lt final_size (Z.of_int (Array.length tb.buffer))
               then begin
                 let buf2 = Array.make (Z.to_int final_size) ([] ) in
                 let buf1 = tb.buffer in
                 Array.blit buf1 (Z.to_int zero) buf2 (Z.to_int zero) (Z.to_int final_size);
                 tb.buffer <- buf2 end;
               let tm0 = tb.current_time in
               tb.current_time <- t1.time; unroll (Z.sub tm0 t1.time)

type prover_return = unit

let destruct_tableau (t1: nlimpl_tableau) : cons_tableau =
  let fv0 = t1.nlfree_var_symbol_set_abstraction_tableau_field in
  let fv1 = t1.nlfree_var_fo_term_set_abstraction_tableau_field in
  match t1.nlrepr_tableau_field with
  | NL_Root -> NLC_Root
  | NL_Node (v0,
    v1,
    v2) ->
    (let resv0 =
       { nlrepr_tableau_field = v0;
         nlfree_var_symbol_set_abstraction_tableau_field = fv0;
         nlfree_var_fo_term_set_abstraction_tableau_field = fv1 } in
     let resv1 =
       { nlrepr_fo_formula_field = v1;
         nlfree_var_symbol_set_abstraction_fo_formula_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_field = fv1 } in
     let resv2 =
       { nlrepr_fo_formula_list_field = v2;
         nlfree_var_symbol_set_abstraction_fo_formula_list_field = fv0;
         nlfree_var_fo_term_set_abstraction_fo_formula_list_field = fv1 } in
     NLC_Node (resv0, resv1, resv2))

let destruct_symbol (t1: nlimpl_symbol) : cons_symbol =
  match t1.nlrepr_symbol_field with
  | NLFVar_symbol v0 -> v0
  | NLBruijn_symbol v0 -> assert false (* absurd *)

type unification_return = unit

let get : type a. (a t) -> (Z.t) ->  (a list) =
  fun tb x -> if Z.geq x (Z.of_int (Array.length tb.buffer))
              then [] 
              else (tb.buffer).(Z.to_int x)

exception UnificationFailure

let rec check_unified_free_var (x: Z.t) (t1: nlimpl_fo_term) (rhob: sdata t) :
  unit =
  match destruct_fo_term t1 with
  | NLCVar_fo_term y ->
    (let by' = get rhob y in
     match by' with
     | [] -> if Z.equal x y then raise UnificationFailure
     | PConflict (_, _) :: _ -> if Z.equal x y then raise UnificationFailure
     | Assign t2 :: _ -> check_unified_free_var x t2 rhob)
  | NLC_App (f, l) -> check_unified_free_var_list x l rhob
and check_unified_free_var_list (x: Z.t) (t1: nlimpl_fo_term_list)
                                (rhob: sdata t) : unit =
  match destruct_fo_term_list t1 with
  | NLC_FONil -> ()
  | NLC_FOCons (u,
    q) ->
    check_unified_free_var x u rhob; check_unified_free_var_list x q rhob

let add_event : type a. (Z.t) -> (a t) ->  unit =
  fun x tb -> tb.history <- x :: tb.history;
              tb.current_time <- Z.add tb.current_time one

let two : Z.t = Z.of_string "2"

let resize_for : type a. (Z.t) -> (a t) ->  unit =
  fun x tb -> let rec aux21 (size1: Z.t) : Z.t =
                add_event mone tb;
                let size2 = Z.mul two size1 in
                if Z.gt size2 x then size2 else aux21 size2 in
              let len = Z.of_int (Array.length tb.buffer) in
              let size1 = aux21 len in
              let buf2 = Array.make (Z.to_int size1) ([] ) in
              let buf1 = tb.buffer in
              Array.blit buf1 (Z.to_int zero) buf2 (Z.to_int zero) (Z.to_int len);
              tb.buffer <- buf2

let iadd : type a. (Z.t) -> a -> (a t) ->  unit =
  fun x b tb -> let buf = tb.buffer in
                buf.(Z.to_int x) <- b :: buf.(Z.to_int x); add_event x tb

let add : type a. (Z.t) -> a -> (a t) ->  unit =
  fun x b tb -> if Z.geq x (Z.of_int (Array.length tb.buffer))
                then resize_for x tb;
                iadd x b tb

let assign (z: Z.t) (t1: nlimpl_fo_term) (lv: ((Z.t) list) ref)
           (rhob: sdata t) : unification_return =
  check_unified_free_var z t1 rhob;
  add z (Assign t1) rhob;
  lv := z :: !lv;
  let rhou = () in ()

let rec unification_term (t1: nlimpl_fo_term) (t2: nlimpl_fo_term)
                         (lv: ((Z.t) list) ref) (rhob: sdata t) :
  unification_return =
  match (destruct_fo_term t1, destruct_fo_term t2) with
  | (NLCVar_fo_term x,
    NLCVar_fo_term y) ->
    if Z.equal x y
    then ()
    else
      begin
        let bx = get rhob x in
        match bx with
        | Assign bx1 :: _ -> unification_term bx1 t2 lv rhob
        | _ ->
          (let by' = get rhob y in
           match by' with
           | Assign by'1 :: _ -> unification_term t1 by'1 lv rhob
           | _ ->
             if Z.lt x y then assign x t2 lv rhob else assign y t1 lv rhob) end
  | (NLC_App (f1,
    l1),
    NLC_App (f2,
    l2)) ->
    (let (f11, f21) = (destruct_symbol f1, destruct_symbol f2) in
     if Z.equal f11 f21
     then unification_term_list l1 l2 lv rhob
     else raise UnificationFailure)
  | (NLCVar_fo_term x,
    NLC_App (f,
    l)) ->
    (let bx = get rhob x in
     match bx with
     | Assign bx1 :: _ -> unification_term bx1 t2 lv rhob
     | _ -> assign x t2 lv rhob)
  | (NLC_App (f,
    l),
    NLCVar_fo_term x) ->
    (let bx = get rhob x in
     match bx with
     | Assign bx1 :: _ -> unification_term t1 bx1 lv rhob
     | _ -> assign x t1 lv rhob)
and unification_term_list (t1: nlimpl_fo_term_list) (t2: nlimpl_fo_term_list)
                          (lv: ((Z.t) list) ref) (rhob: sdata t) :
  unification_return =
  match (destruct_fo_term_list t1, destruct_fo_term_list t2) with
  | (NLC_FONil, NLC_FONil) -> ()
  | (NLC_FOCons (u1,
    q1),
    NLC_FOCons (u2,
    q2)) ->
    (let rho2 = unification_term_list q1 q2 lv rhob in
     let rho3 = unification_term u1 u2 lv rhob in ())
  | (NLC_FONil, NLC_FOCons (u, q)) -> raise UnificationFailure
  | (NLC_FOCons (u, q), NLC_FONil) -> raise UnificationFailure

let conflict (t1: nlimpl_fo_term_list) (t2: nlimpl_fo_term_list)
             (rhob: sdata t) : unit =
  let l = ref ([] ) in
  let t3 = stamp rhob in
  let u =
    try let o = unification_term_list t1 t2 l rhob in Some o with
    | UnificationFailure -> None  in
  match u with
  | Some _ ->
    begin match !l with
    | [] -> raise UnificationFailure
    | v :: _ -> backtrack t3 rhob; add v (PConflict (t1, t2)) rhob
    end
  | None -> backtrack t3 rhob

let rec conflicts (lv: sdata list) (rhob: sdata t) : unit =
  match lv with
  | [] -> ()
  | Assign _ :: q -> conflicts q rhob
  | PConflict (t1, t2) :: q -> conflict t1 t2 rhob; conflicts q rhob

let rec unif_conflicts (lv: (Z.t) list) (rhob: sdata t) : unit =
  match lv with
  | [] -> ()
  | v0 :: q -> conflicts (get rhob v0) rhob; unif_conflicts q rhob

let unify_term_list (t1: nlimpl_fo_term_list) (t2: nlimpl_fo_term_list)
                    (watch: ((Z.t) list) ref) (rhob: sdata t) :
  unification_return =
  let u = unification_term_list t1 t2 watch rhob in
  unif_conflicts !watch rhob; u

let rec merge1 (phi1: nlimpl_fo_formula_list) (phi2: nlimpl_fo_formula_list) :
  nlimpl_fo_formula_list =
  match destruct_fo_formula_list phi1 with
  | NLC_FOFNil -> phi2
  | NLC_FOFCons (phi0,
    q) ->
    (let phi3 = construct_fo_formula_list (NLC_FOFCons (phi0, phi2)) in
     merge1 q phi3)

let rec branch_conflict_atom (p1: Z.t) (t1: nlimpl_fo_term_list)
                             (tab: nlimpl_tableau) (rhob: sdata t) : unit =
  match destruct_tableau tab with
  | NLC_Root -> ()
  | NLC_Node (tnext,
    phi1,
    phib) ->
    begin match destruct_fo_formula phi1 with
    | NLC_PApp (p2,
      t2) ->
      (let p3 = let p31 = destruct_symbol p2 in p31 in
       if Z.equal p1 p3
       then
         begin
           begin try conflict t1 t2 rhob with
           | UnificationFailure -> raise Failure
           end;
           branch_conflict_atom p1 t1 tnext rhob
         end
       else branch_conflict_atom p1 t1 tnext rhob)
    | NLC_Not _ -> branch_conflict_atom p1 t1 tnext rhob
    | _ -> assert false (* absurd *)
    end

let rec branch_conflict_neg_atom (p1: Z.t) (t1: nlimpl_fo_term_list)
                                 (tab: nlimpl_tableau) (rhob: sdata t) : unit
  =
  match destruct_tableau tab with
  | NLC_Root -> ()
  | NLC_Node (tnext,
    phi1,
    phib) ->
    begin match destruct_fo_formula phi1 with
    | NLC_Not phi2 ->
      begin match destruct_fo_formula phi2 with
      | NLC_PApp (p2,
        t2) ->
        (let p3 = let p31 = destruct_symbol p2 in p31 in
         if Z.equal p1 p3
         then
           begin
             begin try conflict t1 t2 rhob with
             | UnificationFailure -> raise Failure
             end;
             branch_conflict_atom p1 t1 tnext rhob
           end
         else branch_conflict_atom p1 t1 tnext rhob)
      | _ -> assert false (* absurd *)
      end
    | NLC_PApp (_, _) -> branch_conflict_atom p1 t1 tnext rhob
    | _ -> assert false (* absurd *)
    end

let rec clause_conflicts (phil: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                         (rhob: sdata t) : unit =
  match destruct_fo_formula_list phil with
  | NLC_FOFNil -> ()
  | NLC_FOFCons (phi0,
    phiq) ->
    begin match destruct_fo_formula phi0 with
    | NLC_PApp (p1,
      t1) ->
      (let p1' = let p1'1 = destruct_symbol p1 in p1'1 in
       branch_conflict_atom p1' t1 tab rhob; clause_conflicts phiq tab rhob)
    | NLC_Not phi1 ->
      begin match destruct_fo_formula phi1 with
      | NLC_PApp (p1,
        t1) ->
        (let p1' = let p1'1 = destruct_symbol p1 in p1'1 in
         branch_conflict_neg_atom p1' t1 tab rhob;
         clause_conflicts phiq tab rhob)
      | _ -> assert false (* absurd *)
      end
    | _ -> assert false (* absurd *)
    end

let rec contract_tableau (tab: nlimpl_tableau)
                         (branch: nlimpl_fo_formula_list) (ndepth: (Z.t) ref) :
  nlimpl_tableau option =
  match destruct_fo_formula_list branch with
  | NLC_FOFNil ->
    begin match destruct_tableau tab with
    | NLC_Root -> None 
    | NLC_Node (tnext,
      phi0,
      phib) ->
      ndepth := Z.add !ndepth Z.one; contract_tableau tnext phib ndepth
    end
  | NLC_FOFCons (phi0,
    qb) ->
    (let ftab = construct_tableau (NLC_Node (tab, phi0, qb)) in Some ftab)

let rec decompose (base: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                  (unifb: sdata t) (fresh: Z.t) (phi0: nlimpl_fo_formula)
                  (clause: nlimpl_fo_formula_list)
                  (remaining: nlimpl_fo_formula_list) (depth: Z.t)
                  (goalnum: Z.t) : prover_return =
  match destruct_fo_formula phi0 with
  | NLC_Or (a,
    b) ->
    (let rmg = construct_fo_formula_list (NLC_FOFCons (b, remaining)) in
     decompose base tab unifb fresh a clause rmg depth goalnum)
  | NLC_And (a,
    b) ->
    (let tp = stamp unifb in
     try decompose base tab unifb fresh a clause remaining depth goalnum with
     | Failure ->
         backtrack tp unifb;
         decompose base tab unifb fresh b clause remaining depth goalnum)
  | NLC_Exists (_, _) -> assert false (* absurd *)
  | NLC_FTrue -> assert false (* absurd *)
  | NLC_FFalse -> assert false (* absurd *)
  | NLC_Forall (x,
    phi1) ->
    (let vfresh = construct_fo_term (NLCVar_fo_term fresh) in
     let phi2 = nlsubst_fo_term_in_fo_formula phi1 x vfresh in
     decompose base
     tab
     unifb
     (Z.add fresh Z.one)
     phi2
     clause
     remaining
     depth
     goalnum)
  | NLC_PApp (p,
    l) ->
    decompose_literal base
    tab
    unifb
    fresh
    phi0
    clause
    remaining
    depth
    goalnum
  | NLC_Not phi1 ->
    decompose_literal base
    tab
    unifb
    fresh
    phi0
    clause
    remaining
    depth
    goalnum
and decompose_literal (base: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                      (unifb: sdata t) (fresh: Z.t) (phi0: nlimpl_fo_formula)
                      (clause: nlimpl_fo_formula_list)
                      (remaining: nlimpl_fo_formula_list) (depth: Z.t)
                      (goalnum: Z.t) : prover_return =
  match destruct_fo_formula_list remaining with
  | NLC_FOFNil ->
    begin match destruct_tableau tab with
    | NLC_Root ->
      (let tab' = construct_tableau (NLC_Node (tab, phi0, clause)) in
       if Z.equal depth Z.zero
       then raise Failure
       else
         select_lemma base
         base
         tab'
         unifb
         fresh
         (Z.sub depth Z.one)
         goalnum
         (Z.of_string "-1"))
    | NLC_Node (tnext,
      phi1,
      phib) ->
      (let clse = construct_fo_formula_list (NLC_FOFCons (phi0, clause)) in
       let fonil = construct_fo_formula_list NLC_FOFNil in
       match destruct_fo_formula phi1 with
       | NLC_PApp (ptab,
         ttab) ->
         (let ptab2 = let ptab21 = destruct_symbol ptab in ptab21 in
          contradiction_atom base
          tab
          unifb
          fresh
          ptab2
          ttab
          clse
          fonil
          depth
          goalnum)
       | NLC_Not phi2 ->
         begin match destruct_fo_formula phi2 with
         | NLC_PApp (ptab,
           ttab) ->
           (let ptab2 = let ptab21 = destruct_symbol ptab in ptab21 in
            contradiction_neg_atom base
            tab
            unifb
            fresh
            ptab2
            ttab
            clse
            fonil
            depth
            goalnum)
         | _ -> assert false (* absurd *)
         end
       | _ -> assert false (* absurd *))
    end
  | NLC_FOFCons (phi1,
    qr) ->
    (let clse = construct_fo_formula_list (NLC_FOFCons (phi0, clause)) in
     decompose base tab unifb fresh phi1 clse qr depth goalnum)
and contradiction_atom (base: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                       (unifb: sdata t) (fresh: Z.t) (p: Z.t)
                       (t1: nlimpl_fo_term_list)
                       (phil: nlimpl_fo_formula_list)
                       (phiacc: nlimpl_fo_formula_list) (depth: Z.t)
                       (goalnum: Z.t) : prover_return =
  match destruct_fo_formula_list phil with
  | NLC_FOFNil -> raise Failure
  | NLC_FOFCons (phi0,
    q) ->
    (let phiacc2 = construct_fo_formula_list (NLC_FOFCons (phi0, phiacc)) in
     match destruct_fo_formula phi0 with
     | NLC_Not phi1 ->
       begin match destruct_fo_formula phi1 with
       | NLC_PApp (p2,
         t2) ->
         (let p3 = destruct_symbol p2 in
          if Z.equal p p3
          then
            let tp = stamp unifb in
            let l0 = ref ([] ) in
            match
              try let u = unify_term_list t1 t2 l0 unifb in Some u with
              | UnificationFailure -> None 
            with
            | Some u ->
              (let phifinal = merge1 phiacc q in
               let b =
                 try clause_conflicts phifinal tab unifb; false with
                 | Failure -> true in
               match b with
               | true ->
                 backtrack tp unifb;
                 contradiction_atom base
                 tab
                 unifb
                 fresh
                 p
                 t1
                 q
                 phiacc2
                 depth
                 goalnum
               | false ->
                 (let nd = ref depth in
                  let ct = contract_tableau tab phifinal nd in
                  let depth1 = !nd in
                  match ct with
                  | None -> ()
                  | Some tab2 ->
                    begin match !l0 with
                    | [] ->
                      extend_branch base tab2 unifb fresh depth1 goalnum
                    | _ ->
                      begin
                        try
                        extend_branch base tab2 unifb fresh depth1 goalnum
                      with
                      | Failure ->
                          backtrack tp unifb;
                          begin try conflict t1 t2 unifb with
                          | UnificationFailure -> raise Failure
                          end;
                          contradiction_atom base
                          tab
                          unifb
                          fresh
                          p
                          t1
                          q
                          phiacc2
                          depth1
                          goalnum
                      end
                    end))
            | None ->
              backtrack tp unifb;
              contradiction_atom base
              tab
              unifb
              fresh
              p
              t1
              q
              phiacc2
              depth
              goalnum
          else
            contradiction_atom base
            tab
            unifb
            fresh
            p
            t1
            q
            phiacc2
            depth
            goalnum)
       | _ -> assert false (* absurd *)
       end
     | NLC_PApp (_,
       _) ->
       contradiction_atom base tab unifb fresh p t1 q phiacc2 depth goalnum
     | _ -> assert false (* absurd *))
and contradiction_neg_atom (base: nlimpl_fo_formula_list)
                           (tab: nlimpl_tableau) (unifb: sdata t)
                           (fresh: Z.t) (p: Z.t) (t1: nlimpl_fo_term_list)
                           (phil: nlimpl_fo_formula_list)
                           (phiacc: nlimpl_fo_formula_list) (depth: Z.t)
                           (goalnum: Z.t) : prover_return =
  match destruct_fo_formula_list phil with
  | NLC_FOFNil -> raise Failure
  | NLC_FOFCons (phi0,
    q) ->
    (let phiacc2 = construct_fo_formula_list (NLC_FOFCons (phi0, phiacc)) in
     match destruct_fo_formula phi0 with
     | NLC_PApp (p2,
       t2) ->
       (let p3 = destruct_symbol p2 in
        if Z.equal p p3
        then
          let tp = stamp unifb in
          let l0 = ref ([] ) in
          match
            try let u = unify_term_list t1 t2 l0 unifb in Some u with
            | UnificationFailure -> None 
          with
          | Some u ->
            (let phifinal = merge1 phiacc q in
             let b =
               try clause_conflicts phifinal tab unifb; false with
               | Failure -> true in
             match b with
             | true ->
               backtrack tp unifb;
               contradiction_neg_atom base
               tab
               unifb
               fresh
               p
               t1
               q
               phiacc2
               depth
               goalnum
             | false ->
               (let nd = ref depth in
                let ct = contract_tableau tab phifinal nd in
                let depth1 = !nd in
                match ct with
                | None -> ()
                | Some tab2 ->
                  begin match !l0 with
                  | [] -> extend_branch base tab2 unifb fresh depth1 goalnum
                  | _ ->
                    begin
                      try
                      extend_branch base tab2 unifb fresh depth1 goalnum
                    with
                    | Failure ->
                        backtrack tp unifb;
                        begin try conflict t1 t2 unifb with
                        | UnificationFailure -> raise Failure
                        end;
                        contradiction_neg_atom base
                        tab
                        unifb
                        fresh
                        p
                        t1
                        q
                        phiacc2
                        depth1
                        goalnum
                    end
                  end))
          | None ->
            backtrack tp unifb;
            contradiction_neg_atom base
            tab
            unifb
            fresh
            p
            t1
            q
            phiacc2
            depth
            goalnum
        else
          contradiction_neg_atom base
          tab
          unifb
          fresh
          p
          t1
          q
          phiacc2
          depth
          goalnum)
     | NLC_Not _ ->
       contradiction_neg_atom base
       tab
       unifb
       fresh
       p
       t1
       q
       phiacc2
       depth
       goalnum
     | _ -> assert false (* absurd *))
and extend_branch (base: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                  (unifb: sdata t) (fresh: Z.t) (depth: Z.t) (goalnum: Z.t) :
  prover_return =
  match destruct_tableau tab with
  | NLC_Root ->
    if Z.equal depth Z.zero
    then raise Failure
    else
      begin
        let depth1 = Z.sub depth Z.one in
        select_lemma base base tab unifb fresh depth1 goalnum goalnum end
  | NLC_Node (tnext,
    phi0,
    phib) ->
    begin match destruct_fo_formula phi0 with
    | NLC_PApp (ps,
      t1) ->
      (let p = let p1 = destruct_symbol ps in p1 in
       contradiction_find_atom base
       tab
       tnext
       tnext
       unifb
       fresh
       p
       t1
       phib
       depth
       goalnum)
    | NLC_Not phi1 ->
      begin match destruct_fo_formula phi1 with
      | NLC_PApp (ps,
        t1) ->
        (let p = let p1 = destruct_symbol ps in p1 in
         contradiction_find_neg_atom base
         tab
         tnext
         tnext
         unifb
         fresh
         p
         t1
         phib
         depth
         goalnum)
      | _ -> assert false (* absurd *)
      end
    | _ -> assert false (* absurd *)
    end
and contradiction_find_atom (base: nlimpl_fo_formula_list)
                            (tab0: nlimpl_tableau) (tab1: nlimpl_tableau)
                            (tab: nlimpl_tableau) (unifb: sdata t)
                            (fresh: Z.t) (p: Z.t) (t1: nlimpl_fo_term_list)
                            (philist: nlimpl_fo_formula_list) (depth: Z.t)
                            (goalnum: Z.t) : prover_return =
  match destruct_tableau tab with
  | NLC_Root ->
    if Z.equal depth Z.zero
    then raise Failure
    else
      select_lemma base
      base
      tab0
      unifb
      fresh
      (Z.sub depth Z.one)
      goalnum
      (Z.of_string "-1")
  | NLC_Node (tnext,
    phi0,
    phib) ->
    begin match destruct_fo_formula phi0 with
    | NLC_PApp (_,
      _) ->
      contradiction_find_atom base
      tab0
      tab1
      tnext
      unifb
      fresh
      p
      t1
      philist
      depth
      goalnum
    | NLC_Not phi1 ->
      begin match destruct_fo_formula phi1 with
      | NLC_PApp (p2,
        t2) ->
        (let p3 = let p31 = destruct_symbol p2 in p31 in
         if Z.equal p p3
         then
           let tp = stamp unifb in
           let l0 = ref ([] ) in
           match
             try let u = unify_term_list t1 t2 l0 unifb in Some u with
             | UnificationFailure -> None 
           with
           | Some u ->
             (let nd = ref depth in
              let ct = contract_tableau tab1 philist nd in
              let depth1 = !nd in
              match ct with
              | Some tab2 ->
                begin match !l0 with
                | [] -> extend_branch base tab2 unifb fresh depth1 goalnum
                | _ ->
                  begin
                    try
                    extend_branch base tab2 unifb fresh depth1 goalnum
                  with
                  | Failure ->
                      backtrack tp unifb;
                      begin try conflict t1 t2 unifb with
                      | UnificationFailure -> raise Failure
                      end;
                      contradiction_find_atom base
                      tab0
                      tab1
                      tnext
                      unifb
                      fresh
                      p
                      t1
                      philist
                      depth1
                      goalnum
                  end
                end
              | None -> ())
           | None ->
             backtrack tp unifb;
             contradiction_find_atom base
             tab0
             tab1
             tnext
             unifb
             fresh
             p
             t1
             philist
             depth
             goalnum
         else
           contradiction_find_atom base
           tab0
           tab1
           tnext
           unifb
           fresh
           p
           t1
           philist
           depth
           goalnum)
      | _ -> assert false (* absurd *)
      end
    | _ -> assert false (* absurd *)
    end
and contradiction_find_neg_atom (base: nlimpl_fo_formula_list)
                                (tab0: nlimpl_tableau) (tab1: nlimpl_tableau)
                                (tab: nlimpl_tableau) (unifb: sdata t)
                                (fresh: Z.t) (p: Z.t)
                                (t1: nlimpl_fo_term_list)
                                (philist: nlimpl_fo_formula_list)
                                (depth: Z.t) (goalnum: Z.t) : prover_return =
  match destruct_tableau tab with
  | NLC_Root ->
    if Z.equal depth Z.zero
    then raise Failure
    else
      select_lemma base
      base
      tab0
      unifb
      fresh
      (Z.sub depth Z.one)
      goalnum
      (Z.of_string "-1")
  | NLC_Node (tnext,
    phi0,
    phib) ->
    begin match destruct_fo_formula phi0 with
    | NLC_Not _ ->
      contradiction_find_neg_atom base
      tab0
      tab1
      tnext
      unifb
      fresh
      p
      t1
      philist
      depth
      goalnum
    | NLC_PApp (p2,
      t2) ->
      (let p3 = let p31 = destruct_symbol p2 in p31 in
       if Z.equal p p3
       then
         let tp = stamp unifb in
         let l0 = ref ([] ) in
         match
           try let u = unify_term_list t1 t2 l0 unifb in Some u with
           | UnificationFailure -> None 
         with
         | Some u ->
           (let nd = ref depth in
            let ct = contract_tableau tab1 philist nd in let depth1 = !nd in
            match ct with
            | Some tab2 ->
              begin match !l0 with
              | [] -> extend_branch base tab2 unifb fresh depth1 goalnum
              | _ ->
                begin try extend_branch base tab2 unifb fresh depth1 goalnum
                with
                | Failure ->
                    backtrack tp unifb;
                    begin try conflict t1 t2 unifb with
                    | UnificationFailure -> raise Failure
                    end;
                    contradiction_find_neg_atom base
                    tab0
                    tab1
                    tnext
                    unifb
                    fresh
                    p
                    t1
                    philist
                    depth1
                    goalnum
                end
              end
            | None -> ())
         | None ->
           backtrack tp unifb;
           contradiction_find_neg_atom base
           tab0
           tab1
           tnext
           unifb
           fresh
           p
           t1
           philist
           depth
           goalnum
       else
         contradiction_find_neg_atom base
         tab0
         tab1
         tnext
         unifb
         fresh
         p
         t1
         philist
         depth
         goalnum)
    | _ -> assert false (* absurd *)
    end
and select_lemma (base: nlimpl_fo_formula_list)
                 (basecursor: nlimpl_fo_formula_list) (tab: nlimpl_tableau)
                 (unifb: sdata t) (fresh: Z.t) (depth: Z.t) (goalnum: Z.t)
                 (number: Z.t) : prover_return =
  if Z.equal number Z.zero then raise Failure;
  match destruct_fo_formula_list basecursor with
  | NLC_FOFNil -> raise Failure
  | NLC_FOFCons (x,
    q) ->
    (let fonil = construct_fo_formula_list NLC_FOFNil in
     let tp = stamp unifb in
     try decompose base tab unifb fresh x fonil fonil depth goalnum with
     | Failure ->
         backtrack tp unifb;
         select_lemma base
         q
         tab
         unifb
         fresh
         depth
         goalnum
         (Z.sub number Z.one))

let main (base: nlimpl_fo_formula_list) (gnum: Z.t) : Z.t =
  let root = construct_tableau NLC_Root in
  try
    let phip = preprocessing base gnum in
    let phip0 = phip.preprocessed in
    let gnum2 = phip.final_goals_number in
    let gnum3 = if Z.leq gnum2 Z.zero then Z.of_string "-1" else gnum2 in
    let rec aux22 (n: Z.t) : (Z.t) * prover_return =
      let unifb = create () in
      let unif = () in
      try let o = extend_branch phip0 root unifb Z.zero n gnum3 in (n, o)
      with
      | Failure -> aux22 (Z.add n Z.one) in
    let (n, r) = aux22 Z.zero in n
  with
  | Unsat -> Z.zero

let test (_: unit) : unit = ignore (main (zenon10 (Z.of_string "2")) Z.one)

