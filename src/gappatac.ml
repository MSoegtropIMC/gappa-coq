(***************************************************)
(* Copyright 2008 Jean-Christophe Filliâtre        *)
(* Copyright 2008-2016 Guillaume Melquiond         *)
(*                                                 *)
(* This file is distributed under the terms of the *)
(* GNU Lesser General Public License Version 2.1   *)
(***************************************************)

open Format
open Util
open Pp
open Tacmach
open Names
open Coqlib
open Evarutil

let global_env = ref Environ.empty_env
let global_evd = ref Evd.empty

let existential_type evd ex = Evd.existential_type evd ex

open CErrors

let generalize a = Proofview.V82.of_tactic (Tactics.generalize a)

open Ltac_plugin
open EConstr

let is_global t1 t2 = is_global !global_evd t1 t2

let kind_of_term t = kind !global_evd t

let decompose_app t = decompose_app !global_evd t

let closed0 t = Vars.closed0 !global_evd t

let eq_constr t1 t2 = eq_constr !global_evd t1 t2

let pr_constr t =
  let sigma, env = Vernacstate.Proof_global.get_current_context () in
  Printer.pr_econstr_env env sigma t

let constr_of_global = UnivGen.constr_of_monomorphic_global

let binder_name = Context.binder_name

let refine_no_check t gl =
  Refiner.refiner ~check:false (EConstr.Unsafe.to_constr t) gl

let map_constr f t =
  EConstr.map !global_evd f t

let keep a = Proofview.V82.of_tactic (Tactics.keep a)
let convert_concl_no_check a b = Proofview.V82.of_tactic (Tactics.convert_concl_no_check a b)

let parse_entry e s = Pcoq.Entry.parse e (Pcoq.Parsable.make s)

let coq_lib_ref n = lazy (lib_ref n)

let is_global c t = is_global (Lazy.force c) t

let constr_of_global f = of_constr (constr_of_global (Lazy.force f))

let __coq_plugin_name = "gappatac"
let _ = Mltop.add_known_module __coq_plugin_name

let debug = ref false

(* 1. gappa syntax trees and output *)

module Constant = struct

  open Bigint

  type t = { mantissa : bigint; base : int; exp : bigint }

  let create (b, m, e) =
    { mantissa = m; base = b; exp = e }

  let of_int x =
    { mantissa = x; base = 1; exp = zero }

  let print fmt x = match x.base with
    | 1 -> fprintf fmt "%s" (to_string x.mantissa)
    | 2 -> fprintf fmt "%sb%s" (to_string x.mantissa) (to_string x.exp)
    | 10 -> fprintf fmt "%se%s" (to_string x.mantissa) (to_string x.exp)
    | _ -> assert false

end

type binop = Bminus | Bplus | Bmult | Bdiv

type unop = Usqrt | Uabs | Uopp

type rounding_mode = string

type term =
  | Tconst of Constant.t
  | Tvar of string
  | Tbinop of binop * term * term
  | Tunop of unop * term
  | Tround of rounding_mode * term

type atom =
  | Ain of term * Constant.t option * Constant.t option
  | Arel of term * term * Constant.t * Constant.t
  | Aeq of term * term

type pred =
  | Patom of atom
  | Pand of pred * pred
  | Por of pred * pred
  | Pnot of pred

(** {1 Symbols needed by the tactics} *)

let coq_False = coq_lib_ref "core.False.type"
let coq_True = coq_lib_ref "core.True.type"
let coq_eq = coq_lib_ref "core.eq.type"
let coq_eq_refl = coq_lib_ref "core.eq.refl"
let coq_not = coq_lib_ref "core.not.type"
let coq_and = coq_lib_ref "core.and.type"
let coq_or = coq_lib_ref "core.or.type"

let coq_Some = coq_lib_ref "core.option.Some"
let coq_cons = coq_lib_ref "core.list.cons"
let coq_nil = coq_lib_ref "core.list.nil"
let coq_bool = coq_lib_ref "core.bool.type"
let coq_true = coq_lib_ref "core.bool.true"

let coq_Z0 = coq_lib_ref "num.Z.Z0"
let coq_Zpos = coq_lib_ref "num.Z.Zpos"
let coq_Zneg = coq_lib_ref "num.Z.Zneg"
let coq_xH = coq_lib_ref "num.pos.xH"
let coq_xI = coq_lib_ref "num.pos.xI"
let coq_xO = coq_lib_ref "num.pos.xO"

let coq_R = coq_lib_ref "reals.R.type"
let coq_R0 = coq_lib_ref "reals.R.R0"
let coq_R1 = coq_lib_ref "reals.R.R1"
let coq_Rle = coq_lib_ref "reals.R.Rle"
let coq_Rplus = coq_lib_ref "reals.R.Rplus"
let coq_Ropp = coq_lib_ref "reals.R.Ropp"
let coq_Rminus = coq_lib_ref "reals.R.Rminus"
let coq_Rmult = coq_lib_ref "reals.R.Rmult"
let coq_Rinv = coq_lib_ref "reals.R.Rinv"
let coq_Rdiv = coq_lib_ref "reals.R.Rdiv"
let coq_IZR = coq_lib_ref "reals.R.IZR"
let coq_Rabs = coq_lib_ref "reals.R.Rabs"
let coq_sqrt = coq_lib_ref "reals.R.sqrt"
let coq_powerRZ = coq_lib_ref "reals.R.powerRZ"

let coq_convert_tree = coq_lib_ref "gappa.gappa_private.convert_tree"
let coq_RTree = coq_lib_ref "gappa.gappa_private.RTree"
let coq_rtTrue = coq_lib_ref "gappa.gappa_private.rtTrue"
let coq_rtFalse = coq_lib_ref "gappa.gappa_private.rtFalse"
let coq_rtAtom = coq_lib_ref "gappa.gappa_private.rtAtom"
let coq_rtNot = coq_lib_ref "gappa.gappa_private.rtNot"
let coq_rtAnd = coq_lib_ref "gappa.gappa_private.rtAnd"
let coq_rtOr = coq_lib_ref "gappa.gappa_private.rtOr"
let coq_rtImpl = coq_lib_ref "gappa.gappa_private.rtImpl"
let coq_RAtom = coq_lib_ref "gappa.gappa_private.RAtom"
let coq_raBound = coq_lib_ref "gappa.gappa_private.raBound"
let coq_raRel = coq_lib_ref "gappa.gappa_private.raRel"
let coq_raEq = coq_lib_ref "gappa.gappa_private.raEq"
let coq_raLe = coq_lib_ref "gappa.gappa_private.raLe"
let coq_raGeneric = coq_lib_ref "gappa.gappa_private.raGeneric"
let coq_raFormat = coq_lib_ref "gappa.gappa_private.raFormat"
let coq_RExpr = coq_lib_ref "gappa.gappa_private.RExpr"
let coq_reUnknown = coq_lib_ref "gappa.gappa_private.reUnknown"
let coq_reFloat2 = coq_lib_ref "gappa.gappa_private.reFloat2"
let coq_reFloat10 = coq_lib_ref "gappa.gappa_private.reFloat10"
let coq_reBpow2 = coq_lib_ref "gappa.gappa_private.reBpow2"
let coq_reBpow10 = coq_lib_ref "gappa.gappa_private.reBpow10"
let coq_rePow2 = coq_lib_ref "gappa.gappa_private.rePow2"
let coq_rePow10 = coq_lib_ref "gappa.gappa_private.rePow10"
let coq_reInteger = coq_lib_ref "gappa.gappa_private.reInteger"
let coq_reBinary = coq_lib_ref "gappa.gappa_private.reBinary"
let coq_reUnary = coq_lib_ref "gappa.gappa_private.reUnary"
let coq_reRound = coq_lib_ref "gappa.gappa_private.reRound"
let coq_mRndDN = coq_lib_ref "gappa.gappa_private.mRndDN"
let coq_mRndNA = coq_lib_ref "gappa.gappa_private.mRndNA"
let coq_mRndNE = coq_lib_ref "gappa.gappa_private.mRndNE"
let coq_mRndUP = coq_lib_ref "gappa.gappa_private.mRndUP"
let coq_mRndZR = coq_lib_ref "gappa.gappa_private.mRndZR"
let coq_fFloat = coq_lib_ref "gappa.gappa_private.fFloat"
let coq_fFloatx = coq_lib_ref "gappa.gappa_private.fFloatx"
let coq_fFixed = coq_lib_ref "gappa.gappa_private.fFixed"
let coq_boAdd = coq_lib_ref "gappa.gappa_private.boAdd"
let coq_boSub = coq_lib_ref "gappa.gappa_private.boSub"
let coq_boMul = coq_lib_ref "gappa.gappa_private.boMul"
let coq_boDiv = coq_lib_ref "gappa.gappa_private.boDiv"
let coq_uoAbs = coq_lib_ref "gappa.gappa_private.uoAbs"
let coq_uoNeg = coq_lib_ref "gappa.gappa_private.uoNeg"
let coq_uoInv = coq_lib_ref "gappa.gappa_private.uoInv"
let coq_uoSqrt = coq_lib_ref "gappa.gappa_private.uoSqrt"

let coq_rndNE = coq_lib_ref "gappa.round_def.rndNE"
let coq_rndNA = coq_lib_ref "gappa.round_def.rndNA"

let coq_radix_val = coq_lib_ref "flocq.zaux.radix_val"
let coq_bpow = coq_lib_ref "flocq.raux.bpow"
let coq_rndDN = coq_lib_ref "flocq.raux.Zfloor"
let coq_rndUP = coq_lib_ref "flocq.raux.Zceil"
let coq_rndZR = coq_lib_ref "flocq.raux.Ztrunc"

let coq_round = coq_lib_ref "flocq.generic_fmt.round"
let coq_generic_format = coq_lib_ref "flocq.generic_fmt.generic_format"

let coq_FLT_format = coq_lib_ref "flocq.flt.FLT_format"
let coq_FLT_exp = coq_lib_ref "flocq.flt.FLT_exp"

let coq_FLX_format = coq_lib_ref "flocq.flx.FLX_format"
let coq_FLX_exp = coq_lib_ref "flocq.flx.FLX_exp"

let coq_FIX_format = coq_lib_ref "flocq.fix.FIX_format"
let coq_FIX_exp = coq_lib_ref "flocq.fix.FIX_exp"

(** {1 Reification from Coq user goal: the [gappa_quote] tactic} *)

exception NotGappa of constr

let var_terms = Hashtbl.create 17
let var_names = Hashtbl.create 17
let var_list = ref []

let mkLApp f v = mkApp (constr_of_global f, v)

let mkList t =
  List.fold_left (fun acc v -> mkLApp coq_cons [|t; v; acc|]) (mkLApp coq_nil [|t|])

let rec mk_pos n =
  if n = 1 then constr_of_global coq_xH
  else if n land 1 = 0 then mkLApp coq_xO [|mk_pos (n / 2)|]
  else mkLApp coq_xI [|mk_pos (n / 2)|]

type int_type = It_1 | It_2 | It_even of constr | It_int of constr | It_none of constr
type int_type_partial = Itp_1 | Itp_2 | Itp_even of int | Itp_int of int

(** translate a closed Coq term [p:positive] into [int] *)
let rec tr_positive p = match kind_of_term p with
  | Constr.Construct _ when is_global coq_xH p -> 1
  | Constr.App (f, [|a|]) when is_global coq_xI f -> 2 * (tr_positive a) + 1
  | Constr.App (f, [|a|]) when is_global coq_xO f -> 2 * (tr_positive a)
  | Constr.Cast (p, _, _) -> tr_positive p
  | _ -> raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [int] *)
let rec tr_arith_constant t = match kind_of_term t with
  | Constr.Construct _ when is_global coq_Z0 t -> 0
  | Constr.App (f, [|a|]) when is_global coq_Zpos f -> tr_positive a
  | Constr.App (f, [|a|]) when is_global coq_Zneg f -> - (tr_positive a)
  | Constr.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise (NotGappa t)

(** translate a closed Coq term [t:R] into [int] *)
let tr_real_constant t =
  let rec aux t =
    match decompose_app t with
      | c, [] when is_global coq_R1 c -> Itp_1
      | c, [a] when is_global coq_IZR c ->
          Itp_int (tr_arith_constant a)
      | c, [a;b] ->
          if is_global coq_Rplus c then
            if aux a = Itp_1 then
              match aux b with
                | Itp_1 -> Itp_2
                | Itp_2 -> Itp_int 3
                | Itp_even n -> Itp_int (2 * n + 1)
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else if is_global coq_Rmult c then
            if aux a = Itp_2 then
              match aux b with
                | Itp_2 -> Itp_even 2
                | Itp_even n -> Itp_even (2 * n)
                | Itp_int n -> Itp_even n
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else
            raise (NotGappa t)
      | _ ->
        raise (NotGappa t)
    in
  match aux t with
    | Itp_1 -> 1
    | Itp_2 -> 2
    | Itp_even n -> 2 * n
    | Itp_int n -> n

(** create a term of type [Z] from a quoted real (supposedly constant) *)
let plain_of_int =
  let wrap t =
    mkLApp coq_reInteger [|mkLApp coq_Zpos [|t|]|] in
  function
    | It_1 -> wrap (constr_of_global coq_xH)
    | It_2 -> wrap (mkLApp coq_xO [|constr_of_global coq_xH|])
    | It_even n -> wrap (mkLApp coq_xO [|n|])
    | It_int n -> wrap n
    | It_none n -> n

(** reify a format [Z->Z] *)
let qt_fmt f =
  match decompose_app f with
    | c, [e;p] when is_global coq_FLT_exp c -> mkLApp coq_fFloat [|e;p|]
    | c, [p] when is_global coq_FLX_exp c -> mkLApp coq_fFloatx [|p|]
    | c, [e] when is_global coq_FIX_exp c -> mkLApp coq_fFixed [|e|]
    | _ -> raise (NotGappa f)

(** reify a Coq term [t:R] *)
let rec qt_term t =
  plain_of_int (qt_Rint t)
and qt_Rint t =
  match decompose_app t with
    | c, [] when is_global coq_R1 c -> It_1
    | c, [a;b] ->
        if is_global coq_Rplus c then
          let a = qt_Rint a in
          if a = It_1 then
            match qt_Rint b with
              | It_1 -> It_2
              | It_2 -> It_int (mkLApp coq_xI [|constr_of_global coq_xH|])
              | It_even n -> It_int (mkLApp coq_xI [|n|])
              | (It_int n) as b ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boAdd; plain_of_int a; plain_of_int b|])
              | It_none e ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boAdd; plain_of_int a; e|])
          else
            It_none (mkLApp coq_reBinary
              [|constr_of_global coq_boAdd; plain_of_int a; qt_term b|])
        else if is_global coq_Rmult c then
          let a = qt_Rint a in
          if a = It_2 then
            match qt_Rint b with
              | It_2 -> It_even (mkLApp coq_xO [|constr_of_global coq_xH|])
              | It_even n -> It_even (mkLApp coq_xO [|n|])
              | It_int n -> It_even n
              | _ as b ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boMul; plain_of_int a; plain_of_int b|])
          else
            It_none (mkLApp coq_reBinary
              [|constr_of_global coq_boMul; plain_of_int a; qt_term b|])
        else
          It_none (qt_no_Rint t)
    | _ ->
      It_none (qt_no_Rint t)
and qt_no_Rint t =
  try
    match decompose_app t with
      | c, [] when is_global coq_R0 c ->
        mkLApp coq_reInteger [|constr_of_global coq_Z0|]
      | c, [a] when is_global coq_IZR c ->
        ignore (tr_arith_constant a);
        mkLApp coq_reInteger [|a|]
      | c, [a] ->
        begin
          let gen_un f = mkLApp coq_reUnary [|constr_of_global f; qt_term a|] in
          if is_global coq_Ropp c then gen_un coq_uoNeg else
          if is_global coq_Rinv c then gen_un coq_uoInv else
          if is_global coq_Rabs c then gen_un coq_uoAbs else
          if is_global coq_sqrt c then gen_un coq_uoSqrt else
          raise (NotGappa t)
        end
      | c, [_;v;w;b] when is_global coq_round c ->
          (* TODO: check radix *)
          let mode = match decompose_app w with
            | c, [] when is_global coq_rndDN c -> coq_mRndDN
            | c, [] when is_global coq_rndNA c -> coq_mRndNA
            | c, [] when is_global coq_rndNE c -> coq_mRndNE
            | c, [] when is_global coq_rndUP c -> coq_mRndUP
            | c, [] when is_global coq_rndZR c -> coq_mRndZR
            | _ -> raise (NotGappa w) in
          mkLApp coq_reRound [|qt_fmt v; constr_of_global mode; qt_term b|]
      | c, [a;b] ->
          let gen_bin f = mkLApp coq_reBinary [|constr_of_global f; qt_term a; qt_term b|] in
          if is_global coq_Rminus c then gen_bin coq_boSub else
          if is_global coq_Rdiv c then gen_bin coq_boDiv else
          if is_global coq_powerRZ c then
            let p =
              match tr_real_constant a with
                | 2 -> coq_rePow2
                | 10 -> coq_rePow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|] else
          if is_global coq_bpow c then
            let p =
              match tr_arith_constant
                      (Tacred.compute !global_env !global_evd
                                      (mkLApp coq_radix_val [|a|])) with
                | 2 -> coq_reBpow2
                | 10 -> coq_reBpow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|]
          else raise (NotGappa t)
      | _ -> raise (NotGappa t)
  with NotGappa _ ->
    try
      Hashtbl.find var_terms t
    with Not_found ->
      let e = mkLApp coq_reUnknown [|mk_pos (Hashtbl.length var_terms + 1)|] in
      Hashtbl.add var_terms t e;
      var_list := t :: !var_list;
      e

(** reify a Coq term [p:Prop] *)
let rec qt_pred p = match kind_of_term p with
  | Constr.Prod (_,a,b) ->
    if not (closed0 b) then raise (NotGappa p);
    mkLApp coq_rtImpl [|qt_pred a; qt_pred b|]
  | _ ->
match decompose_app p with
  | c, [] when is_global coq_True c ->
      constr_of_global coq_rtTrue
  | c, [] when is_global coq_False c ->
      constr_of_global coq_rtFalse
  | c, [a] when is_global coq_not c ->
      mkLApp coq_rtNot [|qt_pred a|]
  | c, [a;b] when is_global coq_and c ->
      begin match decompose_app a, decompose_app b with
        | (c1, [a1;b1]), (c2, [a2;b2])
          when is_global coq_Rle c1 && is_global coq_Rle c2 && eq_constr b1 a2 ->
            mkLApp coq_rtAtom [|mkLApp coq_raBound
              [|mkLApp coq_Some [|constr_of_global coq_RExpr; qt_term a1|]; qt_term b1;
                mkLApp coq_Some [|constr_of_global coq_RExpr; qt_term b2|]|]|]
        | _ ->
            mkLApp coq_rtAnd [|qt_pred a; qt_pred b|]
      end
  | c, [a;b] when is_global coq_or c ->
      mkLApp coq_rtOr [|qt_pred a; qt_pred b|]
  | c, [a;b] when is_global coq_Rle c ->
      mkLApp coq_rtAtom [|mkLApp coq_raLe [|qt_term a; qt_term b|]|]
  | c, [t;a;b] when is_global coq_eq c && is_global coq_R t ->
      mkLApp coq_rtAtom [|mkLApp coq_raEq [|qt_term a; qt_term b|]|]
  | c, [_;e;x] when is_global coq_FIX_format c ->
      let fmt = mkLApp coq_fFixed [|e|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;e;p;x] when is_global coq_FLT_format c ->
      let fmt = mkLApp coq_fFloat [|e;p|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;p;x] when is_global coq_FLX_format c ->
      let fmt = mkLApp coq_fFloatx [|p|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;f;x] when is_global coq_generic_format c ->
      mkLApp coq_rtAtom [|mkLApp coq_raGeneric [|qt_fmt f; qt_term x|]|]
  | _ -> raise (NotGappa p)

(** reify hypotheses *)
let qt_hyps =
  List.fold_left (fun acc (n, h) ->
    let old_var_list = !var_list in
    try (n, qt_pred h) :: acc
    with NotGappa _ ->
      while not (!var_list == old_var_list) do
        match !var_list with
        | h :: q ->
          Hashtbl.remove var_terms h;
          var_list := q
        | [] -> assert false
      done;
      acc) []

(** the [gappa_quote] tactic *)
let gappa_quote gl =
  try
    global_env := pf_env gl;
    global_evd := project gl;
    let l = qt_hyps (pf_hyps_types gl) in
    let _R = constr_of_global coq_R in
    let g = List.fold_left
      (fun acc (_, h) -> mkLApp coq_rtImpl [|h; acc|])
      (qt_pred (pf_concl gl)) l in
    let uv = mkList _R !var_list in
    let e = mkLApp coq_convert_tree [|uv; g|] in
    (*Pp.msgerrnl (pr_constr e);*)
    Hashtbl.clear var_terms;
    var_list := [];
    Tacticals.tclTHEN
      (Tacticals.tclTHEN
        (generalize (List.map (fun (n, _) -> mkVar (binder_name n)) (List.rev l)))
        (keep []))
      (convert_concl_no_check e Constr.DEFAULTcast) gl
  with
    | NotGappa t ->
      Hashtbl.clear var_terms;
      var_list := [];
      anomaly ~label:"gappa_quote"
        (Pp.str "something wrong happened with term " ++ pr_constr t)

(** {1 Goal parsing, call to Gappa, and proof building: the [gappa_internal] tactic} *)

(** translate a closed Coq term [p:positive] into [bigint] *)
let rec tr_bigpositive p = match kind_of_term p with
  | Constr.Construct _ when is_global coq_xH p ->
      Bigint.one
  | Constr.App (f, [|a|]) when is_global coq_xI f ->
      Bigint.add_1 (Bigint.mult_2 (tr_bigpositive a))
  | Constr.App (f, [|a|]) when is_global coq_xO f ->
      (Bigint.mult_2 (tr_bigpositive a))
  | Constr.Cast (p, _, _) ->
      tr_bigpositive p
  | _ ->
      raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [bigint] *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Constr.Construct _ when is_global coq_Z0 t -> Bigint.zero
  | Constr.App (f, [|a|]) when is_global coq_Zpos f -> tr_bigpositive a
  | Constr.App (f, [|a|]) when is_global coq_Zneg f ->
      Bigint.neg (tr_bigpositive a)
  | Constr.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise (NotGappa t)

let tr_float b m e =
  (b, tr_arith_bigconstant m, tr_arith_bigconstant e)

let tr_binop c = match decompose_app c with
  | c, [] when is_global coq_boAdd c -> Bplus
  | c, [] when is_global coq_boSub c -> Bminus
  | c, [] when is_global coq_boMul c -> Bmult
  | c, [] when is_global coq_boDiv c -> Bdiv
  | _ -> assert false

let tr_unop c = match decompose_app c with
  | c, [] when is_global coq_uoNeg c -> Uopp
  | c, [] when is_global coq_uoSqrt c -> Usqrt
  | c, [] when is_global coq_uoAbs c -> Uabs
  | _ -> raise (NotGappa c)

(** translate a Coq term [c:RExpr] into [term] *)
let rec tr_term uv t =
  match decompose_app t with
    | c, [a] when is_global coq_reUnknown c ->
        let n = tr_positive a - 1 in
        if (n < Array.length uv) then Tvar uv.(n)
        else raise (NotGappa t)
    | c, [a; b] when is_global coq_reFloat2 c ->
        Tconst (Constant.create (tr_float 2 a b))
    | c, [a; b] when is_global coq_reFloat10 c ->
        Tconst (Constant.create (tr_float 10 a b))
    | c, [a] when is_global coq_reInteger c ->
        Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | c, [op;a;b] when is_global coq_reBinary c ->
        Tbinop (tr_binop op, tr_term uv a, tr_term uv b)
    | c, [op;a] when is_global coq_reUnary c ->
        Tunop (tr_unop op, tr_term uv a)
    | c, [fmt;mode;a] when is_global coq_reRound c ->
        let mode = match decompose_app mode with
          | c, [] when is_global coq_mRndDN c -> "dn"
          | c, [] when is_global coq_mRndNA c -> "na"
          | c, [] when is_global coq_mRndNE c -> "ne"
          | c, [] when is_global coq_mRndUP c -> "up"
          | c, [] when is_global coq_mRndZR c -> "zr"
          | _ -> raise (NotGappa mode) in
        let rnd = match decompose_app fmt with
          | c, [e;p] when is_global coq_fFloat c ->
              let e = tr_arith_constant e in
              let p = tr_arith_constant p in
              sprintf "float<%d,%d,%s>" p e mode
          | c, [p] when is_global coq_fFloatx c ->
              let p = tr_arith_constant p in
              sprintf "float<%d,%s>" p mode
          | c, [e] when is_global coq_fFixed c ->
              let e = tr_arith_constant e in
              sprintf "fixed<%d,%s>" e mode
          | _ -> raise (NotGappa fmt) in
        Tround (rnd, tr_term uv a)
    | _ ->
        raise (NotGappa t)

let tr_const c =
  match tr_term [||] c with
    | Tconst v -> v
    | _ -> raise (NotGappa c)

(** translate a Coq term [t:RAtom] into [pred] *)
let tr_atom uv t =
  match decompose_app t with
    | c, [l;e;u] when is_global coq_raBound c ->
        let l = match decompose_app l with
          | (_, [_;l]) -> Some (tr_const l)
          | (_, [_]) -> None
          | _ -> assert false in
        let u = match decompose_app u with
          | (_, [_;u]) -> Some (tr_const u)
          | (_, [_]) -> None
          | _ -> assert false in
        if l = None && u = None then raise (NotGappa t);
        Ain (tr_term uv e, l, u)
    | c, [er;ex;l;u] when is_global coq_raRel c ->
        Arel (tr_term uv er, tr_term uv ex, tr_const l, tr_const u)
    | c, [er;ex] when is_global coq_raEq c ->
        Aeq (tr_term uv er, tr_term uv ex)
    | _ ->
        raise (NotGappa t)

(** translate a Coq term [t:RTree] into [pred] *)
let rec tr_pred uv t =
  match decompose_app t with
    | c, [a] when is_global coq_rtAtom c ->
        Patom (tr_atom uv a)
    | c, [a] when is_global coq_rtNot c ->
        Pnot (tr_pred uv a)
    | c, [a;b] when is_global coq_rtAnd c ->
        Pand (tr_pred uv a, tr_pred uv b)
    | c, [a;b] when is_global coq_rtOr c ->
        Por (tr_pred uv a, tr_pred uv b)
    | _ ->
        raise (NotGappa t)

let tr_var c = match kind_of_term c with
  | Constr.Var x ->
    let s = Id.to_string x in
    let l = String.length s in
    let s = Bytes.init l (fun i ->
      let c = s.[i] in
      if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') ||
        ('0' <= c && c <= '9') || c == '_' then c else '_';
    ) in
    if Bytes.get s 0 = '_' then Bytes.set s 0 'G';
    let b = Buffer.create l in
    Buffer.add_bytes b s;
    begin try
      while true do
        ignore (Hashtbl.find var_names (Buffer.contents b));
        Buffer.add_string b "_";
      done;
      assert false
    with Not_found ->
      let s = Buffer.contents b in
      Hashtbl.add var_names s c;
      s
    end
  | _ -> raise (NotGappa c)

(** translate a Coq term [t:list] into [list] by applying [f] to each element *)
let tr_list f =
  let rec aux c =
    match decompose_app c with
      | _, [_;h;t] -> f h :: aux t
      | _, [_] -> []
      | _ -> raise (NotGappa c)
    in
  aux

(** translate a Coq term [c] of kind [convert_tree ...] *)
let tr_goal c =
  match decompose_app c with
    | c, [uv;e] when is_global coq_convert_tree c ->
        let uv = Array.of_list (tr_list tr_var uv) in
        tr_pred uv e
    | _ -> raise (NotGappa c)

(** print a Gappa term *)
let rec print_term fmt = function
  | Tconst c -> Constant.print fmt c
  | Tvar s -> pp_print_string fmt s
  | Tbinop (op, t1, t2) ->
      let op =
        match op with
          | Bplus -> "+" | Bminus -> "-" | Bmult -> "*" | Bdiv -> "/"
        in
      fprintf fmt "(%a %s %a)" print_term t1 op print_term t2
  | Tunop (Uabs, t) ->
      fprintf fmt "|%a|" print_term t
  | Tunop (Uopp | Usqrt as op, t) ->
      let s =
        match op with
          | Uopp -> "-" | Usqrt -> "sqrt" | _ -> assert false
        in
      fprintf fmt "(%s(%a))" s print_term t
  | Tround (m, t) ->
      fprintf fmt "(%s(%a))" m print_term t

(** print a Gappa predicate *)
let print_atom fmt = function
  | Ain (t, Some c1, Some c2) ->
      fprintf fmt "%a in [%a, %a]"
        print_term t Constant.print c1 Constant.print c2
  | Ain (t, Some c, None) ->
      fprintf fmt "%a >= %a" print_term t Constant.print c
  | Ain (t, None, Some c) ->
      fprintf fmt "%a <= %a" print_term t Constant.print c
  | Ain (_, None, None) -> assert false
  | Arel (t1, t2, c1, c2) ->
      fprintf fmt "%a -/ %a in [%a,%a]"
        print_term t1 print_term t2 Constant.print c1 Constant.print c2
  | Aeq (t1, t2) ->
      fprintf fmt "%a = %a" print_term t1 print_term t2

let rec print_pred fmt = function
  | Patom a -> print_atom fmt a
  | Pnot t -> fprintf fmt "not (%a)" print_pred t
  | Pand (t1, t2) -> fprintf fmt "(%a) /\\ (%a)" print_pred t1 print_pred t2
  | Por (t1, t2) -> fprintf fmt "(%a) \\/ (%a)" print_pred t1 print_pred t2

let temp_file f = if !debug then f else Filename.temp_file f ""
let remove_file f = if not !debug then try Sys.remove f with _ -> ()

exception GappaFailed of string

(** print a Gappa goal from [p] and call Gappa on it,
    build a Coq term by calling [c_of_s] *)
let call_gappa c_of_s p =
  let gappa_in = temp_file "gappa_inp" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ %a }@]@." print_pred p;
  close_out c;
  let gappa_out = temp_file "gappa_out" in
  let gappa_err = temp_file "gappa_err" in
  let cmd = sprintf "gappa -Bcoq-lambda %s > %s 2> %s" gappa_in gappa_out gappa_err in
  let out = Sys.command cmd in
  if out <> 0 then begin
    let c = open_in_bin gappa_err in
    let len = in_channel_length c in
    let buf = Bytes.create len in
    ignore (input c buf 0 len);
    close_in c;
    raise (GappaFailed (Bytes.unsafe_to_string buf))
  end;
  remove_file gappa_err;
  let cin = open_in gappa_out in
  let constr = c_of_s (Stream.of_channel cin) in
  close_in cin;
  remove_file gappa_in;
  remove_file gappa_out;
  constr

(** execute [f] after disabling globalization *)
let no_glob f =
  Dumpglob.pause ();
  let res =
    try f () with e ->
      Dumpglob.continue ();
      raise e
    in
  Dumpglob.continue ();
  res

(** replace all evars of any type [ty] by [(refl_equal true : ty)] *)
let evars_to_vmcast env emap c =
  let emap = nf_evar_map emap in
  let change_exist evar =
    let ty = Reductionops.nf_betaiota env emap (existential_type emap evar) in
    mkCast (mkLApp coq_eq_refl
      [|constr_of_global coq_bool; constr_of_global coq_true|], Constr.VMcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Constr.Evar ev -> change_exist ev
      | _ -> map_constr replace c
    in
  replace c

let constr_of_stream env evd s =
  no_glob (fun () -> Constrintern.interp_open_constr env evd
    (parse_entry Pcoq.Constr.constr s))

let var_name = function
  | Name id ->
      let s = Id.to_string id in
      let s = String.sub s 1 (String.length s - 1) in
      Hashtbl.find var_names s
  | Anonymous ->
      assert false

(** apply to the proof term [c] all the needed variables from the context
    and as many metas as needed to match hypotheses *)
let build_proof_term evd c =
  let bl, _ = decompose_lam evd c in
  List.fold_right (fun (x,t) pf -> mkApp (pf, [| var_name (binder_name x) |])) bl c

(** the [gappa_internal] tactic *)
let gappa_internal gl =
  try
    global_env := pf_env gl;
    global_evd := project gl;
    Hashtbl.clear var_names;
    List.iter (let dummy = mkVar (Id.of_string "dummy") in
      fun n -> Hashtbl.add var_names n dummy)
      ["fma"; "sqrt"; "not"; "in"; "float"; "fixed"; "int";
       "homogen80x"; "homogen80x_init"; "float80x";
       "add_rel"; "sub_rel"; "mul_rel"; "fma_rel" ];
    let g = tr_goal (pf_concl gl) in
    let (emap, pf) = call_gappa (constr_of_stream !global_env !global_evd) g in
    global_evd := emap;
    let pf = evars_to_vmcast !global_env emap pf in
    let pf = build_proof_term emap pf in
    refine_no_check pf gl
  with
    | NotGappa t ->
      user_err ~hdr:"gappa_internal"
        (Pp.str "translation to Gappa failed (not a reduced constant?): " ++ pr_constr t)
    | GappaFailed s ->
      user_err ~hdr:"gappa_internal"
        (Pp.str "execution of Gappa failed:" ++ Pp.fnl () ++ Pp.str s)

let gappa_quote = Proofview.V82.tactic gappa_quote
let gappa_internal = Proofview.V82.tactic gappa_internal

let () =
  Tacentries.tactic_extend __coq_plugin_name "gappatac_gappa_internal" ~level:0
    [Tacentries.TyML
       (Tacentries.TyIdent ("gappa_internal", Tacentries.TyNil),
        (fun ist -> gappa_internal))]

let () =
  Tacentries.tactic_extend __coq_plugin_name "gappatac_gappa_quote" ~level:0
    [Tacentries.TyML
       (Tacentries.TyIdent ("gappa_quote", Tacentries.TyNil),
        (fun ist -> gappa_quote))]
