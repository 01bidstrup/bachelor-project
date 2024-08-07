open Semant.Ast
open Semant.StaticSemantObj
open Substitute
open Unify
open Rename
open Pretty.StringOf
open Utils
open FreshTvars

let fresh_tvar, reset_fresh_var = fresh_and_reset ()
let fresh_tvar () = fresh_tvar 0 "t"
let reset_fresh_var = reset_fresh_var

let rec type_check (tenv : tenv) (e : exp) : tyres =
  let result =
    match e with
    | BaseVal bv -> TyRes { sub = id_sub; ty = type_check_base_val bv }
    | Var v -> type_check_var tenv v
    | Lambda { var; exp } -> type_check_lambda tenv var exp
    | App { e1; e2 } -> type_check_app tenv e1 e2
    | Let { var; e1; e2 } -> type_check_let tenv var e1 e2
    | Pair { first; second } -> type_check_pair tenv first second
    | First exp -> type_check_first tenv exp
    | Second exp -> type_check_second tenv exp
  in
  result

and type_check_base_val bv =
  match bv with Int _ -> TyCon Int | Bool _ -> TyCon Bool

and type_check_var tenv v =
  let res =
    try TyRes { sub = id_sub; ty = rename_tvars (TEnv.find v tenv) fresh_tvar }
    with Not_found -> Fail
  in
  res

and type_check_lambda tenv var exp =
  let alpha = Typ (TyVar (fresh_tvar ())) in
  let tenv = TEnv.add var alpha tenv in
  let res = type_check tenv exp in
  match res with
  | Fail -> Fail
  | TyRes { sub; ty } ->
      let restyp =
        FunVar
          {
            source = typ_from_typescheme (substitute_typescheme sub alpha);
            target = ty;
          }
      in
      TyRes { sub; ty = restyp }

and type_check_app tenv e1 e2 =
  match type_check tenv e1 with
  | Fail -> Fail
  | TyRes { sub = sub1; ty = ts1 } -> (
      match type_check (substitute_tenv sub1 tenv) e2 with
      | Fail -> Fail
      | TyRes { sub = sub2; ty = ts2 } -> (
          let alpha = TyVar (fresh_tvar ()) in
          let sub3option =
            unify (substitute_typ sub2 ts1)
              (FunVar { source = ts2; target = alpha })
          in
          match sub3option with
          | None -> Fail
          | Some sub3 ->
              TyRes
                { sub = sub3 @@@ sub2 @@@ sub1; ty = substitute_typ sub3 alpha }
          ))

and type_check_let tenv var e1 e2 =
  match type_check tenv e1 with
  | Fail -> Fail
  | TyRes { sub = sub1; ty = ts1 } -> (
      let sub_tenv = substitute_tenv sub1 tenv in
      let clos = type_closure sub_tenv ts1 in
      let tenv = TEnv.add var clos sub_tenv in
      match type_check tenv e2 with
      | Fail -> Fail
      | TyRes { sub = sub2; ty = ts2 } ->
          TyRes { sub = sub2 @@@ sub1; ty = ts2 })

and type_check_pair tenv first second =
  match type_check tenv first with
  | Fail -> Fail
  | TyRes { sub = sub1; ty = ts1 } -> (
      match type_check (substitute_tenv sub1 tenv) second with
      | Fail -> Fail
      | TyRes { sub = sub2; ty = ts2 } ->
          let restyp =
            PairVar { first = substitute_typ sub2 ts1; second = ts2 }
          in
          TyRes { sub = sub2 @@@ sub1; ty = restyp })

and type_check_first tenv exp =
  let result, _ = pair_idx tenv exp in
  result

and type_check_second tenv exp =
  let _, result = pair_idx tenv exp in
  result

and pair_idx tenv exp =
  match type_check tenv exp with
  | Fail -> (Fail, Fail)
  | TyRes { sub = sub1; ty = ts1 } -> (
      let alpha = TyVar (fresh_tvar ()) in
      let beta = TyVar (fresh_tvar ()) in
      let sub2option = unify ts1 (PairVar { first = alpha; second = beta }) in
      match sub2option with
      | None -> (Fail, Fail)
      | Some sub2 ->
          let sub = sub2 @@@ sub1 in
          ( TyRes { sub; ty = substitute_typ sub2 alpha },
            TyRes { sub; ty = substitute_typ sub2 beta } ))

and type_closure tenv typ =
  let clos = TyvarSet.diff (tyvars_typ typ) (tyvars_tenv tenv) in
  let result =
    TyvarSet.fold (fun t ts' -> ForAll { tv = t; ts = ts' }) clos (Typ typ)
  in
  result

and tyvars_typ typ =
  let rec inner acc typ =
    match typ with
    | TyVar tv -> TyvarSet.add tv acc
    | FunVar { source; target } ->
        TyvarSet.union (inner acc source) (inner acc target)
    | PairVar { first; second } ->
        TyvarSet.union (inner acc first) (inner acc second)
    | _ -> acc
  in
  inner TyvarSet.empty typ

and tyvars_ts ts =
  (*Find all tvars in ts, then remove those that are bound*)
  let rec remove_bound_tvars ts acc =
    match ts with
    | Typ _ -> acc
    | ForAll { tv; ts } ->
        if TyvarSet.mem tv acc then
          let acc' = TyvarSet.remove tv acc in
          remove_bound_tvars ts acc'
        else remove_bound_tvars ts acc
  in
  (* For ever bound type t in ts, check if it exist in tyvars,  *)
  remove_bound_tvars ts (tyvars_typ (typ_from_typescheme ts))

(**@retrun tvars that accour free in tenv*)
and tyvars_tenv tenv =
  TEnv.fold (fun _ t s -> TyvarSet.union (tyvars_ts t) s) tenv TyvarSet.empty
