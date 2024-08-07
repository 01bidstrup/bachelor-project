open Semant.Ast
open Semant.StaticSemantObj
open Substitute
open Rename
open UnionFind
open Pretty.StringOf
open Utils
open FreshTvars

let fresh_tvar, reset_fresh_var = fresh_and_reset ()
let fresh_tvar lvl = fresh_tvar lvl "t"

let rec find_in_typ (ty : typ) : typ =
  match find ty with
  | FunVar { source; target } ->
      FunVar { source = find_in_typ source; target = find_in_typ target }
  | PairVar { first; second } ->
      PairVar { first = find_in_typ first; second = find_in_typ second }
  | _ -> find ty

let replace_typs_in_tyres tyres =
  match tyres with Fail -> Fail | OptTyRes ty -> OptTyRes (find_in_typ ty)

let rec type_check (tenv : tenv) (e : exp) : opt_tyres =
  replace_typs_in_tyres
    (try type_check_with_lvl 0 tenv e with UnificationFail _ -> Fail)

and type_check_with_lvl (lvl : int) (tenv : tenv) (e : exp) : opt_tyres =
  let result =
    match e with
    | BaseVal bv -> OptTyRes (type_check_base_val lvl bv)
    | Var v -> type_check_var lvl tenv v
    | Lambda { var; exp } -> type_check_lambda lvl tenv var exp
    | App { e1; e2 } -> type_check_app lvl tenv e1 e2
    | Let { var; e1; e2 } -> type_check_let lvl tenv var e1 e2
    | Pair { first; second } -> type_check_pair lvl tenv first second
    | First exp -> type_check_first lvl tenv exp
    | Second exp -> type_check_second lvl tenv exp
  in
  result

and type_check_base_val _ bv =
  match bv with Int _ -> TyCon Int | Bool _ -> TyCon Bool

and type_check_var lvl tenv v =
  try OptTyRes (rename_tvars (TEnv.find v tenv) (fun () -> fresh_tvar lvl))
  with Not_found -> Fail

and type_check_lambda lvl tenv var exp =
  let alpha = TyVar (fresh_tvar lvl) in
  let tenv = TEnv.add var (Typ alpha) tenv in
  let res = type_check_with_lvl lvl tenv exp in
  match res with
  | Fail -> Fail
  | OptTyRes ty -> OptTyRes (FunVar { source = alpha; target = ty })

and type_check_app lvl tenv e1 e2 =
  match type_check_with_lvl lvl tenv e1 with
  | Fail -> Fail
  | OptTyRes ts1 -> (
      match type_check_with_lvl lvl tenv e2 with
      | Fail -> Fail
      | OptTyRes ts2 ->
          let alpha = TyVar (fresh_tvar lvl) in
          let () = unify ts1 (FunVar { source = ts2; target = alpha }) in
          OptTyRes alpha)

and type_check_let lvl tenv var e1 e2 =
  match type_check_with_lvl (lvl + 1) tenv e1 with
  | Fail -> Fail
  | OptTyRes ts1 ->
      let clos = type_closure_lvl_based lvl ts1 in
      let tenv = TEnv.add var clos tenv in
      type_check_with_lvl lvl tenv e2

and type_check_pair lvl tenv first second =
  match type_check_with_lvl lvl tenv first with
  | Fail -> Fail
  | OptTyRes ts1 -> (
      match type_check_with_lvl lvl tenv second with
      | Fail -> Fail
      | OptTyRes ts2 ->
          let restyp = PairVar { first = ts1; second = ts2 } in
          OptTyRes restyp)

and type_check_first lvl tenv exp =
  let result, _ = pair_idx lvl tenv exp in
  result

and type_check_second lvl tenv exp =
  let _, result = pair_idx lvl tenv exp in
  result

and pair_idx lvl tenv exp =
  match type_check tenv exp with
  | Fail -> (Fail, Fail)
  | OptTyRes ts1 ->
      let alpha = TyVar (fresh_tvar lvl) in
      let beta = TyVar (fresh_tvar lvl) in
      let () = unify ts1 (PairVar { first = alpha; second = beta }) in
      (OptTyRes alpha, OptTyRes beta)

(**Generalizes only type variables whose level is not lover than the level of the let-binding*)
and type_closure_lvl_based lvl ty : type_scheme =
  let s = TypeCheck.tyvars_typ ty in

  TyvarSet.fold
    (fun tv acc ->
      match !tv with
      | _, tv_lvl, _ ->
          if tv_lvl >= lvl + 1 then ForAll { tv; ts = acc } else acc)
    s (Typ ty)
