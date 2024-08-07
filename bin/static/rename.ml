open Semant.StaticSemantObj
open Substitute
open Utils

let generate_tvar_sub tvarset fresh : substitition =
  List.fold_left
    (fun submap tv -> SubstitutionMap.add tv (TyVar (fresh ())) submap)
    SubstitutionMap.empty
    (TyvarSet.elements tvarset)

let bound_tyvars_in_type_scheme type_scheme =
  let rec inner acc type_scheme =
    match type_scheme with
    | ForAll { tv; ts } -> TyvarSet.add tv (inner acc ts)
    | Typ _ -> acc
  in
  inner TyvarSet.empty type_scheme

(**@return a type (not a typscheme) with all forall types repaces by fresh ty_vars*)
let rename_tvars type_scheme fresh =
  let sub : substitition =
    generate_tvar_sub (bound_tyvars_in_type_scheme type_scheme) fresh
  in
  substitute_typ sub (typ_from_typescheme type_scheme)
