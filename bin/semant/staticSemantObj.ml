open Ast

type ty_con = Int | Bool
type lvl = int

type rank = int
and ty_var = (tyvarkind * lvl * rank) ref
and tyvarkind = NoLink of string | LinkTo of typ

and typ =
  | TyCon of ty_con
  | TyVar of ty_var
  | FunVar of funvar
  | PairVar of pairvar

and funvar = { source : typ; target : typ }
and pairvar = { first : typ; second : typ }
and type_scheme = Typ of typ | ForAll of { tv : ty_var; ts : type_scheme }

module TEnv = Map.Make (struct
  type t = var

  let compare = compare
end)

type tenv = type_scheme TEnv.t

let empty_tenv : tenv = TEnv.empty

module TyvarSet = Set.Make (struct
  type t = ty_var

  let compare = compare
end)

type tvarset = TyvarSet.t

module SubstitutionMap = Map.Make (struct
  type t = ty_var

  let compare = compare
end)

type substitition = typ SubstitutionMap.t

let id_sub = SubstitutionMap.empty

type tyres = TyRes of { sub : substitition; ty : typ } | Fail
type opt_tyres = OptTyRes of typ | Fail

let mk_tyvar lvl x : ty_var =
  let l = NoLink x in
  ref (l, lvl, 0)

let sub_equal (map1 : substitition) (map2 : substitition) =
  let is_in key map = SubstitutionMap.mem key map in
  let is_value_same key =
    SubstitutionMap.find key map1 = SubstitutionMap.find key map2
  in
  let is_subset m1 m2 =
    SubstitutionMap.fold
      (fun key v acc ->
        (if is_in key m2 then is_value_same key else false) && acc)
      m1 true
  in
  is_subset map1 map2 && is_subset map2 map1

let subo_equal (subo1 : substitition option) (subo2 : substitition option) =
  match (subo1, subo2) with
  | Some sub1, Some sub2 -> sub_equal sub1 sub2
  | _ -> false

(* rank always starts out as 0*)
