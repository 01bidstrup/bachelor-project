open Semant.StaticSemantObj
open Semant.Ast

let rec typ_from_typescheme ts =
  match ts with Typ t -> t | ForAll { ts; _ } -> typ_from_typescheme ts

let mk_sub (maps : (ty_var * typ) list) : substitition =
  List.fold_left
    (fun acc (v, t) -> SubstitutionMap.add v t acc)
    id_sub (List.rev maps)

let mk_tenv (mappings : (var * type_scheme) list) : tenv =
  List.fold_left
    (fun acc mapping ->
      let v, ts = mapping in
      TEnv.add v ts acc)
    TEnv.empty mappings

(**@return a typescheme with the seciefied forall quantified variables and levels*)
let mk_ts_lvl (forall_quantified : (string * lvl) list) (ty : typ) : type_scheme
    =
  List.fold_left
    (fun acc (t, lvl) -> ForAll { tv = mk_tyvar lvl t; ts = acc })
    (Typ ty)
    (List.rev forall_quantified)

(**returns a tyscheme where all levels are 0*)
let mk_ts_0 forall_quantified ty =
  mk_ts_lvl (List.map (fun a -> (a, 0)) forall_quantified) ty

let mk_ty_con x = TyCon x
let ty_int = mk_ty_con Int
let q1 = TyVar (mk_tyvar 0 "q1")
let q2 = TyVar (mk_tyvar 0 "q2")
let t0 = TyVar (mk_tyvar 0 "t0")
let t1 = TyVar (mk_tyvar 0 "t1")
let t2 = TyVar (mk_tyvar 0 "t2")
let ty_bool = mk_ty_con Bool
let mk_ty_pair f s = PairVar { first = f; second = s }
let mk_ty_lambda t1 t2 = FunVar { source = t1; target = t2 }
let ty_id_fun = mk_ty_lambda t0 t0

let example_1_typ =
  (* (int × bool) *)
  Typ (mk_ty_pair ty_int ty_bool)

let example_2_typ = Fail

let example_3_typ =
  (*  t1 → ((int × t1) × (bool × t1)) *)
  Typ
    (let t0 = TyVar (mk_tyvar 0 "t0") in
     mk_ty_lambda t0 (mk_ty_pair (mk_ty_pair ty_int t0) (mk_ty_pair ty_bool t0)))
