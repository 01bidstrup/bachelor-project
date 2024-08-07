open OUnit2
open Semant.StaticSemantObj
open Semant.Ast
open Pretty.StringOf
open Static.Unify
open Static.Utils
open Dynamic.Utils

let mk_tyvar x = mk_tyvar 0 x
let typ_int = TyCon Int
let fresh = Static.TypeCheck.fresh_tvar
let reset = Static.TypeCheck.reset_fresh_var

open Semant.DynamicSemantObj

let assert_typechek tenv e expected =
  reset ();
  (*reset typevar generator counter*)
  let res = Static.TypeCheck.type_check tenv e in
  let witch_was_wrong =
    match (res, expected) with
    | TyRes { sub; ty }, TyRes { sub = expected_sub; ty = expected_ts } ->
        Printf.sprintf "\nWas wrong: %s"
          (if sub != expected_sub then "Subsitutions"
           else if ty != expected_ts then "Types"
           else "")
    | _, _ -> ""
  in

  fun _ ->
    assert_bool
      (Printf.sprintf "expected %s but got %s\n%s" (string_of_tyres res)
         (string_of_tyres expected) witch_was_wrong)
      (res = expected)

let assert_typechek_empty_te e expected = assert_typechek TEnv.empty e expected
let mk_base_val x = Semant.Ast.BaseVal x
let mk_int x = mk_base_val (Int x)
let mk_bool x = mk_base_val (Bool x)
let id_fun = Lambda { var = "x"; exp = Var "x" }
let r s t = TyRes { sub = s; ty = t }
let typ_of_ts = Static.Utils.typ_from_typescheme
let mk_ty_pair f s = PairVar { first = f; second = s }
let mk_ty_con x = TyCon x
let ty_int = mk_ty_con Int
let ty_bool = mk_ty_con Bool
let x = Var "x"
let q1 = TyVar (mk_tyvar "q1")
let q2 = TyVar (mk_tyvar "q2")

let mk_tenv (mappings : (var * type_scheme) list) : tenv =
  List.fold_left
    (fun acc mapping ->
      let v, ts = mapping in
      TEnv.add v ts acc)
    TEnv.empty mappings

let mk_ts (forall_quantified : string list) (ty : typ) : type_scheme =
  List.fold_left
    (fun acc t -> ForAll { tv = mk_tyvar t; ts = acc })
    (Typ ty)
    (List.rev forall_quantified)

let sub_te = Static.Substitute.substitute_tenv

let ty_cons_suite =
  [
    "10: int" >:: assert_typechek_empty_te (mk_int 10) (r id_sub ty_int);
    "True: bool" >:: assert_typechek_empty_te (mk_bool true) (r id_sub ty_bool);
  ]

let vars_suite =
  [
    "x not in tenv" >:: assert_typechek_empty_te x Fail;
    ("W(x, {x->[q1, q2].int} )"
    >::
    let init_tenv = mk_tenv [ ("x", mk_ts [ "q1"; "q2" ] ty_int) ] in
    (* let expected_ts = mk_ts [ "t0"; "t1" ] ty_int in *)
    assert_typechek init_tenv x (r id_sub ty_int));
    ("W(x, {x->[q1].(q1, q2)} )"
    >::
    let p = mk_ty_pair q1 q2 in
    let init_tenv = mk_tenv [ ("x", mk_ts [ "q1" ] p) ] in
    (*{x->(forall q1. (q1 x q2))}*)
    let p_new = mk_ty_pair (TyVar (mk_tyvar "t0")) (TyVar (mk_tyvar "q2")) in
    (* let expected_ts = mk_ts [ "t0" ] p_new in *)
    assert_typechek init_tenv x (r id_sub p_new));
  ]

let abstraction_suite =
  [
    ("W(λ.x.x, {})"
    >::
    let expected_ts = ty_id_fun in
    assert_typechek_empty_te id_fun (r id_sub expected_ts));
    ("W(λ.x.x, {x->[q0].q0})"
    >::
    let init_tenv = mk_tenv [ ("x", mk_ts [ "q1" ] q1) ] in
    let expected_ts = ty_id_fun in
    assert_typechek init_tenv id_fun (r id_sub expected_ts));
  ]

let application_suite =
  [
    ("W([(λ.x.x)(10), {}])"
    >::
    let expected_ts = ty_int in
    let expected_sub =
      mk_sub [ (mk_tyvar "t0", typ_int); (mk_tyvar "t1", typ_int) ]
    in
    assert_typechek_empty_te
      (App { e1 = id_fun; e2 = mk_int 10 })
      (r expected_sub expected_ts));
  ]

let let_suite =
  [
    ("W([let id = (λx.x) in id 3, {}])"
    >::
    let expected_ts = ty_int in
    let expected_sub =
      mk_sub [ (mk_tyvar "t1", typ_int); (mk_tyvar "t2", typ_int) ]
    in
    assert_typechek_empty_te
      (Let
         { var = "id"; e1 = id_fun; e2 = App { e1 = Var "id"; e2 = mk_int 3 } })
      (r expected_sub expected_ts));
  ]

let pair_suite =
  [
    ("W([(3, false), {}])"
    >::
    let expected_ts = PairVar { first = ty_int; second = ty_bool } in
    let expected_sub = mk_sub [] in
    assert_typechek_empty_te
      (mk_pair (mk_int 3) (mk_bool false))
      (r expected_sub expected_ts));
  ]

let index_suite =
  [
    ("W([first(3, false), {}])"
    >::
    let expected_ts = ty_int in
    let expected_sub =
      mk_sub [ (mk_tyvar "t0", typ_int); (mk_tyvar "t1", ty_bool) ]
    in
    assert_typechek_empty_te
      (First (mk_pair (mk_int 3) (mk_bool false)))
      (r expected_sub expected_ts));
    ("W([second(3, false), {}])"
    >::
    let expected_ts = ty_bool in
    let expected_sub =
      mk_sub [ (mk_tyvar "t0", typ_int); (mk_tyvar "t1", ty_bool) ]
    in
    assert_typechek_empty_te
      (Second (mk_pair (mk_int 3) (mk_bool false)))
      (r expected_sub expected_ts));
  ]

let test_regular_typecheker =
  "typecheker W test suite"
  >::: vars_suite @ ty_cons_suite @ abstraction_suite @ application_suite
       @ let_suite @ pair_suite @ index_suite
