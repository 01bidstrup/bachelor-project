open OUnit2
open Semant.Ast
open Semant.StaticSemantObj
open Static.TypeCheck
open Pretty.StringOf
open Dynamic.Utils
open Static.Utils
open Static.Rename
open Static.FreshTvars
open Static.Substitute

let assert_type (typecheck_fun : tenv -> exp -> tyres) tag exp expected_typ =
  Static.TypeCheck.reset_fresh_var ();
  Static.OptimizedTypeCheck.reset_fresh_var ();
  let res = typecheck_fun TEnv.empty exp in
  let typed, resmsg =
    match res with
    | Fail -> (false, "Fail")
    | TyRes { ty; _ } -> (ty = expected_typ, string_of_typ ty)
  in

  fun _ ->
    assert_bool
      (Printf.sprintf
         "[%s] Expected the expression '%s' to have type '%s', \nbut got '%s'"
         tag (string_of_exp exp)
         (string_of_typ expected_typ)
         resmsg)
      typed

let assert_typfail (typecheck_fun : tenv -> exp -> tyres) tag exp =
  let res = typecheck_fun TEnv.empty exp in
  let typfail, resmsg =
    match res with
    | Fail -> (true, "Fail")
    | TyRes { ty; _ } -> (false, string_of_typ ty)
  in
  fun _ ->
    assert_bool
      (Printf.sprintf
         "[%s]Expected the expression '%s' to fail typechecking, \n\
          but instead got '%s'" tag (string_of_exp exp) resmsg)
      typfail

let typ_int = TyCon Int
let typ_bool = TyCon Bool
let typ_pair_int_bool = PairVar { first = typ_int; second = typ_bool }
let e10 = mk_int 10
let etrue = mk_bool true
let exp_lambda_app e1 e2 = App { e1; e2 }
let exp_pair_int_bool = mk_pair e10 etrue
let exp_lambda_fail = mk_lambda "x" (Var "y")
let mk_tyvar = mk_tyvar 0

let test_typeCheck (typecheck_fun : tenv -> exp -> tyres) tag =
  let assert_type = assert_type typecheck_fun tag in
  let assert_typfail = assert_typfail typecheck_fun tag in

  let base_vals_tests =
    [
      "test typecheck int" >:: assert_type e10 typ_int;
      "test typecheck bool" >:: assert_type etrue typ_bool;
    ]
  in
  let lambda_tests =
    [
      "test typecheck lambda"
      >:: assert_type id_fun
            (FunVar
               {
                 source = TyVar (mk_tyvar "t0");
                 target = TyVar (mk_tyvar "t0");
               });
      "test fail typecheck lambda" >:: assert_typfail exp_lambda_fail;
    ]
  in
  let app_tests =
    [
      "test typecheck app int"
      >:: assert_type (exp_lambda_app id_fun e10) typ_int;
      "test typecheck app bool"
      >:: assert_type (exp_lambda_app id_fun etrue) typ_bool;
      "test fail typecheck app"
      >:: assert_typfail (exp_lambda_app exp_lambda_fail e10);
    ]
  in
  let pair_tests =
    [
      "test typecheck pair" >:: assert_type exp_pair_int_bool typ_pair_int_bool;
      "test typecheck first" >:: assert_type (First exp_pair_int_bool) typ_int;
      "test typecheck second"
      >:: assert_type (Second exp_pair_int_bool) typ_bool;
      "test fail pair" >:: assert_typfail (mk_pair e10 (Var "x"));
      "test fail first" >:: assert_typfail (First e10);
      "test fail second" >:: assert_typfail (First etrue);
    ]
  in

  let let_tests =
    [
      "test let generalizes id fun in let id = λ x.x in ( id 3, id false)"
      >:: assert_type example_1 (typ_from_typescheme example_1_typ);
      "test fail in λ id.( id 3, id false)(λ x.x)" >:: assert_typfail example_2;
      "test let generalizes type for x but not for y in λ y.let f = λ x.(x, y) \
       in ( f 3, f false)"
      >:: assert_type example_3 (typ_from_typescheme example_3_typ);
    ]
  in
  "typechek test suite"
  >::: base_vals_tests @ lambda_tests @ app_tests @ pair_tests @ let_tests

let _fun a b c = a (b c)
let a = _fun (fun _ -> 10) (fun _ -> true) 10
let b = _fun (fun _ -> true) (fun _ -> 10) true
