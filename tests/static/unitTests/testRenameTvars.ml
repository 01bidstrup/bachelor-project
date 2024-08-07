open OUnit2
open Semant.StaticSemantObj
open Semant.Ast
open Pretty.StringOf
open Static.Rename
open Static.FreshTvars
open Static.Utils

let fresh_tvar, reset_fresh_var = fresh_and_reset ()

let assert_rename lvl (ts : type_scheme) (expect : typ) =
  reset_fresh_var ();
  let (new_typ : typ) = rename_tvars ts (fun () -> fresh_tvar lvl "t") in
  fun _ ->
    assert_bool
      (Printf.sprintf "On input %s Expected type: %s when renaming but got: %s"
         (string_of_ts ts) (string_of_typ expect) (string_of_typ new_typ))
      (new_typ = expect)

let q1 lvl = TyVar (mk_tyvar lvl "q1")
let q2 lvl = TyVar (mk_tyvar lvl "q2")
let t0 lvl = TyVar (mk_tyvar lvl "t0")
let t1 lvl = TyVar (mk_tyvar lvl "t1")

let test_rename_tvars =
  "rename tvars testsuite"
  >::: [
         ("∀q1.q1->q1 should be renamed to t0->t0"
         >::
         let q1 = q1 2 in
         let input = mk_ts_lvl [ ("q1", 2) ] (mk_ty_lambda q1 q1) in
         let lvl = 3 in
         let t0 = t0 lvl in
         let expected = mk_ty_lambda t0 t0 in
         assert_rename lvl input expected);
       ]
       @ [
           ("∀q1.q1->q2 should be renamed to t0->q2"
           >::
           let q1 = q1 2 in
           let q2 = q2 2 in
           let lvl = 3 in
           let t0 = t0 lvl in
           let input = mk_ts_lvl [ ("q2", 2) ] (mk_ty_lambda q1 q2) in
           let expected = mk_ty_lambda q1 t0 in
           assert_rename lvl input expected);
         ]
