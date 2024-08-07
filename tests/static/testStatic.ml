open OUnit2
open UnitTests
open IntegrationTests
open TestUnify
open TestTypeCheck
open Semant.StaticSemantObj
open TestRenameTvars
open TestSubstitute
open TestUnionFind
open TestTypeCheckUnit

let wrap_opt_tyres opt_tyres : tyres =
  match opt_tyres with
  | Fail -> Fail
  | OptTyRes type_scheme -> TyRes { sub = id_sub; ty = type_scheme }

let optimized_typecheck t e =
  wrap_opt_tyres (Static.OptimizedTypeCheck.type_check t e)

let () =
  List.iter run_test_tt_main
    [
      test_typeCheck Static.TypeCheck.type_check "Regular";
      test_typeCheck optimized_typecheck "Optimized";
      test_occurs_in;
      test_choose_dissagreement_pair;
      test_unify;
      test_rename_tvars;
      test_regular_typecheker;
      test_substitute;
      test_compose;
      test_union_find;
    ]
