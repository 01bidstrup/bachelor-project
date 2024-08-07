open OUnit2
open Semant.StaticSemantObj
open Semant.Ast
open Pretty.StringOf
open Static.Rename
open Static.FreshTvars
open Static.Utils
open Static.Substitute

let assert_subsitute sub_fun string_of (sub : substitition) test expected =
  let test_sustitued = sub_fun test in
  fun _ ->
    assert_bool
      (Printf.sprintf "With S=%s applied on %s  expected %s but got: %s"
         (string_of_sub sub) (string_of test) (string_of expected)
         (string_of test_sustitued))
      (test_sustitued = expected)

let assert_subsitute_typ sub =
  ((assert_subsitute (substitute_typ sub)) string_of_typ) sub

let assert_subsitute_ts sub =
  ((assert_subsitute (substitute_typescheme sub)) string_of_ts) sub

let assert_subsitute_tenv sub =
  ((assert_subsitute (substitute_tenv sub)) string_of_tenv) sub

let mk_tyvar = mk_tyvar 0

(* mk_sub  *)
let a = mk_tyvar "a"
let b = mk_tyvar "b"
let c = mk_tyvar "c"
let d = mk_tyvar "d"
let e = mk_tyvar "e"
let f = mk_tyvar "f"
let parameterize params test = List.map test params
let sub = mk_sub [ (mk_tyvar "t0", t1); (mk_tyvar "t2", ty_bool) ]

let test_substitute =
  "substitute testsuite"
  >::: []
       @ parameterize
           [ t0; mk_ty_lambda t0 t1; mk_ty_pair t1 t0; mk_ty_con Int ]
           (fun ty ->
             "ID sub should give the same" >:: assert_subsitute_typ id_sub ty ty)
       @ parameterize
           [
             (t0, t1);
             (t2, ty_bool);
             (mk_ty_lambda t0 t1, mk_ty_lambda t1 t1);
             ( mk_ty_lambda t0 (mk_ty_lambda t1 t2),
               mk_ty_lambda t1 (mk_ty_lambda t1 ty_bool) );
           ]
           (fun (got, expected) ->
             "Sub on " >:: assert_subsitute_typ sub got expected)
       @ [
           ("Subsititute a->b wiht {a->(b->c), b->(a->c)}"
           >::
           let sub =
             mk_sub
               [
                 (a, mk_ty_lambda (TyVar b) (TyVar c));
                 (b, mk_ty_lambda (TyVar a) (TyVar c));
               ]
           in
           let ty = mk_ty_lambda (TyVar a) (TyVar b) in
           let expected =
             mk_ty_lambda
               (mk_ty_lambda (TyVar b) (TyVar c))
               (mk_ty_lambda (TyVar a) (TyVar c))
           in
           assert_subsitute_typ sub ty expected);
         ]
       @ parameterize
           [
             (Typ t0, Typ t1);
             (mk_ts_0 [] t0, mk_ts_0 [] t1);
             (mk_ts_0 [ "t0" ] t0, mk_ts_0 [ "t1" ] t1);
           ]
           (fun (got, expected) ->
             "Sub on typescheme" >:: assert_subsitute_ts sub got expected)
       @ parameterize
           [
             ( mk_tenv [ ("x", Typ t0); ("y", Typ t2) ],
               mk_tenv [ ("x", Typ t1); ("y", Typ ty_bool) ] );
           ]
           (fun (got, expected) ->
             "Sub on typescheme" >:: assert_subsitute_tenv sub got expected)

(* let overlapping_subs = (mk_sub [ (mk_tyvar "t0", t1); (mk_tyvar "t1", ty_bool) ],
   mk_sub [ (mk_tyvar "t1", t2)]) *)

(** assrert composition of subs Notice the composition order is sub2 sub1 unlike compose function*)
let assert_compose (sub1 : substitition) (sub2 : substitition)
    (expected : substitition) =
  let composed = sub2 @@@ sub1 in
  (*apply first s1, then s2*)
  fun _ ->
    assert_bool
      (Printf.sprintf
         "With S1=%s and S2=%s aplied S2 S1 expected compose %s but got: %s"
         (string_of_sub sub1) (string_of_sub sub2) (string_of_sub expected)
         (string_of_sub composed))
      (sub_equal composed expected)

let test_compose =
  "compose testsuite"
  >::: []
       @ parameterize
           [ (id_sub, id_sub, id_sub); (id_sub, sub, sub) ]
           (fun (s1, s2, expected) ->
             "ID should compose to sake" >:: assert_compose s1 s2 expected)
       @ parameterize
           (let test_set1 =
              ( mk_sub [ (a, TyVar b) ],
                mk_sub [ (c, TyVar a) ],
                mk_sub [ (a, TyVar b); (c, TyVar a) ] )
            in
            let test_set2 =
              ( mk_sub [ (a, TyVar c) ],
                mk_sub [ (a, TyVar b); (c, TyVar d) ],
                mk_sub [ (a, TyVar d); (c, TyVar d) ] )
            in
            let test_set3 =
              ( mk_sub [ (a, TyVar b); (b, TyVar a) ],
                mk_sub [ (a, TyVar c); (b, TyVar d) ],
                mk_sub [ (a, TyVar d); (b, TyVar c) ] )
            in
            let test_set4 =
              ( mk_sub [ (a, TyVar b); (b, TyVar c); (d, TyVar a) ],
                mk_sub [ (a, TyVar e); (c, TyVar f) ],
                mk_sub
                  [ (a, TyVar b); (b, TyVar f); (d, TyVar e); (c, TyVar f) ] )
            in
            [ test_set1; test_set2; test_set3; test_set4 ])
           (fun (s1, s2, expected) ->
             "Overlapping subs" >:: assert_compose s1 s2 expected)
       @ parameterize
           (let test_set1 mk_ty =
              ( mk_sub [ (a, mk_ty (TyVar b) (TyVar c)) ],
                mk_sub [ (b, TyVar c) ],
                mk_sub [ (a, mk_ty (TyVar c) (TyVar c)); (b, TyVar c) ] )
            in
            [ test_set1 mk_ty_lambda; test_set1 mk_ty_pair ])
           (fun (s1, s2, expected) ->
             "subs with bigger types" >:: assert_compose s1 s2 expected)

(* @ parameterize [(let s1, s2 = overlapping_subs in (s1, s2, id_sub)); ]
   (fun (s1, s2, expected) ->
     "composing overlappijg"
     >:: assert_compose s1 s2 expected)
*)
