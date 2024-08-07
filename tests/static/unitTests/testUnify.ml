open OUnit2
open Semant.StaticSemantObj
open Semant.Ast
open Pretty.StringOf
open Static.Unify
open Static.Utils
open Dynamic.Utils

let mk_tyvar x = mk_tyvar 0 x
let var_t = mk_tyvar "t"
let var_t2 = mk_tyvar "t2"
let typ_bool = TyCon Bool
let typ_int = TyCon Int
let typ_t = TyVar (mk_tyvar "t")
let typ_t2 = TyVar (mk_tyvar "t2")
let typ_int_to_int = FunVar { source = typ_int; target = typ_int }
let typ_t_to_int = FunVar { source = typ_t; target = typ_int }
let typ_int_to_t = FunVar { source = typ_int; target = typ_t }
let typ_t_to_t = FunVar { source = typ_t; target = typ_t }
let typ_int_and_int = PairVar { first = typ_int; second = typ_int }
let typ_t_and_int = PairVar { first = typ_t; second = typ_int }
let typ_int_and_t = PairVar { first = typ_int; second = typ_t }
let typ_t_and_t = PairVar { first = typ_t; second = typ_t }

let typ_t_to_t2_and_t =
  FunVar { source = typ_t; target = PairVar { first = typ_t2; second = typ_t } }
(* t -> (t2, t) *)

let typ_int_to_t_and_t2 =
  FunVar
    { source = typ_int; target = PairVar { first = typ_t; second = typ_t2 } }
(* int -> (t, t2)  *)

let assert_occurs_in (v : ty_var) (u : typ) expect _ =
  assert_bool
    (Printf.sprintf "Expected '%s' to occur in the typ:\n%s\nbut it does not."
       (string_of_tyvar !v) (string_of_typ u))
    (occurs_in v u = expect)

let test_occurs_in =
  "occurs_in test suite"
  >::: [
         "t not in false" >:: assert_occurs_in var_t typ_bool false;
         "t in t" >:: assert_occurs_in var_t typ_t true;
         "t not in int -> int" >:: assert_occurs_in var_t typ_int_to_int false;
         "t in t -> int" >:: assert_occurs_in var_t typ_t_to_int true;
         "t in int -> t" >:: assert_occurs_in var_t typ_int_to_t true;
         "t in t -> t" >:: assert_occurs_in var_t typ_t_to_t true;
         "t not in (int x int)" >:: assert_occurs_in var_t typ_int_and_int false;
         "t in (t x int)" >:: assert_occurs_in var_t typ_t_and_int true;
         "t in (int x t)" >:: assert_occurs_in var_t typ_int_and_t true;
         "t in (t x t)" >:: assert_occurs_in var_t typ_t_and_t true;
         "t2 not in t -> t" >:: assert_occurs_in var_t2 typ_t_to_t false;
         "t2 not in (t x t)" >:: assert_occurs_in var_t2 typ_t_and_t false;
       ]

let assert_dissagreement_pair t1 t2 expect =
  let string_of_expected_disagreement_pair (pair : disagreement_pair option) =
    match pair with
    | None -> "None"
    | Some (d1, d2) ->
        Printf.sprintf "(%s, %s)" (string_of_typ d1) (string_of_typ d2)
  in
  fun _ ->
    assert_bool
      (string_of_expected_disagreement_pair expect)
      (choose_dissagreement_pair t1 t2 = expect)

(** Test choose_dissagreement_pair *)
let test_choose_dissagreement_pair =
  "choose_dissagreement_pair test suite"
  >::: [
         "t disagree t" >:: assert_dissagreement_pair typ_t typ_t None;
         "int disagree int" >:: assert_dissagreement_pair typ_int typ_int None;
         "t disagree t2"
         >:: assert_dissagreement_pair typ_t typ_t2 (Some (typ_t, typ_t2));
         "t->t disagree t->t"
         >:: assert_dissagreement_pair typ_t_to_t typ_t_to_t None;
         "t->t disagree t->int"
         >:: assert_dissagreement_pair typ_t_to_t typ_t_to_int
               (Some (typ_t, typ_int));
         "int->t disagree t->int"
         >:: assert_dissagreement_pair typ_int_to_t typ_t_to_int
               (Some (typ_int, typ_t));
         "int->int disagree t->t"
         >:: assert_dissagreement_pair typ_int_to_int typ_t_to_t
               (Some (typ_int, typ_t));
         "(t x t) disagree (t x t)"
         >:: assert_dissagreement_pair typ_t_and_t typ_t_and_t None;
         "(t x t) disagree (t x int)"
         >:: assert_dissagreement_pair typ_t_and_t typ_t_and_int
               (Some (typ_t, typ_int));
         "(int x t) disagree (t x int)"
         >:: assert_dissagreement_pair typ_int_and_t typ_t_and_int
               (Some (typ_int, typ_t));
         "(int x int) disagree (t x t)"
         >:: assert_dissagreement_pair typ_int_and_int typ_t_and_t
               (Some (typ_int, typ_t));
         "t->t disagree (int x int)"
         >:: assert_dissagreement_pair typ_t_to_t typ_int_and_int
               (Some (typ_t_to_t, typ_int_and_int));
         "t disagree int->int"
         >:: assert_dissagreement_pair typ_t typ_int_to_int
               (Some (typ_t, typ_int_to_int));
       ]

let assert_unify t1 t2 expect =
  let s = unify t1 t2 in
  fun _ ->
    assert_bool
      (Printf.sprintf
         "Expected substitution:\n%s\nwhen unifying %s and %s, but got:\n%s"
         (string_of_sub expect) (string_of_typ t1) (string_of_typ t2)
         (match s with None -> "None" | Some sub -> string_of_sub sub))
      (subo_equal (unify t1 t2) (Some expect))

let assert_unify_fail t1 t2 _ =
  assert_raises
    (Invalid_argument
       (Printf.sprintf "The typ '%s' occurs in '%s'" (string_of_typ t1)
          (string_of_typ t2)))
    (fun () -> unify t1 t2)

let test_unify =
  "unify test suite"
  >::: [
         "t unify t2"
         >:: assert_unify typ_t typ_t2
               (SubstitutionMap.add (mk_tyvar "t") typ_t2 id_sub);
         "t unify t->t" >:: assert_unify_fail typ_t typ_t_to_t;
         "(int x int) unify (t x t)"
         >:: assert_unify typ_int_and_int typ_int_and_t
               (SubstitutionMap.add (mk_tyvar "t") typ_int id_sub);
         "t -> (t2, t) unify  int -> (t, t2) "
         >:: assert_unify typ_t_to_t2_and_t typ_int_to_t_and_t2
               (SubstitutionMap.add (mk_tyvar "t2") typ_int
                  (SubstitutionMap.add (mk_tyvar "t") typ_int id_sub));
       ]
