open OUnit2
open Semant.StaticSemantObj
open Semant.Ast
open Static.UnionFind
open Pretty.StringOf
open Static.Utils

(**Length of the chain counted in number of elements. ex a-b has length 2*)
let length_of_chain (t : typ) : int =
  let rec counter (t : typ) length =
    match t with
    | TyVar tv -> (
        match !tv with
        | link, _, _ -> (
            match link with
            | NoLink _ -> length
            | LinkTo tv' -> counter tv' length + 1))
    | _ -> length
  in
  counter t 1

let rec string_of_chain (t : typ) : string =
  match t with
  | TyVar t -> (
      match !t with
      | link, _, _ -> (
          match link with
          | NoLink can_name -> can_name
          | LinkTo t -> "t->" ^ string_of_chain t))
  | _ -> string_of_typ t

let assert_find typ expected_canon =
  let canon = find typ in
  fun _ ->
    assert_bool
      (Printf.sprintf
         "Expected the type '%s' to have canonical representation '%s', \n\
          but got '%s'" (string_of_chain typ)
         (string_of_typ expected_canon)
         (string_of_typ canon))
      (expected_canon = canon)

let assert_length_of_chain typ expected_length =
  let length_of_typ = length_of_chain typ in
  fun _ ->
    assert_bool
      (Printf.sprintf "expected length %s but was %s for chain %s"
         (string_of_int expected_length)
         (string_of_int length_of_typ)
         (string_of_chain typ))
      (length_of_typ = expected_length)

let mk_tyvar_wiht_parrent lvl rank parrent_link : ty_var =
  let l = parrent_link in
  ref (l, lvl, rank)

let mk_tyvar_with_rank lvl rank x = mk_tyvar_wiht_parrent lvl rank (NoLink x)
let a = TyVar (mk_tyvar 1 "a")

let b, b_parrent =
  let c = TyVar (mk_tyvar_with_rank 0 1 "c") in
  (TyVar (mk_tyvar_wiht_parrent 0 0 (LinkTo c)), c)
(*b->c*)

(**Makes a chain of the specified length wiht the name.
    @return first element, last element and list of all types except the last in chain*)
let mk_type_chain chain_length cannon_name : typ * typ * typ list =
  let chain_length = chain_length - 1 in
  let cannon =
    TyVar
      (mk_tyvar_with_rank 0 chain_length
         (cannon_name ^ string_of_int chain_length))
  in
  let rec inner parrent length all_types : typ * typ list =
    if length < 1 then (parrent, all_types)
    else
      let length = length - 1 in
      let new_tv = TyVar (mk_tyvar_wiht_parrent 0 length (LinkTo parrent)) in
      inner new_tv length (new_tv :: all_types)
  in

  let first, all_types = inner cannon chain_length [] in
  (first, cannon, all_types)

let parameterize params test = List.map test params

let test_find =
  parameterize
    [ ty_int; ty_bool; mk_ty_pair ty_int a; mk_ty_lambda a ty_bool ]
    (fun ty -> "test find on non-tyvar" >:: assert_find ty ty)
  @ [
      "test find new tyvar that point to itself" >:: assert_find a a;
      "test find type var with a single parrent" >:: assert_find b b_parrent;
      ("test find type var with 10 parrents"
      >::
      let t, t_parrent, _ = mk_type_chain 10 "t" in
      assert_find t t_parrent);
      "test length new tyvar should be 0" >:: assert_length_of_chain a 1;
      "test length of type with single parrent has length 1"
      >:: assert_length_of_chain b 2;
      ("test length of type with 9 parrents has length 10"
      >::
      let t, _, _ = mk_type_chain 10 "t" in
      assert_length_of_chain t 10);
    ]
  @ parameterize
      (*the list of types in a chain of 10 elements after find is called*)
      (let t, _, all_types = mk_type_chain 10 "t" in
       ();
       let _ = find t in
       all_types)
      (fun t_to_test ->
        "test after list comprehension chain of length 10 becomes 9 chains og \
         length 2 + root"
        >:: assert_length_of_chain t_to_test 2)

let assert_link_kind t1 t2 expkind =
  let () = link t1 t2 in
  match (t1, t2) with
  | TyVar tv1, TyVar tv2 ->
      let kind1, _, _ = !tv1 in
      let kind2, _, _ = !tv2 in
      fun _ ->
        assert_bool
          (Printf.sprintf
             "Expected the kinds to be '%s' after linking, \nbut got '%s', '%s'"
             (string_of_tyvarkind expkind)
             (string_of_tyvarkind kind1)
             (string_of_tyvarkind kind2))
          (kind1 = expkind && kind2 = expkind)
  | _ ->
      fun _ -> assert_bool "Attempted to link non type variables in test" false

let assert_link_lvl t1 t2 explvl =
  let () = link t1 t2 in
  match (t1, t2) with
  | TyVar tv1, TyVar tv2 ->
      let _, lvl1, _ = !tv1 in
      let _, lvl2, _ = !tv2 in
      fun _ ->
        assert_bool
          (Printf.sprintf
             "Expected the levels to be '%s' after linking, \n\
              but got '%s', '%s'" (string_of_int explvl) (string_of_int lvl1)
             (string_of_int lvl2))
          (lvl1 = explvl && lvl2 = explvl)
  | _ ->
      fun _ -> assert_bool "Attempted to link non type variables in test" false

let assert_link_rank t1 t2 exprank1 exprank2 =
  let () = link t1 t2 in
  match (t1, t2) with
  | TyVar tv1, TyVar tv2 ->
      let _, _, rank1 = !tv1 in
      let _, _, rank2 = !tv2 in
      fun _ ->
        assert_bool
          (Printf.sprintf
             "Expected the ranks to be '%s', '%s' after linking, \n\
              but got '%s', '%s'" (string_of_int exprank1)
             (string_of_int exprank2) (string_of_int rank1)
             (string_of_int rank2))
          (rank1 = exprank1 && rank2 = exprank2)
  | _ ->
      fun _ -> assert_bool "Attempted to link non type variables in test" false

let a () = TyVar (mk_tyvar_with_rank 0 1 "a")
let b () = TyVar (mk_tyvar_with_rank 5 10 "b")
let c () = TyVar (mk_tyvar_with_rank 3 1 "c")

let test_link =
  [
    "test link kind" >:: assert_link_kind (a ()) (b ()) (NoLink "b");
    "test link kind swapped" >:: assert_link_kind (b ()) (a ()) (NoLink "b");
    "test link kind same rank" >:: assert_link_kind (a ()) (c ()) (NoLink "c");
    "test link level" >:: assert_link_lvl (a ()) (b ()) 0;
    "test link level swapped" >:: assert_link_lvl (b ()) (a ()) 0;
    "test link level non-zero" >:: assert_link_lvl (b ()) (c ()) 3;
    "test link rank" >:: assert_link_rank (a ()) (b ()) 1 10;
    "test link rank swapped" >:: assert_link_rank (b ()) (a ()) 10 1;
    "test link rank same" >:: assert_link_rank (a ()) (c ()) 1 2;
    "test link rank same swapped" >:: assert_link_rank (c ()) (a ()) 1 2;
    "test link rank other" >:: assert_link_rank (b ()) (c ()) 10 1;
  ]

let rec ty_equality t1 t2 =
  match (t1, t2) with
  | TyCon Int, TyCon Int | TyCon Bool, TyCon Bool -> true
  | FunVar { source = t1; target = t2 }, FunVar { source = t3; target = t4 }
  | PairVar { first = t1; second = t2 }, PairVar { first = t3; second = t4 } ->
      ty_equality t1 t3 && ty_equality t2 t4
  | TyVar a, TyVar b -> (
      let t1 = find (TyVar a) in
      let t2 = find (TyVar b) in
      match (t1, t2) with
      | TyVar a, TyVar b ->
          let kind1, _, _ = !a in
          let kind2, _, _ = !b in
          kind1 = kind2
      | _ -> ty_equality t1 t2)
  | TyVar v, t | t, TyVar v -> find (TyVar v) = t
  | _ -> false

let assert_unify t1 t2 =
  let () = unify t1 t2 in
  fun _ ->
    assert_bool
      (Printf.sprintf
         "Expected the types to be '%s', '%s' to be the same after unifying, \n\
          but they were not"
         (string_of_typ (find t1))
         (string_of_typ (find t2)))
      (ty_equality t1 t2)

let assert_unify_fail t1 t2 fail _ =
  assert_raises (UnificationFail fail) (fun () -> unify t1 t2)

let assert_unify_fail_unification t1 t2 =
  assert_unify_fail t1 t2 "Not possiple to unify"

let assert_unify_fail_occursin t1 t2 =
  assert_unify_fail t1 t2
    (Printf.sprintf "The typ '%s' occurs in '%s'" (string_of_typ t1)
       (string_of_typ t2))

let test_unify_list =
  [
    "test unify two tyvars" >:: assert_unify (a ()) (b ());
    "test unify swapped tyvars" >:: assert_unify (b ()) (a ());
    "test unify int tyvar" >:: assert_unify (TyCon Int) (a ());
    "test unify int fun"
    >:: assert_unify_fail_unification (TyCon Int) (mk_ty_lambda (a ()) (a ()));
    "test unify fun fun"
    >:: assert_unify (mk_ty_lambda (b ()) (b ())) (mk_ty_lambda (a ()) (a ()));
    "test unify intfun boolfun"
    >:: assert_unify_fail_unification
          (mk_ty_lambda (TyCon Int) (TyCon Int))
          (mk_ty_lambda (TyCon Bool) (TyCon Bool));
    "test unify pair pair"
    >:: assert_unify
          (mk_ty_pair (TyCon Int) (TyCon Bool))
          (mk_ty_pair (a ()) (a ()));
    "test unify fun pair"
    >:: assert_unify_fail_unification
          (mk_ty_lambda (TyCon Int) (TyCon Bool))
          (mk_ty_pair (a ()) (a ()));
    "test unify occurs in"
    >:: assert_unify_fail_occursin (a ()) (mk_ty_pair (a ()) (a ()));
  ]

let test_union_find =
  "union-find test suite" >::: test_find @ test_link @ test_unify_list
