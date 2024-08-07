open Semant.StaticSemantObj
open Unify
open Pretty.StringOf

exception UnificationFail of string

let rec find (t : typ) : typ =
  let rec find_can (t : typ) : typ =
    match t with
    | TyVar tv -> (
        let link, _, _ = !tv in
        match link with NoLink _ -> t | LinkTo t' -> find_can t')
    | _ -> t
  in
  let rec path_comprehend (t : typ) (can_t : typ) : unit =
    match t with
    | TyVar tv -> (
        let link, lvl, rank = !tv in
        match link with
        | NoLink _ -> ()
        | LinkTo old_parrent ->
            tv := (LinkTo can_t, lvl, rank);
            path_comprehend old_parrent can_t)
    | _ -> ()
  in
  let res = find_can t in
  let () = path_comprehend t res in
  res

let link x y : unit =
  match (x, y) with
  | TyVar t_x, TyVar t_y ->
      let kind_x, lvl_x, rank_x = !t_x in
      let kind_y, lvl_y, rank_y = !t_y in

      let min_lvl = Int.min lvl_x lvl_y in
      (* lowest level*)
      let kind_with_greatest_rank =
        if rank_x > rank_y then kind_x else kind_y
      in

      t_x := (kind_with_greatest_rank, min_lvl, rank_x);
      t_y :=
        ( kind_with_greatest_rank,
          min_lvl,
          if rank_x = rank_y then rank_y + 1 else rank_y )
  | TyVar t1, a | a, TyVar t1 ->
      let _, lvl, rank = !t1 in
      t1 := (LinkTo a, lvl, rank)
  | _ -> raise (UnificationFail "was not tyvars")

let union (n1 : typ) (n2 : typ) = link (find n1) (find n2)

let rec unify (t1 : typ) (t2 : typ) : unit =
  match (t1, t2) with
  | TyCon Int, TyCon Int | TyCon Bool, TyCon Bool -> ()
  | FunVar { source = t1; target = t2 }, FunVar { source = t3; target = t4 }
  | PairVar { first = t1; second = t2 }, PairVar { first = t3; second = t4 } ->
      let () = unify t1 t3 in
      unify t2 t4
  | TyVar a, TyVar b -> if a = b then () else union (TyVar a) (TyVar b)
  | TyVar v, t | t, TyVar v -> unify_typevar_and_typ v t
  | _ -> raise @@ UnificationFail "Not possiple to unify"

and unify_typevar_and_typ v t =
  if occurs_in v t then
    raise
      (UnificationFail
         (Printf.sprintf "The typ '%s' occurs in '%s'" (string_of_tyvar !v)
            (string_of_typ t)))
  else union (TyVar v) t
