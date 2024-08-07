open Semant.StaticSemantObj
open Substitute
open Pretty.StringOf

type disagreement_pair = typ * typ

let rec choose_dissagreement_pair (t1 : typ) (t2 : typ) :
    disagreement_pair option =
  match (t1, t2) with
  | TyCon tc1, TyCon tc2 ->
      if tc1 = tc2 then None else Some (TyCon tc1, TyCon tc2)
  | TyVar tv1, TyVar tv2 ->
      if tv1 = tv2 then None else Some (TyVar tv1, TyVar tv2)
  | FunVar { source = s1; target = t1 }, FunVar { source = s2; target = t2 } ->
      if s1 = s2 && t1 = t2 then None
      else if s1 <> s2 then choose_dissagreement_pair s1 s2
      else choose_dissagreement_pair t1 t2
  | PairVar { first = f1; second = s1 }, PairVar { first = f2; second = s2 } ->
      if f1 = f2 && s1 = s2 then None
      else if f1 <> f2 then choose_dissagreement_pair f1 f2
      else choose_dissagreement_pair s1 s2
  | t1, t2 -> Some (t1, t2)

(**return [true] if v] occurs in [u]. *)
let rec occurs_in (v : ty_var) (u : typ) =
  match u with
  | TyCon _ -> false
  | TyVar tv -> v = tv
  | FunVar { source; target } -> occurs_in v source || occurs_in v target
  | PairVar { first; second } -> occurs_in v first || occurs_in v second

let unify (t1 : typ) (t2 : typ) : substitition option =
  let rec inner t1 t2 sk : substitition option =
    let s t = substitute_typ sk t in
    let dp = choose_dissagreement_pair (s t1) (s t2) in
    match dp with
    | None -> Some sk
    | Some (d1, d2) -> (
        match (d1, d2) with
        | TyVar v, t | t, TyVar v ->
            if occurs_in v t then
              raise
                (Invalid_argument
                   (Printf.sprintf "The typ '%s' occurs in '%s'"
                      (string_of_tyvar !v) (string_of_typ t)))
            else inner t1 t2 (SubstitutionMap.add v t id_sub @@@ sk)
        | _, _ -> None)
  in

  inner t1 t2 id_sub
