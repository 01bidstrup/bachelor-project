open Semant.Ast
open Semant.StaticSemantObj
open Pretty.StringOf

(** Compose substitutionts as such: S2 S1*)
let rec substitute_typescheme sub type_scheme : type_scheme =
  match type_scheme with
  | Typ typ -> Typ (substitute_typ sub typ)
  | ForAll { tv; ts } ->
      if SubstitutionMap.mem tv sub then
        let tv =
          match SubstitutionMap.find tv sub with
          | TyVar tv -> tv
          | _ -> raise (Invalid_argument "Not a type variable")
        in
        ForAll { tv; ts = substitute_typescheme sub ts }
        (* if no mapping exists then default to ID,
           since the sub is always composite with ID*)
      else ForAll { tv; ts = substitute_typescheme sub ts }

and substitute_typ sub typ =
  match typ with
  | TyCon tc -> TyCon tc
  | TyVar tv -> ( try SubstitutionMap.find tv sub with Not_found -> TyVar tv)
  | FunVar { source; target } ->
      FunVar
        {
          source = substitute_typ sub source;
          target = substitute_typ sub target;
        }
  | PairVar { first; second } ->
      PairVar
        { first = substitute_typ sub first; second = substitute_typ sub second }

and substitute_tenv sub tenv =
  TEnv.fold
    (fun v t tenv' -> TEnv.add v (substitute_typescheme sub t) tenv')
    tenv TEnv.empty

let compose (s1 : substitition) (s2 : substitition) : substitition =
  (*list keys in s1*)
  let get_keys sub =
    let keys, _ = SubstitutionMap.bindings sub |> List.split in
    keys
  in
  let all_unique_keys =
    List.fold_left
      (fun acc a -> if List.mem a acc then acc else a :: acc)
      (get_keys s1) (get_keys s2)
  in

  let list_of_values_in_new_s =
    all_unique_keys
    |> List.map (fun tv -> substitute_typ s1 (TyVar tv))
    |> List.map (fun ty -> substitute_typ s2 ty)
  in

  List.fold_left
    (fun acc (k, v) -> SubstitutionMap.add k v acc)
    SubstitutionMap.empty
    (List.combine all_unique_keys list_of_values_in_new_s)

let ( @@@ ) s2 s1 : substitition = compose s1 s2
