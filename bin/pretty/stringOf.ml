open Semant.Ast
open Semant.DynamicSemantObj

let string_of_baseval (bv : base_val) =
  match bv with
  | Int i -> Printf.sprintf "%i" i
  | Bool b -> Printf.sprintf "%b" b

let rec string_of_exp (e : exp) =
  match e with
  | BaseVal bv -> string_of_baseval bv
  | Var v -> v
  | Lambda { var; exp } -> Printf.sprintf "(λ%s.%s)" var (string_of_exp exp)
  | App { e1; e2 } ->
      Printf.sprintf "(%s %s)" (string_of_exp e1) (string_of_exp e2)
  | Let { var; e1; e2 } ->
      Printf.sprintf "let %s = %s in %s" var (string_of_exp e1)
        (string_of_exp e2)
  | Pair { first; second } ->
      Printf.sprintf "(%s, %s)" (string_of_exp first) (string_of_exp second)
  | First e -> Printf.sprintf "first(%s)" (string_of_exp e)
  | Second e -> Printf.sprintf "second(%s)" (string_of_exp e)

let rec string_of_clos { var; exp; env } =
  Printf.sprintf "[%s, %s, ρ]" var (string_of_exp exp)

and string_of_pair { first; second } =
  Printf.sprintf "(%s, %s)" (string_of_val first) (string_of_val second)

and string_of_val v =
  match v with
  | BaseVal bv -> string_of_baseval bv
  | Clos c -> string_of_clos c
  | Pair p -> string_of_pair p

and string_of_result res =
  match res with Val v -> string_of_val v | Wrong -> "Wrong"

open Semant.StaticSemantObj

let string_of_tycon tc = match tc with Int -> "Int" | Bool -> "Bool"

let rec string_of_typ t =
  match t with
  | TyCon tc -> string_of_tycon tc
  | TyVar tv -> string_of_tyvar !tv
  | FunVar { source; target } ->
      Printf.sprintf "(%s->%s)" (string_of_typ source) (string_of_typ target)
  | PairVar { first; second } ->
      Printf.sprintf "(%s x %s)" (string_of_typ first) (string_of_typ second)

and string_of_tyvar (tv : tyvarkind * lvl * rank) =
  let kind, _, _ = tv in
  match kind with NoLink s -> s | LinkTo t -> string_of_typ t

let rec string_of_ts ts =
  match ts with
  | Typ tp -> string_of_typ tp
  | ForAll { tv; ts } ->
      let rec inner acc ts =
        match ts with
        | Typ t -> acc ^ "." ^ string_of_typ t
        | ForAll { tv; ts } -> string_of_tyvar !tv ^ "," ^ inner acc ts
      in
      Printf.sprintf "∀%s" (inner (string_of_tyvar !tv) ts)

let string_of_tyres res =
  match res with TyRes { ty; _ } -> string_of_typ ty | Fail -> "Fail"

let string_of_opt_tyres (res : opt_tyres) : string =
  match res with OptTyRes ty -> string_of_typ ty | Fail -> "Fail"

let string_of_sub (m : substitition) =
  Printf.sprintf "{%s}"
    (String.concat ",  "
       (SubstitutionMap.fold
          (fun k v acc ->
            Printf.sprintf "%s ↦ %s" (string_of_tyvar !k) (string_of_typ v)
            :: acc)
          m []))

let string_of_tyres res =
  match res with
  | TyRes { sub; ty } ->
      Printf.sprintf "(%s, %s)" (string_of_sub sub) (string_of_typ ty)
  | Fail -> "Fail"

let string_of_tenv (tenv : tenv) =
  Printf.sprintf "{%s}"
    (String.concat ", "
       (TEnv.fold
          (fun v ts acc -> Printf.sprintf "%s ↦ %s" v (string_of_ts ts) :: acc)
          tenv []))

let string_of_tyvarkind (tk : tyvarkind) =
  match tk with NoLink s -> s | LinkTo t -> "->" ^ string_of_typ t
