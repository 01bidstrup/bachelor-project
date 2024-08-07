type var = string
type base_val = Int of int | Bool of bool

type exp =
  | BaseVal of base_val
  | Var of var
  | Lambda of { var : var; exp : exp }
  | App of { e1 : exp; e2 : exp }
  | Let of { var : var; e1 : exp; e2 : exp }
  | Pair of { first : exp; second : exp }
  | First of exp
  | Second of exp
