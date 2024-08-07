open Ast

module Env = Map.Make (struct
  type t = var

  let compare = compare
end)

type value = BaseVal of base_val | Clos of clos | Pair of pair
and env = value Env.t
and pair = { first : value; second : value }
and clos = { var : var; exp : exp; env : env }
and result = Val of value | Wrong
