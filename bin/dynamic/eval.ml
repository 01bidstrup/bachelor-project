open Semant.Ast
open Semant.DynamicSemantObj

let rec eval (exp : exp) (env : env) : result =
  match exp with
  | BaseVal bv -> Val (BaseVal bv)
  | Var v -> eval_lookup v env
  | Lambda { var; exp } -> eval_lambda_abs var exp env
  | App { e1; e2 } -> eval_app e1 e2 env
  | Let { var; e1; e2 } -> eval_let var e1 e2 env
  | Pair { first; second } -> eval_pair first second env
  | First e -> eval_first e env
  | Second e -> eval_second e env

and eval_lookup var env = try Val (Env.find var env) with Not_found -> Wrong
and eval_lambda_abs var exp env = Val (Clos { var; exp; env })

and eval_app e1 e2 env =
  match eval e1 env with
  | Val v -> (
      match v with
      | Clos { var; exp = e0; env = env0 } -> (
          match eval e2 env with
          | Val v ->
              let env0 = Env.add var v env0 in
              eval e0 env0
          | Wrong -> Wrong)
      | _ -> Wrong)
  | Wrong -> Wrong

and eval_let var e1 e2 env =
  match eval e1 env with
  | Val v ->
      let env = Env.add var v env in
      eval e2 env
  | Wrong -> Wrong

and eval_pair first second env =
  match eval first env with
  | Val v1 -> (
      match eval second env with
      | Val v2 -> Val (Pair { first = v1; second = v2 })
      | Wrong -> Wrong)
  | Wrong -> Wrong

and eval_first exp env =
  match eval exp env with Val (Pair { first; _ }) -> Val first | _ -> Wrong

and eval_second exp env =
  match eval exp env with Val (Pair { second; _ }) -> Val second | _ -> Wrong
