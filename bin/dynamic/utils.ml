open Semant.DynamicSemantObj
open Semant.Ast

let mk_base_val x = Semant.Ast.BaseVal x
let mk_int x = mk_base_val (Int x)
let mk_bool x = mk_base_val (Bool x)
let mk_var x = Semant.Ast.Var x
let mk_lambda x e = Lambda { var = x; exp = e }
let mk_pair a b = Pair { first = a; second = b }
let mk_app fn arg = App { e1 = fn; e2 = arg }
let mk_let id e1 e2 = Let { var = id; e1; e2 }
let id_fun = mk_lambda "x" (mk_var "x")
let double_fun a = mk_lambda "x" (mk_pair a a)

let mk_fun_mul_args (args : var list) (body : exp) =
  List.fold_left (fun acc x -> mk_lambda x acc) body (List.rev args)

let mk_env (mappings : (var * value) list) : env =
  List.fold_left
    (fun acc mapping ->
      let v, ts = mapping in
      Env.add v ts acc)
    Env.empty mappings

let example_1 =
  (*et id = λ x.x in ( id 3, id false)*)
  mk_let "id" (mk_lambda "x" (Var "x"))
    (mk_pair (mk_app (Var "id") (mk_int 3)) (mk_app (Var "id") (mk_bool false)))

let example_2 =
  (*λ id.( id 3, id false)(λ x.x)*)
  mk_app
    (mk_lambda "id"
       (mk_pair
          (mk_app (Var "id") (mk_int 3))
          (mk_app (Var "id") (mk_bool false))))
    (mk_lambda "x" (Var "x"))

let e2 =
  Semant.Ast.Pair
    {
      first = App { e1 = Var "f"; e2 = BaseVal (Int 3) };
      second = App { e1 = Var "f"; e2 = BaseVal (Bool false) };
    }

let example_3 =
  (* λ y.let f = λ x.(x, y) in ( f 3, f false) *)
  let e1 = mk_lambda "x" (mk_pair (Var "x") (Var "y")) in

  let e2 =
    mk_pair (mk_app (Var "f") (mk_int 3)) (mk_app (Var "f") (mk_bool false))
  in

  mk_lambda "y" (mk_let "f" e1 e2)

let example_4 = Semant.Ast.First example_1
