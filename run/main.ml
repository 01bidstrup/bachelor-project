open Semant.Ast
open Semant.DynamicSemantObj
open Semant.StaticSemantObj
open Dynamic.Eval
open Static
open TypeCheck
open OptimizedTypeCheck
open Static.Unify
open Pretty.StringOf
open Static.Utils
open Dynamic.Utils

let run e i =
  Printf.printf "Example %s:\n%s\n" (string_of_int i) (string_of_exp e);
  Printf.printf "Evaluated Result: %s\n" (string_of_result (eval e Env.empty));
  Printf.printf "Elaborated Type (Regular Type Checker): %s\n"
    (string_of_opt_tyres (type_check TEnv.empty e));
  Printf.printf "Elaborated Type (Optimised Type Checker): %s\n"
    (string_of_opt_tyres (OptimizedTypeCheck.type_check TEnv.empty e));
  print_endline "";
  ()

let () = run example_1 1
let () = run example_2 2
let () = run example_3 3
let () = run (Semant.Ast.First example_1) 4
let () = run (Semant.Ast.Second example_1) 5
let () = run (Semant.Ast.First example_3) 6
