open Semant.Ast
open Semant.StaticSemantObj
open Substitute
open Unify
open Pretty.StringOf

let fresh_and_reset () =
  let c = ref 0 in
  let fresh lvl char =
    let n = !c in
    c := n + 1;
    mk_tyvar lvl (char ^ string_of_int n)
  in
  let reset () = c := 0 in
  (fresh, reset)
