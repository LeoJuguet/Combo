open Combo.Entry
open Combo

let rec solver_1 formule =
  match formule with
  | Func ("=",[|a;b|]) -> if a = b then SAT([])
        else UNSAT
  | And fs -> if List.for_all (fun f -> solver_1 f <> UNSAT) fs then
                SAT [] else UNSAT
  | _ -> UNSAT



let () =
  let theories = [|
    new_theorie [""] ["=",[Some ""; Some ""]] ["a", Some ""] solver_1
  |] in
  let a = solve_entry (And [Func("=",[|Var("a"); Var("a")|])], theories) in
  match a with
  | SAT _ -> ()
  | UNSAT -> failwith "unsat"



(* Example *)


let rec solver_theory_f formule =
  match formule with
  | Func (">=",_) | Func ("<=",_ ) -> failwith "problem"
  | Func ("f", _) -> SAT []
  | Func ("=",_) -> SAT []
  | And fa -> if List.for_all (fun f -> solver_theory_f f <> UNSAT) fa then
      SAT [] else UNSAT
  | _ -> failwith "todo"


let () =
  let f =
    And [
      Func(">=", [|Func("f",[|Var "x1"; Const (Intv 0) |]); Var "x3"|]);
      Func("<=", [|Func("f",[|Var "x2"; Const (Intv 0) |]); Var "x3"|]);
      Func(">=", [|Var "x1"; Var "x2"|]);
      Func(">=", [|Var "x2"; Var "x1"|]);
      Func(">=", [|
          Func("-",[|Var "x3"; Func("f", [|Var "x1"; Const (Intv 0)|])|]);
          Const (Intv 0)
        |])
    ] in
  let theories = [|
    new_theorie ["int"] ["f", [Some "int"; Some "int"]; "=", [Some "int"; Some "int"]] [] solver_theory_f;
    new_theorie ["int"] [">=", [Some "int"; Some "int"]; "<=", [Some "int"; Some "int"]; "=", [Some "int"; Some "int"]] [] solver_1;
    new_theorie ["int"] ["-", [Some "int"; Some "int"]; "=", [Some "int"; Some "int"]] [] solver_1
  |]
  in
  match solve_entry (f,theories) with
  | SAT _ -> failwith "etonnant"
  | UNSAT -> failwith "ok"
