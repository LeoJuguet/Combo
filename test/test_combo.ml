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
  let a = solve_entry (And [Func("=",[|Var("a"); Var("a")|])]) theories in
  match a with
  | SAT _ -> ()
  | UNSAT -> failwith "unsat"



(* Example *)


let solver_theory_f formule =
  let rec solver_theory_f_aux f equality =
    match equality with
    | UNSAT -> UNSAT
    | SAT eq_sat ->
    match f with
    | Func (">=",_) | Func ("<=",_ ) -> failwith "problem"
    | Func ("f", _) -> failwith "function f is not a boolean"
    | Func ("=",[|a;b|]) ->
      begin
        match a, b with
        | Var va, Var vb -> if va = vb then SAT []
          else (
            if List.exists (fun f1 ->
                match f1 with
                | Func("=",[|c;d|]) -> c = a && d <> b || (c = b && d <> a)
                | _   -> false
          ) eq_sat then UNSAT
            else SAT (Func("=",[|a;b|])::eq_sat)
          )
        | Var _, _ ->
          if List.exists (fun f1 ->
              match f1 with
              | Func("=",[|c;d|]) -> c = a && d <> b
              | _-> false) eq_sat then UNSAT
          else SAT(Func("=",[|a;b|])::eq_sat)
        | _ , Var _ ->
          if List.exists (fun f1 ->
              match f1 with
              | Func("=",[|c;d|]) -> c = a && d <> b
              | _-> false) eq_sat then UNSAT
          else SAT(Func("=",[|b;a|])::eq_sat)
        | _,_ -> if a <> b then UNSAT
          else SAT []
      end
    | And fa ->
      begin
        List.fold_right (fun f eq -> solver_theory_f_aux f eq) fa (equality)
      end
    | _ -> failwith "not a valid formule for this theory"
  in solver_theory_f_aux formule (SAT [])


let solver_theory_eq f =
  let rec solver_theory_eq f equalities =
    match equalities with
    | UNSAT -> UNSAT
    | SAT eql ->
      match f with
      | Func("<=", [|a;b|])::q -> if List.exists (fun f -> match f with
          | Func("<=", [|c;d|]) -> b = c && a = d
          | Func(">=", [|c;d|]) -> c = a && c = d
          | _ -> false
        ) q then SAT(Func("=", [|a;b|])::eql)
            else SAT eql
      | Func(">=", [|a;b|])::q -> solver_theory_eq (Func("<=",[|b;a|])::q) equalities
      | _ -> failwith "todo"
  in match f with
  | And fa -> solver_theory_eq fa (SAT [])
  | _ -> failwith "implemented only for conjonction"

let () =
  let f =
    And [
      Func(">=", [|Func("f",[|Var "x1"; Const (Intv 0) |]); Var "x3"|]);
      Func("<=", [|Func("f",[|Var "x2"; Const (Intv 0) |]); Var "x3"|]);
      Func(">=", [|Var "x1"; Var "x2"|]);
      Func(">=", [|Var "x2"; Var "x1"|]);
      Func(">=", [|
          Func("f", [|Var "x1"; Const (Intv 0)|]);
          Const (Intv 0)
        |])
    ] in
  let theories = [|
    new_theorie ["int"] ["f", [Some "int";Some "int"; Some "int"]; "=", [Some "int";Some "int"; Some "int"]] [] solver_theory_f;
    new_theorie ["int"] [">=", [Some "int";Some "int"; Some "int"]; "<=", [Some "int";Some "int"; Some "int"]; "=", [Some "int";Some "int";Some "int"; Some "int"]] [] solver_theory_eq;
  |]
  in
  match solve_entry f theories with
  | SAT _ -> ()
  | UNSAT ->
    failwith "error this formula is satisfiable"
