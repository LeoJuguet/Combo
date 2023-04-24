module Theory =
  sig
    type formule
    type fonction

    val solver : formule -> bool

    val axiomes : formule list

    val fonctions : fonction list

  end



module Entry =
struct
  type sorte = string option
  type var = string*sorte
  type fonction = string*(sorte list)

  type formule = Forall of var*formule
             | Exists of var*formule
             | Func of string*(formule array)
             | Const of var
             | Var of  string
             | And of formule list
             | Or of formule list

  type theorie = {axiomes : formule list;
                  sortes : string list;
                  fonctions : fonction list;
                  variables : var list ;
                  solver : formule -> bool}

(*   let rec aux form lt ct = match form with (\* form : la formule, lt : la liste des théories, ct : la théorie en cours *\) *)
(*     | Forall _ | Exists _ | Or _-> assert false *)
(*     | Func(f,arg) -> assert false *)
(*     | Const c -> (let v,s = c in match s with *)
(*              | Some sor -> (if (List.mem sor ct.sortes) then else failwith"la formule passée en entrée est mal formée") *)
(*              | None -> ) *)
(*     | And fl -> assert false *)

  let find f a =
    let rec find f a n =
      if f a.(n) then Some n
      else find f a (n+1)
    in
    try
      find f a 0
    with _ -> None


  let get_theory_function f theories =
    match find (fun th -> List.exists (fun x -> fst x = f) th.fonctions) theories with
    | Some a -> a
    | None -> failwith "fonction symbol not found in theories"

end

module FormuleTheory =
struct

  let add_formule f th separate_and =
    let open Entry in
    separate_and.(th) <- f :: separate_and.(th)

  let new_variable =
    let n = ref 0 in
    fun () -> incr n; "_"^string_of_int !n

  let separate formules theories =
    let open Entry in
    let separate_and = Array.make (Array.length theories) [] in
      let rec separate_and_aux f t = match f with
        | Func(fname,args) -> begin
            match get_theory_function fname theories with
            | thf when thf = t -> Func(fname, Array.map (fun f -> separate_and_aux f t) args)
            | thf ->
              let new_var = new_variable () in
              add_formule (Func("=",[|Var(new_var);separate_and_aux f thf|])) thf separate_and;
              Var new_var
          end
        | Var a -> Var a
        | _ -> failwith "not implemented"
    in
    List.iter (fun f ->
        match f with
        | Func(fname,_) -> let th =get_theory_function fname theories in
                             add_formule (separate_and_aux f th) th separate_and
        | _ -> failwith "not implemented") formules


  let verify_variable s =
    if s.[0] = '_' then print_newline ("WARNING : the variable "^s^" start with '_' this will be ignore")

end
