type valeur =
  | Intv : int -> valeur
  | Stringv : string -> valeur
  | Arrayv : 'a array -> valeur
  | Listv : 'a list -> valeur
  | Floatv : float -> valeur
  | Boolv : bool -> valeur

type valeur_type = Intt | Stringt | Arrayt | Listt | Floatt | Boolt
let get_kind_of_valeur_out_of_sorte s = match s with
  | Some "int" -> Intt
  | Some "string" -> Stringt
  | Some "array" -> Arrayt
  | Some "list" -> Listt
  | Some "float" -> Floatt
  | Some "bool" -> Boolt
  | _ -> failwith "no Caml type available to define a variable of this sorte"

module Entry =
struct
  type sorte = string option
  type var = string
  type fonction = string*(sorte list)

  type formule = Forall of var*formule
             | Exists of var*formule
             | Func of string*(formule array)
             | Const of valeur
             | Var of string
             | And of formule list
             | Or of formule list

  type result = UNSAT | SAT of formule list

  type theorie = {sortes : string list;
                  fonctions : fonction list;
                  variables : (var* sorte) list ;
                  solver : formule -> result}


  type entry = formule * (theorie array)

  let new_entry formule theories : entry = formule, theories

  let new_theorie sortes fonctions variables solver =
    {
       sortes; fonctions; variables; solver
    }

  let find f a =
    let rec find_aux f a n =
      if f a.(n) then Some n
      else find_aux f a (n+1)
    in
    try
      find_aux f a 0
    with _ -> None


  let get_theory_function f theories = (* renvoie l'entier indexant la théorie à laquelle se raporte f dans la liste theories *)
    match find (fun th -> List.exists (fun x -> fst x = f) th.fonctions) theories with
    | Some a -> a
    | None -> failwith "fonction symbol not found in theories"


  let add_formule f th separate_and =
    separate_and.(th) <- f :: separate_and.(th)

  let new_variable =
    let n = ref 0 in
    fun () -> incr n; "_"^string_of_int !n



  let separate formules theories =
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
      | Const c -> Const c
      | _ -> failwith "not implemented 1"
    in
    List.iter (fun f ->
        match f with
        | Func(fname,_) -> let th = get_theory_function fname theories in
                             add_formule (separate_and_aux f th) th separate_and
        | _ -> failwith "not implemented 2") formules;
    separate_and

  let conj_eq l = (*l est une liste de couples valeur/variables. On prend les égalités. *)
    let a = Array.of_list l in (* plus simple à manipuler ici, de très loin *)
    let q = ref [] in
    let m = Array.length a in
    for i = 0 to m -1 do
      for j = 0 to m-1 do (* aïe le quadratique *)
        if (j <> i) then
          match a.(i), a.(j) with
          | Func("=", [|fa;fb|]), Func("=", [|fc;fd|]) ->
            if  fb = fd then
            q := (Func("=",[|fa; fc|]))::!q;
          | _ -> ()
      done;
    done;
    !q

  let rec new_equalities f l = match f with(* liste les éléments de f non présents dans la liste l *)
    | [] -> []
    | eq::q -> if (List.mem eq l) then new_equalities q l else eq::(new_equalities q l)

  exception Return of result

  let solving separate_and theories =
    let n = Array.length separate_and in
    let b = ref false in
    let th = ref 0 in
    let visited = Array.make n false in
    let contraints = ref [] in
    try
      while not (!b && (!th = n-1)) && !th < n do
        b := true;
        match theories.(!th).solver (And (separate_and.(!th))) with
        | UNSAT -> raise (Return UNSAT)
        | SAT [] -> raise (Return (SAT []))
        | SAT l -> begin
            let f = conj_eq l in
            (* pour optimiser : faire une concat sans répétitions ici, car il peut y en avoir *)
            if not visited.(!th) then (
              separate_and.(!th) <- separate_and.(!th)@f;
              visited.(!th) <- true );
            for j = (n-1) downto 0 do (* on fait un downto pour repartir de la théorie modifiée la plus basse dans la liste *)
              let neweq = new_equalities f separate_and.(j) in
              match neweq with
              | [] -> th := !th + 1
              | q -> b := false;
                separate_and.(j) <- separate_and.(j)@q;
                th := j
            done;
            contraints := l @ !contraints;
          end
      done;
      SAT !contraints (* la on collecte pas les valeurs, mais si y a besoin ca prend qlq lignes *)
      with Return a -> a
    (*for th = 0 to (n-1) do
      match solver th (And (separate_and.(th))) with
        | UNSAT -> return UNSAT
        | SAT [] | SAT l when i = (n-1) -> ()
        | SAT l when i < (n-1) -> (let f = conj_eq l in
          for j = (i+1) to (n-1) do
            let f = conj_eq l in separate_and.(j) <- And (conj_eq l)@(separate_and.(j));
          done)
      done;
    return SAT [] (* ou alors on aurait pu collecté les valeurs des variables *) *)


  let solve_entry f ths =
    match f with
    | And fa -> solving (separate fa ths) ths
    | _ -> failwith "not implemented, this alogirthm takes only conjunction"

  let verify_variable s =
    if s.[0] = '_' then
      print_endline ("WARNING : the variable "^s^" start with '_' this will be ignore")

end
