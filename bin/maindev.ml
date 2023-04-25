module Theory =
  sig
    type formule
    type fonction
    type result

    val solver : formule -> result

    val axiomes : formule list

    val fonctions : fonction list

  end

type valeur = Intv of int | Stringv of string | Arrayv of array | Listv of list | Floatv of Float | Boolv of bool
type valeur_type = Intt | Stringt | Arrayt | Listt | Floatt | Boolt
let get_kind_of_valeur_out_of_sorte s = match s with
  | Some "int" -> Intt
  | Some "string" -> Stringt
  | Some "array" -> Arrayt
  | Some "list" -> Listt
  | Some "float" -> Floatt
  | Some "bool" -> Boolt
  | None -> failwith "no Caml type available to define a variable of this sorte"

module Entry =
struct
  type sorte = string option
  type var = string*sorte
  type fonction = string*(sorte list)
  type result = UNSAT | SAT of ((valeur*var) list)

  type formule = Forall of var*formule
             | Exists of var*formule
             | Func of string*(formule array)
             | Const of var
             | Var of string
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


  let get_theory_function f theories = (* renvoie l'entier indexant la théorie à laquelle se raporte f dans la liste theories *)
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

  let rec conj_eq l = (*l est une liste de couples valeur/variables. On prend les égalités. *)
    let a = Array.of_list l in (* plus simple à manipuler ici, de très loin *)
    let q = ref [] in
    let m = Array.length a in
    for i = 0 to m do
      for j = 0 to m do (* aïe le quadratique *)
        if (j <> i) then (if fst a.(i) = fst a.(j) then q := (Func("=",[|Var(fst (snd a.(i))); Var(fst (snd a.(j)))|]))::!q)
        done;
      done;
    return !q

  let rec new_equalities f l = match f with(* liste les éléments de f non présents dans la liste l *)
    | [] -> []
    | eq::q -> if (List.mem eq l) then new_equalities q l else eq::(new_equalities q l)

  let solving separate_and =
    let open Entry in
    let n = Array.length separate_and in
    let b = ref false in
    let th = ref 0 in
    let visited = Array.make n false in
    while not (!b && (!th = n-1)) do
      b := true;
      begin
        match solver !th (And (separate_and.(!th))) with
          | UNSAT -> return UNSAT
          | SAT [] -> skip
          | SAT l -> (let f = conj_eq l in
            if visited.(!th) then skip else (separate_and.(!th) <- separate_and.(!th)@f; visited.(!th) <- true); (* pour optimiser : faire une concat sans répétitions ici, car il peut y en avoir *)
            for j = (n-1) down to 0 do (* on fait un downto pour repartir de la théorie modifiée la plus basse dans la liste *)
              let neweq = new_equalities f separate_and.(j) in 
              match neweq with
                | [] -> th := !th + 1
                | q -> b := false; separte_and.(j) <- separate_and.(j)@q; th := j
            done;)
      end;
    done;
    return SAT [] (* la on collecte pas les valeurs, mais si y a besoin ca prend qlq lignes *)
    
    (*for th = 0 to (n-1) do
      match solver th (And (separate_and.(th))) with
        | UNSAT -> return UNSAT
        | SAT [] | SAT l when i = (n-1) -> skip
        | SAT l when i < (n-1) -> (let f = conj_eq l in
          for j = (i+1) to (n-1) do
            let f = conj_eq l in separate_and.(j) <- And (conj_eq l)@(separate_and.(j));
          done)
      done;
    return SAT [] (* ou alors on aurait pu collecté les valeurs des variables *) *)

  let verify_variable s =
    if s.[0] = '_' then print_newline ("WARNING : the variable "^s^" start with '_' this will be ignore")

end
