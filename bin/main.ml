
type sorte = string option
type var = string*sorte
type fonction = string*(sorte list)

type formule = Forall of var*formule 
| Exists of var*formule 
| Func of string*(formule list)
| Const of var
| And of formule list
| Or of formule list

type theorie = {axiomes : formule list; sortes : string list; fonctions : fonction list; variables : var list}

let rec aux form lt ct = match form with (* form : la formule, lt : la liste des théories, ct : la théorie en cours *)
  | Forall _ | Exists _ | Or _-> assert false
  | Func(f,arg) -> assert false
  | Const c -> (let v,s = c in match s with
    | Some sor -> (if (List.mem sor ct.sortes) then else failwith"la formule passée en entrée est mal formée")
    | None -> )
  | And fl -> assert false
