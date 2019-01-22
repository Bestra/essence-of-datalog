open Base

(* data Rule = Rule { _head :: Atom, _body :: [ Atom ] }
   data Atom = Atom { _predSym :: String, _terms :: [ Term ] } deriving Eq
   data Term = Var String | Sym String deriving Eq *)

type term = Var of string | Sym of string

type atom = {predSym: string; terms: term list}

type rule = {head: atom; body: atom}

type program = rule list

type knowledge_base = atom list

type substitution = (term * term) list

let empty_substitution = []

(* substitute :: Atom -> Substitution -> Atom
   substitute atom substitution = atom { _terms = map go (_terms atom) }
   where
   go sym@Sym{} = sym
   go var@Var{} = fromMaybe var (var `lookup` substitution) *)
let substitute atom (substitution: substitution) =
  let go = function
    | Sym _ as s -> s
    | Var _ as v ->
      let sub = List.Assoc.find substitution v ~equal:phys_equal in
      Option.value sub ~default:v
  in
  {atom with terms= List.map ~f:go atom.terms}

(* 
unify :: Atom -> Atom -> Maybe Substitution
unify (Atom predSym ts) (Atom predSym' ts')
  | predSym == predSym' = go $ zip ts ts'
  | otherwise           = Nothing
  where
  go :: [ (Term, Term) ] -> Maybe Substitution
  go []                           = Just emptySubstitution
  go ((s@Sym{}, s'@Sym{}) : rest) = if s == s' then go rest else Nothing
  go ((v@Var{}, s@Sym{})  : rest) = do
    incompleteSubstitution <- go rest
    case v `lookup` incompleteSubstitution of
      Just s' | s /= s'   -> Nothing
      _                   -> return $ (v,s) : incompleteSubstitution
  go ((_, Var{}) : _) = error "The second atom is assumed to be ground." *)

let unify {predSym; terms} {predSym= predSym'; terms= terms'}: substitution option =
  let open Option.Let_syntax in
  let rec go = function
    | [] -> Some empty_substitution
    | ((Sym _ as s), (Sym _ as s')) :: rest ->
      if phys_equal s s' then go rest else None
    | ((Var _ as v), (Sym _ as s)) :: rest -> (
        let%bind incomplete_substitution = go rest in
        match List.Assoc.find incomplete_substitution v ~equal:phys_equal with
        | Some s' when not (phys_equal s s') -> None
        | _ -> Some ((v, s) :: incomplete_substitution) )
    | (_, Var _) :: _ -> failwith "Foo"
  in
  if phys_equal predSym predSym' then List.zip_exn terms terms' |> go else None

(* evalAtom :: KnowledgeBase -> Atom -> [ Substitution ] -> [ Substitution ]
   evalAtom kb atom substitutions = do
   substitution <- substitutions
   let downToEarthAtom = substitute atom substitution
   extension <- mapMaybe (unify downToEarthAtom) kb
   return $ substitution <> extension *)

let eval_atom kb atom substitutions =
  List.concat_map substitutions ~f:(fun substitution ->
      let down_to_earth_atom = substitute atom substitution in
      List.map kb ~f:(unify down_to_earth_atom) |> List.filter_opt
      |> List.map  ~f:(fun extension -> List.append substitution extension)
    )