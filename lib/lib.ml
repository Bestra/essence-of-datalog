open Base

(* data Rule = Rule { _head :: Atom, _body :: [ Atom ] }
   data Atom = Atom { _predSym :: String, _terms :: [ Term ] } deriving Eq
   data Term = Var String | Sym String deriving Eq *)

type term = Var of string | Sym of string [@@deriving compare]

type atom = {predSym: string; terms: term list} [@@deriving compare]

type rule = {head: atom; body: atom list}

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
  let append_subs s1 s2: substitution = List.append s1 s2 in

  List.concat_map substitutions ~f:(fun substitution ->
      let down_to_earth_atom = substitute atom substitution in
      List.map kb ~f:(unify down_to_earth_atom) |> List.filter_opt |>
      List.map  ~f:(fun extension -> append_subs substitution extension)
    )

(* walk :: KnowledgeBase -> [ Atom ] -> [ Substitution ] *)

let walk kb = List.fold_right ~f:(eval_atom kb) ~init:[ empty_substitution ]

(* evalRule :: KnowledgeBase -> Rule -> KnowledgeBase
evalRule kb (Rule head body) = map (substitute head) (walk kb body) *)
let eval_rule kb {head; body} = List.map ~f:(substitute head) (walk kb body)

(* immediateConsequence :: Program -> KnowledgeBase -> KnowledgeBase
immediateConsequence rules kb =
  nub . (kb <>) . concatMap (evalRule kb) $ rules *)

let immediate_consequence (rules: program) (kb: knowledge_base): knowledge_base =
  List.concat_map ~f:(eval_rule kb) rules
  |> List.append kb
  |> List.dedup_and_sort ~compare:compare_atom

let is_range_restricted rules = true

(* solve :: Program -> KnowledgeBase
solve rules =
  if all isRangeRestricted rules
    then fix step []
    else error "The input program is not range-restricted."
  where
  step :: (KnowledgeBase -> KnowledgeBase)
       -> (KnowledgeBase -> KnowledgeBase)
  step f currentKB | nextKB <- immediateConsequence rules currentKB =
    if nextKB == currentKB
      then currentKB
      else f nextKB *)
let solve (rules: program): knowledge_base =
  let step f (current_kb :: next_kb :: _) =
    if (phys_equal next_kb current_kb) then current_kb else f next_kb
  in
  