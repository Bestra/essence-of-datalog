open Base

(* data Rule = Rule { _head :: Atom, _body :: [ Atom ] }
   data Atom = Atom { _predSym :: String, _terms :: [ Term ] } deriving Eq
   data Term = Var String | Sym String deriving Eq *)

module Term = struct
  module T = struct
    type t = Var of string | Sym of string [@@deriving compare, sexp]
  end

  include T
  include Comparator.Make (T)
end

type atom = {predSym: string; terms: Term.t list} [@@deriving compare, sexp]

type rule = {head: atom; body: atom list} [@@deriving sexp]

type program = rule list

type knowledge_base = atom list [@@deriving compare]

type substitution = (Term.t * Term.t) list [@@deriving sexp]

let empty_substitution = []

let make_atom predSym terms = {predSym; terms}

let make_rule head body = {head; body}

let make_fact head = {head; body= []}

module Parser = struct
  open Angstrom
  let ws = skip_while (function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _ -> false)

  let atom = take_till (function | 'a' .. 'z' | 'A' .. 'Z' -> false | _ -> true)
  let var = atom >>| (fun k -> Term.Var(k))
  let sym = char '"' *> atom <* char '"' >>| (fun k -> Term.Sym(k))
  let term = sym <|> var
  let head = take_till (function | '(' -> true | _ -> false)
  let horn_clause = lift2 (fun h terms -> (make_atom h terms))
      (head <* char '(')  (sep_by (char ',' <* ws) term <* char ')')
  let horn_clauses = sep_by (char ',' <* ws) horn_clause
  let fact = horn_clause <* char('.') >>| make_fact
  let rule = lift2
    (fun head body -> make_rule head body)
    (horn_clause <* ws <* string ":-" <* ws)
    (horn_clauses <* char '.')
  let line = fact <|> rule
  let run_parser p s = parse_string p s

  let parse_line s = parse_string line s
end

let cmp_equal comparator =
  (fun a b -> match (comparator a b) with | 0 -> true | _ -> false)

(* substitute :: Atom -> Substitution -> Atom
   substitute atom substitution = atom { _terms = map go (_terms atom) }
   where
   go sym@Sym{} = sym
   go var@Var{} = fromMaybe var (var `lookup` substitution) *)
let substitute atom (substitution : substitution) =
  let go = function
    | Term.Sym _ as s -> s
    | Var _ as v ->
      let sub = List.Assoc.find substitution v ~equal:(cmp_equal Term.compare) in
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

let unify {predSym; terms} {predSym= predSym'; terms= terms'} :
  substitution option =
  let open Option.Let_syntax in
  let rec go = function
    | [] -> Some empty_substitution
    | ((Term.Sym _ as s), (Term.Sym _ as s')) :: rest ->
      if (cmp_equal Term.compare) s s' then go rest else None
    | ((Var _ as v), (Sym _ as s)) :: rest -> (
        let%bind incomplete_substitution = go rest in
        match List.Assoc.find incomplete_substitution v ~equal:(cmp_equal Term.compare) with
        | Some s' when not ((cmp_equal Term.compare) s s') -> None
        | _ -> Some ((v, s) :: incomplete_substitution) )
    | (_, Var _) :: _ -> failwith "Foo"
  in
  (* Stdio.printf "Unifying %s and %s\n" predSym predSym'; *)
  if (cmp_equal compare_string) predSym predSym' then List.zip_exn terms terms' |> go else None

(* evalAtom :: KnowledgeBase -> Atom -> [ Substitution ] -> [ Substitution ]
   evalAtom kb atom substitutions = do
   substitution <- substitutions
   let downToEarthAtom = substitute atom substitution
   extension <- mapMaybe (unify downToEarthAtom) kb
   return $ substitution <> extension *)

let eval_atom kb atom substitutions =
  let append_subs s1 s2 : substitution = List.append s1 s2 in
  List.concat_map substitutions ~f:(fun substitution ->
      let down_to_earth_atom = substitute atom substitution in
      List.map kb ~f:(unify down_to_earth_atom)
      |> List.filter_opt
      |> List.map ~f:(fun extension -> append_subs substitution extension) )

(* walk :: KnowledgeBase -> [ Atom ] -> [ Substitution ] *)

let walk kb = List.fold_right ~f:(eval_atom kb) ~init:[empty_substitution]

(* evalRule :: KnowledgeBase -> Rule -> KnowledgeBase
   evalRule kb (Rule head body) = map (substitute head) (walk kb body) *)
let eval_rule kb {head; body} = List.map ~f:(substitute head) (walk kb body)

(* immediateConsequence :: Program -> KnowledgeBase -> KnowledgeBase
   immediateConsequence rules kb =
   nub . (kb <>) . concatMap (evalRule kb) $ rules *)

let immediate_consequence (rules : program) (kb : knowledge_base) :
  knowledge_base =
  List.concat_map ~f:(eval_rule kb) rules
  |> List.append kb
  |> List.dedup_and_sort ~compare:compare_atom

(* isRangeRestricted :: Rule -> Bool
   isRangeRestricted Rule{..} =
   vars _head `isSubsequenceOf` concatMap vars _body
   where
   vars Atom{..} = nub $ filter (\case {Var{} -> True; _ -> False}) _terms *)

(* every var in the head must appear in the body *)
let is_range_restricted {head; body} =
  let vars {terms; _} =
    List.filter terms ~f:(function Var _ -> true | _ -> false)
    |> List.dedup_and_sort ~compare:Term.compare
  in
  let is_subsequence_of parent child =
    let term_set = Set.of_list (module Term) in
    Set.is_subset ~of_:(term_set child) (term_set parent)
  in
  is_subsequence_of (vars head) (List.concat_map ~f:vars body)

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
let solve (rules : program) : knowledge_base =
  let rec step current_kb =
    let next_kb = immediate_consequence rules current_kb in
    Stdio.print_endline "***********step";
    Stdio.print_endline "current kb ----------------";
    (sexp_of_list sexp_of_atom current_kb) |> Sexp.to_string_hum |> Stdio.print_endline;
    Stdio.print_endline "next kb ----------------";
    (sexp_of_list sexp_of_atom next_kb) |> Sexp.to_string_hum |> Stdio.print_endline;
    Stdio.print_endline "^^^^^^^^^step";
    let c = (compare_knowledge_base next_kb current_kb) in
    if c = 0 then current_kb else step next_kb
  in
  if List.for_all rules ~f:is_range_restricted then step []
  else failwith "The input program is not range-restricted"

(* ancestor =
   -- Facts
   fmap (\terms -> Rule (Atom "adviser" terms) [])
    [ [ Sym "Andrew Rice",     Sym "Mistral Contrastin" ]
    , [ Sym "Dominic Orchard", Sym "Mistral Contrastin" ]
    , [ Sym "Andy Hopper",     Sym "Andrew Rice" ]
    , [ Sym "Alan Mycroft",    Sym "Dominic Orchard" ]
    , [ Sym "David Wheeler",   Sym "Andy Hopper" ]
    , [ Sym "Rod Burstall",    Sym "Alan Mycroft" ]
    , [ Sym "Robin Milner",    Sym "Alan Mycroft" ]
    ] <>
   -- Actual rules
   [ Rule (Atom "academicAncestor" [ Var "X", Var "Y" ])
      [ Atom "adviser" [ Var "X", Var "Y" ] ]
   , Rule (Atom "academicAncestor" [ Var "X", Var "Z" ])
      [ Atom "adviser"          [ Var "X", Var "Y" ]
      , Atom "academicAncestor" [ Var "Y", Var "Z" ] ]
   ] <>
   -- Queries
   [ Rule (Atom "query1" [ Var "Intermediate" ])
      (fmap (Atom "academicAncestor")
        [ [ Sym "Robin Milner", Var "Intermediate" ]
        , [ Var "Intermediate", Sym "Mistral Contrastin" ] ])
   , Rule (Atom "query2" [ ])
      [ Atom "academicAncestor"
          [ Sym "Alan Turing", Sym "Mistral Contrastin" ] ]
   , Rule (Atom "query3" [ ])
      [ Atom "academicAncestor"
          [ Sym "David Wheeler", Sym "Mistral Contrastin" ] ]
   ] *)

let adviser t = make_fact (make_atom "adviser" t)

let ancestor =
  [ adviser [Sym "Andrew Rice"; Sym "Mistral Contrastin"]
  ; adviser [Sym "Dominic Orchard"; Sym "Mistral Contrastin"]
  ; adviser [Sym "Andy Hopper"; Sym "Andrew Rice"]
  ; adviser [Sym "Alan Mycroft"; Sym "Dominic Orchard"]
  ; adviser [Sym "David Wheeler"; Sym "Andy Hopper"]
  ; adviser [Sym "Rod Burstall"; Sym "Alan Mycroft"]
  ; adviser [Sym "Robin Milner"; Sym "Alan Mycroft"]
  ; (* rules *)
    make_rule
      (make_atom "academicAncestor" [Var "X"; Var "Y"])
      [make_atom "adviser" [Var "X"; Var "Y"]]
  ; make_rule
      (make_atom "academicAncestor" [Var "X"; Var "Z"])
      [ make_atom "adviser" [Var "X"; Var "Y"]
      ; make_atom "academicAncestor" [Var "Y"; Var "Z"] ]
  (* queries *)
  ; make_rule
      (make_atom "query1" [Var "Intermediate"])
      [ make_atom "academicAncestor" [Sym "Robin Milner"; Var "Intermediate"]
      ; make_atom "academicAncestor" [Var "Intermediate"; Sym "Mistral Contrastin"] ]
  ; make_rule
      (make_atom "query2" [])
      [ make_atom "academicAncestor" [Sym "Alan Turing"; Sym "Mistral Contrastin"] ]
  ; make_rule
      (make_atom "query3" [])
      [ make_atom "academicAncestor" [Sym "David Wheeler"; Sym "Mistral Contrastin"] ]
  ]

(* query :: String -> Program -> [ Substitution ]
   query predSym pr =
   case queryVarsL of
    [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    [] -> error $ "The query '" ++ predSym ++ "' doesn't exist."
    _  -> error $ "The query '" ++ predSym ++ "' has multiple clauses."
   where
   relevantKnowledgeBase = filter ((== predSym) . _predSym) $ solve pr
   relevantKnowledgeBaseSyms = _terms <$> relevantKnowledgeBase

   queryRules = filter ((== predSym) . _predSym . _head) pr
   queryVarsL = _terms . _head <$> queryRules *)

type query_result = {vars: Term.t list; syms: Term.t list list} [@@deriving sexp]

let query predSym pr =
  let solved = solve pr in
  Stdio.print_endline "********Solution";
  sexp_of_list sexp_of_atom solved |> Sexp.to_string_hum |> Stdio.print_endline;
  Stdio.print_endline "^^^^^^^^Solution";
  let relevant_knowledge_base = List.filter solved ~f:(fun k -> (cmp_equal compare_string) predSym k.predSym) in
  let relevant_knowledge_base_syms = List.map ~f:(fun k -> k.terms) relevant_knowledge_base in
  let query_rules = List.filter pr ~f:(fun r -> (cmp_equal compare_string) predSym r.head.predSym) in
  let query_vars = List.map query_rules ~f:(fun r -> r.head.terms) in
  match query_vars with
  | [ vars ] -> {vars; syms=relevant_knowledge_base_syms}
  | [] -> failwith ("The query" ^ predSym ^ "does not exist")
  | _ -> failwith ("The query" ^ predSym ^ "has multiple clauses")