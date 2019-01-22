type term = Var of string | Sym of string

type atom = {predSym: string; terms: term list}

type rule = {head: atom; body: atom list}

type program = rule list

type knowledge_base = atom list

type substitution = (term * term) list

val empty_substitution: term list

val substitute: atom -> substitution -> atom

val unify: atom -> atom -> substitution option

val eval_atom: knowledge_base -> atom -> substitution list -> substitution list

val walk: knowledge_base -> atom list  -> substitution list

val eval_rule: knowledge_base -> rule -> knowledge_base

