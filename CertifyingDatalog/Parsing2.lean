import Std.Data.List.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.Basic
import Lean.Data.Json.FromToJson

def tokenizeHelper (s: List Char) (currToken: Option String) (tokens: List String): List String :=
  match s with
  | List.nil =>
    match currToken with
    | Option.none => tokens
    | Option.some token => tokens.concat token
  | List.cons hd tl =>
    if (hd ∈ ['(', ')'])
      then
        match currToken with
        | Option.none => tokenizeHelper tl Option.none (tokens.append [hd.toString])
        | Option.some token => tokenizeHelper tl Option.none (tokens.append [token, hd.toString])
      else  if hd ∈ [' ', ',']
            then
               match currToken with
                | Option.none => tokenizeHelper tl Option.none tokens
                | Option.some token => tokenizeHelper tl Option.none (tokens.append [token])
            else
              match currToken with
              | Option.none => tokenizeHelper tl hd.toString tokens
              | Option.some token => tokenizeHelper tl (token.push hd) tokens

def tokenize (s: String): List String := tokenizeHelper s.data Option.none List.nil

inductive mockTerm
| constant: String → mockTerm
| variable: String → mockTerm
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

def mockTerm.toString (mt: mockTerm): String :=
  match mt with
  | mockTerm.constant c => "constant " ++ c
  | mockTerm.variable v => "variable " ++ v

#eval Lean.toJson (mockTerm.constant "b")

structure mockAtom where
  (symbol: String)
  (terms: List mockTerm)
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

#eval Lean.toJson (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"])

structure mockRule where
  head: mockAtom
  body: List (mockAtom)
deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

inductive jsonTree
| node (label: String) (children: List jsonTree)
deriving Repr, Lean.ToJson, Lean.FromJson

structure problemInput where
  (trees: List jsonTree)
  (program: List (mockRule))
  (completion: Bool)
deriving Repr, Lean.FromJson, Lean.ToJson

structure parsingArityHelper where
  (relationList: List String)
  (arity: {x // x ∈ relationList} → Nat)

def extendParsingArityHelper (sig: parsingArityHelper) (symbol: String) (arity: Nat): Except String parsingArityHelper :=
  if h: symbol ∈ sig.relationList
  then
    if sig.arity (Subtype.mk symbol h) == arity
    then
      Except.ok sig
    else
      Except.error ("Mismatched arity for " ++ symbol ++ " Given ")
  else
    Except.ok {relationList := sig.relationList ++ [symbol], arity := (fun x => if q:(x = symbol) then arity else
      have p: x.val ∈ sig.relationList := by
        have h': x.val ∈ (sig.relationList ++ [symbol] )
        apply x.property
        simp at h'
        cases h' with
        | inl h' =>
          apply h'
        | inr h' =>
          exact absurd h' q

     sig.arity (Subtype.mk x.val p))}

def parsingSignature (helper: parsingArityHelper): signature :=
  {constants:= String, vars:= String, relationSymbols := {x // x ∈ helper.relationList}, relationArity := helper.arity}

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).constants :=
by
  unfold parsingSignature
  simp
  apply instDecidableEqString

instance (helper: parsingArityHelper): Nonempty (parsingSignature helper).constants :=
by
  unfold parsingSignature
  simp
  sorry

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).vars :=
by
  unfold parsingSignature
  simp
  apply instDecidableEqString

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).relationSymbols :=  Subtype.instDecidableEqSubtype

def getArityHelperFromMockAtom (helper: parsingArityHelper) (ma: mockAtom): Except String parsingArityHelper := extendParsingArityHelper helper ma.symbol (ma.terms.length)

def getArityHelperFromMockAtomList (helper: parsingArityHelper) (l: List mockAtom): Except String parsingArityHelper :=
  match l with
  | [] => Except.ok helper
  | hd::tl =>
    match getArityHelperFromMockAtom helper hd with
    | Except.error e => Except.error e
    | Except.ok newHelper =>
      getArityHelperFromMockAtomList newHelper tl

def getArityHelperFromMockRule (helper: parsingArityHelper) (mr: mockRule): Except String parsingArityHelper :=
  match getArityHelperFromMockAtom helper mr.head with
  | Except.error e => Except.error e
  | Except.ok newHelper => getArityHelperFromMockAtomList newHelper mr.body

def transformMockTermToTerm (helper: parsingArityHelper) (mt: mockTerm): term (parsingSignature helper) :=
  match mt with
  | mockTerm.constant c => term.constant c
  | mockTerm.variable v => term.variableDL v

def transformMockAtomToAtom (helper: parsingArityHelper) (ma: mockAtom): Except String (atom (parsingSignature helper)) :=
  if h: ma.symbol ∈ helper.relationList
  then
    if p: helper.arity (Subtype.mk ma.symbol h) = ma.terms.length
    then
      have q: List.length (List.map (transformMockTermToTerm helper) ma.terms) =
    signature.relationArity (parsingSignature helper) { val := ma.symbol, property := h } := by
        rw [List.length_map]
        rw [← p]
        unfold parsingSignature
        simp

    Except.ok {symbol := (Subtype.mk ma.symbol h), atom_terms := List.map (transformMockTermToTerm helper) ma.terms, term_length := q}
    else Except.error ("Wrong arity for " ++ ma.symbol)
  else Except.error ("Unknown symbol" ++ ma.symbol)

def transformMockRuleToRule (helper: parsingArityHelper) (mr: mockRule): Except String (rule (parsingSignature helper)) :=
  match transformMockAtomToAtom helper mr.head with
  | Except.error e => Except.error e
  | Except.ok head =>
    match List.map_except (transformMockAtomToAtom helper) mr.body with
    | Except.error e => Except.error e
    | Except.ok body => Except.ok {head:= head, body:= body}


def parseGroundAtomFromStack (helper: parsingArityHelper) (stack: List String): Except String (groundAtom (parsingSignature helper)) :=
  match stack with
  | [] => Except.error "Can't parse ground atom from empty string"
  | hd::tl =>
    if h: hd ∈  helper.relationList
    then
      if p:tl.length = (parsingSignature helper).relationArity (Subtype.mk hd h)
      then
        Except.ok {symbol:= Subtype.mk hd h, atom_terms := tl, term_length := p}
      else
        Except.error ("Wrong arity for symbol " ++ hd)
    else Except.error ("Unknown symbol " ++ hd)


def parseGroundAtom.go (helper: parsingArityHelper) (l: List String) (stack: List String): Except String (groundAtom (parsingSignature helper)) :=
  match l with
  | List.nil => Except.error "No closing bracket"
  | hd::tl =>
    if hd == "("
    then parseGroundAtom.go helper tl stack
    else
      if hd == ")"
      then  if tl.isEmpty
            then parseGroundAtomFromStack helper stack
            else Except.error "Symbols after the closing bracket when parsing atom"
      else
        parseGroundAtom.go helper tl (stack.append [hd])

def parseGroundAtom (helper: parsingArityHelper) (l: List String):  Except String (groundAtom (parsingSignature helper)) := parseGroundAtom.go helper l []


def proofTreeFromTree (helper: parsingArityHelper) (t: jsonTree) : Except String (proofTree (parsingSignature helper)) :=
  match t with
  | jsonTree.node label children =>
    match parseGroundAtom helper (tokenize label) with
    | Except.ok a =>
      let s:= List.map_except (fun ⟨x, _h⟩  => proofTreeFromTree  helper x) children.attach
      match s with
      | Except.ok l =>
        Except.ok (proofTree.node a l)
      | Except.error msg => Except.error msg
    | Except.error msg => Except.error msg
termination_by proofTreeFromTree relationList t => sizeOf t
decreasing_by
  simp_wf
  decreasing_trivial
  apply Nat.zero_le

structure verificationProblem (helper: parsingArityHelper) where
  (trees: List (proofTree (parsingSignature helper)))
  (program: List (rule (parsingSignature helper)))
  (completion: Bool)

def converProblemInputToVerificationProblem (helper: parsingArityHelper) (input: problemInput) : Except String (verificationProblem helper) :=
  match List.map_except (proofTreeFromTree helper) input.trees with
  | Except.error e => Except.error ("Error parsing trees -- " ++ e)
  | Except.ok trees =>
    match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {trees := trees, program := program, completion := input.completion}
