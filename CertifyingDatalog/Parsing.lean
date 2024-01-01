import Std.Data.List.Basic
import CertifyingDatalog.Datalog
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

def List.map_except.go {A B C: Type} (f: A → Except B C) (l: List A) (curr: Except B (List C)): Except B (List C) :=
  match l with
  | nil => curr
  | cons hd tl =>
    match curr with
    | Except.ok l' =>
      match f hd with
      | Except.ok c =>
        List.map_except.go f tl (Except.ok (l'.append [c]))
      | Except.error msg =>
        Except.error msg
    | Except.error msg => Except.error msg

def List.map_except {A B C: Type} (f: A → Except B C) (l: List A): Except B (List C) := List.map_except.go f l (Except.ok [])

def listStringToString (l: List String): String :=
  List.foldl (fun (x y: String) => x ++ "," ++ y) "" l

structure mockAtom where
  symbol: String
  terms: List (String)
deriving Repr, DecidableEq

def mockAtom.toString (ma: mockAtom) := ma.symbol ++ "(" ++ (listStringToString ma.terms) ++ ")"

structure mockRule where
  head: mockAtom
  body: List (mockAtom)
deriving Repr, DecidableEq

def mockRule.toString (mr: mockRule) := mr.head.toString ++ " :- " ++ listStringToString (List.map mockAtom.toString mr.body)

def findArity (symbol: String) (relationList: List (String × Nat)): Option Nat :=
  match relationList with
  | [] => Option.none
  | (a,b)::tl =>
    if symbol == a
    then Option.some b
    else findArity symbol tl

def parseMockAtomFromStack (relationList: List (String × Nat)) (stack: List String): Except String (mockAtom × List (String × Nat)) :=
  match stack with
  | [] => Except.error "Can't parse an atom from an empty stack"
  | hd::tl =>
    let arity:= findArity hd relationList
    match arity with
    | Option.some a =>
      if tl.length == a
      then Except.ok ({symbol:= hd, terms:= tl}, relationList)
      else Except.error ("Relation symbol " ++ hd ++ "occurs multiple times with different arity")
    | Option.none =>
      Except.ok ({symbol:= hd, terms:= tl}, relationList.insert (hd, tl.length))

def parseMockAtom.go (relationList: List (String × Nat)) (l: List String) (stack: List String): Except String (mockAtom × List (String × Nat)) :=
  match l with
  | [] => Except.error "No closing bracket"
  | hd::tl =>
    if hd == ")"
    then
      if tl.isEmpty
      then parseMockAtomFromStack relationList stack
      else
        if tl = ["."]
        then parseMockAtomFromStack relationList stack
        else Except.error ("Symbols after closing bracket" ++ listStringToString tl)
    else
      if hd == "("
      then parseMockAtom.go relationList tl stack
      else parseMockAtom.go relationList tl (stack.concat hd)

def parseMockAtom (relationList: List (String × Nat)) (l: List String): Except String (mockAtom × List (String × Nat)) :=
  match parseMockAtom.go relationList l [] with
  | Except.ok x => Except.ok x
  | Except.error msg => Except.error ("Error parsing" ++ (List.foldl (fun (x y: String) => x ++ y) "" l) ++ msg)



def parseMockAtomList.go (relationList: List (String × Nat)) (l: List String) (stack: List String) (curr: List mockAtom): Except String (List mockAtom × List (String × Nat)) :=
  match l with
  | [] =>
    if stack.isEmpty ∨ stack == ["."]
    then Except.ok (curr, relationList)
    else Except.error "No closing bracket"
  | hd :: tl =>
    if hd == ")"
    then
      match parseMockAtomFromStack relationList stack with
      | Except.error msg => Except.error msg
      | Except.ok (atom, relationList') =>
        parseMockAtomList.go relationList' tl [] (curr.concat atom)
    else
      if hd == "("
      then parseMockAtomList.go relationList tl stack curr
      else parseMockAtomList.go relationList tl (stack.concat hd) curr

def parseMockAtomList (relationList: List (String × Nat)) (l: List String): Except String (List mockAtom × List (String × Nat)) := parseMockAtomList.go relationList l [] []

def parseMockRule (relationList: List (String × Nat)) (l: List String): Except String (mockRule × List (String × Nat )) :=
  match l with
  | [] => Except.error "Cannot parse a rule from a empty String"
  | hd::tl =>
  let splitResult := List.splitOn ":-" (hd::tl)
    if h: splitResult.length = 1
    then
      have p: 0 < splitResult.length := by
        simp [h]
      match parseMockAtom relationList (splitResult.get (Fin.mk 0 p)) with
      | Except.error msg => Except.error msg
      | Except.ok (atom, relationList') =>
        Except.ok ({head:= atom, body:= []}, relationList')
    else
      if h:splitResult.length = 2
      then
        have p: 0 < splitResult.length := by
          simp [h]
        have q: 1 < splitResult.length := by
          simp [h]
        match parseMockAtom relationList (splitResult.get (Fin.mk 0 p)) with
        | Except.error msg => Except.error msg
        | Except.ok (head, relationList') =>
          match parseMockAtomList relationList' (splitResult.get (Fin.mk 1 q)) with
          | Except.error msg => Except.error msg
          | Except.ok (body, relationList'') =>
            Except.ok ({head:= head, body:= body}, relationList'')
      else Except.error "Too many occurences of :-"

def extendFunctionFromList {A B: Type} [DecidableEq A] (l1 l2: List (A × B)) (f: {x: A // x ∈ Prod.fst (List.unzip l2) } → B) : {x: A // x ∈ Prod.fst (List.unzip l2) } → B :=
  match l1 with
  | List.nil => f
  | (a,b)::tl => extendFunctionFromList tl l2 (fun (x: { y // y ∈ Prod.fst (List.unzip l2) })  => if (x.val = a )then b else f x)

def parsingSignature (relationList: List (String × Nat )): signature := {constants:= {x: String // ¬ x.startsWith "?"}, vars := {x: String // x.startsWith "?"}, relationSymbols := {x: String // x ∈ Prod.fst (List.unzip relationList)}, relationArity := extendFunctionFromList relationList relationList (fun _ => 0)}

instance (relationList: List (String × Nat )): DecidableEq (parsingSignature relationList).constants := Subtype.instDecidableEqSubtype

instance (relationList: List (String × Nat )): Nonempty (parsingSignature relationList).constants := by
  use ""
  simp


instance (relationList: List (String × Nat )): DecidableEq (parsingSignature relationList).vars := Subtype.instDecidableEqSubtype

instance (relationList: List (String × Nat )): DecidableEq (parsingSignature relationList).relationSymbols := Subtype.instDecidableEqSubtype

def parseConstantFromString (relationList: List (String × Nat)) (s: String): Except String (parsingSignature relationList).constants :=
  if p: s.startsWith "?"
  then Except.error "Constants are not allowed to start with a ?"
  else Except.ok (Subtype.mk s p)

def parseTermFromString (relationList: List (String × Nat)) (s: String): term (parsingSignature relationList) :=
  if p: s.startsWith "?"
  then (term.variableDL (Subtype.mk s p))
  else (term.constant (Subtype.mk s p))

def mockAtom.toAtom (ma: mockAtom) (relationList: List (String × Nat)): Except String (atom (parsingSignature relationList)) :=
  if p: ma.symbol ∈ Prod.fst (List.unzip relationList)
  then
    if h: (parsingSignature relationList).relationArity (Subtype.mk ma.symbol p) = ma.terms.length
    then
      have h': List.length (List.map (parseTermFromString relationList) ma.terms) = signature.relationArity (parsingSignature relationList) { val := ma.symbol, property := p } := by
        rw [List.length_map, ← h]
      Except.ok {symbol := (Subtype.mk ma.symbol p), atom_terms := List.map (parseTermFromString relationList) ma.terms, term_length := h' }
    else
      Except.error ("Number of atom terms does not match arity for " ++ ma.toString)
  else
    Except.error ("Unknown symbol" ++ ma.symbol)


def mockRule.toRule (mr: mockRule) (relationList: List (String × Nat)): Except String (rule (parsingSignature relationList)) :=
  match mr.head.toAtom  relationList with
  | Except.error msg => Except.error ("Error parsing " ++ mr.toString ++ " -- " ++ msg)
  | Except.ok head =>
    match List.map_except (fun x => mockAtom.toAtom x relationList) mr.body with
    | Except.error msg => Except.error ("Error parsing " ++ mr.toString ++ " -- " ++ msg)
    | Except.ok body => Except.ok {head:= head, body:= body}


def parseMockProgram.go (relationList: List (String × Nat)) (l: List String) (currProgram: List mockRule): Except String ((List mockRule) × List (String × Nat)) :=
  match l with
  | [] => Except.ok (currProgram, relationList)
  | hd::tl =>
    -- ignore empty lines or declarations
    if hd.startsWith "@" ∨ hd = ""
    then parseMockProgram.go relationList tl currProgram
    else
      match parseMockRule relationList (tokenize hd) with
      | Except.error msg => Except.error ("Error parsing " ++ hd ++ " -- " ++ msg)
      | Except.ok (r, relationList') => parseMockProgram.go relationList' tl (currProgram.concat r)

def parseMockProgram (l: List String): Except String ((List mockRule) × List (String × Nat)) := parseMockProgram.go [] l []

def mockProgramToProgram.go (p: List mockRule) (relationList: List (String × Nat)) (curr: List (rule (parsingSignature relationList))): Except String (List (rule (parsingSignature relationList))) :=
  match p with
  | [] => Except.ok curr
  | hd::tl =>
    match hd.toRule relationList with
    | Except.error msg => Except.error msg
    | Except.ok r => mockProgramToProgram.go tl relationList (curr.concat r)

def mockProgramToProgram (p: List mockRule) (relationList: List (String × Nat)): Except String (List (rule (parsingSignature relationList))) :=
  mockProgramToProgram.go p relationList []


inductive Tree
| node (label: String) (children: List Tree): Tree
deriving Repr, Lean.ToJson, Lean.FromJson



def parseGroundAtomFromStack (relationList: List (String × Nat)) (stack: List String): Except String (groundAtom (parsingSignature relationList)) :=
  match stack with
  | List.nil => Except.error "Cannot parse an atom from an empty stack"
  | hd::tl =>
    if h:hd ∈ Prod.fst (List.unzip relationList)
    then
      let terms := List.map_except (fun x => parseConstantFromString relationList x) tl
      match terms with
      | Except.ok l =>
        if p: l.length = (parsingSignature relationList).relationArity (Subtype.mk hd h)
        then
          Except.ok (groundAtom.mk (Subtype.mk hd h) l p)
        else Except.error ("relation arity does not match. Terms: " ++ listStringToString tl)
      | Except.error msg => Except.error msg
    else Except.error (hd ++ " is not a relation symbol")


def parseGroundAtom.go (relationList: List (String × Nat)) (l: List String) (stack: List String): Except String (groundAtom (parsingSignature relationList)) :=
  match l with
  | List.nil => Except.error "No closing bracket"
  | hd::tl =>
    if hd == "("
    then parseGroundAtom.go relationList tl stack
    else
      if hd == ")"
      then  if tl.isEmpty
            then parseGroundAtomFromStack  relationList stack
            else Except.error "Symbols after the closing bracket when parsing atom"
      else
        parseGroundAtom.go relationList tl (stack.append [hd])

def parseGroundAtom (relationList: List (String × Nat)) (l: List String): Except String (groundAtom (parsingSignature relationList)) := parseGroundAtom.go relationList l []


def proofTreeFromTree (relationList: List (String × Nat)) (t: Tree) : Except String (proofTree (parsingSignature relationList)) :=
  match t with
  | Tree.node label children =>
    match parseGroundAtom relationList (tokenize label) with
    | Except.ok a =>
      let s:= List.map_except (fun ⟨x, _h⟩  => proofTreeFromTree  relationList x) children.attach
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
