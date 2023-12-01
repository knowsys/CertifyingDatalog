import Std.Data.List.Basic
import CertifyingDatalog.Datalog
import Lean.Data.Json.FromToJson

def tokenizeHelper (s: List Char) (currToken: String) (tokens: List String): List String :=
  match s with
  | List.nil => tokens.append [currToken]
  | List.cons hd tl =>
    if (hd ∈ ['(', ')'])
      then  if currToken == ""
            then tokenizeHelper tl "" (tokens.append [hd.toString])
            else tokenizeHelper tl "" (tokens.append [currToken, hd.toString])
      else  if hd ∈ [' ', ',']
            then  if currToken == ""
                  then tokenizeHelper tl "" tokens
                  else tokenizeHelper tl "" (tokens.append [currToken])
            else tokenizeHelper tl (currToken.push hd) tokens

def tokenize (s: String): List String := tokenizeHelper s.data "" List.nil

inductive Tree
| node (label: String) (children: List Tree): Tree
deriving Repr, Lean.ToJson, Lean.FromJson

structure parsingResult where
  (constList: List String)
  (varList: List String)
  (relationList: List (String × Nat))
  (model: List String)
  (trees: List Tree)
deriving Lean.FromJson, Lean.ToJson, Repr

#eval Lean.toJson ({constList := ["a"],varList:= ["v"], relationList := [⟨"R", 2⟩, ⟨"T", 3⟩], model := [], trees := [Tree.node "label" []] }: parsingResult)

def extendFunctionFromList {A B: Type} [DecidableEq A] (l1 l2: List (A × B)) (f: {x: A // x ∈ Prod.fst (List.unzip l2) } → B) : {x: A // x ∈ Prod.fst (List.unzip l2) } → B :=
  match l1 with
  | List.nil => f
  | (a,b)::tl => extendFunctionFromList tl l2 (fun (x: { y // y ∈ Prod.fst (List.unzip l2) })  => if (x.val = a )then b else f x)

def signatureFromLists (constList varList: List String) (relationList: List (String × Nat)): signature :=
{constants := {x: String // x ∈ constList}, vars := {x: String // x ∈ varList}, relationSymbols := {x: String // x ∈ Prod.fst (List.unzip relationList) }, relationArity := extendFunctionFromList relationList relationList (fun _ => 0)}

instance (constList varList: List String) (relationList: List (String × Nat)): DecidableEq (signatureFromLists constList varList relationList).constants := Subtype.instDecidableEqSubtype

instance (constList varList: List String) (relationList: List (String × Nat)): DecidableEq (signatureFromLists constList varList relationList).vars := Subtype.instDecidableEqSubtype

instance (constList varList: List String) (relationList: List (String × Nat)): DecidableEq (signatureFromLists constList varList relationList).relationSymbols := Subtype.instDecidableEqSubtype

#eval List.splitOn ":-" (tokenize "C(?Y) :- B(?VariableThatIsNotNeeded, ?Y) .")

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

def parseConstantFromString (constList varList: List String) (relationList: List (String × Nat)) (symbol: String): Except String ((signatureFromLists constList varList relationList).constants) :=
  if p:symbol ∈ constList
  then Except.ok (Subtype.mk symbol p)
  else Except.error (symbol ++ " is not a constant symbol")

def parseVariableFromString (constList varList: List String) (relationList: List (String × Nat)) (symbol: String): Except String ((signatureFromLists constList varList relationList).vars) :=
  if p:symbol ∈ varList
  then Except.ok (Subtype.mk symbol p)
  else Except.error (symbol ++ " is not a variable symbol")

def parseTermFromString (constList varList: List String) (relationList: List (String × Nat)) (symbol: String): Except String (term (signatureFromLists constList varList relationList)) :=
  match parseConstantFromString constList varList relationList symbol with
  | Except.ok c => Except.ok (term.constant c)
  | Except.error _ =>
    match parseVariableFromString constList varList relationList symbol with
    | Except.ok v => Except.ok (term.variableDL v)
    | Except.error _ => Except.error (symbol ++ " is neither a variable nor a constant symbol")

def parseGroundAtomFromStack (constList varList: List String) (relationList: List (String × Nat)) (stack: List String): Except String (groundAtom (signatureFromLists constList varList relationList)) :=
  match stack with
  | List.nil => Except.error "Cannot parse an atom from an empty stack"
  | hd::tl =>
    if h:hd ∈ Prod.fst (List.unzip relationList)
    then
      let terms := List.map_except (fun x => parseConstantFromString constList varList relationList x) tl
      match terms with
      | Except.ok l =>
        if p: l.length = (signatureFromLists constList varList relationList).relationArity (Subtype.mk hd h)
        then
          Except.ok (groundAtom.mk (Subtype.mk hd h) l p)
        else Except.error "relation arity does not match"
      | Except.error msg => Except.error msg
    else Except.error (hd ++ " is not a relation symbol")


def parseGroundAtom.go (constList varList: List String) (relationList: List (String × Nat)) (l: List String) (stack: List String): Except String (groundAtom (signatureFromLists constList varList relationList)) :=
  match l with
  | List.nil => Except.error "No closing bracket"
  | hd::tl =>
    if hd == "("
    then parseGroundAtom.go constList varList relationList tl stack
    else
      if hd == ")"
      then  if tl.isEmpty
            then parseGroundAtomFromStack constList varList relationList stack
            else Except.error "Symbols after the closing bracket when parsing atom"
      else
        parseGroundAtom.go constList varList relationList tl (stack.append [hd])

def parseGroundAtom (constList varList: List String) (relationList: List (String × Nat)) (l: List String): Except String (groundAtom (signatureFromLists constList varList relationList)) := parseGroundAtom.go constList varList relationList l []

def parseAtomFromStack (constList varList: List String) (relationList: List (String × Nat)) (stack: List String): Except String (atom (signatureFromLists constList varList relationList)) :=
  match stack with
  | List.nil => Except.error "Cannot parse an atom from an empty stack"
  | hd::tl =>
    if h:hd ∈ Prod.fst (List.unzip relationList)
    then
      let terms := List.map_except (fun x => parseTermFromString constList varList relationList x) tl
      match terms with
      | Except.ok l =>
        if p: l.length = (signatureFromLists constList varList relationList).relationArity (Subtype.mk hd h)
        then
          Except.ok (atom.mk (Subtype.mk hd h) l p)
        else Except.error "relation arity does not match"
      | Except.error msg => Except.error msg
    else Except.error (hd ++ " is not a relation symbol")


def parseAtom.go (constList varList: List String) (relationList: List (String × Nat)) (l: List String) (stack: List String): Except String (atom (signatureFromLists constList varList relationList)) :=
  match l with
  | List.nil => Except.error "No closing bracket"
  | hd::tl =>
    if hd == "("
    then parseGroundAtom.go constList varList relationList tl stack
    else
      if hd == ")"
      then  if tl.isEmpty
            then parseAtomFromStack constList varList relationList stack
            else Except.error "Symbols after the closing bracket when parsing atom"
      else
        parseGroundAtom.go constList varList relationList tl (stack.append [hd])

def parseAtom (constList varList: List String) (relationList: List (String × Nat)) (l: List String): Except String (atom (signatureFromLists constList varList relationList)) := parseAtom.go constList varList relationList l []

def parseAtomList.go (constList varList: List String) (relationList: List (String × Nat)) (l: List String) (curr: List (atom (signatureFromLists constList varList relationList) )) (stack: List String): Except String (List (atom (signatureFromLists constList varList relationList))) :=
  match l with
  | List.nil =>
    if stack.isEmpty
    then Except.ok curr
    else Except.error "no closing bracket for "
  | List.cons hd tl =>
     if hd == "("
    then parseAtomList.go constList varList relationList tl curr stack
    else
      if hd == ")"
      then
        let atom := parseAtomFromStack constList varList relationList stack
        if tl = ["."]
        then
          match atom with
          | Except.ok a => Except.ok (curr ++ [a])
          | Except.error msg => Except.error msg
        else
          match atom with
          | Except.ok a => parseAtomList.go constList varList relationList tl (curr ++ [a]) []
          | Except.error msg => Except.error msg
      else
        parseAtomList.go constList varList relationList tl curr (stack.append [hd])

def parseAtomList (constList varList: List String) (relationList: List (String × Nat)) (l: List String): Except String (List (atom (signatureFromLists constList varList relationList))) := parseAtomList.go constList varList relationList l [] []

def parseRule (constList varList: List String) (relationList: List (String × Nat)) (l: List String): Except String (rule (signatureFromLists constList varList relationList)) :=
  let splitResult := List.splitOn ":-" l
  if h: splitResult.length == 1
  then
    have p: 0 < splitResult.length := by
      simp at h
      rw [h]
      simp
    match parseAtom constList varList relationList (splitResult.get (Fin.mk 0 p)) with
    | Except.ok a => Except.ok (rule.mk a [])
    | Except.error msg => Except.error msg
  else
    if h: splitResult.length == 2
    then
      have p: 0 < splitResult.length := by
        simp at h
        rw [h]
        simp
      have q: 1 < splitResult.length := by
        simp at h
        rw [h]
        simp
      match parseAtom constList varList relationList (splitResult.get (Fin.mk 0 p)) with
      | Except.ok head =>
        match parseAtomList constList varList relationList (splitResult.get (Fin.mk 1 q)) with
        | Except.ok body => Except.ok (rule.mk head body)
        | Except.error msg => Except.error msg
      | Except.error msg => Except.error msg
    else Except.error " has too many occurences of :-"

def proofTreeFromTree (constList varList: List String) (relationList: List (String × Nat)) (t: Tree) : Except String (proofTree (signatureFromLists constList varList relationList)) :=
  match t with
  | Tree.node label children =>
    match parseGroundAtom constList varList relationList (tokenize label) with
    | Except.ok a =>
      let s:= List.map_except (fun ⟨x, _h⟩  => proofTreeFromTree constList varList relationList x) children.attach
      match s with
      | Except.ok l =>
        Except.ok (proofTree.node a l)
      | Except.error msg => Except.error msg
    | Except.error msg => Except.error msg
termination_by proofTreeFromTree constList varList relationList t => sizeOf t
decreasing_by
  simp_wf
  decreasing_trivial
  apply Nat.zero_le
