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

def extendFunctionFromList {A B: Type} [DecidableEq A] (l: List (A × B)) (f: {x:A // x ∈ List.map Prod.fst l} → B) : {x:A // x ∈ List.map Prod.fst l} → B :=
  match l with
  | List.nil => f
  | ⟨a,b⟩::tl => extendFunctionFromList (fun x => if x = a then b else f x) tl

def signatureFromLists (constList varList: List String) (relationList: List (String × Nat)): signature :=
{constants := {x: String // x ∈ constList}, vars := {x: String // x ∈ varList}, relationSymbols := {x: String // x ∈ List.map Prod.fst relationList}, relationArity := extendFunctionFromList relationList (fun _ => 0)}

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

def parseGroundAtom (constList varList: List String) (relationList: List (String × Nat)) (l: List String): Except String (groundAtom (signatureFromLists constList varList relationList)) :=
  sorry


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
