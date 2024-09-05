import CertifyingDatalog.Datalog
import CertifyingDatalog.Basic
import CertifyingDatalog.GraphValidation
import CertifyingDatalog.OrderedGraphValidation
import Lean.Data.Json.FromToJson

def Nat.toString (n: ℕ): String :=
  match n with
  | 0 => " "
  | Nat.succ n => "I" ++ n.toString

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

inductive InputTerm
| constant: String → InputTerm
| variable: String → InputTerm
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

namespace InputTerm
  def toString (t: InputTerm): String :=
    match t with
    | .constant c => "constant " ++ c
    | .variable v => "variable " ++ v

  def listToString (l: List InputTerm): String :=
    match l with
    | [] => ""
    | hd::tl => hd.toString ++ "," ++ InputTerm.listToString tl
end InputTerm

structure InputAtom where
  (symbol: String)
  (terms: List InputTerm)
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

namespace InputAtom
  def toString (a: InputAtom): String := a.symbol ++ "(" ++ InputTerm.listToString a.terms ++ ")"
end InputAtom

structure InputRule where
  head: InputAtom
  body: List (InputAtom)
deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

inductive InputTree (A : Type u)
| node (label: A) (children: List (InputTree A))
deriving Lean.FromJson, Lean.ToJson

structure TreeProblemInput where
  (trees: List (InputTree InputAtom))
  (program: List (InputRule))
deriving Lean.FromJson, Lean.ToJson

structure ParseArityHelper where
  (relationList: List String)
  (arity: {x // x ∈ relationList} → Nat)

namespace ParseArityHelper
  def empty: ParseArityHelper := {relationList := [], arity := fun _ => 0}

  def extend (helper: ParseArityHelper) (symbol: String) (arity: Nat) : Except String ParseArityHelper :=
    if h: symbol ∈ helper.relationList
    then if helper.arity ⟨symbol, h⟩ = arity then Except.ok helper else Except.error ("Mismatched arity for " ++ symbol ++ " Given ")
    else
      Except.ok {
        relationList := symbol :: helper.relationList,
        arity := (fun x =>
          if q:(x = symbol)
          then arity
          else helper.arity ⟨x, by have prop := x.prop; simp [q] at prop; exact prop⟩
        )
      }

  def extend_inputAtom (helper : ParseArityHelper) (a : InputAtom) : Except String ParseArityHelper :=
    helper.extend a.symbol a.terms.length

  def extend_inputAtomList (helper : ParseArityHelper) (as : List InputAtom) : Except String ParseArityHelper :=
    as.foldl_except (fun acc a => acc.extend_inputAtom a) (Except.ok helper)

  def extend_inputRule (helper : ParseArityHelper) (r : InputRule) : Except String ParseArityHelper :=
    helper.extend_inputAtomList (r.head :: r.body)

  def extend_inputRuleList (helper : ParseArityHelper) (rs : List InputRule) : Except String ParseArityHelper :=
    rs.foldl_except (fun acc r => acc.extend_inputRule r) (Except.ok helper)

  def fromInputProgram (prog : List InputRule) : Except String ParseArityHelper :=
    ParseArityHelper.empty.extend_inputRuleList prog

  def toSignature (helper : ParseArityHelper) : Signature :=
    {constants:= String, vars:= String, relationSymbols := {x // x ∈ helper.relationList}, relationArity := helper.arity}

  instance (helper: ParseArityHelper): DecidableEq helper.toSignature.constants := by
    unfold toSignature; simp; apply instDecidableEqString
  instance (helper: ParseArityHelper): DecidableEq helper.toSignature.vars := by
    unfold toSignature; simp; apply instDecidableEqString
  instance (helper: ParseArityHelper): DecidableEq helper.toSignature.relationSymbols := Subtype.instDecidableEq

  instance (helper: ParseArityHelper): Inhabited helper.toSignature.constants where
    default := "DEFAULT_CONSTANT"

  instance (helper: ParseArityHelper): Hashable helper.toSignature.constants := instHashableString
  instance (helper: ParseArityHelper): Hashable helper.toSignature.vars := instHashableString
  instance (helper: ParseArityHelper): Hashable helper.toSignature.relationSymbols := instHashableSubtype

  instance (helper: ParseArityHelper): ToString helper.toSignature.constants := instToStringString
  instance (helper: ParseArityHelper): ToString helper.toSignature.vars := instToStringString
  instance (helper: ParseArityHelper): ToString helper.toSignature.relationSymbols := instToStringSubtype
end ParseArityHelper

namespace InputTerm
  def toTerm (helper : ParseArityHelper) : InputTerm -> Term (helper.toSignature)
  | .constant c => Term.constant c
  | .variable v => Term.variableDL v

  def toGroundTerm (helper : ParseArityHelper) : InputTerm -> Except String (helper.toSignature).constants
  | .constant c => Except.ok c
  | .variable v => Except.error ("Encountered variable" ++ v ++ "in ground atom ")
end InputTerm

namespace InputAtom
  def toAtom (helper : ParseArityHelper) (a : InputAtom) : Except String (Atom helper.toSignature) :=
    if h: a.symbol ∈ helper.relationList
    then
      if p: helper.arity ⟨a.symbol, h⟩ = a.terms.length
      then
        Except.ok {
          symbol := ⟨a.symbol, h⟩
          atom_terms := a.terms.map (InputTerm.toTerm helper)
          term_length := by rw [List.length_map]; rw [← p]; unfold ParseArityHelper.toSignature; simp
        }
      else Except.error ("Wrong arity for relation symbol '" ++ a.toString ++ "'. Expected: " ++ (helper.arity ⟨a.symbol, h⟩).toString ++ "Got: " ++ a.terms.length.toString)
    else Except.error ("Unknown relation symbol: " ++ a.symbol)

  def toGroundAtom (helper : ParseArityHelper) (a : InputAtom) : Except String (GroundAtom helper.toSignature) :=
    if h: a.symbol ∈ helper.relationList
    then
      if p: helper.arity ⟨a.symbol, h⟩ = a.terms.length
      then
        match q : a.terms.mapExcept (InputTerm.toGroundTerm helper) with
        | .error err => Except.error err
        | .ok terms =>
          Except.ok {
            symbol := ⟨a.symbol, h⟩
            atom_terms := terms
            term_length := by rw [← List.mapExcept_ok_length (InputTerm.toGroundTerm helper)]; unfold ParseArityHelper.toSignature; simp; rw [p]; exact q
          }
      else Except.error ("Wrong arity for relation symbol '" ++ a.toString ++ "'. Expected: " ++ (helper.arity ⟨a.symbol, h⟩).toString ++ "Got: " ++ a.terms.length.toString)
    else Except.error ("Unknown relation symbol: " ++ a.symbol)
end InputAtom

namespace InputRule
  def toRule (helper : ParseArityHelper) (r : InputRule) : Except String (Rule helper.toSignature) :=
    match r.head.toAtom helper with
    | .error err => Except.error err
    | .ok head =>
      (r.body.mapExcept (InputAtom.toAtom helper)).map (fun body => {
        head := head
        body := body
      })
end InputRule

namespace InputTree
  def toProofTreeSkeleton (helper : ParseArityHelper) : InputTree InputAtom -> Except String (ProofTreeSkeleton helper.toSignature)
  | .node label children =>
    match label.toGroundAtom helper with
    | .error err => Except.error err
    | .ok root =>
      (children.attach.mapExcept (fun ⟨t, _t_mem_required_for_termination⟩ =>
        t.toProofTreeSkeleton helper
      )).map (fun ts =>
        Tree.node root ts
      )
end InputTree

structure TreeVerificationProblem where
  helper: ParseArityHelper
  trees: List (ProofTreeSkeleton helper.toSignature)
  program: Program helper.toSignature

namespace TreeVerificationProblem
  def fromProblemInput (input : TreeProblemInput) : Except String TreeVerificationProblem :=
    match ParseArityHelper.fromInputProgram input.program with
    | .error err => Except.error err
    | .ok helper =>
      match input.trees.mapExcept (InputTree.toProofTreeSkeleton helper) with
      | .error err => Except.error err
      | .ok trees =>
        match input.program.mapExcept (InputRule.toRule helper) with
        | .error err => Except.error err
        | .ok program => Except.ok {
          helper
          trees
          program
        }
end TreeVerificationProblem

structure InputEdge where
  vertex : InputAtom
  predecessors : List InputAtom
deriving DecidableEq, Lean.FromJson, Lean.ToJson

structure InputGraph where
  edges : List InputEdge
deriving Lean.FromJson, Lean.ToJson

namespace InputGraph
  def toGraph (helper : ParseArityHelper) (input : InputGraph) : Except String (Graph (GroundAtom helper.toSignature)) :=
    input.edges.foldl_except (fun graph edge =>
      match edge.vertex.toGroundAtom helper with
      | .error err => Except.error err
      | .ok v =>
        (edge.predecessors.mapExcept (InputAtom.toGroundAtom helper)).map (fun preds =>
          graph.add_vertex_with_predecessors v preds
        )
    ) (Except.ok (Graph.from_vertices []))
end InputGraph

structure GraphProblemInput where
  graph : InputGraph
  program : List InputRule
deriving Lean.FromJson, Lean.ToJson

structure GraphVerificationProblem where
  helper: ParseArityHelper
  graph: Graph (GroundAtom helper.toSignature)
  program: Program helper.toSignature

namespace GraphVerificationProblem
  def fromProblemInput (input : GraphProblemInput) : Except String GraphVerificationProblem :=
    match ParseArityHelper.fromInputProgram input.program with
    | .error err => Except.error err
    | .ok helper =>
      match input.graph.toGraph helper with
      | .error err => Except.error err
      | .ok graph =>
        match input.program.mapExcept (InputRule.toRule helper) with
        | .error err => Except.error err
        | .ok program => Except.ok {
          helper
          graph
          program
        }
end GraphVerificationProblem

structure InputOrderedGraphEdge where
  label : InputAtom
  predecessors : List Nat
deriving Lean.FromJson, Lean.ToJson

structure InputOrderedGraph where
  edges : Array InputOrderedGraphEdge
deriving Lean.FromJson, Lean.ToJson

namespace InputOrderedGraph
  def toOrderedProofGraph (helper : ParseArityHelper) (input : InputOrderedGraph) : Except String (OrderedProofGraph helper.toSignature) :=
    input.edges.foldl (fun acc edge =>
      match acc with
      | .error err => Except.error err
      | .ok graph =>
        if h : edge.predecessors.all (fun pred => pred < graph.val.size)
        then
          (edge.label.toGroundAtom helper).map (fun label =>
            ⟨graph.val.push ⟨label, edge.predecessors⟩, by
              intro ⟨i, i_lt⟩
              simp at i_lt
              cases Decidable.em (i < graph.val.size) with
              | inl i_lt_g =>
                simp
                rw [Array.get_push_lt]
                apply graph.prop
                exact i_lt_g
              | inr i_not_lt_g =>
                have : i = graph.val.size := by cases Nat.le_iff_lt_or_eq.mp (Nat.le_of_lt_succ i_lt); contradiction; assumption
                simp [this]
                simp at h
                exact h
            ⟩
          )
        else
          Except.error "The Graph is not properly ordered. Predecessors of nodes must occur before predecessors. You may try the regular graph input instead."
    ) (Except.ok ⟨#[], by intro i; have isLt := i.isLt; simp at isLt⟩)
end InputOrderedGraph

structure OrderedGraphProblemInput where
  graph : InputOrderedGraph
  program : List InputRule
deriving Lean.FromJson, Lean.ToJson

structure OrderedGraphVerificationProblem where
  helper: ParseArityHelper
  graph: OrderedProofGraph helper.toSignature
  program: Program helper.toSignature

namespace OrderedGraphVerificationProblem
  def fromProblemInput (input : OrderedGraphProblemInput) : Except String OrderedGraphVerificationProblem :=
    match ParseArityHelper.fromInputProgram input.program with
    | .error err => Except.error err
    | .ok helper =>
      match input.graph.toOrderedProofGraph helper with
      | .error err => Except.error err
      | .ok graph =>
        match input.program.mapExcept (InputRule.toRule helper) with
        | .error err => Except.error err
        | .ok program => Except.ok {
          helper
          graph
          program
        }
end OrderedGraphVerificationProblem

