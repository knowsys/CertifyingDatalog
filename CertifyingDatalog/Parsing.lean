import Batteries.Data.List.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.Basic
import CertifyingDatalog.GraphValidation
import CertifyingDatalog.OrderedGraphValidation
import Lean.Data.Json.FromToJson

def NatToString (n: ℕ): String :=
  match n with
  | 0 => " "
  | Nat.succ n => "I" ++ NatToString n

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

def mockTermList.toString (l: List mockTerm): String :=
  match l with
  | [] => ""
  | hd::tl => mockTerm.toString hd ++ "," ++ mockTermList.toString tl

--#eval Lean.toJson (mockTerm.constant "b")

structure mockAtom where
  (symbol: String)
  (terms: List mockTerm)
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

def mockAtom.toString (ma: mockAtom): String := ma.symbol ++ "(" ++ mockTermList.toString ma.terms ++ ")"

--#eval Lean.toJson (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"])

structure mockRule where
  head: mockAtom
  body: List (mockAtom)
deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

inductive jsonTree (A: Type)
| node (label: A) (children: List (jsonTree A))
deriving Lean.FromJson, Lean.ToJson

structure problemInput where
  (trees: List (jsonTree mockAtom))
  (program: List (mockRule))
deriving Lean.FromJson, Lean.ToJson

structure parsingArityHelper where
  (relationList: List String)
  (arity: {x // x ∈ relationList} → Nat)

def emptyParsingArityHelper: parsingArityHelper := {relationList:= [], arity:= fun _ => 0}

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
        have h': x.val ∈ (sig.relationList ++ [symbol] ) := by
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

instance (helper: parsingArityHelper): Inhabited (parsingSignature helper).constants :=
by
  unfold parsingSignature
  simp
  use ['a']

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).vars :=
by
  unfold parsingSignature
  simp
  apply instDecidableEqString

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).relationSymbols :=  Subtype.instDecidableEq

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).relationSymbols :=  instHashableSubtype

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).constants :=  instHashableString

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).vars :=  instHashableString

instance (helper: parsingArityHelper): ToString (parsingSignature helper).relationSymbols :=  instToStringSubtype

instance (helper: parsingArityHelper): ToString (parsingSignature helper).constants :=  instToStringString

instance (helper: parsingArityHelper): ToString (parsingSignature helper).vars :=  instToStringString

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

def getArityHelperFromProgram.go (helper: parsingArityHelper) (l: List mockRule): Except String parsingArityHelper :=
  match l with
  | [] => Except.ok helper
  | hd::tl =>
    match getArityHelperFromMockRule helper hd with
    | Except.error e => Except.error e
    | Except.ok newHelper => getArityHelperFromProgram.go newHelper tl

def getArityHelperFromProgram (l: List mockRule): Except String parsingArityHelper := getArityHelperFromProgram.go emptyParsingArityHelper l

def transformMockTermToTerm (helper: parsingArityHelper) (mt: mockTerm): term (parsingSignature helper) :=
  match mt with
  | mockTerm.constant c => term.constant c
  | mockTerm.variable v => term.variableDL v

def transformMockTermToConstant (helper: parsingArityHelper) (mt: mockTerm): Except String (parsingSignature helper).constants :=
  match mt with
  | mockTerm.constant c => Except.ok c
  | mockTerm.variable v => Except.error ("Encountered variable" ++ v ++ "in ground atom ")

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
    else Except.error ("Wrong arity for " ++ ma.toString ++ "Expected " ++ NatToString (helper.arity (Subtype.mk ma.symbol h)) ++ "Actually " ++  NatToString ma.terms.length)
  else Except.error ("Unknown symbol" ++ ma.symbol)

def transformMockAtomToGroundAtom (helper: parsingArityHelper) (ma: mockAtom): Except String (groundAtom (parsingSignature helper)) :=
  if h: ma.symbol ∈ helper.relationList
  then
    if p: helper.arity (Subtype.mk ma.symbol h) = ma.terms.length
    then
      match q: List.map_except (transformMockTermToConstant helper) ma.terms with
      | Except.error msg => Except.error ("Error parsing ground atom" ++ msg)
      | Except.ok l =>

      have length: List.length l = signature.relationArity (parsingSignature helper) { val := ma.symbol, property := h } :=
      by
        unfold parsingSignature
        simp
        rw [p]
        apply Eq.symm
        apply List.map_except_ok_length'
        apply q


    Except.ok {symbol := (Subtype.mk ma.symbol h), atom_terms := l, term_length := length}
    else Except.error ("Transform to groundAtom -- Wrong arity for " ++ ma.toString ++ " Expected " ++ NatToString (helper.arity (Subtype.mk ma.symbol h)) ++ "Actually " ++  NatToString ma.terms.length)
  else Except.error ("Unknown symbol" ++ ma.symbol)

def transformMockRuleToRule (helper: parsingArityHelper) (mr: mockRule): Except String (rule (parsingSignature helper)) :=
  match transformMockAtomToAtom helper mr.head with
  | Except.error e => Except.error e
  | Except.ok head =>
    match List.map_except (transformMockAtomToAtom helper) mr.body with
    | Except.error e => Except.error e
    | Except.ok body => Except.ok {head:= head, body:= body}


def proofTreeFromTree (helper: parsingArityHelper) (t: jsonTree mockAtom) : Except String (proofTree (parsingSignature helper)) :=
  match t with
  | jsonTree.node label children =>
    match transformMockAtomToGroundAtom helper label with
    | Except.ok a =>
      let s:= List.map_except (fun ⟨x, _h⟩  => proofTreeFromTree  helper x) children.attach
      match s with
      | Except.ok l =>
        Except.ok (tree.node a l)
      | Except.error msg => Except.error msg
    | Except.error msg => Except.error msg
termination_by sizeOf t
decreasing_by
  simp_wf
  decreasing_trivial

structure verificationProblem (helper: parsingArityHelper) where
  (trees: List (proofTree (parsingSignature helper)))
  (program: List (rule (parsingSignature helper)))

structure verificationProblemSignatureWrapper where
  (helper: parsingArityHelper)
  (problem: verificationProblem helper)

def convertProblemInputToVerificationProblem (input: problemInput): Except String verificationProblemSignatureWrapper :=
  match getArityHelperFromProgram input.program with
  | Except.error e => Except.error ("Error parsing program --" ++ e)
  | Except.ok helper =>
    match List.map_except (proofTreeFromTree helper) input.trees with
  | Except.error e => Except.error ("Error parsing trees -- " ++ e)
  | Except.ok trees =>
    match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {helper := helper, problem := {trees := trees, program := program}}


-- graph validation
structure mockEdge where
  (vertex: mockAtom)
  (successors: List (mockAtom))
deriving DecidableEq, Lean.FromJson, Lean.ToJson

--#eval Lean.toJson (edge.mk (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"]) (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"]))

structure mockGraph where
  -- (vertices: List mockAtom)
  (edges: List mockEdge)
deriving Lean.FromJson, Lean.ToJson

structure graphInputProblem where
  (graph: mockGraph)
  (program: List mockRule)
deriving Lean.FromJson, Lean.ToJson

def addVertex (helper: parsingArityHelper) (ma: mockAtom) (g: Graph (groundAtom (parsingSignature helper)) )(atomPosMap: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ): Except String ((Graph (groundAtom (parsingSignature helper))) × ℕ ×  Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) :=
  match transformMockAtomToGroundAtom helper ma with
  | Except.error e => Except.error e
  | Except.ok ga =>
    match atomPosMap.find? ga with
    | some i => Except.ok (g, i, atomPosMap)
    | none =>
      let atomPosMap' := atomPosMap.insert ga g.val.size
      let graph' := g.addVertex ga

      Except.ok (graph', g.val.size, atomPosMap')

lemma addVertexSafe (helper: parsingArityHelper) (ma: mockAtom) (g g': Graph (groundAtom (parsingSignature helper)) )(atomPosMap atomPosMap': Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (i: ℕ) (h: addVertex helper ma g atomPosMap = Except.ok (g', i, atomPosMap')) (hmap: ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap.find? ga = some i → i < g.val.size): i < g'.val.size := by
  unfold addVertex at h
  simp at h
  split at h
  · simp at h
  · split at h
    · rename_i ga _ _ j find
      specialize hmap ga j find
      simp at h
      rcases h with ⟨hg, hi, _⟩
      rw [← hg, ← hi]
      exact hmap
    · simp at h
      rcases h with ⟨hg, hi, _⟩
      rw [← hg, ← hi, Graph.addVertex]
      unfold PreGraph.addVertex
      simp


def addVertexList.go (helper: parsingArityHelper) (l: List mockAtom) (g: Graph (groundAtom (parsingSignature helper)) )(atomPosMap: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (currList: List ℕ): Except String ((Graph (groundAtom (parsingSignature helper))) × List ℕ ×  Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) :=
  match l with
  | [] => Except.ok (g, currList, atomPosMap)
  | hd::tl =>
    match addVertex helper hd g atomPosMap with
    | Except.error e => Except.error e
    | Except.ok (g', i, atomPosMap') =>
      addVertexList.go helper tl g' atomPosMap' (currList.concat i)

def addVertexList (helper: parsingArityHelper) (l: List mockAtom) (g: Graph (groundAtom (parsingSignature helper)) )(atomPosMap: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ): Except String ((Graph (groundAtom (parsingSignature helper))) × List ℕ ×  Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) :=
  addVertexList.go helper l g atomPosMap []

lemma addVertexListGraphSizeLE (helper: parsingArityHelper) (l: List mockAtom) (g g': Graph (groundAtom (parsingSignature helper)) ) (l': List ℕ)(atomPosMap atomPosMap': Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (h: addVertexList helper l g atomPosMap = Except.ok (g', l', atomPosMap')): g.val.size ≤ g'.val.size := by
  sorry

def addMockEdgeVertices  (helper: parsingArityHelper) (me:mockEdge) (currGraph: Graph (groundAtom (parsingSignature helper))) (atomPosMap: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ): Except String ((Graph (groundAtom (parsingSignature helper))) × ℕ × List ℕ ×  Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) :=
  match addVertex helper me.vertex currGraph atomPosMap with
  | Except.error e => Except.error e
  | Except.ok (g', i, atomPosMap') =>
    match addVertexList helper me.successors g' atomPosMap' with
    | Except.error e => Except.error e
    | Except.ok (g2, l, atomPosMap2) =>
      Except.ok (g2, i, l, atomPosMap2)

lemma addMockEdgeVerticesSafe (helper: parsingArityHelper) (me:mockEdge) (currGraph g: Graph (groundAtom (parsingSignature helper))) (atomPosMap atomPosMap': Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (i:ℕ) (l: List ℕ) (h: addMockEdgeVertices helper me currGraph atomPosMap = Except.ok (g, i, l, atomPosMap')) (hmap: ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap.find? ga = some i → i < currGraph.val.size) : i < g.val.size := by
  revert h
  unfold addMockEdgeVertices
  split
  · simp
  · rename_i g' j atomPosMap2 h
    split
    · simp
    · rename_i g2 l2 atomPosMap3 h'
      simp
      intro hg hi _ _
      rw [← hi, ← hg]
      apply Nat.lt_of_lt_of_le
      apply addVertexSafe (h:=h) (hmap:=hmap)
      apply addVertexListGraphSizeLE (h:=h')



lemma addMockEdgeVerticesListSafe (helper: parsingArityHelper) (me:mockEdge) (currGraph g: Graph (groundAtom (parsingSignature helper))) (atomPosMap atomPosMap': Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (i:ℕ) (l: List ℕ) (h: addMockEdgeVertices helper me currGraph atomPosMap = Except.ok (g, i, l, atomPosMap')): ∀ (j: ℕ), j ∈ l → j < g.val.size := by
  unfold addMockEdgeVertices at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · sorry

lemma addMockEdgeVerticesPreservesMapProp (helper: parsingArityHelper) (me:mockEdge) (currGraph g: Graph (groundAtom (parsingSignature helper))) (atomPosMap atomPosMap': Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (i:ℕ) (l: List ℕ) (h: addMockEdgeVertices helper me currGraph atomPosMap = Except.ok (g, i, l, atomPosMap')) (hmap: ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap.find? ga = some i → i < g.val.size): ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap'.find? ga = some i → i < g.val.size := by
  sorry


def getGraph.go (helper: parsingArityHelper) (l: List mockEdge) (currGraph: Graph (groundAtom (parsingSignature helper))) (atomPosMap: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) (hmap: ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap.find? ga = some i → i < currGraph.val.size) : Except String (Graph (groundAtom (parsingSignature helper))) :=
  match l with
  | [] => Except.ok currGraph
  | hd::tl =>
    match h:addMockEdgeVertices helper hd currGraph atomPosMap with
    | Except.error e => Except.error e
    | Except.ok (currGraph2, v, succs, atomPosMap2) =>
      have hv: v < currGraph2.val.size := by
        apply addMockEdgeVerticesSafe (h:=h) (hmap:=hmap)
      have hsuccs:∀ (i: ℕ), i ∈ succs → i < currGraph2.val.size := by
        apply addMockEdgeVerticesListSafe (h:=h)

      let currGraph3 := currGraph2.addSuccessors v hv succs hsuccs

      have hmap': ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), atomPosMap2.find? ga = some i → i < currGraph3.val.size := by
        sorry

      getGraph.go helper tl currGraph3 atomPosMap2 hmap'

lemma emptyHashMapMapProp : ∀ (ga: groundAtom (parsingSignature helper)) (i: ℕ), Batteries.HashMap.find? (∅: Batteries.HashMap (groundAtom (parsingSignature helper)) ℕ) ga = some i → i < (Graph.emptyGraph (groundAtom (parsingSignature helper))).val.size := by
  simp

def getGraph (helper: parsingArityHelper) (g: mockGraph): Except String (Graph (groundAtom (parsingSignature helper))) :=
  getGraph.go helper g.edges (Graph.emptyGraph (groundAtom (parsingSignature helper))) ∅ emptyHashMapMapProp

structure graphVerificationProblem (helper: parsingArityHelper) where
  (graph: Graph (groundAtom (parsingSignature helper)))
  (program: List (rule (parsingSignature helper)))

structure graphVerificationProblemSignatureWrapper where
  (helper: parsingArityHelper)
  (problem: graphVerificationProblem helper)

def convertGraphProblemInputToGraphVerificationProblem (input: graphInputProblem): Except String graphVerificationProblemSignatureWrapper :=
  match getArityHelperFromProgram input.program with
  | Except.error e => Except.error ("Error parsing program --" ++ e)
  | Except.ok helper =>
    match getGraph helper input.graph with
    | Except.error e => Except.error ("Error parsing graph --" ++ e)
    | Except.ok graph =>
      match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {helper := helper, problem := {graph := graph, program := program}}

-- orderedGraph

structure mockOrderedGraphVertex where
  (label: mockAtom)
  (predecessors: List ℕ)
deriving Lean.FromJson, Lean.ToJson


structure mockOrderedGraph: Type where
  (vertices: Array mockOrderedGraphVertex)
deriving Lean.FromJson, Lean.ToJson


def getOrderedGraph.go (helper: parsingArityHelper) (mg: mockOrderedGraph) (curr: orderedProofGraph (parsingSignature helper)) (pos: ℕ): Except String (orderedProofGraph (parsingSignature helper)) :=
  if h: pos < mg.vertices.size
  then
    match transformMockAtomToGroundAtom helper mg.vertices[pos].1 with
    | Except.error e => Except.error e
    | Except.ok a =>
      getOrderedGraph.go helper mg (curr.push (a, mg.vertices[pos].2)) (Nat.succ pos)
  else
    Except.ok curr
termination_by mg.vertices.size - pos

def getOrderedGraph (helper: parsingArityHelper) (mg: mockOrderedGraph):  Except String (orderedProofGraph (parsingSignature helper)) := getOrderedGraph.go helper mg #[] 0


structure orderedGraphInputProblem where
  (graph: mockOrderedGraph)
  (program: List mockRule)
deriving Lean.FromJson, Lean.ToJson

structure orderedGraphVerificationProblem (helper: parsingArityHelper) where
  (graph: orderedProofGraph (parsingSignature helper))
  (program: List (rule (parsingSignature helper)))

structure orderedGraphVerificationProblemSignatureWrapper where
  (helper: parsingArityHelper)
  (problem: orderedGraphVerificationProblem helper)

def convertOrderedGraphProblemInputToOrderedGraphVerificationProblem (input: orderedGraphInputProblem): Except String orderedGraphVerificationProblemSignatureWrapper :=
  match getArityHelperFromProgram input.program with
  | Except.error e => Except.error ("Error parsing program --" ++ e)
  | Except.ok helper =>
    match getOrderedGraph helper input.graph with
    | Except.error e => Except.error ("Error parsing graph --" ++ e)
    | Except.ok graph =>
      match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {helper := helper, problem := {graph := graph, program := program}}
