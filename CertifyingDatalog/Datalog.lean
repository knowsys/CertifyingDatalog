import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs

-- basic definitions
structure signature :=
  (constants: Type)
  (vars: Type)
  (relationSymbols: Type)
  (relationArity: relationSymbols → ℕ)

lemma finset_union_empty_iff {A: Type} {s1 s2: Finset A}: (s1 ∪ s2 = ∅) ↔ s1 = ∅ ∧ s2 = ∅ := sorry

section basic
variable (τ: signature)

inductive term : Type
| constant : τ.constants → term
| variableDL : τ.vars → term

structure atom :=
  (symbol: τ.relationSymbols)
  (atom_terms: List (term τ ))
  (term_length: atom_terms.length = τ.relationArity symbol)

structure rule :=
  (head: atom τ)
  (body: List (atom τ))

def Program: Type := Finset (rule τ)

end basic
-- grounding

section grounding
variable (τ: signature) [DecidableEq τ.vars]

def termVariables: term τ → Finset τ.vars
| (term.constant _) => ∅
| (term.variableDL v) => {v}

def collectResultsToFinset {A: Type} (f: A → Finset τ.vars): List A → Finset τ.vars
| [] => ∅
| hd::tl => (f hd) ∪ (collectResultsToFinset f tl)

def atomVariables (a: atom τ) : Finset τ.vars := collectResultsToFinset τ (termVariables τ) a.atom_terms

structure groundAtom :=
  (atom: atom τ)
  (grounded: atomVariables τ atom = ∅)

def groundAtom.toAtom (ga: groundAtom τ) := ga.atom

def ruleVariables (r: rule τ): Finset τ.vars := (atomVariables τ r.head) ∪ (collectResultsToFinset τ (atomVariables τ) r.body)

structure groundRule :=
  (rule: rule τ)
  (grounded: ruleVariables τ rule = ∅)

def groundRule.toRule (gr: groundRule τ) := gr.rule

def grounding:= τ.vars → τ.constants

def applyGroundingTerm (g: grounding τ) (t: term τ): term τ :=
  match t with
  | term.constant c => term.constant c
  | term.variableDL v => term.constant (g v)

lemma applyGroundingTermRemovesVariables (g: grounding τ) (t: term τ): termVariables τ (applyGroundingTerm τ g t) = ∅ :=
by
  cases t with
  | constant c =>
    unfold applyGroundingTerm
    unfold termVariables
    simp
  | variableDL v =>
    unfold applyGroundingTerm
    unfold termVariables
    simp



lemma applyGroundingTermPreservesLength (g:grounding τ) (a: atom τ): (List.map (applyGroundingTerm τ g) a.atom_terms ).length = τ.relationArity a.symbol :=
by
  rcases a with ⟨symbol, terms, term_length⟩
  simp
  rw [ term_length]


def applyGroundingAtom (g: grounding τ) (a: atom τ): atom τ := {symbol:= a.symbol, atom_terms:= List.map (applyGroundingTerm τ g) a.atom_terms, term_length := applyGroundingTermPreservesLength τ g a}

lemma groundingRemovesAtomVariables (a: atom τ) (g: grounding τ): atomVariables τ (applyGroundingAtom τ g a) = ∅ :=
by
  unfold applyGroundingAtom
  unfold atomVariables
  simp
  induction a.atom_terms with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    simp
    rw [ih, Finset.union_empty, applyGroundingTermRemovesVariables]

def atomGrounding (a: atom τ) (g: grounding τ): groundAtom τ := {atom := applyGroundingAtom τ g a, grounded := groundingRemovesAtomVariables τ a g}

def applyGroundingRule (r: rule τ) (g: grounding τ): rule τ := {head := applyGroundingAtom τ g r.head, body := List.map (applyGroundingAtom τ g) r.body }

lemma groundingRemovesRuleVariables (r: rule τ) (g: grounding τ): ruleVariables τ (applyGroundingRule τ r g) = ∅ := by
  unfold applyGroundingRule
  unfold ruleVariables
  simp
  rw [groundingRemovesAtomVariables, Finset.empty_union]
  induction r.body with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    simp
    rw [ih, groundingRemovesAtomVariables, Finset.empty_union]

def ruleGrounding (r: rule τ) (g:grounding τ): groundRule τ := {rule := applyGroundingRule τ r g, grounded := groundingRemovesRuleVariables τ r g}

lemma headOfGroundRuleIsGrounded (r: groundRule τ): atomVariables τ r.rule.head = ∅ := sorry

def groundRuleHead (r: groundRule τ): groundAtom τ := {atom:= r.rule.head, grounded := headOfGroundRuleIsGrounded τ r}

lemma bodyOfGroundRuleIsGrounded (r: groundRule τ) (a: atom τ) (mem: a ∈ r.rule.body): atomVariables τ a = ∅ := sorry

def groundRuleBodySet (r: groundRule τ): Set (groundAtom τ) := sorry

def groundRuleFromAtoms (head: groundAtom τ) (body: List (groundAtom τ)): groundRule τ := sorry

def groundProgram (P: Set (rule τ)) := {r: groundRule τ | ∃ (r': rule τ) (g: grounding τ), r' ∈ P ∧ r = ruleGrounding τ r' g}

end grounding
section semantics
variable (τ:signature) [DecidableEq τ.vars]

class database:=
  (contains: groundAtom τ → Prop)

inductive proofTree
| node: (groundAtom τ) → List proofTree →  proofTree

def root: proofTree τ → groundAtom τ
| proofTree.node a _ => a

def children: proofTree τ → List (proofTree τ)
| proofTree.node _ l => l

def isValid (P: Set (rule τ)) (d: database τ) (t: proofTree τ): Prop := ( ∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding τ r g = groundRuleFromAtoms τ (root τ t) (List.map (root τ) (children τ t)) ) ∨ (children τ t = [] ∧ d.contains (root τ t))

def proofTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∃ (t: proofTree τ), root τ t = a ∧ isValid τ P d t}

def ruleTrue (r: groundRule τ) (i: Set (groundAtom τ)): Prop := groundRuleBodySet τ r ⊆ i → groundRuleHead τ r ∈ i

def model (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) : Prop := ∀ (r: groundRule τ), r ∈ groundProgram τ P → ruleTrue τ r i ∧ ∀ (a: groundAtom τ), d.contains a → a ∈ i

theorem proofTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model τ P d (proofTheoreticSemantics τ P d) := sorry

def modelTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= sorry

theorem SemanticsEquivalence (P: Set (rule τ)) (d: database τ): proofTheoreticSemantics τ P d = modelTheoreticSemantics τ P d := sorry

end semantics
