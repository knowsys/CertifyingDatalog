import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs

-- basic definitions
structure signature :=
  (constants: Type)
  (vars: Type)
  (relationSymbols: Type)
  (relationArity: relationSymbols → ℕ)


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

end basic
-- grounding

section grounding
variable (τ: signature) [DecidableEq τ.vars]

def termVariables: term τ → Set τ.vars
| (term.constant _) => ∅
| (term.variableDL v) => {v}

def collectResultsToFinset {A: Type} (f: A → Set τ.vars): List A → Set τ.vars
| [] => ∅
| hd::tl => (f hd) ∪ (collectResultsToFinset f tl)

lemma collectResultsToFinset_Empty{A: Type} (f: A → Set τ.vars) (l: List A): collectResultsToFinset τ f l = ∅ ↔ ∀(a:A), a ∈ l → f a = ∅ := sorry

lemma collectResultsToFinsetIsEmptyIfMemberAre{A: Type} (f: A → Set τ.vars) (l: List A)(a: A)(mem: a ∈ l) (empty: collectResultsToFinset τ f l = ∅): f a = ∅ := sorry


def atomVariables (a: atom τ) : Set τ.vars := collectResultsToFinset τ (termVariables τ) a.atom_terms

structure groundAtom :=
  (atom: atom τ)
  (grounded: atomVariables τ atom = ∅)

def groundAtom.toAtom (ga: groundAtom τ) := ga.atom

def ruleVariables (r: rule τ): Set τ.vars := (atomVariables τ r.head) ∪ (collectResultsToFinset τ (atomVariables τ) r.body)

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
    constructor
    rw [applyGroundingTermRemovesVariables]
    apply ih

def atomGrounding (a: atom τ) (g: grounding τ): groundAtom τ := {atom := applyGroundingAtom τ g a, grounded := groundingRemovesAtomVariables τ a g}

def applyGroundingRule (r: rule τ) (g: grounding τ): rule τ := {head := applyGroundingAtom τ g r.head, body := List.map (applyGroundingAtom τ g) r.body }

lemma groundingRemovesRuleVariables (r: rule τ) (g: grounding τ): ruleVariables τ (applyGroundingRule τ r g) = ∅ := by
  unfold applyGroundingRule
  unfold ruleVariables
  simp
  rw [groundingRemovesAtomVariables]
  induction r.body with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    simp
    constructor
    rw [groundingRemovesAtomVariables]
    rcases ih with ⟨_, right⟩
    apply right


def ruleGrounding (r: rule τ) (g:grounding τ): groundRule τ := {rule := applyGroundingRule τ r g, grounded := groundingRemovesRuleVariables τ r g}

lemma headOfGroundRuleIsGrounded (r: groundRule τ): atomVariables τ r.rule.head = ∅ :=
by
  have rground: ruleVariables τ r.rule = ∅
  apply r.grounded
  unfold ruleVariables at rground
  rw [Set.union_empty_iff] at rground
  rcases rground with ⟨left,_⟩
  apply left

def groundRuleHead (r: groundRule τ): groundAtom τ := {atom:= r.rule.head, grounded := headOfGroundRuleIsGrounded τ r}

lemma bodyOfGroundRuleIsGrounded (r: groundRule τ) (a: atom τ) (mem: a ∈ r.rule.body): atomVariables τ a = ∅ :=
by
  have rground: ruleVariables τ r.rule = ∅
  apply r.grounded
  unfold ruleVariables at rground
  rw [Set.union_empty_iff] at rground
  apply collectResultsToFinsetIsEmptyIfMemberAre
  apply mem
  rcases rground with ⟨_,right⟩
  apply right

def groundAtomFromBody (r: groundRule τ)(a: atom τ) (mem: a ∈ r.rule.body): groundAtom τ := {atom:= a, grounded:= bodyOfGroundRuleIsGrounded τ r a mem}


def groundRuleBodySet (r: groundRule τ): Set (groundAtom τ) := sorry

def ruleFromGroundAtoms (head: groundAtom τ) (body: List (groundAtom τ)): rule τ := {head := head.atom,body := List.map (groundAtom.toAtom τ) body}

lemma ruleFromGroundAtomsHasNoVars (head: groundAtom τ) (body: List (groundAtom τ)): ruleVariables τ (ruleFromGroundAtoms τ head body) = ∅ :=
by
  unfold ruleVariables
  rw [Set.union_empty_iff]
  constructor
  unfold ruleFromGroundAtoms
  simp
  apply head.grounded
  unfold ruleFromGroundAtoms
  simp
  rw [collectResultsToFinset_Empty]
  intro a
  simp
  intros x _ xa
  have xground: atomVariables τ x.atom = ∅
  apply x.grounded
  unfold groundAtom.toAtom at xa
  rw [xa] at xground
  exact xground

def groundRuleFromAtoms (head: groundAtom τ) (body: List (groundAtom τ)): groundRule τ := {rule := ruleFromGroundAtoms τ head body, grounded := ruleFromGroundAtomsHasNoVars τ head body }

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

def listMax {A: Type} (f: A → ℕ): List A → ℕ
| [] => 0
| (hd::tl) => if f hd > listMax f tl then f hd else listMax f tl

def height: proofTree τ → ℕ
| proofTree.node a l => 1 + listMax height l

def isValid (P: Set (rule τ)) (d: database τ) (t: proofTree τ): Prop := ( ∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding τ r g = groundRuleFromAtoms τ (root τ t) (List.map (root τ) (children τ t)) ∧ List.All₂ (isValid P d) (children τ t)) ∨ (children τ t = [] ∧ d.contains (root τ t))

lemma databaseElementsHaveValidProofTree (P: Set (rule τ)) (d: database τ) (a: groundAtom τ) (mem: d.contains a): ∃ (t: proofTree τ), root τ t = a ∧ isValid τ P d t:=
by
  use (proofTree.node a [])
  constructor
  unfold root
  simp
  unfold isValid
  right
  constructor
  unfold children
  simp
  unfold root
  simp
  apply mem

def proofTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∃ (t: proofTree τ), root τ t = a ∧ isValid τ P d t}

def ruleTrue (r: groundRule τ) (i: Set (groundAtom τ)): Prop := groundRuleBodySet τ r ⊆ i → groundRuleHead τ r ∈ i

def model (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) : Prop := ∀ (r: groundRule τ), r ∈ groundProgram τ P → ruleTrue τ r i ∧ ∀ (a: groundAtom τ), d.contains a → a ∈ i

theorem proofTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model τ P d (proofTheoreticSemantics τ P d) :=
by
  unfold model
  intros r rGP
  constructor
  unfold ruleTrue
  unfold proofTheoreticSemantics
  simp
  intro h

  admit
  intros a mem
  unfold proofTheoreticSemantics
  simp
  apply databaseElementsHaveValidProofTree
  apply mem

def modelTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∀ (i: Set (groundAtom τ)), model τ P d i → a ∈ i}

lemma modelTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model τ P d (modelTheoreticSemantics τ P d) :=
by
  unfold model
  intros r rGP
  constructor
  unfold ruleTrue
  sorry
  sorry

lemma leastModel (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) (m: model τ P d i): modelTheoreticSemantics τ P d ⊆ i :=
by
  unfold modelTheoreticSemantics
  rw [Set.subset_def]
  intro a
  rw [Set.mem_setOf]
  intro h
  apply h
  apply m


theorem SemanticsEquivalence (P: Set (rule τ)) (d: database τ): proofTheoreticSemantics τ P d = modelTheoreticSemantics τ P d :=
by
  apply Set.Subset.antisymm
  unfold proofTheoreticSemantics
  rw [Set.subset_def]
  intro x
  rw [Set.mem_setOf]

  admit
  apply leastModel
  apply proofTheoreticSemanticsIsModel

end semantics
