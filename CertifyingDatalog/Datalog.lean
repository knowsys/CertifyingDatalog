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

def member (t1 t2: proofTree τ): Prop :=
  match t1 with
    | proofTree.node _ l => t2 ∈ l

def root: proofTree τ → groundAtom τ
| proofTree.node a _ => a

def children: proofTree τ → List (proofTree τ)
| proofTree.node _ l => l

def listMax {A: Type} (f: A → ℕ): List A → ℕ
| [] => 0
| (hd::tl) => if f hd > listMax f tl then f hd else listMax f tl


def height: proofTree τ → ℕ
| proofTree.node a l => 1 + listMax (fun ⟨x, _h⟩ => height x) l.attach
termination_by height t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp

def isValid(P: Set (rule τ)) (d: database τ) (t: proofTree τ): Prop :=
  match t with
  | proofTree.node a l => ( ∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding τ r g = groundRuleFromAtoms τ a (List.map (root τ) l) ∧ l.attach.All₂ (fun ⟨x, _h⟩ => isValid P d x)) ∨ (l = [] ∧ d.contains a)
termination_by isValid t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp


lemma databaseElementsHaveValidProofTree (P: Set (rule τ)) (d: database τ) (a: groundAtom τ) (mem: d.contains a): ∃ (t: proofTree τ), root τ t = a ∧ isValid τ P d t:=
by
  use (proofTree.node a [])
  constructor
  unfold root
  simp
  unfold isValid
  right
  constructor
  rfl
  apply mem

def proofTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∃ (t: proofTree τ), root τ t = a ∧ isValid τ P d t}

def ruleTrue (r: groundRule τ) (i: Set (groundAtom τ)): Prop := groundRuleBodySet τ r ⊆ i → groundRuleHead τ r ∈ i

def model (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) : Prop := (∀ (r: groundRule τ), r ∈ groundProgram τ P → ruleTrue τ r i) ∧ ∀ (a: groundAtom τ), d.contains a → a ∈ i

lemma createProofTreeForRule (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (rGP: r ∈ groundProgram τ P)(subs: groundRuleBodySet τ r ⊆ proofTheoreticSemantics τ P d): ∃ t, root τ t = groundRuleHead τ r ∧ isValid τ P d t :=
by
  sorry

theorem proofTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model τ P d (proofTheoreticSemantics τ P d) :=
by
  unfold model
  constructor
  intros r rGP
  unfold ruleTrue
  unfold proofTheoreticSemantics
  simp
  intro h
  apply createProofTreeForRule _ _ _ _ rGP h
  intros a mem
  unfold proofTheoreticSemantics
  simp
  apply databaseElementsHaveValidProofTree
  apply mem

def modelTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∀ (i: Set (groundAtom τ)), model τ P d i → a ∈ i}

lemma leastModel (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) (m: model τ P d i): modelTheoreticSemantics τ P d ⊆ i :=
by
  unfold modelTheoreticSemantics
  rw [Set.subset_def]
  intro a
  rw [Set.mem_setOf]
  intro h
  apply h
  apply m

lemma modelTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model τ P d (modelTheoreticSemantics τ P d) :=
by
  unfold model
  constructor
  intros r rGP
  unfold ruleTrue
  intro h
  unfold modelTheoreticSemantics
  simp [Set.mem_setOf]
  by_contra h'
  push_neg at h'
  rcases h' with ⟨i, m, n_head⟩
  have m': model τ P d i
  apply m
  unfold model at m
  rcases m with ⟨left,_⟩
  have r_true: ruleTrue τ r i
  apply left
  apply rGP
  unfold ruleTrue at r_true
  have head: groundRuleHead τ r ∈ i
  apply r_true
  apply subset_trans h
  apply leastModel (m:= m')
  exact absurd head n_head

  intros a a_db
  unfold modelTheoreticSemantics
  rw [Set.mem_setOf]
  by_contra h
  push_neg at h
  rcases h with ⟨i, m, a_n_i⟩
  unfold model at m
  have a_i: a ∈ i
  rcases m with ⟨_, right⟩
  apply right
  apply a_db
  exact absurd a_i a_n_i



lemma proofTreeAtomsInEveryModel (P: Set (rule τ)) (d: database τ) (a: groundAtom τ) (pt: a ∈ proofTheoreticSemantics τ P d)(i: Set (groundAtom τ)) (m: model τ P d i): a ∈ i := by
  unfold proofTheoreticSemantics at pt
  rw [Set.mem_setOf] at pt
  rcases pt with ⟨t, root_t, valid_t⟩
  induction (height τ t) with
    | zero =>
      sorry
    | succ n ih =>
      sorry

theorem SemanticsEquivalence (P: Set (rule τ)) (d: database τ): proofTheoreticSemantics τ P d = modelTheoreticSemantics τ P d :=
by
  apply Set.Subset.antisymm
  rw [Set.subset_def]
  apply proofTreeAtomsInEveryModel

  apply leastModel
  apply proofTheoreticSemanticsIsModel

end semantics
