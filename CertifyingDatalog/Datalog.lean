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

structure groundAtom (τ: signature) where
  symbol: τ.relationSymbols
  atom_terms: List (τ.constants )
  term_length: atom_terms.length = τ.relationArity symbol

lemma listMapPreservesTermLength (ga: groundAtom τ): (List.map term.constant ga.atom_terms).length = τ.relationArity ga.symbol :=
by
  rw [List.length_map]
  apply ga.term_length

def groundAtom.toAtom {τ:signature} (ga: groundAtom τ): atom τ:= {symbol:=ga.symbol, atom_terms:= List.map term.constant ga.atom_terms,term_length:= listMapPreservesTermLength τ ga}

def termVariables: term τ → Set τ.vars
| (term.constant _) => ∅
| (term.variableDL v) => {v}

def collectResultsToFinset {A: Type} (f: A → Set τ.vars): List A → Set τ.vars
| [] => ∅
| hd::tl => (f hd) ∪ (collectResultsToFinset f tl)

def atomVariables (a: atom τ) : Set τ.vars := collectResultsToFinset τ (termVariables τ) a.atom_terms

def ruleVariables (r: rule τ): Set τ.vars := (atomVariables τ r.head) ∪ (collectResultsToFinset τ (atomVariables τ) r.body)

-- ext for groundRuleEquality
@[ext]
structure groundRule where
  head: groundAtom τ
  body: List (groundAtom τ)

def groundRule.toRule (r: groundRule τ): rule τ := {head:= r.head.toAtom, body := List.map groundAtom.toAtom r.body}

lemma groundRuleEquality (r1 r2: groundRule τ): r1 = r2 ↔ r1.head = r2.head ∧ r1.body = r2.body :=
by
  constructor
  intro h
  rw [h]
  simp
  intro h
  rcases h with ⟨left,right⟩
  ext
  apply left
  rw [right]

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

def applyGroundingTerm'(g: grounding τ) (t: term τ): τ.constants :=
  match t with
  | term.constant c =>  c
  | term.variableDL v => (g v)

lemma applyGroundingTerm'PreservesLength (g: grounding τ) (a: atom τ): (List.map (applyGroundingTerm' τ g) a.atom_terms ).length = τ.relationArity a.symbol :=
by
  rw [List.length_map]
  apply a.term_length

def atomGrounding (g: grounding τ) (a: atom τ): groundAtom τ := {symbol := a.symbol, atom_terms := List.map (applyGroundingTerm' τ g) a.atom_terms, term_length := applyGroundingTerm'PreservesLength τ g a}

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


def ruleGrounding (r: rule τ) (g:grounding τ): groundRule τ := {head:=atomGrounding τ g r.head, body:= List.map (atomGrounding τ g) r.body }

def listToSet {A: Type} (l:List A): Set A :=
  match l with
  | [] => ∅
  | (hd::tl) => {hd} ∪ listToSet tl

def groundRuleBodySet (r: groundRule τ): Set (groundAtom τ) := listToSet r.body

lemma groundRuleBodySet_iff_groundRuleBody (a: groundAtom τ) (r: groundRule τ): a ∈ r.body ↔ a ∈ groundRuleBodySet τ r :=
by
  unfold groundRuleBodySet
  induction r.body with
  | nil =>
    unfold listToSet
    simp
  | cons hd tl ih =>
    unfold listToSet
    simp
    rw [ih]


def ruleFromGroundAtoms (head: groundAtom τ) (body: List (groundAtom τ)): rule τ := {head := head.toAtom,body := List.map (groundAtom.toAtom) body}

def groundRuleFromAtoms (head: groundAtom τ) (body: List (groundAtom τ)): groundRule τ := {head := head, body := body}

def groundProgram (P: Set (rule τ)) := {r: groundRule τ | ∃ (r': rule τ) (g: grounding τ), r' ∈ P ∧ r = ruleGrounding τ r' g}

end grounding
section semantics
variable {τ:signature} [DecidableEq τ.vars]

class database (τ: signature):=
  (contains: groundAtom τ → Prop)

inductive proofTree (τ: signature)
| node: (groundAtom τ) → List (proofTree τ) →  proofTree τ

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

def natList_max: List ℕ  → ℕ
| [] => 0
| (hd::tl) => if hd > natList_max tl then hd else natList_max tl

lemma listMax_le_f_member {A: Type} (f: A → ℕ) (l: List A) (a:A) (mem: a ∈ l): f a ≤ listMax f l := by
  induction l with
  | nil =>
    exfalso
    simp at mem
  | cons hd tl ih =>
    unfold listMax
    rw [List.mem_cons] at mem
    cases mem with
    | inl a_hd =>
      rw [a_hd]
      by_cases fhd_listMax: f hd > listMax f tl
      rw [if_pos]
      apply fhd_listMax
      rw [if_neg fhd_listMax]
      push_neg at fhd_listMax
      apply fhd_listMax
    | inr a_tl =>
      apply Nat.le_trans (m:= listMax f tl)
      apply ih a_tl
      by_cases fhd_listMax: f hd > listMax f tl
      rw [if_pos fhd_listMax]
      apply Nat.le_of_lt
      apply fhd_listMax
      rw [if_neg fhd_listMax]

-- alternative way of writing listMax, since List.map allows removing the coercion easier
lemma listMax_iff_natList_max_map {A: Type} (f: A → ℕ) (l: List A): listMax f l = natList_max (List.map f l) :=
by
  induction l with
  | nil =>
    rw [List.map_nil]
    unfold listMax
    unfold natList_max
    rfl
  | cons hd tl ih =>
    rw [List.map_cons]
    unfold listMax
    unfold natList_max
    rw [ih]


def height: proofTree τ → ℕ
| proofTree.node a l => 1 + listMax (fun ⟨x, _h⟩ => height x) l.attach
termination_by height t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp

lemma height_case (a: groundAtom τ) (l: List (proofTree τ)): height (proofTree.node a l) = 1 + listMax height l :=
by
  unfold height
  simp
  rw [listMax_iff_natList_max_map, List.attach_map_coe', ← listMax_iff_natList_max_map]

lemma heightOfMemberIsSmaller (t1 t2: proofTree τ) (mem: member t1 t2): height t2 < height t1 :=
by
  cases t1 with
  | node a l =>
    unfold member at mem
    simp at mem
    rw [height_case, Nat.add_comm, ← Nat.succ_eq_add_one, Nat.lt_succ_iff]
    apply listMax_le_f_member _ _ _ mem


def isValid(P: Set (rule τ)) (d: database τ) (t: proofTree τ): Prop :=
  match t with
  | proofTree.node a l => ( ∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding τ r g = groundRuleFromAtoms τ a (List.map root l) ∧ l.attach.All₂ (fun ⟨x, _h⟩ => isValid P d x)) ∨ (l = [] ∧ d.contains a)
termination_by isValid t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp


lemma databaseElementsHaveValidProofTree (P: Set (rule τ)) (d: database τ) (a: groundAtom τ) (mem: d.contains a): ∃ (t: proofTree τ), root t = a ∧ isValid P d t:=
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

def proofTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∃ (t: proofTree τ), root t = a ∧ isValid P d t}

def ruleTrue (r: groundRule τ) (i: Set (groundAtom τ)): Prop := groundRuleBodySet τ r ⊆ i → r.head ∈ i

def model (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) : Prop := (∀ (r: groundRule τ), r ∈ groundProgram τ P → ruleTrue r i) ∧ ∀ (a: groundAtom τ), d.contains a → a ∈ i


noncomputable def proofTreeForElement (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (a: groundAtom τ) (mem: a ∈ r.body): proofTree τ := Classical.choose (subs a mem)

lemma proofTreeForElementSemantics (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (a: groundAtom τ) (mem: a ∈ r.body) (t: proofTree τ) (h: t = proofTreeForElement P d r subs a mem): root t = a ∧ isValid P d t:=
by
  rw [h]
  unfold proofTreeForElement
  apply Classical.choose_spec (h:= subs a mem)

noncomputable def proofTreeList (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t): List (proofTree τ) := List.map (fun ⟨x, _h⟩ => proofTreeForElement P d r subs x _h) r.body.attach

lemma proofTreeListHasValidTrees (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (t: proofTree τ) (mem: t ∈ proofTreeList P d r subs): isValid P d t :=
by
  unfold proofTreeList at mem
  rw [List.mem_map] at mem
  simp at mem
  rcases mem with ⟨a,b,c⟩
  have h: root t = a ∧ isValid P d t
  apply proofTreeForElementSemantics
  symm
  apply c
  rcases h with ⟨_,right⟩
  apply right

lemma replaceFuncInMap {A B: Type} {f g: A → B} (h: f = g): ∀ l, List.map f l = List.map g l :=
by
  intro l
  induction l with
  | nil =>
    rw [List.map_nil]
    rw [List.map_nil]
  | cons hd tl ih =>
    rw [List.map_cons]
    rw [List.map_cons]
    rw [ih]
    rw [h]


lemma rootProofTreeListIsOriginal (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t): r.body = List.map root (proofTreeList P d r subs) :=
by
  unfold proofTreeList
  simp

  sorry
/-
noncomputable def proofTreeList (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t): List (proofTree τ) :=
List.map (fun ⟨x, _h⟩ => Classical.choose (subs x _h)) r.body.attach

lemma cancel_and_under_exists_right {A: Type} {p q: A → Prop} (h: ∃ a, p a ∧ q a ): ∃ a, q a :=
by
  rcases h with ⟨a,_,qa⟩
  use a

lemma proofTreeListHasValidTrees (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (t: proofTree τ) (mem: t ∈ proofTreeList P d r subs): isValid P d t :=
by
  unfold proofTreeList at mem
  rw [List.mem_map] at mem
  simp at mem
  rcases mem with ⟨a,b,c⟩
  have h: root t = a ∧ isValid P d t
  rw [← c]
  apply Classical.choose_spec (h:= subs a b)
  rcases h with ⟨_,right⟩
  apply right
-/

lemma createProofTreeForRule (P: Set (rule τ)) (d: database τ) (r: groundRule τ) (rGP: r ∈ groundProgram τ P)(subs: groundRuleBodySet τ r ⊆ proofTheoreticSemantics P d): ∃ t, root t = r.head ∧ isValid P d t :=
by
  simp [proofTheoreticSemantics, Set.subset_def, ← groundRuleBodySet_iff_groundRuleBody] at subs
  use proofTree.node r.head (proofTreeList P d r subs)
  constructor
  unfold root
  simp
  unfold isValid
  unfold groundProgram at rGP
  rw [Set.mem_setOf] at rGP
  rcases rGP with ⟨r', g, rP, r_ground⟩
  left
  use r'
  use g
  constructor
  exact rP
  constructor
  unfold groundRuleFromAtoms
  rw [← r_ground, groundRuleEquality]
  constructor
  simp
  simp
  unfold proofTreeList
  apply rootProofTreeListIsOriginal
  rw [List.all₂_iff_forall]
  simp
  apply proofTreeListHasValidTrees

theorem proofTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model P d (proofTheoreticSemantics P d) :=
by
  unfold model
  constructor
  intros r rGP
  unfold ruleTrue
  unfold proofTheoreticSemantics
  simp
  intro h
  apply createProofTreeForRule  _ _ _ rGP h
  intros a mem
  unfold proofTheoreticSemantics
  simp
  apply databaseElementsHaveValidProofTree
  apply mem

def modelTheoreticSemantics (P: Set (rule τ)) (d: database τ): Set (groundAtom τ ):= {a: groundAtom τ | ∀ (i: Set (groundAtom τ)), model P d i → a ∈ i}

lemma leastModel (P: Set (rule τ)) (d: database τ) (i: Set (groundAtom τ)) (m: model P d i): modelTheoreticSemantics P d ⊆ i :=
by
  unfold modelTheoreticSemantics
  rw [Set.subset_def]
  intro a
  rw [Set.mem_setOf]
  intro h
  apply h
  apply m

lemma modelTheoreticSemanticsIsModel (P: Set (rule τ)) (d: database τ): model P d (modelTheoreticSemantics P d) :=
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
  have m': model P d i
  apply m
  unfold model at m
  rcases m with ⟨left,_⟩
  have r_true: ruleTrue r i
  apply left
  apply rGP
  unfold ruleTrue at r_true
  have head: r.head ∈ i
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

lemma proofTreeAtomsInEveryModel (P: Set (rule τ)) (d: database τ) (a: groundAtom τ) (pt: a ∈ proofTheoreticSemantics P d)(i: Set (groundAtom τ)) (m: model P d i): a ∈ i := by
  unfold proofTheoreticSemantics at pt
  rw [Set.mem_setOf] at pt
  rcases pt with ⟨t, root_t, valid_t⟩
  unfold model at m
  rcases m with ⟨ruleModel,dbModel⟩
  induction' h': (height t) using Nat.strongInductionOn with n ih  generalizing a t
  cases' t with a' l
  unfold isValid at valid_t
  cases valid_t with
  | inl ruleCase =>
    rcases ruleCase with ⟨r,g,rP, r_ground, all⟩
    have r_true: ruleTrue (ruleGrounding τ r g) i
    apply ruleModel
    unfold groundProgram
    rw [Set.mem_setOf]
    use r
    use g
    unfold ruleTrue at r_true
    have head_a: (ruleGrounding τ r g).head = a
    unfold root at root_t
    simp at root_t
    rw [← root_t, r_ground]
    unfold groundRuleFromAtoms
    simp
    rw [head_a] at r_true
    apply r_true
    rw [Set.subset_def]
    intros x x_body
    rw [r_ground, ← groundRuleBodySet_iff_groundRuleBody] at x_body
    unfold groundRuleFromAtoms at x_body
    simp at x_body
    rcases x_body with ⟨t_x, t_x_l, t_x_root⟩
    rw [List.all₂_iff_forall] at all
    simp at all
    apply ih (m:=height t_x)
    rw [← h']
    apply heightOfMemberIsSmaller
    unfold member
    simp
    apply t_x_l
    apply t_x_root
    apply all t_x t_x_l
    rfl
  | inr dbCase =>
    rcases dbCase with ⟨_, contains⟩
    unfold root at root_t
    simp at root_t
    rw [root_t] at contains
    apply dbModel
    apply contains

theorem SemanticsEquivalence (P: Set (rule τ)) (d: database τ): proofTheoreticSemantics P d = modelTheoreticSemantics P d :=
by
  apply Set.Subset.antisymm
  rw [Set.subset_def]
  apply proofTreeAtomsInEveryModel

  apply leastModel
  apply proofTheoreticSemanticsIsModel

end semantics
