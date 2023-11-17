import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs

-- basic definitions
structure signature :=
  (constants: Type)
  (vars: Type)
  (relationSymbols: Type)
  (relationArity: relationSymbols → ℕ)


section basic
variable (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]


inductive term (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]: Type
| constant : τ.constants → term τ
| variableDL : τ.vars → term τ
deriving DecidableEq

instance: Coe (τ.constants) (term τ) where
 coe
    | c => term.constant c

@[ext]
structure atom :=
  (symbol: τ.relationSymbols)
  (atom_terms: List (term τ ))
  (term_length: atom_terms.length = τ.relationArity symbol)
deriving DecidableEq


lemma atomEquality (a1 a2: atom τ): a1 = a2 ↔ a1.symbol = a2.symbol ∧ a1.atom_terms = a2.atom_terms :=
by
  constructor
  intro h
  rw [h]
  simp

  intro h
  rcases h with ⟨left, right⟩
  ext
  apply left
  rw [right]

@[ext]
structure rule :=
  (head: atom τ)
  (body: List (atom τ))
deriving DecidableEq


lemma ruleEquality (r1 r2: rule τ): r1 = r2 ↔ r1.head = r2.head ∧ r1.body = r2.body :=
by
  constructor
  intro h
  rw [h]
  simp

  intro h
  rcases h with ⟨left, right⟩
  ext
  rw [left]
  rw [left]
  rw [right]

abbrev program := Finset (rule τ)

end basic
-- grounding

section grounding
variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]

@[ext]
structure groundAtom (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] where
  symbol: τ.relationSymbols
  atom_terms: List (τ.constants )
  term_length: atom_terms.length = τ.relationArity symbol
  deriving DecidableEq

lemma listMapPreservesTermLength (ga: groundAtom τ): (List.map term.constant ga.atom_terms).length = τ.relationArity ga.symbol :=
by
  rw [List.length_map]
  apply ga.term_length

lemma groundAtomEquality (a1 a2: groundAtom τ): a1 = a2 ↔ a1.symbol = a2.symbol ∧ a1.atom_terms = a2.atom_terms :=
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

def groundAtom.toAtom (ga: groundAtom τ): atom τ:= {symbol:=ga.symbol, atom_terms:= List.map term.constant ga.atom_terms,term_length:= listMapPreservesTermLength ga}

lemma listMapInjectiveEquality {A B: Type} (l1 l2: List A) (f: A → B)(inj: Function.Injective f): l1 = l2 ↔ List.map f l1 = List.map f l2 :=
by
  constructor
  intro h
  rw [h]

  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp
    | cons hd tl =>
      intro f_map
      exfalso
      simp at f_map
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      intro h
      exfalso
      simp at h
    | cons hd' tl' =>
      unfold List.map
      simp
      intros f_hd f_tl
      constructor
      unfold Function.Injective at inj
      apply inj f_hd
      apply ih tl' f_tl

lemma groundAtomToAtomEquality (a1 a2: groundAtom τ): a1 = a2 ↔ a1.toAtom = a2.toAtom :=
by
  constructor
  intro h
  rw [h]

  unfold groundAtom.toAtom
  simp
  intros sym terms
  rw [groundAtomEquality]
  constructor
  apply sym
  rw [listMapInjectiveEquality]
  apply terms
  unfold Function.Injective
  intros a1 a2 term_eq
  injections

instance: Coe (groundAtom τ) (atom τ) where
  coe
    | a => a.toAtom

def termVariables: term τ → Set τ.vars
| (term.constant _) => ∅
| (term.variableDL v) => {v}

def collectResultsToFinset {A: Type} (f: A → Set τ.vars): List A → Set τ.vars
| [] => ∅
| hd::tl => (f hd) ∪ (collectResultsToFinset f tl)

lemma collectResultsToFinsetMemberIffListMember {A: Type} (f: A → Set τ.vars) (v: τ.vars) (l: List A): v ∈ collectResultsToFinset f l ↔ ∃ (a:A), a ∈ l ∧ v ∈ f a :=
by
  induction l with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    simp [collectResultsToFinset]
    constructor
    intro h
    cases h with
    | inl h =>
      left
      apply h
    | inr h =>
      rw [← ih]
      right
      apply h
    intro h
    cases h with
    | inl h =>
      left
      apply h
    | inr h =>
      rw [ih]
      right
      apply h

lemma memberResultIsSubsetCollectResultsToFinset (f: A → Set τ.vars) (a:A) (l: List A) (mem: a ∈ l): f a ⊆ collectResultsToFinset f l :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp at mem
    cases mem with
    | inl h =>
      rw [h]
      unfold collectResultsToFinset
      simp
    | inr h =>
      unfold collectResultsToFinset
      rw [← Set.empty_union (f a)]
      apply Set.union_subset_union
      simp
      apply ih
      apply h

lemma collectResultsToFinsetIsSubsetIffListElementsAre {A: Type} {S: Set (τ.vars)} {l: List A}{f: A → (Set τ.vars)}: collectResultsToFinset f l ⊆ S ↔ ∀ (a:A), a ∈ l → (f a) ⊆ S :=
by
  constructor
  intros h a a_l
  apply Set.Subset.trans (b:= collectResultsToFinset f l)
  apply memberResultIsSubsetCollectResultsToFinset
  apply a_l
  apply h

  intro h
  rw [Set.subset_def]
  intros x x_mem
  rw [collectResultsToFinsetMemberIffListMember] at x_mem
  rcases x_mem with ⟨a, a_l, x_fa⟩
  apply Set.mem_of_subset_of_mem
  apply h
  apply a_l
  apply x_fa

def atomVariables (a: atom τ) : Set τ.vars := collectResultsToFinset termVariables  a.atom_terms

lemma atomVariablesSubsetImpltermVariablesSubset {a: atom τ} {t: term τ}{S: Set τ.vars}(mem: t ∈ a.atom_terms) (subs: atomVariables a ⊆ S): termVariables t ⊆ S :=
by
  apply Set.Subset.trans (b:= atomVariables a)
  unfold atomVariables
  apply memberResultIsSubsetCollectResultsToFinset _ _ _ mem
  apply subs


def ruleVariables (r: rule τ): Set τ.vars := (atomVariables  r.head) ∪ (collectResultsToFinset atomVariables  r.body)

lemma ruleVariablesSubsetImplAtomVariablesSubset {r: rule τ} {a: atom τ}{S: Set τ.vars}(mem: a = r.head ∨ a ∈ r.body) (subs: ruleVariables r ⊆ S): atomVariables a ⊆ S :=
by
  apply Set.Subset.trans (b:= ruleVariables r) (bc:= subs)
  unfold ruleVariables
  cases mem with
  | inl h =>
    rw [h]
    nth_rw 1 [← Set.union_empty (atomVariables r.head)]
    apply Set.union_subset_union
    apply Set.Subset.rfl
    simp
  | inr h =>
    nth_rw 1 [← Set.empty_union (atomVariables a)]
    apply Set.union_subset_union
    simp
    apply memberResultIsSubsetCollectResultsToFinset (mem:=h)


-- ext for groundRuleEquality
@[ext]
structure groundRule (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] where
  head: groundAtom τ
  body: List (groundAtom τ)
  deriving DecidableEq

def groundRule.toRule (r: groundRule τ): rule τ := {head:= r.head.toAtom, body := List.map groundAtom.toAtom r.body}

lemma groundRuletoRulePreservesLength (r: groundRule τ): List.length r.body = List.length r.toRule.body :=
by
  unfold groundRule.toRule
  simp

instance: Coe (groundRule τ) (rule τ) where
  coe
    | r => r.toRule

lemma groundRuleEquality (r1 r2: groundRule τ): r1 = r2 ↔ r1.head = r2.head ∧ r1.body = r2.body :=
by
  constructor
  intro h
  rw [h]
  simp
  intro h
  rcases h with ⟨left,right⟩
  ext
  rw [left]
  rw [left]
  rw [right]

lemma groundRuleToRuleEquality (r1 r2: groundRule τ): r1 = r2 ↔ r1.toRule = r2.toRule :=
by
  constructor
  intro h
  rw [h]

  unfold groundRule.toRule
  rw [groundRuleEquality]
  intro h
  simp at h
  rcases h with ⟨head_eq, body_eq⟩
  have inj_toAtom: Function.Injective (groundAtom.toAtom (τ:= τ))
  unfold Function.Injective
  intros a1 a2 h
  rw [groundAtomToAtomEquality]
  apply h
  constructor
  unfold Function.Injective at inj_toAtom
  apply inj_toAtom head_eq
  rw [listMapInjectiveEquality (inj:=inj_toAtom)]
  apply body_eq

def grounding (τ: signature):= τ.vars → τ.constants

def applyGroundingTerm (g: grounding τ) (t: term τ): term τ :=
  match t with
  | term.constant c => term.constant c
  | term.variableDL v => term.constant (g v)

lemma applyGroundingTermRemovesVariables (g: grounding τ) (t: term τ): termVariables (applyGroundingTerm g t) = ∅ :=
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

lemma applyGroundingTermPreservesLength (g:grounding τ) (a: atom τ): (List.map (applyGroundingTerm g) a.atom_terms ).length = τ.relationArity a.symbol :=
by
  rcases a with ⟨symbol, terms, term_length⟩
  simp
  rw [ term_length]


def applyGroundingAtom (g: grounding τ) (a: atom τ): atom τ := {symbol:= a.symbol, atom_terms:= List.map (applyGroundingTerm g) a.atom_terms, term_length := applyGroundingTermPreservesLength g a}

lemma groundingRemovesAtomVariables (a: atom τ) (g: grounding τ): atomVariables (applyGroundingAtom g a) = ∅ :=
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

lemma applyGroundingTerm'PreservesLength (g: grounding τ) (a: atom τ): (List.map (applyGroundingTerm' g) a.atom_terms ).length = τ.relationArity a.symbol :=
by
  rw [List.length_map]
  apply a.term_length

def atomGrounding (g: grounding τ) (a: atom τ): groundAtom τ := {symbol := a.symbol, atom_terms := List.map (applyGroundingTerm'  g) a.atom_terms, term_length := applyGroundingTerm'PreservesLength  g a}

def applyGroundingRule (r: rule τ) (g: grounding τ): rule τ := {head := applyGroundingAtom  g r.head, body := List.map (applyGroundingAtom  g) r.body }

lemma groundingRemovesRuleVariables (r: rule τ) (g: grounding τ): ruleVariables  (applyGroundingRule r g) = ∅ := by
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


def ruleGrounding (r: rule τ) (g:grounding τ): groundRule τ := {head:=atomGrounding g r.head, body:= List.map (atomGrounding g) r.body }

def listToSet {A: Type} (l:List A): Set A :=
  match l with
  | [] => ∅
  | (hd::tl) => {hd} ∪ listToSet tl

def groundRuleBodySet (r: groundRule τ): Set (groundAtom τ) := listToSet r.body

lemma groundRuleBodySet_iff_groundRuleBody (a: groundAtom τ) (r: groundRule τ): a ∈ r.body ↔ a ∈ groundRuleBodySet r :=
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

def groundProgram (P: program τ) := {r: groundRule τ | ∃ (r': rule τ) (g: grounding τ), r' ∈ P ∧ r = ruleGrounding r' g}

end grounding
section substitutions
variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]

def substitution (τ: signature):= τ.vars → Option (τ.constants)

def substitution_domain (s: substitution τ): Set (τ.vars) := {v | Option.isSome (s v) = true}

def applySubstitutionTerm (s: substitution τ) (t: term τ): term τ :=
  match t with
  | term.constant c => term.constant c
  | term.variableDL v => if p: Option.isSome (s v) then term.constant (Option.get (s v) p) else term.variableDL v

lemma applySubstitutionTermMapPreservesLength (s: substitution τ) (a: atom τ): (List.map (applySubstitutionTerm s) a.atom_terms ).length = τ.relationArity a.symbol :=
by
  rw [List.length_map]
  apply a.term_length

def applySubstitutionAtom (s: substitution τ) (a: atom τ) : atom τ :=
{symbol := a.symbol, atom_terms := List.map (applySubstitutionTerm s) a.atom_terms, term_length := applySubstitutionTermMapPreservesLength s a}

def applySubstitutionRule (s: substitution τ) (r: rule τ): rule τ := {head := applySubstitutionAtom s r.head, body := List.map (applySubstitutionAtom s) r.body}

lemma VarInDomainIffApplySubstitutionTermIsConst {v: τ.vars}  {s: substitution τ}: v ∈ substitution_domain s ↔ ∃ (c: τ.constants), applySubstitutionTerm s (term.variableDL v) = term.constant c :=
by
  constructor
  intro h
  unfold substitution_domain at h
  rw [Set.mem_setOf] at h
  simp [applySubstitutionTerm, h]

  intro h
  rcases h with ⟨c, c_prop⟩
  unfold applySubstitutionTerm at c_prop
  simp at c_prop
  by_cases p: Option.isSome (s v) = true
  unfold substitution_domain
  rw [Set.mem_setOf]
  apply p
  simp [p] at c_prop


-- Adopted from Mathlibs List.get_map which didn't work in the way I needed it
lemma List.get_map' {A B: Type} (f: A → B) (l: List A) (n: ℕ)(isLt1: n < l.length) (isLt2: n < (List.map f l).length): List.get (List.map f l) {val:=n, isLt:= isLt2} = f (List.get l {val:=n, isLt:= isLt1}) := by
  apply Option.some.inj
  rw [← get?_eq_get, get?_map, get?_eq_get]
  rfl

lemma applySubstitutionAtomIsGroundImplVarsSubsetDomain {a: atom τ} {s: substitution τ} (subs_ground: ∃ (a': groundAtom τ), applySubstitutionAtom s a = a'): atomVariables a ⊆ substitution_domain s :=
by
  unfold atomVariables
  simp at subs_ground
  rcases subs_ground with ⟨a', a'_prop⟩
  unfold applySubstitutionAtom at a'_prop
  unfold groundAtom.toAtom at a'_prop
  rw [atomEquality] at a'_prop
  simp at a'_prop
  rcases a'_prop with ⟨_, terms_eq⟩
  rw [collectResultsToFinsetIsSubsetIffListElementsAre]
  intros t t_mem
  cases t with
  | constant c =>
    unfold termVariables
    simp
  | variableDL v =>
    unfold termVariables
    simp
    rw [VarInDomainIffApplySubstitutionTermIsConst]
    rw [List.mem_iff_get] at t_mem
    rcases t_mem with ⟨v_pos, v_pos_proof⟩
    rw [← v_pos_proof]
    rcases v_pos with ⟨v_pos, v_pos_a⟩
    have v_pos_a': v_pos < List.length a'.atom_terms
    rw [← List.length_map (f:= term.constant),←  terms_eq, List.length_map]
    apply v_pos_a
    use List.get a'.atom_terms {val:= v_pos, isLt:= v_pos_a'}
    rw [← List.get_map' (f:= applySubstitutionTerm s), ← List.get_map' (f:= term.constant)]
    apply List.get_of_eq terms_eq
    rw [List.length_map]
    apply v_pos_a


lemma applySubstitutionRuleIsGroundImplVarsSubsetDomain {r: rule τ} {s: substitution τ} (subs_ground: ∃ (r': groundRule τ), applySubstitutionRule s r = r'): ruleVariables r ⊆ substitution_domain s :=
by
  unfold ruleVariables
  simp at subs_ground
  rcases subs_ground with ⟨r', r'_prop⟩
  unfold applySubstitutionRule at r'_prop
  rw [ruleEquality] at r'_prop
  simp at r'_prop
  rcases r'_prop with ⟨left,right⟩
  apply Set.union_subset
  apply applySubstitutionAtomIsGroundImplVarsSubsetDomain
  simp
  use r'.head
  rw [left]
  unfold groundRule.toRule
  simp
  rw [collectResultsToFinsetIsSubsetIffListElementsAre]
  intros a a_mem
  apply applySubstitutionAtomIsGroundImplVarsSubsetDomain
  unfold groundRule.toRule at right
  simp at right
  simp
  rw [List.mem_iff_get] at a_mem
  rcases a_mem with ⟨a_pos, pos_prop⟩
  rcases a_pos with ⟨a_pos, a_pos_proof⟩
  have a_pos_proof': a_pos < List.length r'.body
  rw [← List.length_map r'.body groundAtom.toAtom, ← right, List.length_map r.body]
  apply a_pos_proof
  use List.get r'.body (Fin.mk a_pos a_pos_proof')
  rw [← pos_prop]
  have h: a_pos < (List.map (applySubstitutionAtom s) r.body ).length
  rw [List.length_map]
  apply a_pos_proof
  have h': a_pos < (List.map groundAtom.toAtom r'.body ).length
  rw [List.length_map]
  apply a_pos_proof'
  rw [← List.get_map' (applySubstitutionAtom s) r.body a_pos a_pos_proof h, ← List.get_map' groundAtom.toAtom r'.body a_pos a_pos_proof' h']
  apply List.get_of_eq
  apply right


def groundingToSubstitution (g: grounding τ): substitution τ := fun x => Option.some (g x)

lemma groundingToSubsitutionEquivTerm (t: term τ) (g: grounding τ): applyGroundingTerm' g t = applySubstitutionTerm (groundingToSubstitution g) t :=
by
  simp
  unfold applyGroundingTerm'
  unfold groundingToSubstitution
  unfold applySubstitutionTerm
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    simp


lemma groundingToSubsitutionEquivAtom (a: atom τ) (g: grounding τ): atomGrounding g a = applySubstitutionAtom (groundingToSubstitution g) a :=
by
  simp
  rw [atomEquality]
  unfold atomGrounding
  unfold applySubstitutionAtom
  simp
  constructor
  unfold groundAtom.toAtom
  simp

  unfold groundAtom.toAtom
  simp
  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  simp
  rw [groundingToSubsitutionEquivTerm]

lemma groundingToSubsitutionEquivRule (r: rule τ) (g: grounding τ): ruleGrounding r g = applySubstitutionRule (groundingToSubstitution g) r :=
by
  simp
  unfold ruleGrounding
  unfold applySubstitutionRule
  unfold groundRule.toRule
  rw [ruleEquality]
  constructor
  simp
  apply groundingToSubsitutionEquivAtom

  simp
  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  rw [List.get_map]
  simp
  rw [groundingToSubsitutionEquivAtom]

noncomputable def substitutionToGrounding [ex: Nonempty τ.constants] (s: substitution τ): grounding τ := fun x => if p:Option.isSome (s x) then Option.get (s x) p else Classical.choice ex

lemma substitutionToGroundingEquivTerm [Nonempty τ.constants] (t: term τ) (s: substitution τ) (h: termVariables t ⊆ substitution_domain s): term.constant (applyGroundingTerm' (substitutionToGrounding s) t) = applySubstitutionTerm s t :=
by
  unfold substitutionToGrounding
  unfold applyGroundingTerm'
  unfold applySubstitutionTerm
  simp
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    simp
    by_cases p: Option.isSome (s v) = true
    simp [p]
    simp [p]
    unfold termVariables at h
    simp at h
    unfold substitution_domain at h
    simp at h
    exact absurd h p

lemma substitutionToGroundingEquivAtom [Nonempty τ.constants] (a: atom τ) (s: substitution τ) (h: atomVariables a ⊆ substitution_domain s): groundAtom.toAtom (atomGrounding  (substitutionToGrounding s) a) = applySubstitutionAtom s a :=
by
  unfold atomGrounding
  unfold groundAtom.toAtom
  unfold applySubstitutionAtom
  rw [atomEquality]
  simp

  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  simp
  apply substitutionToGroundingEquivTerm
  apply atomVariablesSubsetImpltermVariablesSubset
  apply List.get_mem
  exact h

lemma substitutionToGroundingEquivRule [Nonempty τ.constants] (r: rule τ) (s: substitution τ) (h: ruleVariables r ⊆ substitution_domain s ): groundRule.toRule (ruleGrounding r (substitutionToGrounding s)) = applySubstitutionRule s r :=
by
  unfold groundRule.toRule
  unfold ruleGrounding
  unfold applySubstitutionRule
  rw [ruleEquality]
  simp
  constructor
  apply substitutionToGroundingEquivAtom
  apply ruleVariablesSubsetImplAtomVariablesSubset (a:=r.head) (r:=r)
  left
  rfl
  apply h

  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  simp
  apply substitutionToGroundingEquivAtom
  apply ruleVariablesSubsetImplAtomVariablesSubset (r:=r)
  right
  apply List.get_mem
  apply h

theorem groundingSubstitutionEquivalence [Nonempty τ.constants](r: groundRule τ) (r': rule τ): (∃ (g: grounding τ), ruleGrounding r' g = r) ↔ (∃ (s: substitution τ), applySubstitutionRule s r'= r) :=
by
  simp
  constructor
  intro h
  rcases h with ⟨g, g_prop⟩
  use groundingToSubstitution g
  rw [← g_prop]
  simp [groundingToSubsitutionEquivRule]

  intro h
  rcases h with ⟨s, s_prop⟩
  use substitutionToGrounding s
  rw [groundRuleToRuleEquality]
  rw [← s_prop]
  apply substitutionToGroundingEquivRule
  apply applySubstitutionRuleIsGroundImplVarsSubsetDomain
  use r

def emptySubstitution: substitution τ := (fun _ => none)

def substitution_subs (s1 s2: substitution τ): Prop :=
  ∀ (v: τ.vars),
    match (s1 v) with
    | Option.some c =>
      match (s2 v) with
      | Option.some c' => c = c'
      | Option.none => False
    | Option.none => True

instance: HasSubset (substitution τ) where
  Subset := substitution_subs

lemma emptySubstitutionIsMinimal (s: substitution τ): emptySubstitution ⊆ s :=
by
  unfold_projs
  unfold substitution_subs
  intro v
  unfold emptySubstitution
  simp

lemma substitution_subs_get (s1 s2: substitution τ) (subs: s1 ⊆ s2)(c: τ.constants) (v: τ.vars) (h: s1 v = Option.some c): s2 v = Option.some c :=
by
  unfold_projs at subs
  unfold substitution_subs at subs
  specialize subs v
  simp [h] at subs
  cases p: s2 v with
  | some c' =>
    simp [p] at subs
    rw [subs]
  | none =>
    simp [p] at *

lemma substitution_subs_none (s1 s2: substitution τ) (subs: s1 ⊆ s2) (v: τ.vars) (h: s2 v = Option.none): s1 v = Option.none :=
by
  unfold_projs at subs
  unfold substitution_subs at subs
  specialize subs v
  cases p: s1 v with
  | some c =>
    simp [p, h] at subs
  | none =>
    rfl

lemma substitution_subs_refl (s: substitution τ): s ⊆ s :=
by
  unfold_projs
  unfold substitution_subs
  intro v
  by_cases sv: s v = Option.none
  simp [sv]
  push_neg at sv
  rw [Option.ne_none_iff_exists] at sv
  rcases sv with ⟨x, some_x⟩
  simp [← some_x]

lemma substitution_subs_antisymm (s1 s2: substitution τ) (s1s2: s1 ⊆ s2)(s2s1: s2 ⊆ s1): s1 = s2 :=
by
  funext x
  cases p: s1 x with
  | some c =>
    apply Eq.symm
    apply substitution_subs_get s1 s2 s1s2 c x p
  | none =>
    apply Eq.symm
    apply substitution_subs_none s2 s1 s2s1 x p

lemma substitution_subs_trans (s1 s2 s3: substitution τ) (s1s2: s1 ⊆ s2) (s2s3: s2 ⊆ s3): s1 ⊆ s3 :=
by
  unfold_projs
  unfold substitution_subs
  intro v
  cases p:s1 v with
  | some c =>
    simp
    have q: s3 v = some c
    apply substitution_subs_get s2 s3 s2s3
    apply substitution_subs_get s1 s2 s1s2 c v p
    simp [q]
  | none =>
    simp

lemma option_get_iff_eq_some {A: Type} (o: Option A) (a:A) (h: Option.isSome o): Option.get o h = a ↔ o = some a :=
by
  constructor
  intro h'
  cases p: o with
  | some a' =>
    simp [p] at h'
    rw [h']
  | none =>
    exfalso
    simp [p] at h

  intro h'
  simp [h']

lemma subs_ext_groundTerm {s1 s2: substitution τ} {t: term τ} {c: τ.constants} (subs: s1 ⊆ s2) (eq: applySubstitutionTerm s1 t = c): applySubstitutionTerm s2 t = c :=
by
  simp at *
  cases t with
  | constant c' =>
    unfold applySubstitutionTerm
    simp
    unfold applySubstitutionTerm at eq
    simp at eq
    apply eq
  | variableDL v =>
    unfold applySubstitutionTerm at *
    simp at *
    have p: Option.isSome (s1 v) = true
    by_contra h'
    simp [h'] at eq
    simp [p] at eq
    rw [option_get_iff_eq_some] at eq
    have s2_v: s2 v = some c
    apply substitution_subs_get s1 s2 subs _ _ eq
    simp [s2_v]

lemma subs_ext_listConstant {s1 s2: substitution τ} {l1: List (term τ)} {l2: List (τ.constants)} (subs: s1 ⊆ s2) (eq: List.map (applySubstitutionTerm s1) l1 = List.map term.constant l2): List.map (applySubstitutionTerm s2) l1 = List.map term.constant l2 :=
by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp
    | cons hd tl =>
      simp at eq
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at eq
    | cons hd' tl' =>
      simp at eq
      rcases eq with ⟨left,right⟩
      simp
      constructor
      apply subs_ext_groundTerm (subs:= subs) (eq:=left)
      apply ih
      apply right

lemma subs_ext_groundAtom {s1 s2: substitution τ} {a: atom τ} {ga: groundAtom τ} (subs: s1 ⊆ s2) (eq: applySubstitutionAtom s1 a = ga): applySubstitutionAtom s2 a = ga :=
by
  unfold applySubstitutionAtom at *
  unfold groundAtom.toAtom at *
  simp at *
  rcases eq with ⟨left,right⟩
  constructor
  apply left
  apply subs_ext_listConstant (s1 := s1) (subs:= subs) (eq:= right)


end substitutions
section semantics
variable {τ:signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]

class database (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]:=
  (contains: groundAtom τ → Bool)

abbrev interpretation (τ: signature)[DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] := Set (groundAtom τ)

inductive proofTree (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants]
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


def isValid(P: program τ) (d: database τ) (t: proofTree τ): Prop :=
  match t with
  | proofTree.node a l => ( ∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding r g = groundRuleFromAtoms a (List.map root l) ∧ l.attach.All₂ (fun ⟨x, _h⟩ => isValid P d x)) ∨ (l = [] ∧ d.contains a)
termination_by isValid t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp


lemma databaseElementsHaveValidProofTree (P: program τ) (d: database τ) (a: groundAtom τ) (mem: d.contains a): ∃ (t: proofTree τ), root t = a ∧ isValid P d t:=
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

def proofTheoreticSemantics (P: program τ) (d: database τ): interpretation τ:= {a: groundAtom τ | ∃ (t: proofTree τ), root t = a ∧ isValid P d t}

def ruleTrue (r: groundRule τ) (i: interpretation τ): Prop := groundRuleBodySet r ⊆ i → r.head ∈ i

def model (P: program τ) (d: database τ) (i: interpretation τ) : Prop := (∀ (r: groundRule τ), r ∈ groundProgram P → ruleTrue r i) ∧ ∀ (a: groundAtom τ), d.contains a → a ∈ i


noncomputable def proofTreeForElement (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (a: groundAtom τ) (mem: a ∈ r.body): proofTree τ := Classical.choose (subs a mem)

lemma proofTreeForElementSemantics (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (a: groundAtom τ) (mem: a ∈ r.body) (t: proofTree τ) (h: t = proofTreeForElement P d r subs a mem): root t = a ∧ isValid P d t:=
by
  rw [h]
  unfold proofTreeForElement
  apply Classical.choose_spec (h:= subs a mem)

lemma proofTreeRootPreserved (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (a: groundAtom τ) (mem: a ∈ r.body): root (proofTreeForElement P d r subs a mem) = a :=
by
  have h: root (proofTreeForElement P d r subs a mem) = a ∧ isValid P d (proofTreeForElement P d r subs a mem)
  apply proofTreeForElementSemantics P d r subs a mem
  rfl
  rcases h with ⟨left,_⟩
  exact left

noncomputable def proofTreeList (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t): List (proofTree τ) := List.map (fun ⟨x, _h⟩ => proofTreeForElement P d r subs x _h) r.body.attach

lemma proofTreeListHasValidTrees (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t) (t: proofTree τ) (mem: t ∈ proofTreeList P d r subs): isValid P d t :=
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


lemma rootProofTreeListIsOriginal (P: program τ) (d: database τ) (r: groundRule τ) (subs: ∀ (x : groundAtom τ), x ∈ r.body → ∃ t, root t = x ∧ isValid P d t): r.body = List.map root (proofTreeList P d r subs) :=
by
  unfold proofTreeList
  apply List.ext_get
  rw [List.length_map, List.length_map, List.length_attach]
  intros n h1 h2
  rw [List.get_map, List.get_map]
  simp[List.get_attach]
  rw [proofTreeRootPreserved]

lemma createProofTreeForRule (P: program τ) (d: database τ) (r: groundRule τ) (rGP: r ∈ groundProgram P)(subs: groundRuleBodySet r ⊆ proofTheoreticSemantics P d): ∃ t, root t = r.head ∧ isValid P d t :=
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

theorem proofTheoreticSemanticsIsModel (P: program τ) (d: database τ): model P d (proofTheoreticSemantics P d) :=
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

def modelTheoreticSemantics (P: program τ) (d: database τ): interpretation τ := {a: groundAtom τ | ∀ (i: interpretation τ), model P d i → a ∈ i}

lemma leastModel (P: program τ) (d: database τ) (i: interpretation τ) (m: model P d i): modelTheoreticSemantics P d ⊆ i :=
by
  unfold modelTheoreticSemantics
  rw [Set.subset_def]
  intro a
  rw [Set.mem_setOf]
  intro h
  apply h
  apply m

lemma modelTheoreticSemanticsIsModel (P: program τ) (d: database τ): model P d (modelTheoreticSemantics P d) :=
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

lemma proofTreeAtomsInEveryModel (P: program τ) (d: database τ) (a: groundAtom τ) (pt: a ∈ proofTheoreticSemantics P d)(i: interpretation τ) (m: model P d i): a ∈ i := by
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
    have r_true: ruleTrue (ruleGrounding r g) i
    apply ruleModel
    unfold groundProgram
    rw [Set.mem_setOf]
    use r
    use g
    unfold ruleTrue at r_true
    have head_a: (ruleGrounding r g).head = a
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

theorem SemanticsEquivalence (P: program τ) (d: database τ): proofTheoreticSemantics P d = modelTheoreticSemantics P d :=
by
  apply Set.Subset.antisymm
  rw [Set.subset_def]
  apply proofTreeAtomsInEveryModel

  apply leastModel
  apply proofTheoreticSemanticsIsModel

end semantics
