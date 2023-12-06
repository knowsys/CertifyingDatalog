import CertifyingDatalog.Datalog
import CertifyingDatalog.Database
import CertifyingDatalog.Unification
import Mathlib.Data.Set.Basic

structure partialGroundRule (τ: signature)[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Nonempty τ.constants] (i: interpretation τ) where
  head: atom τ
  groundedBody: List (groundAtom τ)
  ungroundedBody: List (atom τ)

  members: ∀ (ga: groundAtom τ), ga ∈ groundedBody → ga ∈ i

variable  {τ: signature}[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Nonempty τ.constants] {i: interpretation τ}

def partialGroundRule.isSafe (pgr: partialGroundRule τ i): Prop :=
  atomVariables pgr.head ⊆ collectResultsToFinset atomVariables pgr.ungroundedBody

def rule.isSafe (r: rule τ): Prop := atomVariables r.head ⊆ collectResultsToFinset atomVariables r.body

def partialGroundRuleFromRule (r: rule τ): partialGroundRule τ i :=
  have members: ∀ (ga: groundAtom τ), ga ∈ [] → ga ∈ i:= by
    simp
  {head := r.head, groundedBody := [], ungroundedBody := r.body, members := members}

def partialGroundRule.toRule (pgr: partialGroundRule τ i): rule τ :=
  {head:= pgr.head, body := (List.map (groundAtom.toAtom) pgr.groundedBody) ++ pgr.ungroundedBody}

def partialGroundRule.isTrue (pgr: partialGroundRule τ i): Prop := ∀ (g: grounding τ), ruleTrue (ruleGrounding pgr.toRule g) i

def termWithoutVariablesToConstant (t: term τ) (h: termVariables t = ∅): τ.constants :=
  match t with
  | term.constant c => c
  | term.variableDL v =>
      have h': False := by
        unfold termVariables at h
        simp at h
      False.elim h'

lemma union_is_empty_iff_both {A: Type} (s1 s2: Set A): s1 ∪ s2 = ∅ ↔ s1 = ∅ ∧ s2 = ∅ :=
by
  constructor
  intro h
  rw [Set.ext_iff] at h
  simp at h
  push_neg at h

  constructor
  rw [Set.ext_iff]
  intro x
  simp
  specialize h x
  simp [h]
  rw [Set.ext_iff]
  intro x
  simp
  specialize h x
  simp [h]

  intro h
  rcases h with ⟨left,right⟩
  rw [left]
  rw [Set.empty_union]
  apply right

lemma atomVariablesEmptyIffAllTermVariablesEmpty (a: atom τ): atomVariables a = ∅ ↔ ∀ (t: term τ), t ∈ a.atom_terms → termVariables t = ∅ :=
by
  unfold atomVariables
  have h: ∀ (l: List (term τ)), (collectResultsToFinset termVariables l = ∅ ↔ ∀ (t : term τ), t ∈ l → termVariables t = ∅)
  intro l
  induction l with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    constructor
    intros h t t_l
    rw [union_is_empty_iff_both] at h
    rcases h with ⟨termVarHd, termVarTl⟩
    simp at t_l
    cases t_l with
    | inl t_hd =>
      rw [t_hd]
      apply termVarHd
    | inr t_tl =>
      rw [ih] at termVarTl
      apply termVarTl t t_tl

    intro h
    rw [union_is_empty_iff_both]
    constructor
    apply h
    simp

    rw [ih]
    intros t t_tl
    apply h
    simp
    right
    apply t_tl
  apply h


def atomWithoutVariablesToGroundAtom (a: atom τ) (h: atomVariables a = ∅): groundAtom τ :=
  have h: ∀ (t: term τ), t ∈ a.atom_terms → termVariables t = ∅ := by
    rw [← atomVariablesEmptyIffAllTermVariablesEmpty]
    apply h
  have term_length: (List.map (fun ⟨x, _h⟩ => termWithoutVariablesToConstant x (h x _h)) a.atom_terms.attach).length = τ.relationArity (a.symbol) := by
    rw [List.length_map, List.length_attach]
    apply a.term_length
{symbol:= a.symbol, atom_terms := List.map (fun ⟨x, _h⟩ => termWithoutVariablesToConstant x (h x _h)) a.atom_terms.attach, term_length := term_length }

def List.map_except_unit {A B: Type} (l: List A) (f: A → Except B Unit): Except B Unit :=
  match l with
  | [] => Except.ok ()
  | hd::tl =>
    match f hd with
    | Except.ok () => List.map_except_unit tl f
    | Except.error b => Except.error b

def getSubstitutions (i: List (groundAtom τ))(a: atom τ): List (substitution τ) := List.filterMap (fun x => matchAtom emptySubstitution a x) i

def List.toSet {A: Type} (l: List A): Set A :=
  match l with
  | [] => ∅
  | hd::tl => {hd} ∪ tl.toSet

def groundingStep (s: substitution τ) (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: atom τ) (tl: List (atom τ)) (ungroundedBody: pgr.ungroundedBody = hd::tl) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅ ): partialGroundRule τ i.toSet := sorry

def exploreGrounding (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (safe: pgr.isSafe): Except String Unit :=
  match h: pgr.ungroundedBody with
  | [] =>
    have varHead: atomVariables pgr.head = ∅ := by
      unfold partialGroundRule.isSafe at safe
      rw [h] at safe
      unfold collectResultsToFinset at safe
      rw [Set.ext_iff]
      simp
      intro v
      push_neg
      rw [Set.subset_def] at safe
      specialize safe v
      apply safe
    if (atomWithoutVariablesToGroundAtom pgr.head varHead) ∈ i
    then Except.ok ()
    else Except.error "Error"
  | hd::tl =>
    sorry

theorem exploreGroundingSemantics (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (safe: pgr.isSafe): exploreGrounding i pgr safe = Except.ok () ↔ pgr.isTrue := sorry
