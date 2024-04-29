import CertifyingDatalog.Datalog
import CertifyingDatalog.Database
import CertifyingDatalog.Unification
import Mathlib.Data.Set.Basic
import CertifyingDatalog.Basic

structure partialGroundRule (τ: signature)[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.relationSymbols] [Hashable τ.vars] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols] where
  head: atom τ
  groundedBody: List (groundAtom τ)
  ungroundedBody: List (atom τ)

variable  {τ: signature}[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants]  [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols] {i: interpretation τ}

def partialGroundRule.isSafe (pgr: partialGroundRule τ): Prop :=
  atomVariables pgr.head ⊆ List.foldl_union atomVariables ∅ pgr.ungroundedBody

def partialGroundRule.fromRule (r: rule τ) : partialGroundRule τ :=
  {head := r.head, groundedBody := [], ungroundedBody := r.body}

def partialGroundRule.toRule (pgr: partialGroundRule τ): rule τ :=
  {head:= pgr.head, body := (List.map (groundAtom.toAtom) pgr.groundedBody) ++ pgr.ungroundedBody}

lemma partialGroundRuleToRuleInverseToFromRule (r: rule τ): r = partialGroundRule.toRule (partialGroundRule.fromRule r) := by
  unfold partialGroundRule.fromRule
  unfold partialGroundRule.toRule
  simp

def partialGroundRule.isActive (pgr: partialGroundRule τ) (i: interpretation τ): Prop := ∀ (ga: groundAtom τ), ga ∈ pgr.groundedBody → ga ∈ i


lemma partialGroundRule.fromRuleIsActive (r: rule τ)  (i: interpretation τ): (partialGroundRule.fromRule r).isActive i := by
  unfold isActive
  unfold fromRule
  simp

def partialGroundRule.isTrue (pgr: partialGroundRule τ) (i: interpretation τ): Prop := ∀ (g: grounding τ), ruleTrue (ruleGrounding pgr.toRule g) i

lemma partialGroundRule.isTrue_of_equal_toRule (pgr1 pgr2: partialGroundRule τ) (i: interpretation τ) (h: pgr1.toRule = pgr2.toRule): pgr1.isTrue i ↔ pgr2.isTrue i :=
by
  unfold isTrue
  simp_rw [h]

lemma applyGroundingTerm'OnConstantRetunsSame (c: τ.constants) (g: grounding τ): applyGroundingTerm' g c = c :=
by
  unfold applyGroundingTerm'
  simp

lemma atomGroundingOnGroundAtomReturnsSame (ga: groundAtom τ) (g: grounding τ): atomGrounding g ga = ga :=
by
  unfold atomGrounding
  congr
  simp
  apply List.ext_get
  unfold groundAtom.toAtom
  simp

  intro n h1 h2
  rw [List.get_map]
  simp
  unfold groundAtom.toAtom
  simp
  apply applyGroundingTerm'OnConstantRetunsSame

lemma groundingOnPartialGroundRule (pgr: partialGroundRule τ) (g:grounding τ): ruleGrounding (partialGroundRule.toRule pgr) g = {head:= atomGrounding g pgr.head, body:= pgr.groundedBody ++ List.map (atomGrounding g) pgr.ungroundedBody} := by
  unfold ruleGrounding
  congr
  unfold partialGroundRule.toRule
  simp

  apply List.ext_get
  simp
  intro n h1 h2
  simp
  rw [atomGroundingOnGroundAtomReturnsSame]

lemma notActiveRuleIsTrue (pgr: partialGroundRule τ) (i: interpretation τ) (notActive: ¬ pgr.isActive i): pgr.isTrue i := by
  unfold partialGroundRule.isTrue
  intro g
  unfold ruleTrue
  intro h
  unfold partialGroundRule.isActive at notActive
  simp at notActive
  have not_subs: ¬ ↑(groundRuleBodySet (ruleGrounding (partialGroundRule.toRule pgr) g)) ⊆ i := by
    rw [Set.subset_def]
    simp
    rcases notActive with ⟨a, a_mem, a_i⟩
    use a
    simp [a_i]
    rw [← groundRuleBodySet_iff_groundRuleBody]
    rw [groundingOnPartialGroundRule]
    simp
    left
    apply a_mem
  contradiction

def getSubstitutions (i: List (groundAtom τ))(a: atom τ): List (substitution τ) := List.filterMap (fun x => matchAtom emptySubstitution a x) i

lemma groundAtomsHaveNoVariables (ga: groundAtom τ): atomVariables ga.toAtom = ∅ := by
  cases ga with
  | mk symbol atom_terms term_length =>
    unfold atomVariables
    unfold groundAtom.toAtom
    simp
    rw [List.foldl_union_empty]
    simp
    intros t _
    unfold termVariables
    simp


lemma inGetSubstitutionsImplNoVars (i: List (groundAtom τ))(a: atom τ) (s: substitution τ) (h: s ∈ getSubstitutions i a): atomVariables (applySubstitutionAtom s a) = ∅ := by
  unfold getSubstitutions at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨ga, _, match_ga⟩
  have matchAtomSome: Option.isSome (matchAtom emptySubstitution a ga) = true := by
    rw [match_ga]
    simp
  have matchSemantic:applySubstitutionAtom (Option.get (matchAtom emptySubstitution a ga) matchAtomSome) a = ga := by
    simp [matchAtomFindsSolution]

  simp at matchSemantic
  have matchAtom_s: Option.get (matchAtom emptySubstitution a ga) matchAtomSome= s := by
    simp [match_ga]
  rw [← matchAtom_s]
  rw [matchSemantic]
  apply groundAtomsHaveNoVariables

lemma atomWithoutVariablesToGroundAtomOfGroundAtom (ga: groundAtom τ) (h: atomVariables ga.toAtom = ∅): atomWithoutVariablesToGroundAtom ga.toAtom h = ga :=
by
  cases ga with
  | mk symbol terms term_length =>
    unfold atomWithoutVariablesToGroundAtom
    unfold groundAtom.toAtom
    simp
    apply List.ext_get
    rw [List.length_map, List.length_attach, List.length_map]

    intros n h1 h2
    rw [List.get_map]
    simp [List.get_map]
    unfold termWithoutVariablesToConstant
    simp

lemma groundingAtomWithoutVariablesYieldsSelf (a: atom τ) (noVars: atomVariables a = ∅): ∀ (g: grounding τ), atomGrounding g a = a := by
  intro  g
  simp
  unfold atomGrounding
  unfold groundAtom.toAtom
  simp
  congr
  apply List.ext_get
  simp
  intro n h1 h2
  simp

  have h: ∀ (t: term τ) (g:grounding τ), termVariables t = ∅ → applyGroundingTerm' g t = t := by
    intro t g
    simp
    cases t with
    | constant c =>
      unfold applyGroundingTerm'
      simp
    | variableDL v =>
      unfold termVariables
      simp
  simp at h
  rw [h]
  unfold atomVariables at noVars
  rw [List.foldl_union_empty] at noVars
  simp at noVars
  apply noVars
  apply List.get_mem

lemma inGetSubstitutionsImplInInterpretation (i: List (groundAtom τ))(a: atom τ) (s: substitution τ) (h: s ∈ getSubstitutions i a)  (noVars: atomVariables (applySubstitutionAtom s a) = ∅): atomWithoutVariablesToGroundAtom (applySubstitutionAtom s a) noVars ∈ i :=
by
  unfold getSubstitutions at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨ga, ga_i, match_ga⟩

  have matchAtomSome: Option.isSome (matchAtom emptySubstitution a ga) = true := by
    rw [match_ga]
    simp
  have matchSemantic:applySubstitutionAtom (Option.get (matchAtom emptySubstitution a ga) matchAtomSome) a = ga := by
    simp [matchAtomFindsSolution]

  simp at matchSemantic
  have matchAtom_s: Option.get (matchAtom emptySubstitution a ga) matchAtomSome= s := by
    simp [match_ga]

  simp [← matchAtom_s]
  simp [matchSemantic]
  rw [atomWithoutVariablesToGroundAtomOfGroundAtom]
  exact ga_i


lemma inGetSubstitutionsIffMinimalSolutionAndInInterpretation (i: List (groundAtom τ))(a: atom τ): ∀ (s: substitution τ), s ∈ getSubstitutions i a ↔ ∃ (ga: groundAtom τ), ga ∈ List.toSet i  ∧ applySubstitutionAtom s a = ga ∧ ∀ (s': substitution τ), applySubstitutionAtom s' a = ga → s ⊆ s' :=
by
  intro s
  unfold getSubstitutions
  rw [List.mem_filterMap]
  constructor
  intro h
  rcases h with ⟨ga, ga_i, match_ga⟩
  use ga
  constructor
  rw [← List.toSet_mem]
  apply ga_i
  simp
  have match_some: Option.isSome (matchAtom emptySubstitution a ga) = true := by
    rw [Option.isSome_iff_exists]
    use s
  have s_get: s = Option.get (matchAtom emptySubstitution a ga) match_some := by
    simp [match_ga]
  constructor
  rw [s_get]
  simp [matchAtomFindsSolution]
  intros s' s'_ga
  rw [s_get]
  apply matchAtomFindsMinimalSolution
  simp
  constructor
  apply s'_ga
  apply emptySubstitutionIsMinimal

  intro h
  rcases h with ⟨ga, ga_i, apply_s, s_min ⟩
  use ga
  constructor
  rw [← List.toSet_mem] at ga_i
  apply ga_i
  cases h:(matchAtom emptySubstitution a ga) with
  | none =>
    exfalso
    have noneGa: Option.isNone (matchAtom emptySubstitution a ga) = true := by
      simp [h]
    have p:  ∀ (s': substitution τ), emptySubstitution ⊆ s' →  ¬ applySubstitutionAtom s' a = ga := by
      apply matchAtomNoneImplNoSolution
      apply noneGa
    specialize p s
    have emptySubs_s: emptySubstitution ⊆ s := by
      apply emptySubstitutionIsMinimal
    specialize p emptySubs_s
    simp at p
    simp at apply_s
    exact absurd apply_s p
  | some s' =>
    have someGa: Option.isSome (matchAtom emptySubstitution a ga) = true := by
      rw [h]
      simp
    have min_s': ∀ (s2: substitution τ), applySubstitutionAtom s2 a = ga ∧ emptySubstitution ⊆ s2 → (Option.get (matchAtom emptySubstitution a ga) someGa) ⊆ s2 := by
      apply matchAtomFindsMinimalSolution
    specialize s_min s'
    have apply_s': applySubstitutionAtom s' a = ga := by
      have s'_match: s' = Option.get (matchAtom emptySubstitution a ga) someGa := by
        simp [h]
      rw [s'_match]
      simp [matchAtomFindsSolution]
    specialize s_min apply_s'
    specialize min_s' s
    simp  [apply_s, emptySubstitutionIsMinimal, h] at min_s'
    have s_s': s= s' := by
      apply substitution_subs_antisymm
      apply s_min
      apply min_s'
    rw [s_s']

lemma headOfSafePgrWithoutGroundedBodyHasNoVariables (pgr: partialGroundRule τ) (safe: pgr.isSafe) (body: pgr.ungroundedBody = []): atomVariables pgr.head = ∅ :=
by
  unfold partialGroundRule.isSafe at safe
  rw [body] at safe
  unfold List.foldl_union at safe
  simp at safe
  apply Finset.Subset.antisymm
  apply safe
  simp

def moveAtomWithoutVariables (pgr: partialGroundRule τ) (hd: atom τ) (tl: List (atom τ)) (noVars: atomVariables hd = ∅): partialGroundRule τ :=
{
  head := pgr.head,
  groundedBody := pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom hd noVars]
  ungroundedBody := tl
}

lemma moveAtomWithoutVariablesPreservesSafety (pgr: partialGroundRule τ) (hd: atom τ) (tl: List (atom τ)) (body: pgr.ungroundedBody = hd::tl) (noVars: atomVariables hd = ∅) (safe: pgr.isSafe): (moveAtomWithoutVariables pgr hd tl noVars).isSafe :=
by
  unfold partialGroundRule.isSafe at *
  unfold moveAtomWithoutVariables
  simp
  rw [body] at safe
  unfold List.foldl_union at safe
  simp at safe
  rw [noVars] at safe
  unfold List.foldl_union
  apply safe


def groundingStep (pgr: partialGroundRule τ) (hd: atom τ) (tl: List (atom τ)) (s: substitution τ) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅ ): partialGroundRule τ :=
{
  head := applySubstitutionAtom s pgr.head,
  groundedBody := pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars],
  ungroundedBody := List.map (applySubstitutionAtom s) tl
}

lemma groundingStepPreservesSafety (pgr: partialGroundRule τ) (hd: atom τ) (tl: List (atom τ)) (s: substitution τ) (h: pgr.ungroundedBody = hd::tl) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅ ) (safe: pgr.isSafe): (groundingStep pgr hd tl s noVars).isSafe :=
by
  unfold partialGroundRule.isSafe
  unfold groundingStep
  simp
  rw [atomVariablesApplySubstitution]
  rw [Finset.subset_iff]

  intro v
  rw [List.mem_foldl_union]
  simp
  simp_rw [atomVariablesApplySubstitution]
  rw [Finset.mem_filter_nc]
  intro h
  rcases h with ⟨v_dom, v_head⟩
  unfold partialGroundRule.isSafe at safe
  rw [Finset.subset_iff] at safe
  specialize safe v_head
  rw [List.mem_foldl_union] at safe
  simp at safe
  rcases safe with ⟨a, a_body, v_a⟩
  use a
  rw [h] at a_body
  simp at a_body
  cases a_body with
  | inl a_hd =>
    rw [atomVariablesApplySubstitution] at noVars
    rw [a_hd] at v_a
    have mem_v: v ∈ Finset.filter_nc (fun x => x ∉ substitution_domain s) (atomVariables hd) := by
      rw [Finset.mem_filter_nc]
      simp [v_dom, v_a]
    rw [noVars] at mem_v
    simp at mem_v
  | inr a_tl =>
    simp [a_tl]
    rw [Finset.mem_filter_nc]
    simp [v_dom, v_a]



def exploreGrounding (pgr: partialGroundRule τ) (i: List (groundAtom τ)) (safe: pgr.isSafe): Except String Unit :=
  match h:pgr.ungroundedBody with
  | [] =>
    let head' := atomWithoutVariablesToGroundAtom pgr.head (headOfSafePgrWithoutGroundedBodyHasNoVariables pgr safe h)

    if head' ∈ i
    then Except.ok ()
    else Except.error ("Unfulfilled rule: " ++ ToString.toString pgr.toRule)
  | hd::tl =>
    if noVars:atomVariables hd = ∅
    then
      if atomWithoutVariablesToGroundAtom hd noVars ∈ i
      then exploreGrounding (moveAtomWithoutVariables pgr hd tl noVars) i (moveAtomWithoutVariablesPreservesSafety pgr hd tl h noVars safe)
      else Except.ok ()
    else
      List.map_except_unit (getSubstitutions i hd).attach (fun ⟨s, _h⟩ =>
        let noVars':= inGetSubstitutionsImplNoVars i hd s _h
        exploreGrounding (groundingStep pgr hd tl s noVars') i (groundingStepPreservesSafety pgr hd tl s h noVars' safe)

      )
termination_by pgr.ungroundedBody.length
decreasing_by
  simp_wf
  unfold moveAtomWithoutVariables
  rw [h]
  simp

  simp_wf
  unfold groundingStep
  rw [h]
  simp

lemma applySubstitutionOnConstantIsSame (c: τ.constants) (s: substitution τ): applySubstitutionTerm s c = c := by
  unfold applySubstitutionTerm
  simp

lemma applySubstitutionOnGroundAtomIsSame (ga: groundAtom τ) (s: substitution τ): applySubstitutionAtom s ga = ga := by
  simp
  unfold groundAtom.toAtom
  unfold applySubstitutionAtom
  simp

  apply List.ext_get
  simp
  intro n h1 h2
  simp
  rw [applySubstitutionOnConstantIsSame]


lemma swapPgrApplySubstitution  (head hd: atom τ) (groundedBody: List (groundAtom τ)) (tl: List (atom τ))  (s: substitution τ) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅): ({head:= applySubstitutionAtom s head, groundedBody:= groundedBody ++ [atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars], ungroundedBody:= List.map (applySubstitutionAtom s) tl}: partialGroundRule τ).toRule = applySubstitutionRule s (({head:=head, groundedBody:=groundedBody, ungroundedBody:=hd::tl}: partialGroundRule τ).toRule) := by
  unfold partialGroundRule.toRule
  unfold applySubstitutionRule
  simp

  have h1:List.map groundAtom.toAtom groundedBody = List.map (applySubstitutionAtom s ∘ groundAtom.toAtom) groundedBody := by
    apply List.ext_get
    simp
    intro n h1 h2
    simp
    rw [applySubstitutionOnGroundAtomIsSame]
  rw [h1]
  have h2: groundAtom.toAtom (atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars) = applySubstitutionAtom s hd := by
    rw [← groundAtomToAtomOfAtomWithoutVariablesToGroundAtomIsSelf]
  rw [h2]

def combineSubstitutionGrounding (s: substitution τ) (g: grounding τ): grounding τ := fun x => if h: Option.isSome (s x) then Option.get (s x) h else g x

lemma combineSubstitutionGroundingEquivTerm (t: term τ) (s: substitution τ) (g: grounding τ): applyGroundingTerm' g (applySubstitutionTerm s t) = applyGroundingTerm' (combineSubstitutionGrounding s g) t := by
  unfold applyGroundingTerm'
  unfold applySubstitutionTerm
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    unfold combineSubstitutionGrounding
    by_cases p: Option.isSome (s v)
    simp [p]
    simp [p]

lemma combineSubstitutionGroundingEquivAtom (a: atom τ) (s: substitution τ) (g: grounding τ): atomGrounding g (applySubstitutionAtom s a) = atomGrounding (combineSubstitutionGrounding s g) a := by
  unfold atomGrounding
  unfold applySubstitutionAtom
  simp
  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  simp [← List.map_map, List.get_map, combineSubstitutionGroundingEquivTerm]


lemma combineSubstitutionGroundingEquivRule (r: rule τ) (s: substitution τ) (g: grounding τ): ruleGrounding  (applySubstitutionRule s r) g = ruleGrounding r (combineSubstitutionGrounding s g)  := by
  unfold ruleGrounding
  unfold applySubstitutionRule
  simp [combineSubstitutionGroundingEquivAtom]
  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  simp [← List.map_map, List.get_map, combineSubstitutionGroundingEquivAtom]

def atomSubOfGrounding (a: atom τ) (g: grounding τ): substitution τ := fun x => if x ∈ atomVariables a then some (g x) else none

lemma atomSubOfGroundingEqOnTerm (a: atom τ) (g: grounding τ) (t: term τ) (mem: t ∈ a.atom_terms): applySubstitutionTerm (atomSubOfGrounding a g) t = term.constant (applyGroundingTerm' g t) := by
  unfold atomSubOfGrounding
  unfold applySubstitutionTerm
  unfold applyGroundingTerm'
  simp
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    simp
    have v_atomVars: v ∈ atomVariables a := by
      unfold atomVariables
      rw [List.mem_foldl_union]
      simp
      use (term.variableDL v)
      constructor
      apply mem
      unfold termVariables
      simp

    have h: Option.isSome (if v ∈ atomVariables a then some (g v) else none) = true := by
      rw [Option.isSome_iff_exists]
      use (g v)
      simp [v_atomVars]

    simp [h]
    simp [v_atomVars]

lemma atomSubOfGroundingEqOnAtom (a: atom τ) (g: grounding τ): applySubstitutionAtom (atomSubOfGrounding a g) a = atomGrounding g a := by
  unfold applySubstitutionAtom
  unfold atomGrounding
  unfold groundAtom.toAtom
  simp
  apply List.ext_get
  rw [List.length_map, List.length_map]
  intro n h1 h2
  rw [List.get_map, List.get_map]
  apply atomSubOfGroundingEqOnTerm
  simp
  apply List.get_mem

lemma equalOfListMapEqual {A B: Type} (l:List A) (f g: A → B) (h: List.map f l = List.map g l) (a: A) (mem: a ∈ l): f a = g a := by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp at mem
    simp at h
    cases mem with
    | inl p =>
      rw [← p] at h
      simp [h]
    | inr p =>
      apply ih
      simp [h]
      apply p

lemma atomSubOfGroundingIsMinimalForAtom (a: atom τ) (g: grounding τ):
(∀ (s' : substitution τ), applySubstitutionAtom s' a = groundAtom.toAtom (atomGrounding g a) → atomSubOfGrounding a g ⊆ s') := by
  intro s' s'_a
  unfold_projs
  unfold substitution_subs
  intro v
  intro h'
  unfold substitution_domain at h'
  simp at h'
  unfold atomSubOfGrounding
  cases h:(atomSubOfGrounding a g v) with
  | some c =>
    unfold atomSubOfGrounding at h
    have p: v ∈ atomVariables a := by
      by_contra q
      simp [q] at h
    simp [p] at h
    unfold applySubstitutionAtom at s'_a
    unfold atomGrounding at s'_a
    unfold groundAtom.toAtom at s'_a
    simp at s'_a
    have s'_v: applySubstitutionTerm s' (term.variableDL v) = (term.constant ∘ applyGroundingTerm' g) (term.variableDL v) := by
      apply equalOfListMapEqual (h:= s'_a)
      unfold atomVariables at p
      rw [List.mem_foldl_union] at p
      simp at p
      rcases p with ⟨t, p⟩
      cases t with
      | constant c =>
        unfold termVariables at p
        simp at p
      | variableDL v' =>
        unfold termVariables at p
        simp at p
        simp [p]
    unfold applySubstitutionTerm at s'_v
    unfold applyGroundingTerm' at s'_v
    simp at s'_v
    cases h': (s' v) with
    | some c' =>
      simp [h'] at s'_v
      rw [h] at s'_v
      simp
      simp [p]
      rw [h]
      apply Eq.symm
      apply s'_v
    | none =>
      simp [h'] at *
  | none =>
    rw [h] at h'
    simp at h'

lemma atomSubOfGroundingGroundingEqGroundingOnTerm (a : atom τ)  (g: grounding τ) (t: term τ): applyGroundingTerm' g (applySubstitutionTerm (atomSubOfGrounding a g) t) = applyGroundingTerm' g t := by
  unfold applyGroundingTerm'
  unfold applySubstitutionTerm
  unfold atomSubOfGrounding
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    simp
    by_cases h: Option.isSome (if v ∈ atomVariables a then some (g v) else none) = true
    simp [h]
    by_cases p: v ∈ atomVariables a
    simp [p]
    simp [p] at h
    simp [h]


lemma atomSubOfGroundingGroundingEqGroundingOnAtom (a a': atom τ)  (g: grounding τ) : atomGrounding g (applySubstitutionAtom (atomSubOfGrounding a g) a') = atomGrounding g a' := by
  unfold atomGrounding
  unfold applySubstitutionAtom
  simp
  apply List.ext_get
  rw [List.length_map, List.length_map]

  intro n h1 h2
  simp [← List.map_map]
  simp [atomSubOfGroundingGroundingEqGroundingOnTerm]


lemma atomSubOfGroundingGroundingEqGroundingOnRule (a: atom τ) (g: grounding τ) (r: rule τ): ruleGrounding (applySubstitutionRule (atomSubOfGrounding a g) r) g = ruleGrounding r g := by
  unfold ruleGrounding
  unfold applySubstitutionRule
  simp
  constructor
  apply atomSubOfGroundingGroundingEqGroundingOnAtom

  apply List.ext_get
  rw [List.length_map, List.length_map]
  intros n h1 h2
  rw [List.get_map, List.get_map]
  simp [atomSubOfGroundingGroundingEqGroundingOnAtom]

lemma replaceGroundingWithSubstitutionAndGrounding (a: atom τ) (r: rule τ) (mem: a ∈ r.body ): (∀ (g: grounding τ),   ruleTrue (ruleGrounding r g) i) ↔ ∀ (s: substitution τ), (∃ (ga: groundAtom τ), ga ∈ i ∧ applySubstitutionAtom s a = ga ∧ ∀ (s': substitution τ), applySubstitutionAtom s' a = ga → s ⊆ s') →  ∀ (g': grounding τ),ruleTrue (ruleGrounding (applySubstitutionRule s r) g') i := by
  constructor
  intro h s _ g'
  rw [combineSubstitutionGroundingEquivRule]
  apply h

  intro h g
  by_cases g_a_i: atomGrounding g a ∈ i
  specialize h (atomSubOfGrounding a g)
  simp at h
  specialize h (atomGrounding g a) g_a_i  (atomSubOfGroundingEqOnAtom a g)
  specialize h (atomSubOfGroundingIsMinimalForAtom a g) g
  rw [atomSubOfGroundingGroundingEqGroundingOnRule] at h
  apply h

  unfold ruleTrue
  intro bodySet
  rw [Set.subset_def] at bodySet
  simp at bodySet
  specialize bodySet (atomGrounding g a)
  rw [← groundRuleBodySet_iff_groundRuleBody] at bodySet
  unfold ruleGrounding at bodySet
  simp at bodySet
  specialize bodySet a mem
  simp at bodySet
  contradiction



theorem exploreGroundingSemantics (i: List (groundAtom τ)) (pgr: partialGroundRule τ) (safe: pgr.isSafe) (active: pgr.isActive i.toSet): exploreGrounding pgr i safe = Except.ok () ↔ pgr.isTrue i.toSet := by
  cases pgr with
  | mk head groundedBody ungroundedBody =>
    induction' length: ungroundedBody.length with n ih generalizing head groundedBody ungroundedBody

    rw [List.length_eq_zero] at length
    simp_rw [length]
    unfold exploreGrounding
    simp
    unfold partialGroundRule.isTrue
    simp_rw [groundingOnPartialGroundRule]
    unfold ruleTrue
    simp
    simp_rw [← List.toSet_mem]
    have bodyEmpty: ({head:=head, groundedBody := groundedBody, ungroundedBody := ungroundedBody}:partialGroundRule τ).ungroundedBody = [] :=
      by
        simp
        exact length
    have h': head = atomWithoutVariablesToGroundAtom head (headOfSafePgrWithoutGroundedBodyHasNoVariables {head:=head, groundedBody := groundedBody, ungroundedBody := ungroundedBody} safe bodyEmpty) := by
      simp
      rw [← groundAtomToAtomOfAtomWithoutVariablesToGroundAtomIsSelf]
    unfold groundRuleBodySet
    simp
    constructor
    intro h g _
    rw [h']
    simp
    rw [atomGroundingOnGroundAtomReturnsSame]
    apply h
    intro h
    specialize h (substitutionToGrounding emptySubstitution)
    have subs: {a | a ∈ groundedBody} ⊆ List.toSet i := by
      rw [Set.subset_def]
      intro a
      simp
      intro a_mem
      unfold partialGroundRule.isActive at active
      apply active
      simp
      exact a_mem
    specialize h subs
    rw [h'] at h
    simp at h
    rw [atomGroundingOnGroundAtomReturnsSame] at h
    exact h

    unfold exploreGrounding
    cases ungroundedBody with
    | nil => simp at length
    | cons hd tl =>
      simp
      simp at length
      split
      rename_i noVars

      by_cases hd_i: (atomWithoutVariablesToGroundAtom hd noVars) ∈ i
      simp [hd_i]
      unfold moveAtomWithoutVariables
      simp
      rw [ih]
      apply partialGroundRule.isTrue_of_equal_toRule
      unfold partialGroundRule.toRule
      simp
      rw [← groundAtomToAtomOfAtomWithoutVariablesToGroundAtomIsSelf]
      unfold partialGroundRule.isActive
      intro ga
      simp
      intro h
      cases h with
      | inl ga_body =>
        apply active
        simp
        exact ga_body
      | inr ga_hd =>
        rw [ga_hd]
        rw [← List.toSet_mem]
        exact hd_i
      exact length

      simp[hd_i]
      unfold partialGroundRule.isTrue
      intro g
      unfold ruleTrue
      rw [groundingOnPartialGroundRule]
      simp
      intro body_subs
      rw [Set.subset_def] at body_subs
      simp at body_subs
      specialize body_subs (atomWithoutVariablesToGroundAtom hd noVars)
      rw [← groundRuleBodySet_iff_groundRuleBody] at body_subs
      simp at body_subs
      have n_hd_i: atomWithoutVariablesToGroundAtom hd noVars ∈  i:= by
        rw [List.toSet_mem]
        apply body_subs
        right
        left
        rw [groundAtomToAtomEquality]
        rw [← groundAtomToAtomOfAtomWithoutVariablesToGroundAtomIsSelf, groundingAtomWithoutVariablesYieldsSelf]
        exact noVars
      contradiction

      rw [List.map_except_unitIsUnitIffAll]
      simp
      unfold groundingStep
      simp
      constructor
      intro h
      unfold partialGroundRule.isTrue
      rw [replaceGroundingWithSubstitutionAndGrounding (a:=hd)]
      simp
      intro s ga ga_i s_hd_ga s_min
      specialize h s
      have s_getSubs: s ∈ getSubstitutions i hd := by
        rw [inGetSubstitutionsIffMinimalSolutionAndInInterpretation]
        simp
        use ga
      specialize h s_getSubs
      rw [ih] at h
      unfold partialGroundRule.isTrue at h
      rw [swapPgrApplySubstitution] at h
      apply h
      unfold partialGroundRule.isActive
      simp
      intro ga ga_mem
      cases ga_mem with
      | inl ga_body =>
        unfold partialGroundRule.isActive at active
        apply active
        simp
        exact ga_body
      | inr ga_hd =>
        rw [ga_hd]
        rw [← List.toSet_mem]
        apply inGetSubstitutionsImplInInterpretation
        exact s_getSubs
      simp
      exact length
      unfold partialGroundRule.toRule
      simp

      intro h s s_mem
      rw [ih]
      unfold partialGroundRule.isTrue
      intro g
      rw [swapPgrApplySubstitution, combineSubstitutionGroundingEquivRule]
      unfold partialGroundRule.isTrue at h
      apply h

      unfold partialGroundRule.isActive
      simp
      intro ga ga_mem
      cases ga_mem with
      | inl ga_body =>
        apply active
        simp
        exact ga_body
      | inr ga_hd =>
        rw [ga_hd]
        rw [← List.toSet_mem]
        apply inGetSubstitutionsImplInInterpretation
        exact s_mem
      simp
      exact length



lemma safePreservedBetweenRuleAndPartialGroundRule (r: rule τ) : r.isSafe ↔ (partialGroundRule.fromRule r).isSafe := by
  unfold partialGroundRule.isSafe
  unfold rule.isSafe
  unfold partialGroundRule.fromRule
  simp

def modelChecker (i: List (groundAtom τ)) (P: List (rule τ)) (safe: ∀ (r: rule τ), r ∈ P → r.isSafe): Except String Unit :=
  have safe': ∀ (r: rule τ), r ∈ P → (partialGroundRule.fromRule r).isSafe := by
    intros r rP
    rw [← safePreservedBetweenRuleAndPartialGroundRule]
    apply safe r rP
  List.map_except_unit P.attach (fun ⟨x, _h⟩ => exploreGrounding (partialGroundRule.fromRule x ) i (safe' x _h) )

theorem modelCheckerUnitIffAllRulesTrue (i: List (groundAtom τ)) (P: List (rule τ)) (safe: ∀ (r: rule τ), r ∈ P → r.isSafe): modelChecker i P safe = Except.ok () ↔ (∀ (r: groundRule τ), r ∈ groundProgram P.toFinset → ruleTrue r i.toSet) :=
by
  unfold modelChecker
  rw [List.map_except_unitIsUnitIffAll]
  simp
  constructor
  intro h gr grP
  unfold groundProgram at grP
  simp at grP
  rcases grP with ⟨r, rP, g, r_g⟩
  specialize h r rP
  rw [exploreGroundingSemantics] at h
  unfold partialGroundRule.isTrue at h
  specialize h g
  rw [← partialGroundRuleToRuleInverseToFromRule, ← r_g] at h
  exact h
  apply partialGroundRule.fromRuleIsActive

  intro h r rP
  rw [exploreGroundingSemantics]
  unfold partialGroundRule.isTrue
  intro g
  rw [← partialGroundRuleToRuleInverseToFromRule]
  specialize h (ruleGrounding r g)
  apply h
  unfold groundProgram
  simp
  use r
  simp[*]
  apply partialGroundRule.fromRuleIsActive

