import CertifyingDatalog.Datalog
import CertifyingDatalog.Database
import CertifyingDatalog.Unification
import Mathlib.Data.Set.Basic
import CertifyingDatalog.Basic

structure partialGroundRule (τ: signature)[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.predicateSymbols] [Hashable τ.vars] (i: interpretation τ) where
  head: atom τ
  groundedBody: List (groundAtom τ)
  ungroundedBody: List (atom τ)

  members: ∀ (ga: groundAtom τ), ga ∈ groundedBody → ga ∈ i

variable  {τ: signature}[DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Inhabited τ.constants]  [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.predicateSymbols]
 {i: interpretation τ}
def partialGroundRule.isSafe (pgr: partialGroundRule τ i): Prop :=
  atomVariables pgr.head ⊆ collectResultsToFinset atomVariables pgr.ungroundedBody


def partialGroundRuleFromRule (r: rule τ) (i: interpretation τ): partialGroundRule τ i :=
  have members: ∀ (ga: groundAtom τ), ga ∈ [] → ga ∈ i:= by
    simp
  {head := r.head, groundedBody := [], ungroundedBody := r.body, members := members}

def partialGroundRule.toRule (pgr: partialGroundRule τ i): rule τ :=
  {head:= pgr.head, body := (List.map (groundAtom.toAtom) pgr.groundedBody) ++ pgr.ungroundedBody}

lemma partialGroundRuleToRuleInverseToFromRule (r: rule τ) (i: interpretation τ): r = partialGroundRule.toRule (partialGroundRuleFromRule r i) := by
  unfold partialGroundRuleFromRule
  unfold partialGroundRule.toRule
  simp

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
  have h: ∀ (l: List (term τ)), (collectResultsToFinset termVariables l = ∅ ↔ ∀ (t : term τ), t ∈ l → termVariables t = ∅) := by
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
  have term_length: (List.map (fun ⟨x, _h⟩ => termWithoutVariablesToConstant x (h x _h)) a.atom_terms.attach).length = τ.predicateArity (a.symbol) := by
    rw [List.length_map, List.length_attach]
    apply a.term_length
{symbol:= a.symbol, atom_terms := List.map (fun ⟨x, _h⟩ => termWithoutVariablesToConstant x (h x _h)) a.atom_terms.attach, term_length := term_length }

lemma atomWithoutVariablesToGroundAtomOfGroundAtom (ga: groundAtom τ)(h: atomVariables ga.toAtom = ∅): atomWithoutVariablesToGroundAtom ga.toAtom h = ga :=
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

lemma termConstantOfTermWithoutVariablesIsId (t: term τ)(h: termVariables t = ∅): term.constant (termWithoutVariablesToConstant t h) = t :=
by
  cases t with
  | constant c =>
    unfold termWithoutVariablesToConstant
    simp
  | variableDL v =>
    unfold termVariables at h
    simp at h

lemma toAtomOfatomWithoutVariablesIsSelf (a: atom τ) (h: atomVariables a = ∅): (atomWithoutVariablesToGroundAtom a h).toAtom = a :=
by
  cases a with
  | mk symbol terms term_length =>
    unfold atomWithoutVariablesToGroundAtom
    unfold groundAtom.toAtom
    rw [atomEquality]
    simp
    apply List.ext_get
    rw [List.length_map, List.length_attach]

    intro n h1 h2
    simp [← List.map_map]
    simp[termConstantOfTermWithoutVariablesIsId]




def getSubstitutions (i: List (groundAtom τ))(a: atom τ): List (substitution τ) := List.filterMap (fun x => matchAtom emptySubstitution a x) i

lemma collectResultsToFinsetEmptyIffAllMembersAre {A: Type} (f: A → Set τ.vars) (l: List A): collectResultsToFinset f l = ∅ ↔ ∀ (a:A), a ∈ l → f a = ∅ := by
  induction l with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    rw [union_is_empty_iff_both]
    rw [ih]
    simp

lemma groundAtomsHaveNoVariables (ga: groundAtom τ): atomVariables ga.toAtom = ∅ := by
  cases ga with
  | mk symbol atom_terms term_length =>
    unfold atomVariables
    unfold groundAtom.toAtom
    simp
    rw [collectResultsToFinsetEmptyIffAllMembersAre]
    intros t t_map
    rw [List.mem_map] at t_map
    rcases t_map with ⟨c, _, c_t⟩
    rw [← c_t]
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
  apply ga_i

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

lemma applySubstitutionAtomRemovesDomainFromAtomVars (a: atom τ) (s: substitution τ): atomVariables (applySubstitutionAtom s a) = (atomVariables a) \ (substitution_domain s) :=
by
  unfold atomVariables
  unfold applySubstitutionAtom
  simp
  rw [Set.ext_iff]
  intro v
  simp [collectResultsToFinsetMemberIffListMember]
  constructor
  intro h
  rcases h with ⟨t, t_mem, v_t⟩
  rw [← exists_and_right]
  use t
  rw [and_assoc]
  constructor
  apply t_mem
  unfold applySubstitutionTerm at v_t
  cases t with
  | constant c =>
    simp at v_t
    unfold termVariables at v_t
    simp at v_t
  | variableDL v' =>
    unfold termVariables at v_t
    simp at v_t
    by_cases h: Option.isSome (s v') = true
    simp [h] at v_t
    simp [h] at v_t
    rw [v_t]
    unfold termVariables
    simp
    unfold substitution_domain
    simp
    cases h':s v' with
    | some o =>
      rw [h'] at h
      simp at h
    | none =>
      simp

  intro h
  rw [← exists_and_right] at h
  rcases h with ⟨t, h_t⟩
  use t
  simp [h_t]
  rcases h_t with ⟨left, v_dom⟩
  rcases left with ⟨t_terms, v_t⟩
  unfold applySubstitutionTerm
  unfold termVariables
  cases t with
  | constant c =>
    simp
    unfold termVariables at v_t
    simp at v_t
  | variableDL v' =>
    simp
    unfold termVariables at v_t
    simp at v_t
    unfold substitution_domain at v_dom
    rw [Set.mem_setOf] at v_dom
    rw [v_t] at v_dom
    simp [v_dom]
    apply v_t






def groundingStep (s: substitution τ) (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: atom τ) (tl: List (atom τ)) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅ ) (mem: atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars ∈ i): partialGroundRule τ i.toSet :=
  have h: ∀ (ga : groundAtom τ), ga ∈ pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars] → ga ∈ List.toSet i := by
    intros ga
    simp
    intro h'
    cases h' with
    | inl ga_grounded =>
      apply pgr.members ga ga_grounded
    | inr ga_new =>
      rw [ga_new]
      rw [← List.toSet_mem]
      apply mem
  {head:= applySubstitutionAtom s pgr.head, groundedBody:= pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars] , ungroundedBody := List.map (fun x => applySubstitutionAtom s x) tl, members := h}

def groundingStepPreservesSafety (s: substitution τ) (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: atom τ) (tl: List (atom τ)) (noVars: atomVariables (applySubstitutionAtom s hd) = ∅ ) (mem: atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars ∈ i) (safe: pgr.isSafe) (h: pgr.ungroundedBody = hd::tl ): (groundingStep s i pgr hd tl noVars mem).isSafe := by
  unfold partialGroundRule.isSafe
  unfold groundingStep
  simp
  rw [applySubstitutionAtomRemovesDomainFromAtomVars,collectResultsToFinsetSemantics, Set.subset_def]
  simp
  intros v v_head v_dom
  unfold partialGroundRule.isSafe at safe
  rw [collectResultsToFinsetSemantics, Set.subset_def] at safe
  simp at safe
  specialize safe v v_head
  rcases safe with ⟨a, a_body, v_a⟩
  rw [h] at a_body
  simp at a_body
  cases a_body with
  | inl a_hd =>
    rw [a_hd] at v_a
    exfalso
    rw [applySubstitutionAtomRemovesDomainFromAtomVars] at noVars
    rw [Set.ext_iff] at noVars
    specialize noVars v
    simp at noVars
    specialize noVars v_a
    exact absurd noVars v_dom
  | inr a_tl =>
    use a
    constructor
    exact a_tl
    rw [applySubstitutionAtomRemovesDomainFromAtomVars]
    simp
    constructor
    apply v_a
    apply v_dom

def atomVariablesEmpty.go (l: List (term τ)): Bool :=
  match l with
  | [] => true
  | hd::tl =>
    match hd with
    | term.constant _ => atomVariablesEmpty.go tl
    | term.variableDL _ => false

def atomVariablesEmpty (a: atom τ): Bool := atomVariablesEmpty.go a.atom_terms

lemma atomVariablesEmptyGoSemantics (l: List (term τ)): atomVariablesEmpty.go l = true ↔ collectResultsToFinset termVariables l = ∅  := by
  induction l with
  | nil =>
    unfold atomVariablesEmpty.go
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold atomVariablesEmpty.go
    unfold collectResultsToFinset
    cases hd with
    | constant c =>
      unfold termVariables
      simp
      unfold termVariables at ih
      simp [ih]
    | variableDL v =>
      unfold termVariables
      simp
      rw [Set.ext_iff]
      push_neg
      simp


lemma atomVariablesEmptySemantics (a: atom τ): atomVariablesEmpty a = true ↔ atomVariables a = ∅ :=
by
  unfold atomVariables
  unfold atomVariablesEmpty
  apply atomVariablesEmptyGoSemantics

lemma groundingStepGroundAtomExtendMembers (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: groundAtom τ) (mem: hd ∈ i):  ∀ (ga : groundAtom τ), ga ∈ pgr.groundedBody ++ [hd] → ga ∈ List.toSet i:= by
  intro ga
  simp
  intro p
  cases p with
  | inl q =>
    apply pgr.members
    apply q
  | inr q =>
    rw [← List.toSet_mem,q]
    apply mem

lemma groundingStepGroundAtomExtendMembers_append (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: groundAtom τ) (mem: hd ∈ i):  ∀ (ga : groundAtom τ), ga ∈ (pgr.groundedBody ++ [hd]) → ga ∈ List.toSet i:= by
  intro ga
  simp
  intro p
  cases p with
  | inl q =>
    apply pgr.members
    apply q
  | inr q =>
    rw [← List.toSet_mem,q]
    apply mem

def groundingStepGroundAtom (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: groundAtom τ) (tl: List (atom τ)) (mem: hd ∈ i): partialGroundRule τ i.toSet :=
  {head:= pgr.head, groundedBody := pgr.groundedBody ++ [hd], ungroundedBody := tl, members := groundingStepGroundAtomExtendMembers i pgr hd mem}

def groundingStepGroundAtomPreservesSafe (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (hd: groundAtom τ) (tl: List (atom τ)) (mem: hd ∈ i) (safe: pgr.isSafe) (h: pgr.ungroundedBody = hd.toAtom::tl ): (groundingStepGroundAtom i pgr hd tl mem).isSafe :=
by
  unfold partialGroundRule.isSafe
  unfold groundingStepGroundAtom
  simp
  unfold partialGroundRule.isSafe at safe
  rw [h] at safe
  unfold collectResultsToFinset at safe
  rw [groundAtomsHaveNoVariables, Set.empty_union] at safe
  apply safe


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
      rw [Set.subset_def] at safe
      specialize safe v
      apply safe
    if (atomWithoutVariablesToGroundAtom pgr.head varHead) ∈ i
    then Except.ok ()
    else Except.error "Error"
  | hd::tl =>
    have noVars: ∀ (s: substitution τ), s ∈ getSubstitutions i hd → atomVariables (applySubstitutionAtom s hd) = ∅ := by
      apply inGetSubstitutionsImplNoVars
    if h': atomVariablesEmpty hd = true
    then
      have varsHd: atomVariables hd = ∅ := by
        rw [atomVariablesEmptySemantics] at h'
        apply h'
      have uBody': pgr.ungroundedBody = (atomWithoutVariablesToGroundAtom hd varsHd).toAtom :: tl := by
        rw [toAtomOfatomWithoutVariablesIsSelf]
        apply h
      if p: atomWithoutVariablesToGroundAtom hd varsHd ∈ i
      then
        exploreGrounding i (groundingStepGroundAtom i pgr (atomWithoutVariablesToGroundAtom hd varsHd) tl p) (groundingStepGroundAtomPreservesSafe i pgr (atomWithoutVariablesToGroundAtom hd varsHd) tl p safe uBody')
      else
        Except.ok ()
    else
      List.map_except_unit (getSubstitutions i hd).attach (fun ⟨s, _h⟩ => exploreGrounding i (groundingStep s i pgr hd tl (noVars s _h) (inGetSubstitutionsImplInInterpretation i hd s _h (noVars s _h))) (groundingStepPreservesSafety s i pgr hd tl (noVars s _h) (inGetSubstitutionsImplInInterpretation i hd s _h (noVars s _h)) safe h) )
termination_by pgr.ungroundedBody.length
decreasing_by
  all_goals{
  simp_wf
  simp [groundingStep, groundingStepGroundAtom, h]
  }

lemma applyGroundingTermEqtermWithoutVariablesToConstant (t: term τ) (noVars: termVariables t = ∅) (g: grounding τ): termWithoutVariablesToConstant t noVars = applyGroundingTerm' g t := by
  cases t with
  | constant c =>
    unfold termWithoutVariablesToConstant
    unfold applyGroundingTerm'
    simp
  | variableDL v =>
    exfalso
    unfold termVariables at noVars
    simp at noVars

lemma atomGroundingEqAtomWithoutVariablesToGroundAtom (a: atom τ) (noVars: atomVariables a = ∅) (g: grounding τ): atomWithoutVariablesToGroundAtom a noVars = atomGrounding g a := by
  unfold atomWithoutVariablesToGroundAtom
  unfold atomGrounding
  rw [groundAtomEquality]
  simp
  apply List.ext_get
  rw [List.length_map, List.length_map, List.length_attach]
  intros n h1 h2
  rw [List.length_map, List.length_attach] at h1
  rw [List.get_map, List.get_map]
  simp
  apply applyGroundingTermEqtermWithoutVariablesToConstant



lemma atomGroundingIsSelfOnGroundAtom (ga: groundAtom τ) (g: grounding τ): atomGrounding g ga = ga := by
  unfold atomGrounding
  rw [groundAtomEquality]
  unfold groundAtom.toAtom
  simp
  apply List.ext_get
  rw [List.length_map]
  intros n h1 h2
  rw [List.get_map]
  simp
  unfold applyGroundingTerm'
  simp

lemma moveAtomWithoutVariablesInPartialGroundRule (i: List (groundAtom τ))(pgr: partialGroundRule τ i.toSet) (hd: atom τ) (tl: List (atom τ)) (h: pgr.ungroundedBody = hd::tl) (hdVars: atomVariables hd = ∅) (hd_i: atomWithoutVariablesToGroundAtom hd hdVars ∈ i): partialGroundRule.toRule pgr = partialGroundRule.toRule (i:= i.toSet) {head := pgr.head, groundedBody :=  pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom hd hdVars], ungroundedBody := tl, members := groundingStepGroundAtomExtendMembers i pgr (atomWithoutVariablesToGroundAtom hd hdVars) hd_i} :=
by
  unfold partialGroundRule.toRule
  simp
  rw [h]
  rw [toAtomOfatomWithoutVariablesIsSelf]

lemma moveAtomWithoutVariablesInPartialGroundRule_singleElements (i: List (groundAtom τ))(head: atom τ) (groundedBody: List (groundAtom τ)) (hd: atom τ) (tl: List (atom τ)) (ungroundedBody: List (atom τ)) (members: ∀ (ga: groundAtom τ), ga ∈ groundedBody → ga ∈ List.toSet i) (h:ungroundedBody = hd::tl) (hdVars: atomVariables hd = ∅) (hd_i: atomWithoutVariablesToGroundAtom hd hdVars ∈ i): partialGroundRule.toRule {head:= head, groundedBody:= groundedBody, ungroundedBody:= ungroundedBody, members:= members} = partialGroundRule.toRule (i:= i.toSet) {head := head, groundedBody := groundedBody ++ [atomWithoutVariablesToGroundAtom hd hdVars], ungroundedBody := tl, members := groundingStepGroundAtomExtendMembers_append i {head:= head, groundedBody:= groundedBody, ungroundedBody:= ungroundedBody, members:= members} (atomWithoutVariablesToGroundAtom hd hdVars) hd_i} :=
by
  unfold partialGroundRule.toRule
  simp
  rw [h]
  rw [toAtomOfatomWithoutVariablesIsSelf]

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

def decidableAtomVars.go (l: List (term τ)) (curr: List τ.vars): List τ.vars :=
  match l with
  | [] => curr
  | hd::tl =>
    match hd with
    | term.constant _ => decidableAtomVars.go tl curr
    | term.variableDL v => decidableAtomVars.go tl (curr.insert v)

lemma decidableAtomVarsGoSemantics (l: List (term τ)) (curr: List τ.vars) (v: τ.vars): v ∈ decidableAtomVars.go l curr ↔ v ∈ curr ∨ v ∈ collectResultsToFinset termVariables l := by
  induction l generalizing curr with
  | nil =>
    unfold collectResultsToFinset
    unfold decidableAtomVars.go
    simp
  | cons hd tl ih =>
    unfold decidableAtomVars.go
    unfold collectResultsToFinset
    rw [Set.mem_union, or_comm, or_assoc, or_comm (b:= v ∈ curr)]
    cases hd with
    | constant c =>
      rw [ih]
      unfold termVariables
      simp
    | variableDL w =>
      specialize ih (List.insert w curr)
      simp
      rw [ih]
      simp
      have h: v ∈ termVariables (term.variableDL w) ↔ v = w := by
        unfold termVariables
        simp
      rw [h]
      rw [or_assoc]


def decidableAtomVars (a: atom τ): List (τ.vars) := decidableAtomVars.go a.atom_terms []

lemma inDecidableAtomVarsIffInAtomVariables (a: atom τ) (v: τ.vars): v ∈ atomVariables a ↔ v ∈ decidableAtomVars a := by
  unfold decidableAtomVars
  rw [decidableAtomVarsGoSemantics]
  unfold atomVariables
  simp

def atomSubOfGrounding (a: atom τ) (g: grounding τ): substitution τ := fun x => if x ∈ decidableAtomVars a then some (g x) else none

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
    have v_atomVars: v ∈ decidableAtomVars a := by
      rw [← inDecidableAtomVarsIffInAtomVariables]
      unfold atomVariables
      rw [collectResultsToFinsetSemantics, Set.mem_setOf]
      use (term.variableDL v)
      constructor
      apply mem
      unfold termVariables
      simp

    have h: Option.isSome (if v ∈ decidableAtomVars a then some (g v) else none) = true := by
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

lemma atomSubOfGroundingGroundingEqGroundingOnTerm (a : atom τ)  (g: grounding τ) (t: term τ): applyGroundingTerm' g (applySubstitutionTerm (atomSubOfGrounding a g) t) = applyGroundingTerm' g t := by
  unfold applyGroundingTerm'
  unfold applySubstitutionTerm
  unfold atomSubOfGrounding
  cases t with
  | constant c =>
    simp
  | variableDL v =>
    simp
    by_cases h: Option.isSome (if v ∈ decidableAtomVars a then some (g v) else none) = true
    simp [h]
    by_cases p: v ∈ decidableAtomVars a
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

lemma variableMemberOfcollecResultsIffMemberList (l: List (term τ)) (v: τ.vars): term.variableDL v ∈ l ↔ v ∈ collectResultsToFinset termVariables l := by
  induction l with
  | nil =>
    unfold collectResultsToFinset
    simp
  | cons hd tl ih =>
    unfold collectResultsToFinset
    simp
    rw [← ih]
    unfold termVariables
    cases hd with
    | constant c =>
      simp
    | variableDL w =>
      simp


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
    have p: v ∈ decidableAtomVars a := by
      by_contra q
      simp [q] at h
    simp [p] at h
    rw [← inDecidableAtomVarsIffInAtomVariables] at p
    unfold applySubstitutionAtom at s'_a
    unfold atomGrounding at s'_a
    unfold groundAtom.toAtom at s'_a
    simp at s'_a
    have s'_v: applySubstitutionTerm s' (term.variableDL v) = (term.constant ∘ applyGroundingTerm' g) (term.variableDL v) := by
      apply equalOfListMapEqual (h:= s'_a)
      rw [variableMemberOfcollecResultsIffMemberList]
      unfold atomVariables at p
      apply p
    unfold applySubstitutionTerm at s'_v
    unfold applyGroundingTerm' at s'_v
    simp at s'_v
    cases h': (s' v) with
    | some c' =>
      simp [h'] at s'_v
      rw [h] at s'_v
      simp
      rw [inDecidableAtomVarsIffInAtomVariables] at p
      simp [p]
      rw [h]
      apply Eq.symm
      apply s'_v
    | none =>
      simp [h'] at *
  | none =>
    rw [h] at h'
    simp at h'

lemma replaceGroundingWithSubstitutionAndGrounding (a: atom τ) (r: rule τ) (mem: a ∈ r.body ): (∀ (g: grounding τ), atomGrounding g a ∈ i →  ruleTrue (ruleGrounding r g) i) ↔ ∀  (s: substitution τ), (∃ (ga: groundAtom τ), ga ∈ i ∧ applySubstitutionAtom s a = ga ∧ ∀ (s': substitution τ), applySubstitutionAtom s' a = ga → s ⊆ s') →  ∀ (g': grounding τ),ruleTrue (ruleGrounding (applySubstitutionRule s r) g') i := by
  constructor
  intros h s _ g
  rw [combineSubstitutionGroundingEquivRule]
  by_cases p: atomGrounding (combineSubstitutionGrounding s g) a ∈ i
  apply h
  apply p
  unfold ruleTrue
  unfold groundRuleBodySet
  unfold ruleGrounding
  rw [Set.subset_def]
  intro q
  specialize q (atomGrounding (combineSubstitutionGrounding s g) a)
  simp at q
  exfalso
  specialize q a mem
  simp at q
  exact absurd q p

  intros h g ground_g_a
  specialize h (atomSubOfGrounding a g)
  simp at h
  specialize h (atomGrounding g a) ground_g_a  (atomSubOfGroundingEqOnAtom a g)
  specialize h (atomSubOfGroundingIsMinimalForAtom a g) g
  rw [atomSubOfGroundingGroundingEqGroundingOnRule] at h
  apply h

lemma swapApplySubstitutionPgrToRule (i: List (groundAtom τ)) (s: substitution τ) (pgr: partialGroundRule τ i.toSet) (hd: atom τ) (tl: List (atom τ)) (varsHd: atomVariables (applySubstitutionAtom s hd) = ∅) (mem: (atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) varsHd) ∈ i) (h: pgr.ungroundedBody = hd::tl): applySubstitutionRule s (pgr.toRule) = partialGroundRule.toRule {head:= applySubstitutionAtom s pgr.head, groundedBody:= pgr.groundedBody ++ [atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) varsHd], ungroundedBody:= List.map (applySubstitutionAtom s) tl, members:= groundingStepGroundAtomExtendMembers i pgr (atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) varsHd) mem} :=
by
  unfold partialGroundRule.toRule
  unfold applySubstitutionRule
  rw [h]
  simp
  rw [toAtomOfatomWithoutVariablesIsSelf]
  have groundedBodyEq:  List.map (applySubstitutionAtom s ∘ groundAtom.toAtom) pgr.groundedBody = List.map groundAtom.toAtom pgr.groundedBody := by
    apply List.ext_get
    rw [List.length_map, List.length_map]
    intros n h1 h2
    rw [List.get_map, List.get_map]
    simp
    have p: ∀ (ga:groundAtom τ), applySubstitutionAtom s (groundAtom.toAtom ga) = groundAtom.toAtom ga := by
      intro ga
      unfold groundAtom.toAtom
      unfold applySubstitutionAtom
      simp
      apply List.ext_get
      rw [List.length_map, List.length_map]
      intros n' h1' h2'
      rw [List.get_map, List.get_map]
      simp
      have q: ∀ (c: τ.constants), applySubstitutionTerm s (term.constant c) =term.constant c := by
        intro c
        unfold applySubstitutionTerm
        simp
      rw [q]
    rw [p]
  rw [groundedBodyEq]


theorem exploreGroundingSemantics (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (safe: pgr.isSafe): exploreGrounding i pgr safe = Except.ok () ↔ pgr.isTrue := by
  unfold partialGroundRule.isTrue
  cases pgr with
  | mk head groundedBody ungroundedBody members =>
    induction' length: ungroundedBody.length with n ih generalizing head groundedBody ungroundedBody members

    unfold exploreGrounding
    simp
    cases ungroundedBody with
    | cons hd tl =>
      simp at length
    | nil =>
      simp
      unfold ruleTrue
      unfold partialGroundRule.toRule
      simp
      unfold partialGroundRule.isSafe at safe
      unfold collectResultsToFinset at safe
      rw [Set.subset_empty_iff] at safe
      simp at safe
      unfold ruleGrounding
      simp [imp_false, ← atomGroundingEqAtomWithoutVariablesToGroundAtom head safe, ← List.toSet_mem]
      constructor
      intros h' _ _
      simp [h']
      intro h'
      apply h'
      unfold groundRuleBodySet
      simp
      rw [Set.subset_def]
      intro ga body
      apply members
      have groundingBody: ∀ (g: grounding τ), List.map (atomGrounding g ∘ groundAtom.toAtom ) groundedBody = groundedBody := by
        intro g
        apply List.ext_get
        rw [List.length_map]
        intros n h1 h2
        rw [List.get_map]
        simp
        rw [atomGroundingIsSelfOnGroundAtom]
      simp [groundingBody, atomGroundingIsSelfOnGroundAtom] at body
      apply body
      use (substitutionToGrounding emptySubstitution) -- we have to use some substitution

    unfold exploreGrounding
    simp
    cases ungroundedBody with
    | nil =>
      exfalso
      simp at length
    | cons hd tl =>
      simp
      simp at length
      constructor
      intros h' g
      by_cases varsHd: atomVariablesEmpty hd = true
      simp [varsHd] at h'
      rw [atomVariablesEmptySemantics] at varsHd
      by_cases hd_i: atomWithoutVariablesToGroundAtom hd varsHd ∈ i
      specialize h' hd_i
      unfold groundingStepGroundAtom  at h'
      rw [ih] at h'
      simp at h'
      specialize h' g
      rw [moveAtomWithoutVariablesInPartialGroundRule (hd:= hd)  (tl:=tl) (hdVars:= varsHd) (hd_i:= hd_i)]
      simp
      apply h'
      simp
      apply length
      unfold ruleGrounding
      unfold ruleTrue
      unfold partialGroundRule.toRule
      simp
      unfold groundRuleBodySet
      simp

      rw [Set.subset_def]
      intro body
      specialize body (atomWithoutVariablesToGroundAtom hd varsHd)
      simp [Finset.mem_insert] at body
      have n_hd_i: atomWithoutVariablesToGroundAtom hd varsHd ∈ i := by
        rw [List.toSet_mem]
        apply body
        left
        rw [atomGroundingEqAtomWithoutVariablesToGroundAtom]
      exfalso
      exact absurd n_hd_i hd_i

      simp [varsHd] at h'
      rw [List.map_except_unitIsUnitIffAll] at h'
      by_cases g_hd: atomGrounding g hd ∈ i
      revert g
      simp [List.toSet_mem]
      rw [replaceGroundingWithSubstitutionAndGrounding (a:=hd)]
      intros s s_prop
      rw [←  inGetSubstitutionsIffMinimalSolutionAndInInterpretation] at s_prop
      specialize h' (Subtype.mk s s_prop)
      unfold groundingStep at h'
      simp at h'
      rw [inGetSubstitutionsIffMinimalSolutionAndInInterpretation] at s_prop
      simp at s_prop
      rcases s_prop with ⟨ga, ga_i, apply_s_ga, _⟩
      have varsHdS: atomVariables (applySubstitutionAtom s hd) = ∅ := by
        rw [apply_s_ga]
        apply groundAtomsHaveNoVariables

      rw [swapApplySubstitutionPgrToRule (hd:=hd) (tl:= tl) (varsHd:= varsHdS)]
      simp
      rw [← ih]
      rw [← h']

      simp [apply_s_ga, atomWithoutVariablesToGroundAtomOfGroundAtom]
      rw [List.toSet_mem]
      apply ga_i

      rw [List.length_map]
      apply length

      simp

      unfold partialGroundRule.toRule
      simp

      unfold partialGroundRule.toRule
      unfold ruleGrounding
      unfold ruleTrue
      unfold groundRuleBodySet
      rw [Set.subset_def]
      simp
      intro body
      rw [← List.toSet_mem] at body
      exfalso
      exact absurd body g_hd

      -- back direction
      intro h'
      by_cases varsHd: atomVariablesEmpty hd = true
      simp [varsHd]
      intro hd_i
      rw [ih]
      unfold groundingStepGroundAtom
      simp
      rw [atomVariablesEmptySemantics] at varsHd
      rw [← moveAtomWithoutVariablesInPartialGroundRule_singleElements (hd:= hd) (tl:=tl) (ungroundedBody:= hd::tl) (hdVars:= varsHd) (hd_i:= hd_i)]
      apply h'
      rfl

      unfold groundingStepGroundAtom
      simp
      apply length

      simp [varsHd]
      rw [List.map_except_unitIsUnitIffAll]
      intro s _
      rcases s with ⟨s,s_prop⟩
      unfold groundingStep
      simp
      rw [ih]
      intro g
      rw [← swapApplySubstitutionPgrToRule (pgr := {head:= head, groundedBody:=groundedBody, ungroundedBody:= hd::tl, members := members}) (hd:= hd) (tl:=tl) ]
      rw [combineSubstitutionGroundingEquivRule]
      apply h'

      rw [inGetSubstitutionsIffMinimalSolutionAndInInterpretation] at s_prop
      simp at s_prop
      rcases s_prop with ⟨ga, ga_i, apply_s, _⟩
      simp [apply_s]
      rw [atomWithoutVariablesToGroundAtomOfGroundAtom]
      rw [List.toSet_mem]
      apply ga_i

      simp

      rw [List.length_map]
      apply length

lemma safePreservedBetweenRuleAndPartialGroundRule (r: rule τ) (i: interpretation τ): r.isSafe ↔ (partialGroundRuleFromRule r i).isSafe := by
  unfold partialGroundRule.isSafe
  unfold rule.isSafe
  unfold partialGroundRuleFromRule
  simp

def modelChecker (i: List (groundAtom τ)) (P: List (rule τ)) (safe: ∀ (r: rule τ), r ∈ P → r.isSafe): Except String Unit :=
  have safe': ∀ (r: rule τ), r ∈ P → (partialGroundRuleFromRule r i.toSet ).isSafe := by
    intros r rP
    rw [← safePreservedBetweenRuleAndPartialGroundRule]
    apply safe r rP
  List.map_except_unit P.attach (fun ⟨x, _h⟩ => exploreGrounding i (partialGroundRuleFromRule x i.toSet ) (safe' x _h) )

theorem modelCheckerUnitIffAllRulesTrue (i: List (groundAtom τ)) (P: List (rule τ)) (safe: ∀ (r: rule τ), r ∈ P → r.isSafe): modelChecker i P safe = Except.ok () ↔ (∀ (r: groundRule τ), r ∈ groundProgram P.toFinset → ruleTrue r i.toSet) :=
by
  unfold modelChecker
  rw [List.map_except_unitIsUnitIffAll]
  simp [exploreGroundingSemantics, partialGroundRule.isTrue, groundProgram, ← partialGroundRuleToRuleInverseToFromRule]
  constructor
  intros h gr r rP g gr_r
  rw [gr_r]
  apply h r rP

  intros h r rP g
  specialize h (ruleGrounding r g)
  apply h r rP g
  rfl
