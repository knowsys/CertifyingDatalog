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


def List.map_except_unit {A B: Type} (l: List A) (f: A → Except B Unit): Except B Unit :=
  match l with
  | [] => Except.ok ()
  | hd::tl =>
    match f hd with
    | Except.ok () => List.map_except_unit tl f
    | Except.error b => Except.error b

lemma List.map_except_unitIsUnitIffAll {A B: Type} (l: List A) (f: A → Except B Unit): List.map_except_unit l f = Except.ok () ↔ ∀ (a:A), a ∈ l → f a = Except.ok () :=
by
  induction l with
  | nil =>
    simp
    unfold List.map_except_unit
    rfl
  | cons hd tl ih =>
    unfold List.map_except_unit
    simp
    cases f hd with
    | ok u =>
      simp
      rw [ih]
    | error e =>
      simp

def List.toSet {A: Type} (l: List A): Set A :=
  match l with
  | [] => ∅
  | hd::tl => {hd} ∪ tl.toSet

lemma List.toSet_mem {A: Type} (a:A) (l: List A): a ∈ l ↔ a ∈ l.toSet := by
  induction l with
  | nil =>
    unfold List.toSet
    simp
  | cons hd tl ih =>
    unfold List.toSet
    simp
    rw [ih]

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
  have matchAtomSome: Option.isSome (matchAtom emptySubstitution a ga) = true
  rw [match_ga]
  simp
  have matchSemantic:applySubstitutionAtom (Option.get (matchAtom emptySubstitution a ga) matchAtomSome) a = ga
  simp [matchAtomFindsSolution]

  simp at matchSemantic
  have matchAtom_s: Option.get (matchAtom emptySubstitution a ga) matchAtomSome= s
  simp [match_ga]
  rw [← matchAtom_s]
  rw [matchSemantic]
  apply groundAtomsHaveNoVariables

lemma inGetSubstitutionsImplInInterpretation (i: List (groundAtom τ))(a: atom τ) (s: substitution τ) (h: s ∈ getSubstitutions i a)  (noVars: atomVariables (applySubstitutionAtom s a) = ∅): atomWithoutVariablesToGroundAtom (applySubstitutionAtom s a) noVars ∈ i :=
by
  unfold getSubstitutions at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨ga, ga_i, match_ga⟩

  have matchAtomSome: Option.isSome (matchAtom emptySubstitution a ga) = true
  rw [match_ga]
  simp
  have matchSemantic:applySubstitutionAtom (Option.get (matchAtom emptySubstitution a ga) matchAtomSome) a = ga
  simp [matchAtomFindsSolution]

  simp at matchSemantic
  have matchAtom_s: Option.get (matchAtom emptySubstitution a ga) matchAtomSome= s
  simp [match_ga]

  simp [← matchAtom_s]
  simp [matchSemantic]
  rw [atomWithoutVariablesToGroundAtomOfGroundAtom]
  apply ga_i

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
  have h: ∀ (ga : groundAtom τ), ga ∈ List.concat pgr.groundedBody (atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars) → ga ∈ List.toSet i := by
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
  {head:= applySubstitutionAtom s pgr.head, groundedBody:= List.concat pgr.groundedBody (atomWithoutVariablesToGroundAtom (applySubstitutionAtom s hd) noVars) , ungroundedBody := List.map (fun x => applySubstitutionAtom s x) tl, members := h}

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
    have noVars: ∀ (s: substitution τ), s ∈ getSubstitutions i hd → atomVariables (applySubstitutionAtom s hd) = ∅ := by
      apply inGetSubstitutionsImplNoVars


    List.map_except_unit (getSubstitutions i hd).attach (fun ⟨s, _h⟩ => exploreGrounding i (groundingStep s i pgr hd tl (noVars s _h) (inGetSubstitutionsImplInInterpretation i hd s _h (noVars s _h))) (groundingStepPreservesSafety s i pgr hd tl (noVars s _h) (inGetSubstitutionsImplInInterpretation i hd s _h (noVars s _h)) safe h) )
termination_by exploreGrounding i pgr safe => pgr.ungroundedBody.length
decreasing_by
  simp_wf
  unfold groundingStep
  simp
  rw [h]
  simp


theorem exploreGroundingSemantics (i: List (groundAtom τ)) (pgr: partialGroundRule τ i.toSet ) (safe: pgr.isSafe): exploreGrounding i pgr safe = Except.ok () ↔ pgr.isTrue := sorry

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
