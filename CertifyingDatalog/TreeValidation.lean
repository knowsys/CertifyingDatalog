import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification
import CertifyingDatalog.Basic


variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.predicateSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.predicateSymbols]

def symbolSequence (r: rule τ): List τ.predicateSymbols := r.head.symbol::(List.map atom.symbol r.body)

lemma symbolSequenceOfMatchIsEqual (r: rule τ) (gr: groundRule τ) (match_r: ∃ (s: substitution τ), applySubstitutionRule s r = gr): symbolSequence r = symbolSequence gr :=
by
  simp at *
  rcases match_r with ⟨s, apply_s⟩
  rw [← apply_s]
  unfold applySubstitutionRule
  unfold applySubstitutionAtom
  unfold symbolSequence
  simp

  apply List.ext_get
  rw [List.length_map, List.length_map]

  intro n h1 h2
  rw [List.get_map, List.get_map]
  simp

lemma symbolSequenceNotEq (r1 r2: rule τ) (h: ¬ symbolSequence r1 = symbolSequence r2): ∀ (s: substitution τ), applySubstitutionRule s r1 ≠ r2 :=
by
  by_contra h'
  push_neg at h'
  rcases h' with ⟨s, apply_s⟩
  have symbols2: symbolSequence (applySubstitutionRule s r1) = symbolSequence r2 := by
    rw [apply_s]
  unfold symbolSequence at symbols2
  unfold applySubstitutionRule at symbols2
  simp at symbols2
  rcases symbols2 with ⟨head, body⟩
  unfold applySubstitutionAtom at head
  simp at head
  have map_r1: List.map (atom.symbol ∘ applySubstitutionAtom s) r1.body = List.map atom.symbol r1.body := by
    apply List.ext_get
    rw [List.comp_map, List.length_map, List.length_map, List.length_map]
    intros n h1 h2
    rw [List.get_map, List.get_map]
    unfold applySubstitutionAtom
    simp
  rw [map_r1] at body
  unfold symbolSequence at h
  simp at h
  specialize h head
  exact absurd body h


lemma symbolSequenceEqImplSameLength (r1 r2: rule τ) (h: symbolSequence r1 = symbolSequence r2): r1.body.length = r2.body.length :=
by
  unfold symbolSequence at h
  simp at h
  rcases h with ⟨_, body⟩
  rw [← List.length_map r1.body atom.symbol, ← List.length_map r2.body atom.symbol]
  rw [body]

def parseProgramToSymbolSequenceMap (P: List (rule τ)) (m: List τ.predicateSymbols → List (rule τ)): List τ.predicateSymbols → List (rule τ) :=
  match P with
  | [] => m
  | hd::tl =>
    let seq:= symbolSequence hd
    parseProgramToSymbolSequenceMap tl (fun x => if x = seq then hd::(m x) else m x)

lemma parseProgramToSymbolSequenceMap_mem (P: List (rule τ)) (m: List τ.predicateSymbols → List (rule τ)): ∀ (l: List (τ.predicateSymbols)) (r: rule τ), r ∈ (parseProgramToSymbolSequenceMap P m) l ↔ r ∈ m l ∨ (symbolSequence r = l ∧ r ∈ P) :=
by
  induction P generalizing m with
  | nil =>
    intro l r
    unfold parseProgramToSymbolSequenceMap
    simp
  | cons hd tl ih =>
    intro l r
    unfold parseProgramToSymbolSequenceMap
    simp
    rw [ih]
    by_cases l_symb: l = symbolSequence hd
    simp [l_symb]
    tauto

    simp [l_symb]
    constructor
    intro h
    cases h with
    | inl h =>
      left
      apply h
    | inr h =>
      right
      simp [h]

    intro h
    cases h with
    | inl h =>
      left
      apply h
    | inr h =>
      right
      rcases h with ⟨ss_rl, r_P⟩
      constructor
      apply ss_rl
      cases r_P with
      | inl r_hd =>
        rw [r_hd] at ss_rl
        exact absurd (Eq.symm ss_rl) l_symb
      | inr r_tl =>
        apply r_tl

lemma parseProgramToSymbolSequenceMap_semantics (P: List (rule τ)) (r: rule τ): ∀ (r': rule τ), r' ∈ parseProgramToSymbolSequenceMap P (fun _ => []) (symbolSequence r) ↔ r' ∈ P ∧ symbolSequence r' = symbolSequence r :=
by
  intro r'
  rw [parseProgramToSymbolSequenceMap_mem]
  simp
  rw [And.comm]

lemma groundRuleToRuleBodyLengthEqBodyLength (gr: groundRule τ): gr.body.length = gr.toRule.body.length :=
by
  unfold groundRule.toRule
  simp

def checkRuleMatch (m: List τ.predicateSymbols → List (rule τ)) (gr: groundRule τ): Except String Unit :=
  if List.any (m (symbolSequence gr.toRule)) (fun x => Option.isSome (matchRule x gr)) = true
  then Except.ok ()
  else Except.error ("No match for " ++ ToString.toString gr)

lemma checkRuleMatchOkIffExistsRuleForGroundRule (P: List (rule τ)) (gr: groundRule τ): checkRuleMatch (parseProgramToSymbolSequenceMap P (fun _ => [])) gr = Except.ok () ↔ ∃ (r: rule τ) (g:grounding τ),r ∈ P ∧ ruleGrounding r g = gr :=
by
  simp [groundingSubstitutionEquivalence]
  unfold checkRuleMatch
  split
  rename_i symbolSequenceMatch
  simp
  simp at symbolSequenceMatch
  simp_rw [parseProgramToSymbolSequenceMap_semantics, matchRuleIsSomeIffSolution] at symbolSequenceMatch
  rcases symbolSequenceMatch with ⟨r, h, s, applyS⟩
  use r
  simp [h]
  use s

  rename_i symbolSequenceMatch
  simp at *
  simp_rw [parseProgramToSymbolSequenceMap_semantics] at symbolSequenceMatch
  intro r rP
  specialize symbolSequenceMatch r
  by_cases ssm_r_gr: symbolSequence r = symbolSequence gr.toRule
  simp [rP, ssm_r_gr] at symbolSequenceMatch
  rw [← not_exists]
  apply matchRuleNoneImplNoSolution
  apply symbolSequenceMatch

  apply symbolSequenceNotEq
  apply ssm_r_gr




def treeValidator (m: List τ.predicateSymbols → List (rule τ)) (d: database τ) (t: proofTree τ) : Except String Unit :=
  match t with
  | tree.node a l =>
    if l.isEmpty
    then  if d.contains a
          then Except.ok ()
          else
            match checkRuleMatch m {head:= a, body := List.map root l} with
            | Except.ok _ => Except.ok ()
            | Except.error msg => Except.error msg
    else
      match checkRuleMatch m {head:= a, body := List.map root l} with
      | Except.ok _ => List.map_except_unit l.attach (fun ⟨x, _h⟩ => treeValidator m d x)
      | Except.error msg => Except.error msg
termination_by sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp
  apply Nat.zero_lt_one_add

lemma treeValidatorOkIffIsValid (P: List (rule τ)) (d: database τ) (t: proofTree τ): treeValidator (parseProgramToSymbolSequenceMap P (fun _ => [])) d t = Except.ok () ↔ isValid (List.toFinset P) d t :=
by
  induction' h_t:(height t) using Nat.strongInductionOn with n ih generalizing t
  cases t with
  | node a l =>
    unfold treeValidator
    unfold isValid
    by_cases emptyL: l.isEmpty
    rw [if_pos emptyL]
    by_cases contains_a: d.contains a
    rw [if_pos contains_a]
    constructor
    intro _
    right
    rw [← List.isEmpty_iff_eq_nil]
    simp [*]
    simp
    rw [if_neg contains_a]

    split
    simp
    rename_i u checkRuleMatch
    rw [checkRuleMatchOkIffExistsRuleForGroundRule] at checkRuleMatch
    left
    rw [List.isEmpty_iff_eq_nil] at emptyL
    rcases checkRuleMatch with ⟨r, g, rP, apply_g⟩
    use r
    constructor
    apply rP
    constructor
    use g
    rw [emptyL]
    unfold List.Forall
    simp

    simp
    rename_i checkRuleMatchResult
    rw [List.isEmpty_iff_eq_nil] at emptyL

    have checkRuleMatch': ¬ checkRuleMatch (parseProgramToSymbolSequenceMap P fun _ => []) { head := a, body := List.map root l } = Except.ok () := by
      rw [checkRuleMatchResult]
      simp
    rw [checkRuleMatchOkIffExistsRuleForGroundRule] at checkRuleMatch'
    simp at checkRuleMatch'
    constructor
    rw [emptyL]
    simp
    rw [emptyL] at checkRuleMatch'
    apply checkRuleMatch'
    simp[contains_a]

    simp[emptyL]
    split
    rename_i checkRuleMatchResult
    rw [checkRuleMatchOkIffExistsRuleForGroundRule] at checkRuleMatchResult
    rcases checkRuleMatchResult with ⟨r,g,rP, rulegrounding⟩
    rw [List.map_except_unitIsUnitIffAll]
    constructor
    intro h
    left
    use r
    constructor
    apply rP
    constructor
    use g
    rw [List.forall_iff_forall_mem]
    simp
    intro t t_mem
    specialize ih (height t)
    have height_t: height t < n := by
      rw [← h_t]
      apply heightOfMemberIsSmaller
      unfold member
      simp [t_mem]
    specialize ih height_t t
    simp at ih
    rw [← ih]
    simp at h
    specialize h t t_mem
    apply h

    --back direction
    intro h
    simp
    intro t t_mem
    specialize ih (height t)
    have height_t: height t < n := by
      rw [← h_t]
      apply heightOfMemberIsSmaller
      simp [member, t_mem]
    specialize ih height_t t
    simp at ih
    rw [ih]
    rw [List.isEmpty_iff_eq_nil] at emptyL
    simp [emptyL] at h
    rcases h with ⟨_, _, h⟩
    rcases h with ⟨_,h⟩
    rw [List.forall_iff_forall_mem] at h
    simp at h
    specialize h t t_mem
    apply h

    rw [List.isEmpty_iff_eq_nil] at emptyL
    simp [emptyL]
    rename_i checkRuleMatchResult
    have checkRuleMatch': ¬ checkRuleMatch (parseProgramToSymbolSequenceMap P fun _ => []) { head := a, body := List.map root l } = Except.ok () := by
      rw [checkRuleMatchResult]
      simp
    rw [checkRuleMatchOkIffExistsRuleForGroundRule] at checkRuleMatch'
    simp at checkRuleMatch'
    intro r rP g ground
    specialize checkRuleMatch' r rP g
    contradiction



def validateTreeList (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) : Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap P (fun _ => [])
  List.map_except_unit l (fun t => treeValidator m d t)

lemma validateTreeListUnitIffAllTreesValid (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) : validateTreeList P d l = Except.ok () ↔  ∀ (t: proofTree τ), t ∈ l → isValid P.toFinset d t := by

  unfold validateTreeList
  rw [List.map_except_unitIsUnitIffAll]
  constructor
  intro h t t_l
  rw [← treeValidatorOkIffIsValid]
  apply h t t_l

  intro h t t_l
  rw [treeValidatorOkIffIsValid]
  apply h t t_l


lemma validateTreeListUnitImplSubsetSemantics (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) : validateTreeList P d l = Except.ok () →  {ga: groundAtom τ| ∃ (t: proofTree τ), t ∈ l ∧ elementMember ga t } ⊆ proofTheoreticSemantics P.toFinset d := by
  intro h
  rw [Set.subset_def]
  intro ga
  simp
  intros t t_l ga_t
  apply allTreeElementsOfValidTreeInSemantics
  rw [validateTreeListUnitIffAllTreesValid] at h
  apply h
  apply t_l
  apply ga_t


lemma validateTreeListUnitIffSubsetSemanticsAndAllValid (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) : validateTreeList P d l = Except.ok () ↔ {ga: groundAtom τ| ∃ (t: proofTree τ), t ∈ l ∧ elementMember ga t } ⊆ proofTheoreticSemantics P.toFinset d ∧ ∀ (t: proofTree τ), t ∈ l → isValid P.toFinset d t :=
by
  constructor
  intro h
  constructor
  apply validateTreeListUnitImplSubsetSemantics
  apply h

  rw [validateTreeListUnitIffAllTreesValid] at h
  apply h

  intro h
  rcases h with ⟨_, right⟩
  rw [validateTreeListUnitIffAllTreesValid]
  apply right
