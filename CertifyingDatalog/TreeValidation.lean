import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification
import CertifyingDatalog.Basic


variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants]

def symbolSequence (r: rule τ): List τ.relationSymbols := r.head.symbol::(List.map atom.symbol r.body)

lemma symbolSequenceNotEq (r1 r2: rule τ) (h: ¬ symbolSequence r1 = symbolSequence r2): ∀ (s: substitution τ), applySubstitutionRule s r1 ≠ r2 :=
by
  by_contra h'
  push_neg at h'
  rcases h' with ⟨s, apply_s⟩
  have symbols2: symbolSequence (applySubstitutionRule s r1) = symbolSequence r2
  rw [apply_s]
  unfold symbolSequence at symbols2
  unfold applySubstitutionRule at symbols2
  simp at symbols2
  rcases symbols2 with ⟨head, body⟩
  unfold applySubstitutionAtom at head
  simp at head
  have map_r1: List.map (atom.symbol ∘ applySubstitutionAtom s) r1.body = List.map atom.symbol r1.body
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

def checkRuleMatch (P: List (rule τ)) (gr: groundRule τ) (ruleToString: rule τ → String): Except String Unit :=
  match P with
  | List.nil => Except.error ("No match for " ++ (ruleToString gr.toRule))
  | List.cons hd tl =>
    if symbolSequence hd = symbolSequence gr.toRule
      then  if Option.isSome (matchRule hd gr)
            then Except.ok ()
            else checkRuleMatch tl gr ruleToString
    else checkRuleMatch tl gr ruleToString

lemma checkRuleMatchOkIffExistsRuleForGroundRule (P: List (rule τ)) (gr: groundRule τ) (ruleToString: rule τ → String ): checkRuleMatch P gr ruleToString = Except.ok () ↔ ∃ (r: rule τ) (g:grounding τ),r ∈ P ∧ ruleGrounding r g = gr :=
by
  simp [groundingSubstitutionEquivalence]
  induction P with
  | nil =>
    unfold checkRuleMatch
    simp
  | cons hd tl ih =>
    unfold checkRuleMatch
    by_cases symbols: symbolSequence hd = symbolSequence (groundRule.toRule gr)
    have length: List.length hd.body = List.length gr.body
    have gr_length: gr.body.length = gr.toRule.body.length
    unfold groundRule.toRule
    simp
    rw [gr_length]
    apply symbolSequenceEqImplSameLength _ _ symbols


    rw [if_pos symbols]
    by_cases ruleMatchHead: Option.isSome (matchRule hd gr) = true
    rw [if_pos ruleMatchHead]
    constructor
    intro _
    use hd
    constructor
    simp
    rw [matchRuleIsSomeIffSolution] at ruleMatchHead
    simp at ruleMatchHead
    apply ruleMatchHead
    apply length
    simp

    rw [if_neg ruleMatchHead]
    constructor
    intro h
    rw [ih] at h
    rcases h with ⟨r, r_p, r_s⟩
    use r
    simp [r_p, r_s]

    intro h
    rw [ih]
    rcases h with ⟨r, r_p, r_s⟩
    use r
    simp at r_p
    cases r_p with
    | inl r_hd =>
      rw [r_hd] at r_s
      rw [matchRuleIsSomeIffSolution] at ruleMatchHead
      exfalso
      simp at ruleMatchHead
      rcases r_s with ⟨s, r_s⟩
      specialize ruleMatchHead s
      exact absurd r_s ruleMatchHead
      apply length
    | inr r_tl =>
      constructor
      apply r_tl
      apply r_s

    rw [if_neg symbols]
    rw [ih]
    constructor
    intro h
    simp [h]

    intro h
    rcases h with ⟨r,r_P, s, r_s⟩
    simp at r_P
    cases r_P with
    | inl r_hd =>
      rw [r_hd] at r_s
      exfalso
      have h': applySubstitutionRule s hd ≠ gr.toRule
      apply symbolSequenceNotEq _ _ symbols
      exact absurd r_s h'
    | inr r_tl =>
      use r
      constructor
      apply r_tl
      use s



def treeValidator (P: List (rule τ)) (d: database τ) (t: proofTree τ) (ruleToString: rule τ → String): Except String Unit :=
  match t with
  | proofTree.node a l =>
    if l.isEmpty
    then  if d.contains a
          then Except.ok ()
          else
            match checkRuleMatch P {head:= a, body := List.map root l} ruleToString with
            | Except.ok _ => Except.ok ()
            | Except.error msg => Except.error msg
    else
      match checkRuleMatch P {head:= a, body := List.map root l} ruleToString with
      | Except.ok _ => List.map_except_unit l.attach (fun ⟨x, _h⟩ => treeValidator P d x ruleToString)
      | Except.error msg => Except.error msg
termination_by treeValidator P d t ruleToString => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp

lemma treeValidatorOkIffIsValid (P: List (rule τ)) (d: database τ) (t: proofTree τ) (ruleToString: rule τ → String): treeValidator P d t ruleToString = Except.ok () ↔ isValid (List.toFinset P) d t :=
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



    constructor
    intro h
    have h': checkRuleMatch P { head := a, body := List.map root l } ruleToString = Except.ok ()
    cases p: checkRuleMatch P { head := a, body := List.map root l } ruleToString with
    | ok u =>
      simp
    | error e =>
      simp [p] at h
    simp [h'] at h
    rw [checkRuleMatchOkIffExistsRuleForGroundRule] at h'
    left
    simp [← and_assoc, exists_and_right]
    constructor
    simp at h'
    apply h'
    rw [List.all₂_iff_forall]
    simp
    intros a' a_l
    rw [List.isEmpty_iff_eq_nil] at emptyL
    rw [emptyL] at a_l
    simp at a_l

    intro h'
    by_cases p: checkRuleMatch P { head := a, body := List.map root l } ruleToString = Except.ok ()
    simp [p]
    exfalso
    cases h' with
    | inl h' =>
      rw [checkRuleMatchOkIffExistsRuleForGroundRule] at p
      rcases h' with ⟨r,g,r_P,r_ground,_⟩
      push_neg at p
      specialize p r g
      rw [List.mem_toFinset] at r_P
      specialize p r_P
      unfold groundRuleFromAtoms at r_ground
      simp at p
      exact absurd r_ground p
    | inr h' =>
      rcases h' with ⟨_,right⟩
      exact absurd right contains_a



    rw [if_neg emptyL]
    constructor
    intro h
    cases h': checkRuleMatch P { head := a, body := List.map root l } ruleToString with
    | error e =>
      simp [h'] at h
    | ok _ =>
      simp [h'] at h
      rw [List.map_except_unitIsUnitIffAll] at h
      simp at h
      rw [checkRuleMatchOkIffExistsRuleForGroundRule] at h'
      left
      simp [← and_assoc, exists_and_right]
      constructor
      simp at h'
      apply h'
      rw [List.all₂_iff_forall]
      simp
      intros a' a_l
      specialize ih (height a')
      simp [← h_t] at ih
      have height_case: height a' < height (proofTree.node a l)
      apply heightOfMemberIsSmaller
      unfold member
      simp
      apply a_l
      specialize ih height_case a'
      simp at ih
      rw [← ih]
      apply h a' a_l

    intro h
    cases h with
    | inl h =>
      simp only [← and_assoc, exists_and_right, List.mem_toFinset] at h
      cases' h with left right
      rw [← checkRuleMatchOkIffExistsRuleForGroundRule (ruleToString:= ruleToString)] at left
      simp only [groundRuleFromAtoms] at left
      simp [left]
      rw [List.map_except_unitIsUnitIffAll]
      simp
      intros t t_l
      have height_t: (height t) < height (proofTree.node a l)
      apply heightOfMemberIsSmaller
      unfold member
      simp
      apply t_l
      specialize ih (height t)
      simp [← h_t] at ih
      specialize ih height_t t
      simp at ih
      rw [ih]
      rw [List.all₂_iff_forall] at right
      simp at right
      apply right t t_l

    | inr h =>
      rw [List.isEmpty_iff_eq_nil] at emptyL
      simp [emptyL] at h


def validateTreeList (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) (ruleToString: rule τ → String): Except String Unit :=
  List.map_except_unit l (fun t => treeValidator P d t  ruleToString)

lemma validateTreeListUnitIffAllTreesValid (P: List (rule τ)) (d: database τ) (l: List (proofTree τ))  (ruleToString: rule τ → String): validateTreeList P d l ruleToString = Except.ok () ↔  ∀ (t: proofTree τ), t ∈ l → isValid P.toFinset d t := by

  unfold validateTreeList
  rw [List.map_except_unitIsUnitIffAll]
  simp [treeValidatorOkIffIsValid]


lemma validateTreeListUnitImplSubsetSemantics (P: List (rule τ)) (d: database τ) (l: List (proofTree τ))  (ruleToString: rule τ → String) : validateTreeList P d l  ruleToString  = Except.ok () →  {ga: groundAtom τ| ∃ (t: proofTree τ), t ∈ l ∧ elementMember ga t } ⊆ proofTheoreticSemantics P.toFinset d := by
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


lemma validateTreeListUnitIffSubsetSemanticsAndAllElementsHaveValidTrees (P: List (rule τ)) (d: database τ) (l: List (proofTree τ)) (ruleToString: rule τ → String) : validateTreeList P d l  ruleToString = Except.ok () ↔ {ga: groundAtom τ| ∃ (t: proofTree τ), t ∈ l ∧ elementMember ga t } ⊆ proofTheoreticSemantics P.toFinset d ∧ ∀ (t: proofTree τ), t ∈ l → isValid P.toFinset d t :=
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
