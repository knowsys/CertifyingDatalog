import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification
import CertifyingDatalog.Basic


variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def symbolSequence (r: rule τ): List τ.relationSymbols := r.head.symbol::(List.map atom.symbol r.body)

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

def parseProgramToSymbolSequenceMap (P: List (rule τ)) (m: List τ.relationSymbols → List (rule τ)): List τ.relationSymbols → List (rule τ) :=
  match P with
  | [] => m
  | hd::tl =>
    let seq:= symbolSequence hd
    parseProgramToSymbolSequenceMap tl (fun x => if x = seq then hd::(m x) else m x)

lemma parseProgramToSymbolSequenceMap_mem (P: List (rule τ)) (m: List τ.relationSymbols → List (rule τ)): ∀ (l: List (τ.relationSymbols)) (r: rule τ), r ∈ (parseProgramToSymbolSequenceMap P m) l ↔ r ∈ m l ∨ (symbolSequence r = l ∧ r ∈ P) :=
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

lemma parseProgramToSymbolSequenceMap_semantics (P: List (rule τ)) (m: List τ.relationSymbols → List (rule τ)) (h: m = parseProgramToSymbolSequenceMap P (fun _ => [])) (r: rule τ): ∀ (r': rule τ), r' ∈ m (symbolSequence r) ↔ r' ∈ P ∧ symbolSequence r' = symbolSequence r :=
by
  intro r'
  rw [h]
  rw [parseProgramToSymbolSequenceMap_mem]
  simp
  rw [And.comm]

lemma groundRuleToRuleBodyLengthEqBodyLength (gr: groundRule τ): gr.body.length = gr.toRule.body.length :=
by
  unfold groundRule.toRule
  simp

def checkRuleMatch (m: List τ.relationSymbols → List (rule τ)) (gr: groundRule τ) (ruleToString: rule τ → String): Except String Unit :=
  if List.any (m (symbolSequence gr.toRule)) (fun x => Option.isSome (matchRule x gr)) = true
  then Except.ok ()
  else Except.error ("No match for " ++ ruleToString gr)

lemma checkRuleMatchOkIffExistsRuleForGroundRule (m: List τ.relationSymbols → List (rule τ)) (P: List (rule τ)) (gr: groundRule τ) (ruleToString: rule τ → String ) (ssm: m = parseProgramToSymbolSequenceMap P (fun _ => [])): checkRuleMatch m gr ruleToString = Except.ok () ↔ ∃ (r: rule τ) (g:grounding τ),r ∈ P ∧ ruleGrounding r g = gr :=
by
  simp [groundingSubstitutionEquivalence]
  unfold checkRuleMatch
  constructor
  intro h
  have h': (List.any (m (symbolSequence (groundRule.toRule gr))) fun x => Option.isSome (matchRule x gr)) = true
  by_contra p
  simp [p] at h
  rw [List.any_eq_true] at h'
  rcases h' with ⟨r,r_mem, match_r⟩
  use r
  rw [parseProgramToSymbolSequenceMap_semantics P m ssm] at r_mem
  constructor
  simp [r_mem]
  rw [matchRuleIsSomeIffSolution] at match_r
  simp at match_r
  apply match_r
  rw [groundRuleToRuleBodyLengthEqBodyLength]
  apply symbolSequenceEqImplSameLength
  simp [r_mem]

  intro h
  have h': List.any (m (symbolSequence (groundRule.toRule gr))) (fun x => Option.isSome (matchRule x gr)) = true
  rw [List.any_eq_true]
  rcases h with ⟨r,rP, match_r⟩
  use r
  constructor
  rw [parseProgramToSymbolSequenceMap_semantics P m ssm]
  constructor
  apply rP
  apply symbolSequenceOfMatchIsEqual r gr match_r
  rw [matchRuleIsSomeIffSolution]
  apply match_r
  rw [groundRuleToRuleBodyLengthEqBodyLength]
  apply symbolSequenceEqImplSameLength
  apply symbolSequenceOfMatchIsEqual r gr match_r
  simp [h']


def treeValidator (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (t: proofTree τ) (ruleToString: rule τ → String): Except String Unit :=
  match t with
  | tree.node a l =>
    if l.isEmpty
    then  if d.contains a
          then Except.ok ()
          else
            match checkRuleMatch m {head:= a, body := List.map root l} ruleToString with
            | Except.ok _ => Except.ok ()
            | Except.error msg => Except.error msg
    else
      match checkRuleMatch m {head:= a, body := List.map root l} ruleToString with
      | Except.ok _ => List.map_except_unit l.attach (fun ⟨x, _h⟩ => treeValidator m d x ruleToString)
      | Except.error msg => Except.error msg
termination_by treeValidator m d t ruleToString => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp

lemma treeValidatorOkIffIsValid (m: List τ.relationSymbols → List (rule τ)) (P: List (rule τ)) (d: database τ) (t: proofTree τ) (ruleToString: rule τ → String) (ssm: m = parseProgramToSymbolSequenceMap P (fun _ => [])): treeValidator m d t ruleToString = Except.ok () ↔ isValid (List.toFinset P) d t :=
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
    have h': checkRuleMatch m { head := a, body := List.map root l } ruleToString = Except.ok ()
    cases p: checkRuleMatch m { head := a, body := List.map root l } ruleToString with
    | ok u =>
      simp
    | error e =>
      simp [p] at h
    simp [h'] at h
    rw [checkRuleMatchOkIffExistsRuleForGroundRule m P _ _ ssm] at h'
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
    by_cases p: checkRuleMatch m { head := a, body := List.map root l } ruleToString = Except.ok ()
    simp [p]
    exfalso
    cases h' with
    | inl h' =>
      rw [checkRuleMatchOkIffExistsRuleForGroundRule m P _ _ ssm] at p
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
    cases h': checkRuleMatch m { head := a, body := List.map root l } ruleToString with
    | error e =>
      simp [h'] at h
    | ok _ =>
      simp [h'] at h
      rw [List.map_except_unitIsUnitIffAll] at h
      simp at h
      rw [checkRuleMatchOkIffExistsRuleForGroundRule m P _ _ ssm] at h'
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
      have height_case: height a' < height (tree.node a l)
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
      rw [← checkRuleMatchOkIffExistsRuleForGroundRule m P _ ruleToString ssm] at left
      simp only [groundRuleFromAtoms] at left
      simp [left]
      rw [List.map_except_unitIsUnitIffAll]
      simp
      intros t t_l
      have height_t: (height t) < height (tree.node a l)
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
  let m:= parseProgramToSymbolSequenceMap P (fun _ => [])
  List.map_except_unit l (fun t => treeValidator m d t  ruleToString)

lemma validateTreeListUnitIffAllTreesValid (P: List (rule τ)) (d: database τ) (l: List (proofTree τ))  (ruleToString: rule τ → String): validateTreeList P d l ruleToString = Except.ok () ↔  ∀ (t: proofTree τ), t ∈ l → isValid P.toFinset d t := by

  unfold validateTreeList
  rw [List.map_except_unitIsUnitIffAll]
  constructor
  intro h t t_l
  rw [← treeValidatorOkIffIsValid]
  apply h t t_l
  rfl

  intro h t t_l
  rw [treeValidatorOkIffIsValid]
  apply h t t_l
  rfl


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
