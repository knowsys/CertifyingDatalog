import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification

section SymbolSequenceMap
def SymbolSequenceMap (τ : Signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] :=
  Std.HashMap (List τ.relationSymbols) (List (Rule τ))

variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def SymbolSequenceMap.empty : SymbolSequenceMap τ := Std.HashMap.empty

def SymbolSequenceMap.find (m : SymbolSequenceMap τ) (l : List (τ.relationSymbols)) : List (Rule τ) := m.getD l []

end SymbolSequenceMap
namespace Rule
  def symbolSequence (r: Rule τ): List τ.relationSymbols := r.head.symbol :: (List.map Atom.symbol r.body)

  lemma symbolSequence_eq_matchingGroundRule {r: Rule τ} {gr: GroundRule τ} (match_r: ∃ (s: Substitution τ), s.applyRule r = gr): r.symbolSequence = gr.toRule.symbolSequence := by
    rcases match_r with ⟨s, apply_s⟩
    rw [← apply_s]
    unfold Substitution.applyRule
    unfold Substitution.applyAtom
    unfold symbolSequence
    simp

  lemma ne_of_symbolSequence_ne {r1 r2 : Rule τ} (h : r1.symbolSequence ≠ r2.symbolSequence) : ∀ (s : Substitution τ), s.applyRule r1 ≠ r2 := by
    intro s apply_s
    apply h
    rw [← apply_s]
    unfold symbolSequence
    simp only [List.cons.injEq]
    unfold Substitution.applyRule
    unfold Substitution.applyAtom
    simp

  lemma body_length_eq_of_symbolSequence_eq {r1 r2: Rule τ} (h: r1.symbolSequence = r2.symbolSequence): r1.body.length = r2.body.length := by
    unfold symbolSequence at h
    simp only [List.cons.injEq] at h
    rcases h with ⟨_, body⟩
    rw [← r1.body.length_map Atom.symbol, ← r2.body.length_map Atom.symbol]
    rw [body]
end Rule

namespace Program
  variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]


  def toSymbolSequenceMap_aux (init : SymbolSequenceMap τ) : Program τ -> SymbolSequenceMap τ
  | .nil => init
  | .cons rule p =>
    let new_init := init.insert rule.symbolSequence (rule :: (init.find rule.symbolSequence))
    -- let new_init := fun seq => if seq = rule.symbolSequence then rule :: (init seq) else init seq
    toSymbolSequenceMap_aux new_init p

  def toSymbolSequenceMap (p : Program τ) := p.toSymbolSequenceMap_aux SymbolSequenceMap.empty

  lemma toSymbolSequenceMap_mem {init : SymbolSequenceMap τ} {p : Program τ} : ∀ (l : List (τ.relationSymbols)) (r : Rule τ), r ∈ ((p.toSymbolSequenceMap_aux init).find l) ↔ r ∈ (init.find l) ∨ (r.symbolSequence = l ∧ r ∈ p) := by
    induction p generalizing init with
    | nil =>
      intros
      unfold toSymbolSequenceMap_aux
      simp
    | cons rule p ih =>
      intro l r
      unfold toSymbolSequenceMap_aux
      simp only [List.mem_cons]
      rw [ih]
      by_cases l_symb: l = rule.symbolSequence
      · simp only [l_symb]
        unfold SymbolSequenceMap.find
        rw [Std.HashMap.getD_insert_self]
        simp only [List.mem_cons]
        tauto
      · unfold SymbolSequenceMap.find
        rw [Std.HashMap.getD_insert]
        split
        case neg.isTrue h => simp at h; rw [h] at l_symb; contradiction
        constructor
        · intro h
          cases h with
          | inl h =>
            left
            apply h
          | inr h =>
            right
            simp [h]

        · intro h
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

  lemma toSymbolSequenceMap_semantics {p: Program τ} {r: Rule τ} : ∀ (r': Rule τ), r' ∈ (p.toSymbolSequenceMap.find r.symbolSequence) ↔ r' ∈ p ∧ r'.symbolSequence = r.symbolSequence := by
    intro r'
    unfold toSymbolSequenceMap
    rw [toSymbolSequenceMap_mem]
    simp only [SymbolSequenceMap.find, SymbolSequenceMap.empty, Std.HashMap.getD_empty,
      List.not_mem_nil, false_or]
    rw [And.comm]
end Program
variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols]
  [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]
  [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

def checkRuleMatch (m: SymbolSequenceMap τ) (gr: GroundRule τ): Except String Unit :=
  if (m.find gr.toRule.symbolSequence).any (fun rule => (Substitution.matchRule rule gr).isSome)
  then Except.ok ()
  else Except.error ("No match for " ++ ToString.toString gr)

lemma checkRuleMatchOkIffExistsRule [Inhabited τ.constants] {p: Program τ} {gr: GroundRule τ} : checkRuleMatch p.toSymbolSequenceMap gr = Except.ok () ↔ ∃ (r: Rule τ) (g: Grounding τ), r ∈ p ∧ g.applyRule' r = gr :=
by
  simp [grounding_substitution_equiv]
  unfold checkRuleMatch
  split
  · rename_i symbolSequenceMatch
    simp only [true_iff]
    simp only [List.any_eq_true] at symbolSequenceMatch
    simp_rw [Program.toSymbolSequenceMap_semantics] at symbolSequenceMatch
    rcases symbolSequenceMatch with ⟨r, h, s⟩
    use r
    simp only [h, true_and]
    use (Substitution.matchRule r gr).get s
    apply Substitution.matchRuleYieldsSubs
  · rename_i symbolSequenceMatch
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, reduceCtorEq, false_iff, ne_eq] at *
    simp_rw [Program.toSymbolSequenceMap_semantics] at symbolSequenceMatch
    intro r rP
    specialize symbolSequenceMatch r
    cases (Decidable.em (r.symbolSequence = gr.toRule.symbolSequence)) with
    | inl eq =>
      simp only [rP, eq, and_self, forall_const] at symbolSequenceMatch
      apply Substitution.matchRuleNoneThenNoSubs
      apply symbolSequenceMatch
    | inr neq =>
      apply Rule.ne_of_symbolSequence_ne
      apply neq

namespace ProofTreeSkeleton
  def checkValidity (t : ProofTreeSkeleton τ) (m : SymbolSequenceMap τ) (d : Database τ) : Except String Unit :=
    match t with
    | .node a l =>
      if l.isEmpty
      then  if d.contains a
            then Except.ok ()
            else
              match checkRuleMatch m {head:= a, body := []} with
              | Except.ok _ => Except.ok ()
              | Except.error msg => Except.error msg
      else
        match checkRuleMatch m {head:= a, body := l.map Tree.root} with
        | Except.ok _ => l.attach.mapExceptUnit (fun ⟨t, _h⟩ => checkValidity t m d)
        | Except.error msg => Except.error msg
  termination_by sizeOf t

  lemma checkValidityOkIffIsValid [Inhabited τ.constants] {t: ProofTreeSkeleton τ} {kb: KnowledgeBase τ} : t.checkValidity kb.prog.toSymbolSequenceMap kb.db = Except.ok () ↔ t.isValid kb :=
  by
    induction' h_t : t.height using Nat.strongRecOn with n ih generalizing t
    cases t with
    | node a l =>
      unfold checkValidity
      unfold isValid
      by_cases emptyL: l.isEmpty
      · rw [if_pos emptyL]
        by_cases contains_a: kb.db.contains a
        · rw [if_pos contains_a]
          constructor
          · intro _
            right
            rw [← List.isEmpty_iff]
            constructor
            · exact emptyL
            · exact contains_a
          · simp
        · rw [if_neg contains_a]
          split
          · simp only [exists_and_left, exists_and_right, true_iff]
            rename_i u checkRuleMatch
            rw [checkRuleMatchOkIffExistsRule] at checkRuleMatch
            left
            rw [List.isEmpty_iff] at emptyL
            rcases checkRuleMatch with ⟨r, g, rP, apply_g⟩
            use r
            constructor
            · apply rP
            · constructor
              · use g
                rw [emptyL]
                simp only [List.map_nil]
                exact apply_g
              · rw [emptyL]
                unfold List.Forall
                simp
          · simp only [reduceCtorEq, exists_and_left, exists_and_right, false_iff, not_or,
            not_exists, not_and, forall_exists_index, Bool.not_eq_true]
            rename_i checkRuleMatchResult
            rw [List.isEmpty_iff] at emptyL

            have checkRuleMatch': ¬ checkRuleMatch kb.prog.toSymbolSequenceMap { head := a, body := [] } = Except.ok () := by
              rw [checkRuleMatchResult]
              simp
            rw [checkRuleMatchOkIffExistsRule] at checkRuleMatch'
            simp only [exists_and_left, not_exists, not_and, ne_eq] at checkRuleMatch'
            constructor
            · rw [emptyL]
              simp only [List.map_nil, List.attach_nil, List.Forall, not_true_eq_false, imp_false,
                ne_eq]
              apply checkRuleMatch'
            · simp [contains_a]

      · simp only [emptyL, Bool.false_eq_true, ↓reduceIte, exists_and_left, exists_and_right]
        split
        · rename_i checkRuleMatchResult
          rw [checkRuleMatchOkIffExistsRule] at checkRuleMatchResult
          rcases checkRuleMatchResult with ⟨r,g,rP, rulegrounding⟩
          rw [List.mapExceptUnit_iff]
          constructor
          · intro h
            left
            use r
            constructor
            · apply rP
            · constructor
              · use g
              · rw [List.forall_iff_forall_mem]
                simp only [List.mem_attach, forall_const, Subtype.forall]
                intro t t_mem
                specialize ih t.height
                have height_t: t.height < n := by
                  rw [← h_t]
                  apply Tree.heightOfMemberIsSmaller
                  unfold Tree.member
                  simp [t_mem]
                simp only [List.mem_attach, forall_const, Subtype.forall] at h
                specialize h t t_mem
                rw [ih height_t rfl] at h
                exact h
          · intro h
            simp only [List.mem_attach, forall_const, Subtype.forall]
            intro t t_mem
            specialize ih t.height
            have height_t: t.height < n := by
              rw [← h_t]
              apply Tree.heightOfMemberIsSmaller
              simp [Tree.member, t_mem]
            rw [ih height_t rfl]
            rw [List.isEmpty_iff] at emptyL
            simp only [emptyL, false_and, or_false] at h
            rcases h with ⟨_, _, h⟩
            rcases h with ⟨_,h⟩
            rw [List.forall_iff_forall_mem] at h
            simp only [List.mem_attach, forall_const, Subtype.forall] at h
            specialize h t t_mem
            apply h

        · rw [List.isEmpty_iff] at emptyL
          simp only [reduceCtorEq, emptyL, false_and, or_false, false_iff, not_exists, not_and,
            forall_exists_index]
          rename_i checkRuleMatchResult
          have checkRuleMatch': ¬ checkRuleMatch kb.prog.toSymbolSequenceMap { head := a, body := List.map Tree.root l } = Except.ok () := by
            rw [checkRuleMatchResult]
            simp
          rw [checkRuleMatchOkIffExistsRule] at checkRuleMatch'
          simp only [exists_and_left, not_exists, not_and, ne_eq] at checkRuleMatch'
          intro r rP g ground
          specialize checkRuleMatch' r rP g
          contradiction


  def checkValidityOfList (l: List (ProofTreeSkeleton τ)) (kb : KnowledgeBase τ) : Except String Unit :=
    let m := kb.prog.toSymbolSequenceMap
    l.mapExceptUnit (fun t => t.checkValidity m kb.db)

  lemma checkValidityOfListOkIffAllValid [Inhabited τ.constants] {l: List (ProofTreeSkeleton τ)} {kb: KnowledgeBase τ} : checkValidityOfList l kb = Except.ok () ↔ ∀ t, t ∈ l -> t.isValid kb := by
    unfold checkValidityOfList
    rw [List.mapExceptUnit_iff]
    constructor
    · intro h t t_l
      rw [← checkValidityOkIffIsValid]
      apply h t t_l
    · intro h t t_l
      rw [checkValidityOkIffIsValid]
      apply h t t_l

  lemma checkValidityOfImplSubsetSemantics [Inhabited τ.constants] {l: List (ProofTreeSkeleton τ)} {kb: KnowledgeBase τ} : checkValidityOfList l kb = Except.ok () -> {ga | ∃ t, t ∈ l ∧ t.elem ga } ⊆ kb.proofTheoreticSemantics := by
    intro h
    rw [Set.subset_def]
    intro ga
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intros t t_l ga_t
    rw [checkValidityOfListOkIffAllValid] at h
    apply kb.elementsOfEveryProofTreeInSemantics ⟨t, by apply h; exact t_l⟩
    apply ga_t

  lemma checkValidityOfListOkIffAllValidIffAllValidAndSubsetSemantics [Inhabited τ.constants] (l: List (ProofTreeSkeleton τ)) (kb : KnowledgeBase τ) : checkValidityOfList l kb = Except.ok () ↔ (∀ t, t ∈ l -> t.isValid kb) ∧ {ga | ∃ t, t ∈ l ∧ t.elem ga } ⊆ kb.proofTheoreticSemantics :=
  by
    constructor
    · intro h
      constructor
      · rw [checkValidityOfListOkIffAllValid] at h
        apply h
      · apply checkValidityOfImplSubsetSemantics
        apply h
    · intro h
      rw [checkValidityOfListOkIffAllValid]
      apply h.left
end ProofTreeSkeleton
