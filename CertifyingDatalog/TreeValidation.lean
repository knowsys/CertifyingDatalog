module

public import CertifyingDatalog.Unification
public import CertifyingDatalog.Datalog.Semantics
public import CertifyingDatalog.Datastructures.Except
import Std.Data.HashMap.Lemmas

@[expose] public section

section SymbolSequenceMap
def SymbolSequenceMap (τ : Signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] :=
  Std.HashMap (List τ.relationSymbols) (List (Rule τ))

variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def SymbolSequenceMap.empty : SymbolSequenceMap τ := Std.HashMap.emptyWithCapacity

def SymbolSequenceMap.find (m : SymbolSequenceMap τ) (l : List (τ.relationSymbols)) : List (Rule τ) := m.getD l []

end SymbolSequenceMap
namespace Rule
  def symbolSequence (r: Rule τ): List τ.relationSymbols := r.head.symbol :: (List.map Atom.symbol r.body)

  lemma symbolSequence_eq_matchingGroundRule {r: Rule τ} {gr: GroundRule τ} (match_r: ∃ (s: Substitution τ), s.applyRule r = gr): r.symbolSequence = gr.toRule.symbolSequence := by
    simp only [eq_GroundRule_iff, Substitution.applyRule_head, Atom.eq_GroundAtom_iff,
      Substitution.applyAtom_symbol, Substitution.applyAtom_terms, List.length_map,
      List.getElem_map, Substitution.applyRule_body] at match_r
    rcases match_r with ⟨s, symb_eq, h₁, h₂⟩
    simp only [symbolSequence, GroundRule.toRule_head, GroundAtom.toAtom_symbol,
      GroundRule.toRule_body, List.map_map, List.cons.injEq]
    refine And.intro (Eq.symm symb_eq.1) ?_
    apply List.ext_get
    · simp [h₁]
    · intro n hn₁ hn₂
      simp only [List.length_map] at hn₁
      specialize h₂ n hn₁
      simp [h₂.1]

  lemma ne_of_symbolSequence_ne {r1 r2 : Rule τ} (h : r1.symbolSequence ≠ r2.symbolSequence) : ∀ (s : Substitution τ), s.applyRule r1 ≠ r2 := by
    simp only [symbolSequence, ne_eq, List.cons.injEq, not_and] at h
    simp only [ne_eq, Rule.ext_iff, Substitution.applyRule_head, Substitution.applyRule_body,
      not_and]
    intro s head_eq body_eq
    have head_eq := congrArg Atom.symbol head_eq
    simp only [Substitution.applyAtom_symbol] at head_eq
    apply h head_eq
    simp [List.ext_get_iff, ← body_eq] at ⊢ h

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
      rw [ih l r (init := (Std.HashMap.insert init rule.symbolSequence (rule :: init.find rule.symbolSequence)))]
      by_cases l_symb: l = rule.symbolSequence
      · simp only [l_symb]
        unfold SymbolSequenceMap.find
        rw [Std.HashMap.getD_insert_self (m :=init)]
        simp only [List.mem_cons]
        tauto
      · unfold SymbolSequenceMap.find
        rw [Std.HashMap.getD_insert (m := init)]
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
    simp only [SymbolSequenceMap.find, SymbolSequenceMap.empty, Std.HashMap.getD_emptyWithCapacity,
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
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true,
      reduceCtorEq, false_iff, ne_eq] at *
    simp_rw [Program.toSymbolSequenceMap_semantics] at symbolSequenceMatch
    intro r rP
    specialize symbolSequenceMatch r
    cases (Decidable.em (r.symbolSequence = gr.toRule.symbolSequence)) with
    | inl eq =>
      simp only [rP, eq, and_self, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
        forall_const] at symbolSequenceMatch
      apply Substitution.matchRuleNoneThenNoSubs
      apply symbolSequenceMatch
    | inr neq =>
      apply Rule.ne_of_symbolSequence_ne
      apply neq

namespace ProofTreeSkeleton
  def checkValidity (t : ProofTreeSkeleton τ) (m : SymbolSequenceMap τ) (d : Database τ) : Except String Unit :=
    match t with
    | .node a l =>
      if l = []
      then  if d.contains a
            then Except.ok ()
            else
              (checkRuleMatch m {head:= a, body := []}).map (fun _ => ())
      else
        (checkRuleMatch m {head:= a, body := l.map Tree.root}).bind (fun _ => (l.attach.mapExceptUnit (fun ⟨t, _h⟩ => checkValidity t m d)))

  lemma checkValidityOkIffIsValid [Inhabited τ.constants] {t: ProofTreeSkeleton τ} {kb: KnowledgeBase τ} : t.checkValidity kb.prog.toSymbolSequenceMap kb.db = Except.ok () ↔ t.isValid kb :=
  by
    induction h_t : t.height using Nat.strongRecOn generalizing t with
    | ind n ih =>
      cases t with
      | node a l =>
        unfold checkValidity
        rw [isValid_iff]
        by_cases emptyL: l = []
        · rw [ite_eq_left emptyL]
          by_cases contains_a: kb.db.contains a
          · simp [emptyL, contains_a]
          · simp [contains_a, Except.map_ok_unit, Except.is_ok_unit, checkRuleMatchOkIffExistsRule, emptyL, GroundRule.ext_iff]
        · simp only [emptyL, ↓reduceIte, Except.bind, Grounding.applyRule'_head, Tree.root_def,
          Grounding.applyRule'_body, Tree.children_def, Tree.directSubtrees_def, false_and,
          or_false]
          split
          · simp only [reduceCtorEq, false_iff, not_exists, not_and, not_forall]
            rename_i checkRuleMatchResult
            have checkRuleMatch': ¬ checkRuleMatch kb.prog.toSymbolSequenceMap { head := a, body := List.map Tree.root l } = Except.ok () := by
              rw [checkRuleMatchResult]
              simp
            rw [checkRuleMatchOkIffExistsRule] at checkRuleMatch'
            simp [exists_and_left, not_exists, not_and, ne_eq, GroundRule.ext_iff] at checkRuleMatch'
            grind
          · rename_i e u h
            rw [checkRuleMatchOkIffExistsRule] at h
            simp [GroundRule.ext_iff] at h
            simp [List.mapExceptUnit_iff]
            have height : ∀ (t: Tree (GroundAtom τ)), t ∈ l → t.height < n := by
              simp only [← h_t]
              intro t ht
              apply Tree.heightOfMemberIsSmaller
              simp [ht]
            grind

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
    simp only [checkValidityOfListOkIffAllValid, ge_iff_le, Set.subset_def, Set.mem_ofPred_eq,
      forall_exists_index, and_imp]
    intro h ga t t_l ga_t
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
