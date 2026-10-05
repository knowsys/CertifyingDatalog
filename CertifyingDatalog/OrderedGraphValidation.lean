module

public import CertifyingDatalog.TreeValidation
import CertifyingDatalog.Datastructures.Array

@[expose] public section

abbrev OrderedProofGraph (τ: Signature) :=
  { arr : Array ((GroundAtom τ) × List ℕ) // ∀ i : Fin arr.size, ∀ j ∈ arr[i].snd, j < i }

variable {τ: Signature}
namespace OrderedProofGraph
  def labels (G: OrderedProofGraph τ): List (GroundAtom τ) := (Array.map Prod.fst G.val).toList

  lemma in_labels_iff_exists_index {G : OrderedProofGraph τ} {a : GroundAtom τ} : a ∈ G.labels ↔ ∃ i : Fin G.val.size, G.val[i].fst = a := by
    unfold labels
    rw [← Array.mem_def, Array.mem_iff_get]
    simp
    constructor
    intro h
    rcases h with ⟨i, h⟩
    exists ⟨i, by have isLt := i.isLt; simp at isLt; exact isLt⟩
    intro h
    rcases h with ⟨i, h⟩
    exists ⟨i, by simp⟩

  def locallyValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ)
    (i : Fin G.val.size) : Prop :=
    (G.val[i].snd = [] ∧ kb.db.contains G.val[i].fst)
    ∨ (∃ r ∈ kb.prog, ∃ (g : Grounding τ), g.applyRule' r = {
      head := G.val[i].fst
      body := G.val[i].snd.attach.map (fun n => (G.val[n.val]' (by apply lt_trans; apply G.prop i n.val n.prop; exact i.isLt)).fst)
    })

  def isValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) : Prop :=
    ∀ i : Fin G.val.size, G.locallyValid kb i

  section checkValidity

  variable [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [Hashable τ.vars] [Hashable τ.constants] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols] [Inhabited τ.constants]

  def checkAtIndex (G : OrderedProofGraph τ) (m : SymbolSequenceMap τ) (d : Database τ) (index : Fin G.val.size) : Except String Unit :=
    let predecessors := G.val[index].snd

    if predecessors.isEmpty
      then if d.contains G.val[index].fst then Except.ok () else checkRuleMatch m { head := G.val[index].fst, body := [] }
      else checkRuleMatch m {
        head := G.val[index].fst
        body := G.val[index].snd.attach.map (fun n => (G.val[n.val]'(by apply lt_trans; apply G.prop index n.val n.prop; exact index.isLt)).fst)
      }

  lemma checkAtIndexOkIffLocallyValid {G : OrderedProofGraph τ} {kb : KnowledgeBase τ} {i : Fin G.val.size} :
    G.checkAtIndex kb.prog.toSymbolSequenceMap kb.db i = Except.ok () ↔ G.locallyValid kb i := by
      unfold checkAtIndex
      simp only [Fin.getElem_fin, List.isEmpty_iff]
      split
      case isTrue h =>
        split
        case isTrue h' =>
          simp only [true_iff]
          unfold locallyValid
          apply Or.inl
          constructor; exact h; exact h'
        case isFalse h' =>
          rw [checkRuleMatchOkIffExistsRule]
          unfold locallyValid
          simp [h]
          rw [← List.attach_eq_nil_iff] at h
          rw [h]
          simp only [List.map_nil, iff_or_self]
          intro contra
          contradiction
      case isFalse h =>
        rw [checkRuleMatchOkIffExistsRule]
        unfold locallyValid
        simp only [exists_and_left, Fin.getElem_fin,
          iff_or_self, and_imp]
        intro contra
        contradiction

  def checkValidityStep (G : OrderedProofGraph τ) (m : SymbolSequenceMap τ) (d : Database τ) (n : Nat) : Except String Unit :=
    if h : n < G.val.size
    then match G.checkAtIndex m d ⟨n, h⟩ with
      | .error err => Except.error err
      | .ok () => G.checkValidityStep m d (n+1)
    else Except.ok ()

  lemma checkValidityStep_semantics {G : OrderedProofGraph τ} {kb : KnowledgeBase τ} {n : Nat} :
    G.checkValidityStep kb.prog.toSymbolSequenceMap kb.db n = Except.ok () ↔ ∀ i : Fin G.val.size, n ≤ i.val -> G.locallyValid kb i := by
    unfold checkValidityStep
    split
    case isFalse h =>
      simp only [Fin.getElem_fin, true_iff]
      intro i n_leq_i
      have : n < G.val.size := by apply Nat.lt_of_le_of_lt; exact n_leq_i; exact i.isLt
      contradiction
    case isTrue h =>
      split
      case h_1 heq =>
        simp only [reduceCtorEq, Fin.getElem_fin, false_iff, not_forall]
        exists ⟨n, h⟩
        constructor
        · rw [← checkAtIndexOkIffLocallyValid]
          rw [heq]
          simp
        · simp
      case h_2 heq =>
        constructor
        · intro next_ok i n_leq_i
          cases eq : i.val - n with
          | zero =>
            rw [← checkAtIndexOkIffLocallyValid]
            have : ⟨n, h⟩ = i := by rw [Nat.sub_eq_iff_eq_add n_leq_i] at eq; simp at eq; simp [← eq]
            rw [this] at heq
            rw [heq]
          | succ j =>
            apply (@G.checkValidityStep_semantics kb (n+1)).mp
            exact next_ok
            rw [Nat.sub_eq_iff_eq_add n_leq_i] at eq
            rw [eq]
            rw [Nat.add_comm]
            simp
        intro h
        rw [checkValidityStep_semantics]
        intro i succ_leq_i
        apply h
        apply Nat.le_of_succ_le
        exact succ_leq_i

  def checkValidity (G : OrderedProofGraph τ) (m : SymbolSequenceMap τ) (d : Database τ) : Except String Unit :=
    G.checkValidityStep m d 0

  theorem checkValidity_semantics (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) : G.checkValidity kb.prog.toSymbolSequenceMap kb.db = Except.ok () ↔ G.isValid kb := by
    unfold checkValidity
    rw [checkValidityStep_semantics]
    unfold isValid
    simp

  end checkValidity

  def toProofTreeSkeleton {G : OrderedProofGraph τ} {kb : KnowledgeBase τ} (valid : G.isValid kb) (root : Fin G.val.size) : ProofTreeSkeleton τ :=
    let current := G.val[root]
    let next_trees := current.snd.attach.map (fun i =>
      let j : Fin G.val.size := ⟨i.val, by apply lt_trans; apply G.prop root i.val i.prop; exact root.isLt⟩
      have _termination : j.val < root.val := by apply G.prop root j i.prop
      G.toProofTreeSkeleton valid j)
    Tree.node current.fst next_trees
  termination_by root

  @[simp]
  lemma root_toProfTreeSkeleton {G : OrderedProofGraph τ} {kb : KnowledgeBase τ} (valid : G.isValid kb) (root : Fin G.val.size) :
      Tree.root (toProofTreeSkeleton valid root) = G.val[root].1 := by
    unfold toProofTreeSkeleton
    simp

  @[simp]
  lemma root_toProfTreeSkeleton' {G : OrderedProofGraph τ} {kb : KnowledgeBase τ} (valid : G.isValid kb) (root : ℕ) (h : root < G.val.size) :
      Tree.root (toProofTreeSkeleton valid ⟨root, h⟩) = G.val[root].1 := by
    unfold toProofTreeSkeleton
    simp

  lemma toProofTreeSkeleton_isValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) (root : Fin G.val.size) : (G.toProofTreeSkeleton valid root).isValid kb := by
    rw [ProofTreeSkeleton.isValid_iff]
    unfold toProofTreeSkeleton
    unfold isValid at valid
    unfold locallyValid at valid
    simp only [Grounding.applyRule'_head, Fin.getElem_fin, Tree.root_def, Grounding.applyRule'_body,
      Tree.children_def, List.map_map, Tree.directSubtrees_def, List.mem_map, List.mem_attach,
      true_and, Subtype.exists, forall_exists_index, List.map_eq_nil_iff, List.attach_eq_nil_iff]
    simp only [Fin.getElem_fin] at valid
    cases valid root with
    | inl h =>
      right
      apply h
    | inr h =>
      left
      rcases h with ⟨r, r_mem, g, r_apply⟩
      exists r
      apply And.intro r_mem
      exists g
      rw [GroundRule.ext_iff] at r_apply
      simp only [Grounding.applyRule'_head, Grounding.applyRule'_body] at r_apply
      simp only [r_apply, List.map_inj_left, List.mem_attach, Function.comp_apply, forall_const,
        Subtype.forall, true_and]
      constructor
      · intro a h'
        rw [root_toProfTreeSkeleton' valid]
      · intro t' n hn h
        rw [← h]
        apply toProofTreeSkeleton_isValid
  termination_by root
  decreasing_by
    simp only [Fin.getElem_fin, Fin.sizeOf, Nat.add_lt_add_iff_right]
    apply G.2 _ _ hn

  def toProofTree (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) (root : Fin G.val.size) : ProofTree kb :=
    ⟨G.toProofTreeSkeleton valid root, G.toProofTreeSkeleton_isValid kb valid root⟩

  theorem verticesValidOrderedProofGraphAreInProofTheoreticSemantics [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) : G.labels.toSet ⊆ kb.proofTheoreticSemantics := by
    simp only [ge_iff_le, Set.subset_def, List.toSet_mem,
      KnowledgeBase.mem_proofTheoreticSemantics_iff, ProofTree.root_def]
    intro a a_mem
    rw [in_labels_iff_exists_index] at a_mem
    rcases a_mem with ⟨i, h⟩
    exists G.toProofTree kb valid i
    simp [toProofTree, ← h]
end OrderedProofGraph
