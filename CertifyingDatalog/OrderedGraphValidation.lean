import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation

abbrev OrderedProofGraph (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols] :=
  { arr : Array ((GroundAtom τ) × List ℕ) // ∀ i : Fin arr.size, ∀ j ∈ (arr.get i).snd, j < i }

variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

namespace OrderedProofGraph
  def labels (G: OrderedProofGraph τ): List (GroundAtom τ) := (Array.map Prod.fst G.val).toList

  lemma in_labels_iff_exists_index (G : OrderedProofGraph τ) (a : GroundAtom τ) : a ∈ G.labels ↔ ∃ i : Fin G.val.size, (G.val.get i).fst = a := by
    unfold labels
    rw [Array.toList_eq, ← Array.mem_def, Array.mem_iff_get]
    simp
    constructor
    intro h
    rcases h with ⟨i, h⟩
    exists ⟨i, by have isLt := i.isLt; simp at isLt; exact isLt⟩
    intro h
    rcases h with ⟨i, h⟩
    exists ⟨i, by simp⟩

  def locallyValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (i : Fin G.val.size) : Prop :=
    ((G.val.get i).snd = [] ∧ kb.db.contains (G.val.get i).fst)
    ∨ (∃ r ∈ kb.prog, ∃ (g : Grounding τ), g.applyRule' r = {
      head := (G.val.get i).fst
      body := (G.val.get i).snd.attach.map (fun n => (G.val.get ⟨n.val, by apply lt_trans; apply G.prop i n.val n.prop; exact i.isLt⟩).fst)
    })

  def isValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) : Prop :=
    ∀ i : Fin G.val.size, G.locallyValid kb i

  def checkAtIndex (G : OrderedProofGraph τ) (m : SymbolSequenceMap τ) (d : Database τ) (index : Fin G.val.size) : Except String Unit :=
    let predecessors := (G.val.get index).snd

    if predecessors.isEmpty
      then if d.contains (G.val.get index).fst then Except.ok () else checkRuleMatch m { head := (G.val.get index).fst, body := [] }
      else checkRuleMatch m {
        head := (G.val.get index).fst
        body := (G.val.get index).snd.attach.map (fun n => (G.val.get ⟨n.val, by apply lt_trans; apply G.prop index n.val n.prop; exact index.isLt⟩).fst)
      }

  lemma checkAtIndexOkIffLocallyValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (i : Fin G.val.size) :
    G.checkAtIndex kb.prog.toSymbolSequenceMap kb.db i = Except.ok () ↔ G.locallyValid kb i := by
      unfold checkAtIndex
      simp
      split
      case isTrue h =>
        split
        case isTrue h' =>
          simp
          unfold locallyValid
          apply Or.inl
          constructor; exact h; exact h'
        case isFalse h' =>
          rw [checkRuleMatchOkIffExistsRule]
          unfold locallyValid
          simp [h]
          rw [← List.attach_eq_nil] at h
          rw [h]
          simp
          intro contra
          contradiction
      case isFalse h =>
        rw [checkRuleMatchOkIffExistsRule]
        unfold locallyValid
        simp
        intro contra
        contradiction

  def checkValidityStep (G : OrderedProofGraph τ) (m : SymbolSequenceMap τ) (d : Database τ) (n : Nat) : Except String Unit :=
    if h : n < G.val.size
    then match G.checkAtIndex m d ⟨n, h⟩ with
      | .error err => Except.error err
      | .ok () => G.checkValidityStep m d (n+1)
    else Except.ok ()

  lemma checkValidityStep_semantics (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (n : Nat) :
    G.checkValidityStep kb.prog.toSymbolSequenceMap kb.db n = Except.ok () ↔ ∀ i : Fin G.val.size, n ≤ i.val -> G.locallyValid kb i := by
    unfold checkValidityStep
    split
    case isFalse h =>
      simp
      intro i n_leq_i
      have : n < G.val.size := by apply Nat.lt_of_le_of_lt; exact n_leq_i; exact i.isLt
      contradiction
    case isTrue h =>
      split
      case h_1 heq =>
        simp
        exists ⟨n, h⟩
        constructor
        · simp
        rw [← checkAtIndexOkIffLocallyValid]
        rw [heq]
        simp
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
            apply (G.checkValidityStep_semantics kb (n+1)).mp
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

  def toProofTreeSkeleton (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) (root : Fin G.val.size) : ProofTreeSkeleton τ :=
    let current := G.val.get root
    let next_trees := current.snd.attach.map (fun i =>
      let j : Fin G.val.size := ⟨i.val, by apply lt_trans; apply G.prop root i.val i.prop; exact root.isLt⟩
      have _termination : j.val < root.val := by apply G.prop root j i.prop
      G.toProofTreeSkeleton kb valid j)
    Tree.node current.fst next_trees
  termination_by root

  lemma toProofTreeSkeleton_isValid (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) (root : Fin G.val.size) : (G.toProofTreeSkeleton kb valid root).isValid kb := by
    unfold toProofTreeSkeleton
    unfold ProofTreeSkeleton.isValid
    unfold isValid at valid
    unfold locallyValid at valid
    cases valid root with
    | inl h =>
      apply Or.inr
      simp
      exact h
    | inr h =>
      apply Or.inl
      rcases h with ⟨r, r_mem, g, r_apply⟩
      exists r
      exists g
      constructor
      · exact r_mem
      constructor
      · rw [r_apply]
        simp
        intro a _
        simp [Tree.root]
        unfold toProofTreeSkeleton
        simp
      · rw [List.forall_iff_forall_mem]
        simp
        intro t j j_mem next_tree
        rw [← next_tree]
        have _termination : j < root.val := by apply G.prop root j j_mem
        apply toProofTreeSkeleton_isValid
  termination_by root

  def toProofTree (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) (root : Fin G.val.size) : ProofTree kb :=
    ⟨G.toProofTreeSkeleton kb valid root, G.toProofTreeSkeleton_isValid kb valid root⟩

  theorem verticesValidOrderedProofGraphAreInProofTheoreticSemantics (G : OrderedProofGraph τ) (kb : KnowledgeBase τ) (valid : G.isValid kb) : G.labels.toSet ⊆ kb.proofTheoreticSemantics := by
    unfold KnowledgeBase.proofTheoreticSemantics
    unfold List.toSet
    simp
    intro a a_mem
    rw [in_labels_iff_exists_index] at a_mem
    rcases a_mem with ⟨i, h⟩
    exists G.toProofTree kb valid i
    unfold toProofTree
    unfold toProofTreeSkeleton
    unfold ProofTree.root
    unfold Tree.root
    simp
    exact h
end OrderedProofGraph

