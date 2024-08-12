import CertifyingDatalog.TreeValidation
import CertifyingDatalog.GraphValidation.Basic
import CertifyingDatalog.GraphValidation.Walks
import CertifyingDatalog.GraphValidation.Dfs

variable {A: Type u} [DecidableEq A] [Hashable A]

namespace Graph
  def toTree_of_acyclic (G : Graph A) (root : {a : A // a ∈ G.vertices}) (acyclic : G.isAcyclic) : Tree A := 
    Tree.node root ((G.predecessors root).attach.map (fun ⟨node, node_mem⟩ => 
      have _termination : (G.verticesThatReach node).card < (G.verticesThatReach root).card := by 
        apply Finset.card_lt_card
        apply verticesThatReachPredStrictSubsetReachSelfIfAcyclic
        apply acyclic
        apply node_mem
      G.toTree_of_acyclic ⟨node, by apply mem_of_is_pred; apply node_mem⟩ acyclic))
  termination_by Finset.card (G.verticesThatReach root)

  lemma toTree_root_is_root (G : Graph A) (root : {a : A // a ∈ G.vertices}) (acyclic : G.isAcyclic) : (G.toTree_of_acyclic root acyclic).root = root := by 
    unfold toTree_of_acyclic
    unfold Tree.root
    simp

  variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

  def locallyValid_for_kb (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) (node : GroundAtom τ) : Prop := 
    (∃ r ∈ kb.prog, ∃ (g : Grounding τ), g.applyRule' r = { head := node, body := G.predecessors node }) ∨ (G.predecessors node = [] ∧ kb.db.contains node)

  def check_local_validity (G : Graph (GroundAtom τ)) (m : SymbolSequenceMap τ) (d : Database τ) (node : GroundAtom τ) : Except String Unit :=
    let preds := G.predecessors node
    if preds.isEmpty 
      then if d.contains node then Except.ok () else checkRuleMatch m ⟨node, preds⟩ 
      else checkRuleMatch m ⟨node, preds⟩

  lemma check_local_validity_unit_iff_locallyValid (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) (node : GroundAtom τ) :
    G.check_local_validity kb.prog.toSymbolSequenceMap kb.db node = Except.ok () ↔ G.locallyValid_for_kb kb node := by 
      have : checkRuleMatch kb.prog.toSymbolSequenceMap ⟨node, G.predecessors node⟩ = Except.ok () ↔ (∃ r ∈ kb.prog, ∃ (g : Grounding τ), g.applyRule' r = { head := node, body := G.predecessors node }) := by 
        rw [checkRuleMatchOkIffExistsRule]
        simp

      unfold check_local_validity
      simp
      split
      case isTrue h =>
        split
        case isTrue h' =>
          simp
          unfold locallyValid_for_kb
          apply Or.inr
          constructor; rw [List.isEmpty_iff_eq_nil] at h; exact h; exact h'
        case isFalse h' =>
          unfold locallyValid_for_kb
          rw [this]
          simp
          intro _ conra
          contradiction
      case isFalse h =>
        rw [List.isEmpty_iff_eq_nil] at h
        unfold locallyValid_for_kb
        rw [this]
        simp
        intro contra 
        contradiction

  lemma toTree_of_acyclic_isValid (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) (root : { a : GroundAtom τ // a ∈ G.vertices }) (acyclic : G.isAcyclic) (all_valid : ∀ a ∈ G.vertices, G.locallyValid_for_kb kb a) : ProofTreeSkeleton.isValid (G.toTree_of_acyclic root acyclic) kb := by 
    unfold ProofTreeSkeleton.isValid
    unfold toTree_of_acyclic
    simp
    unfold locallyValid_for_kb at all_valid
    cases all_valid root.val root.prop with 
    | inr h => apply Or.inr; exact h
    | inl h => 
      apply Or.inl
      rcases h with ⟨r, r_mem, g, r_eq⟩
      exists r
      constructor
      · exact r_mem
      constructor
      · exists g; rw [r_eq]; simp; apply List.ext_get; rw [List.length_map, List.length_attach]; intro n _ _; simp; rw [toTree_root_is_root]
      rw [List.forall_iff_forall_mem]
      simp
      intro tree node node_is_pred tree_comes_from_node
      rw [← tree_comes_from_node]
      have _termination : (G.verticesThatReach node).card < (G.verticesThatReach root).card := by 
        apply Finset.card_lt_card
        apply verticesThatReachPredStrictSubsetReachSelfIfAcyclic
        apply acyclic
        apply node_is_pred
      apply toTree_of_acyclic_isValid
      exact all_valid
  termination_by Finset.card (G.verticesThatReach root)

  def toProofTree (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) (root : { a : GroundAtom τ // a ∈ G.vertices }) (acyclic : G.isAcyclic) (all_valid : ∀ a ∈ G.vertices, G.locallyValid_for_kb kb a) : ProofTree kb := ⟨G.toTree_of_acyclic root acyclic, toTree_of_acyclic_isValid G kb root acyclic all_valid⟩  

  theorem verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) (acyclic : G.isAcyclic) (all_valid : ∀ a ∈ G.vertices, G.locallyValid_for_kb kb a) : G.vertices.toSet ⊆ kb.proofTheoreticSemantics := by
    unfold KnowledgeBase.proofTheoreticSemantics
    rw [Set.subset_def]
    intro node node_mem
    unfold List.toSet at node_mem 
    simp at node_mem
    simp
    exists G.toProofTree kb ⟨node, node_mem⟩ acyclic all_valid
    unfold toProofTree
    unfold ProofTree.root
    simp
    rw [toTree_root_is_root]

  def checkValidity (G : Graph (GroundAtom τ)) (m : SymbolSequenceMap τ) (d : Database τ) : Except String Unit := 
    G.verify_acyclicity_and_cond_via_dfs (fun node => G.check_local_validity m d node)

  theorem checkValidityIsOkIffAcyclicAndAllValid (G : Graph (GroundAtom τ)) (kb : KnowledgeBase τ) :
    G.checkValidity kb.prog.toSymbolSequenceMap kb.db = Except.ok () ↔ G.isAcyclic ∧ ∀ a ∈ G.vertices, G.locallyValid_for_kb kb a := by 
    unfold checkValidity
    rw [dfs_semantics]
    unfold NodeCondition.true
    simp
    intro _
    constructor
    · intro h a a_mem
      rw [← check_local_validity_unit_iff_locallyValid]
      apply h
      exact a_mem
    · intro h a a_mem
      rw [check_local_validity_unit_iff_locallyValid]
      apply h
      exact a_mem
end Graph
