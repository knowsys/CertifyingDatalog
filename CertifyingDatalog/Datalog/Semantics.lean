import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog.Basic
import CertifyingDatalog.Datalog.Grounding
import CertifyingDatalog.Datalog.Substitution
import CertifyingDatalog.Datalog.Database

structure KnowledgeBase (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] where
  prog : Program τ
  db : Database τ

abbrev Interpretation (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]
:= Set (GroundAtom τ)

abbrev ProofTreeSkeleton (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]
:= Tree (GroundAtom τ)

variable {τ : Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

namespace Interpretation
  def satisfiesRule (i: Interpretation τ) (r: GroundRule τ) : Prop := r.bodySet.toSet ⊆ i → r.head ∈ i

  def models (i: Interpretation τ) (kb: KnowledgeBase τ) : Prop := (∀ (r: GroundRule τ), r ∈ kb.prog.groundProgram → i.satisfiesRule r) ∧ ∀ (a: GroundAtom τ), kb.db.contains a → a ∈ i
end Interpretation

def ProofTreeSkeleton.isValid (t: ProofTreeSkeleton τ) (kb : KnowledgeBase τ): Prop :=
  match t with
  | .node a l => (∃ (r: Rule τ) (g: Grounding τ), r ∈ kb.prog ∧ g.applyRule' r = {head:= a, body:= l.map Tree.root} ∧ l.attach.Forall (fun ⟨st, _h⟩ => isValid st kb)) ∨ (l = [] ∧ kb.db.contains a)
termination_by sizeOf t

structure ProofTree (kb : KnowledgeBase τ) where
  tree : ProofTreeSkeleton τ
  isValid : tree.isValid kb

namespace ProofTree
  def root {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.root
  def elem {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.elem
  def height {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.height

  def node {kb : KnowledgeBase τ} (a : GroundAtom τ) (l : List (ProofTree kb))
    (a_valid : (∃ (r: Rule τ) (g: Grounding τ), r ∈ kb.prog ∧ g.applyRule' r = {head:= a, body := l.map root}) ∨ (l = [] ∧ kb.db.contains a)) : ProofTree kb :=
    {
      tree := Tree.node a (l.map ProofTree.tree)
      isValid := by
        unfold ProofTreeSkeleton.isValid
        cases a_valid with
        | inl a_valid =>
          apply Or.inl
          rcases a_valid with ⟨r,g,r_in_prog,r_g_apply⟩
          use r
          use g
          constructor
          · exact r_in_prog
          constructor
          · unfold ProofTree.root at r_g_apply
            rw [List.map_map]
            apply r_g_apply
          · rw [List.forall_iff_forall_mem]
            simp
            intro st _
            exact st.isValid
        | inr a_valid =>
          apply Or.inr
          rw [a_valid.left]
          simp
          exact a_valid.right
    }
end ProofTree

namespace KnowledgeBase
  def proofTheoreticSemantics (kb : KnowledgeBase τ) : Interpretation τ := {a: GroundAtom τ | ∃ (t: ProofTree kb), t.root = a}

  lemma elementsOfEveryProofTreeInSemantics (kb : KnowledgeBase τ) : ∀ (t : ProofTree kb) (ga : GroundAtom τ), t.elem ga -> ga ∈ kb.proofTheoreticSemantics := by
    intro t ga mem
    unfold proofTheoreticSemantics
    simp
    induction' h': t.height using Nat.strongRecOn with n ih generalizing t
    cases eq : t.tree with
    | node a' l =>
      unfold ProofTree.elem at mem
      unfold Tree.elem at mem
      simp [eq] at mem
      cases mem with
      | inl mem =>
        use t
        unfold ProofTree.root
        unfold Tree.root
        simp [eq]
        apply Eq.symm
        exact mem
      | inr mem =>
        rcases mem with ⟨t', t'_t, a_t'⟩
        specialize ih t'.height
        have height_t': t'.height < n := by
          rw [← h']
          apply Tree.heightOfMemberIsSmaller
          unfold Tree.member
          simp [eq]
          apply t'_t
        have valid_t': ProofTreeSkeleton.isValid t' kb := by
          have valid := t.isValid
          unfold ProofTreeSkeleton.isValid at valid
          simp [eq] at valid
          cases valid with
          | inl valid =>
            rcases valid with ⟨_,_,_,all⟩
            rw [List.forall_iff_forall_mem] at all
            simp at all
            apply all
            apply t'_t
          | inr valid =>
            exfalso
            rcases valid with ⟨left,_⟩
            rw [left] at t'_t
            simp at t'_t
        specialize ih height_t' ⟨t', valid_t'⟩
        apply ih
        apply a_t'
        rfl

  lemma proofTreeForRule (kb: KnowledgeBase τ) (r: GroundRule τ) (rGP: r ∈ kb.prog.groundProgram) (subs: r.bodySet.toSet ⊆ kb.proofTheoreticSemantics) : ∃ t : ProofTree kb, t.root = r.head := by
    have h: r.body.toFinset.toSet ⊆ kb.proofTheoreticSemantics -> ∃ (l: List (ProofTree kb)), List.map ProofTree.root l = r.body := by
      induction r.body with
      | nil => simp
      | cons r rs ih =>
        intro r_and_rs_valid
        simp at r_and_rs_valid
        simp at ih
        rw [Set.insert_subset_iff] at r_and_rs_valid
        rcases (ih r_and_rs_valid.right) with ⟨rsTrees, h_rsTrees⟩
        have r_valid := r_and_rs_valid.left
        simp [KnowledgeBase.proofTheoreticSemantics] at r_valid
        rcases r_valid with ⟨rTree, h_rTree⟩
        exists rTree::rsTrees
        simp
        constructor
        · exact h_rTree
        · exact h_rsTrees

    rcases (h subs) with ⟨l, l_body⟩
    use ProofTree.node r.head l (by
      apply Or.inl
      unfold Program.groundProgram at rGP
      simp at rGP
      rcases rGP with ⟨r', rP, g, g_r⟩
      use r'
      use g
      constructor
      apply rP
      rw [← g_r]
      rw [GroundRule.ext_iff]
      simp
      rw [l_body]
    )
    simp [ProofTree.root, Tree.root, ProofTree.node]

  lemma dbElementsHaveProofTrees (kb : KnowledgeBase τ) : ∀ a, kb.db.contains a -> ∃ (t: ProofTree kb), t.root = a := by
    intro a mem
    use ProofTree.node a [] (by
      apply Or.inr
      simp
      exact mem
    )
    simp [ProofTree.root, Tree.root, ProofTree.node]

  theorem proofTheoreticSemanticsIsModel (kb: KnowledgeBase τ) : kb.proofTheoreticSemantics.models kb := by
    unfold Interpretation.models
    constructor
    · intro r rGP
      unfold Interpretation.satisfiesRule
      intro h
      apply proofTreeForRule
      apply rGP
      apply h

    · intro a mem
      apply dbElementsHaveProofTrees
      apply mem

  lemma proofTreeAtomsInEveryModel (kb: KnowledgeBase τ) : ∀ a, a ∈ kb.proofTheoreticSemantics -> ∀ i : Interpretation τ, i.models kb -> a ∈ i := by
    intro a pt i m
    unfold proofTheoreticSemantics at pt
    rw [Set.mem_setOf] at pt
    rcases pt with ⟨t, root_t⟩
    unfold Interpretation.models at m
    rcases m with ⟨ruleModel,dbModel⟩
    induction' h': t.height using Nat.strongRecOn with n ih  generalizing a t
    cases' eq : t.tree with a' l
    have valid_t := t.isValid
    unfold ProofTreeSkeleton.isValid at valid_t
    simp [eq] at valid_t
    cases valid_t with
    | inl ruleCase =>
      rcases ruleCase with ⟨r,rP,ex_g,all⟩
      rcases ex_g with ⟨g,r_ground⟩

      have r_true: i.satisfiesRule (g.applyRule' r) := by
        apply ruleModel
        unfold Program.groundProgram
        rw [Set.mem_setOf]
        use r
        use g
      unfold Interpretation.satisfiesRule at r_true
      have head_a: (g.applyRule' r).head = a := by
        unfold ProofTree.root at root_t
        unfold Tree.root at root_t
        simp [eq] at root_t
        rw [← root_t, r_ground]
      rw [head_a] at r_true
      apply r_true
      rw [Set.subset_def]
      intros x x_body
      simp at x_body
      rw [r_ground, ← GroundRule.in_bodySet_iff_in_body] at x_body
      simp at x_body
      rcases x_body with ⟨t_x, t_x_l, t_x_root⟩
      rw [List.forall_iff_forall_mem] at all
      simp at all
      apply ih (m := t_x.height) (t := {
        tree := t_x
        isValid := by
          apply all
          apply t_x_l
        })
      unfold ProofTree.root
      simp
      apply t_x_root
      unfold ProofTree.height
      simp
      rw [← h']
      apply Tree.heightOfMemberIsSmaller
      unfold Tree.member
      simp [eq]
      apply t_x_l
    | inr dbCase =>
      rcases dbCase with ⟨_, contains⟩
      apply dbModel
      unfold ProofTree.root at root_t
      unfold Tree.root at root_t
      simp [eq] at root_t
      rw [root_t] at contains
      apply contains

  def modelTheoreticSemantics (kb: KnowledgeBase τ) : Interpretation τ := {a: GroundAtom τ | ∀ (i: Interpretation τ), i.models kb → a ∈ i}

  lemma modelTheoreticSemanticsSubsetOfEachModel (kb: KnowledgeBase τ) : ∀ i, i.models kb -> kb.modelTheoreticSemantics ⊆ i := by
    intro i m
    unfold modelTheoreticSemantics
    rw [Set.subset_def]
    intro a
    rw [Set.mem_setOf]
    intro h
    apply h
    apply m

  lemma modelTheoreticSemanticsIsModel (kb: KnowledgeBase τ) : kb.modelTheoreticSemantics.models kb := by
    unfold Interpretation.models
    constructor
    intros r rGP
    unfold Interpretation.satisfiesRule
    intro h
    unfold modelTheoreticSemantics
    simp [Set.mem_setOf]
    by_contra h'
    push_neg at h'
    rcases h' with ⟨i, m, n_head⟩
    have m': i.models kb := by
      apply m
    rcases m with ⟨left,_⟩
    have r_true: i.satisfiesRule r := by
      apply left
      apply rGP
    unfold Interpretation.satisfiesRule at r_true
    have head: r.head ∈ i := by
      apply r_true
      apply subset_trans h
      apply modelTheoreticSemanticsSubsetOfEachModel
      apply m'
    exact absurd head n_head

    intros a a_db
    unfold modelTheoreticSemantics
    rw [Set.mem_setOf]
    by_contra h
    push_neg at h
    rcases h with ⟨i, m, a_n_i⟩
    unfold Interpretation.models at m
    have a_i: a ∈ i := by
      rcases m with ⟨_, right⟩
      apply right
      apply a_db
    exact absurd a_i a_n_i

  theorem modelAndProofTreeSemanticsEquivalent (kb: KnowledgeBase τ) : kb.proofTheoreticSemantics = kb.modelTheoreticSemantics := by
    apply Set.Subset.antisymm
    · rw [Set.subset_def]
      apply proofTreeAtomsInEveryModel
    · apply modelTheoreticSemanticsSubsetOfEachModel
      apply proofTheoreticSemanticsIsModel
end KnowledgeBase
