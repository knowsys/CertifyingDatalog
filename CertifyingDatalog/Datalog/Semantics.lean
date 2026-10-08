module

public import CertifyingDatalog.Datalog.Database
public import CertifyingDatalog.Datastructures.Tree

public section

structure KnowledgeBase (τ: Signature) where
  prog : Program τ
  db : Database τ

abbrev Interpretation (τ: Signature)
:= Set (GroundAtom τ)

abbrev ProofTreeSkeleton (τ: Signature)
:= Tree (GroundAtom τ)

variable {τ : Signature}

namespace Interpretation
  def satisfiesRule [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]
    (i: Interpretation τ) (r: GroundRule τ) : Prop := SetLike.coe r.bodySet ⊆ i → r.head ∈ i

  @[simp]
  lemma satisfiesRule_iff [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {i : Interpretation τ} {r : GroundRule τ} :
      i.satisfiesRule r ↔ (∀ x ∈ r.body, x ∈ i) → r.head ∈ i := by
    simp [satisfiesRule, Set.subset_def, ← GroundRule.in_bodySet_iff_in_body]

  def models [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]
    (i: Interpretation τ) (kb: KnowledgeBase τ) : Prop :=
    (∀ (r: GroundRule τ), r ∈ kb.prog.groundProgram → i.satisfiesRule r) ∧ ∀ (a: GroundAtom τ), kb.db.contains a → a ∈ i

  @[simp]
  lemma models_iff [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {i : Interpretation τ} {kb : KnowledgeBase τ} :
      i.models kb ↔ (∀ r ∈ kb.prog, ∀ (g : Grounding τ), i.satisfiesRule (g.applyRule' r)) ∧ ∀ (a: GroundAtom τ), kb.db.contains a → a ∈ i := by
    simp only [models, Program.mem_groundProgram_iff, exists_and_left, satisfiesRule_iff,
      forall_exists_index, and_imp, Grounding.applyRule'_body, List.mem_map,
      forall_apply_eq_imp_iff₂, Grounding.applyRule'_head, and_congr_left_iff]
    intro _
    constructor
    · intro h r hr g h'
      specialize h (g.applyRule' r)
      simp only [Grounding.applyRule'_body, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Grounding.applyRule'_head] at h
      apply h r hr g rfl h'
    · intro h gr r hr g hg h'
      specialize h r hr g
      simp only [hg, Grounding.applyRule'_body, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Grounding.applyRule'_head] at ⊢ h'
      apply h h'

end Interpretation

def ProofTreeSkeleton.isValid (t: ProofTreeSkeleton τ) (kb : KnowledgeBase τ) : Prop :=
  match t with
  | .node a l =>
    (∃ (r: Rule τ) (g: Grounding τ),  r ∈ kb.prog
      ∧ g.applyRule' r = {head:= a, body:= l.map Tree.root}
      ∧ l.attach.Forall (fun ⟨st, _h⟩ => isValid st kb))
    ∨ (l = [] ∧ kb.db.contains a)

  lemma ProofTreeSkeleton.isValid_iff {t : ProofTreeSkeleton τ} {kb : KnowledgeBase τ} :
      t.isValid kb ↔ (∃ (r : Rule τ), r ∈ kb.prog ∧ ∃ (g : Grounding τ),
        (g.applyRule' r).head = t.root ∧ (g.applyRule' r).body = t.children ∧
          ∀ t' ∈ t.directSubtrees, ProofTreeSkeleton.isValid t' kb) ∨
        (t.directSubtrees = [] ∧ kb.db.contains t.root) := by
    cases t with
    | node a l =>
      simp [ProofTreeSkeleton.isValid, GroundRule.ext_iff, List.forall_iff_forall_mem]
      grind

structure ProofTree (kb : KnowledgeBase τ) where
  tree : ProofTreeSkeleton τ
  isValid : tree.isValid kb

namespace ProofTree
  def root {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.root

  @[simp]
  lemma root_def {kb : KnowledgeBase τ} {t : ProofTree kb} :
    t.root = t.tree.root := by rfl

  def elem [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.elem

  @[simp]
  lemma elem_def [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {kb : KnowledgeBase τ} {t : ProofTree kb} :
    t.elem = t.tree.elem := by rfl

  def height {kb : KnowledgeBase τ} (t : ProofTree kb) := t.tree.height

  @[simp]
  lemma height_def {kb : KnowledgeBase τ} {t : ProofTree kb} :
    t.height = t.tree.height := by rfl

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
          · constructor
            · unfold ProofTree.root at r_g_apply
              rw [List.map_map]
              apply r_g_apply
            · rw [List.forall_iff_forall_mem]
              simp only [List.mem_attach, forall_const, Subtype.forall, List.mem_map,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
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

  lemma mem_proofTheoreticSemantics_iff {kb : KnowledgeBase τ} {ga : GroundAtom τ} :
      ga ∈ proofTheoreticSemantics kb ↔ ∃ (t : ProofTree kb), t.root = ga := by
    rfl

  lemma elementsOfEveryProofTreeInSemantics [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) : ∀ (t : ProofTree kb) (ga : GroundAtom τ), t.tree.elem ga → ga ∈ kb.proofTheoreticSemantics := by
    intro t ga mem
    unfold proofTheoreticSemantics
    simp only [Set.mem_ofPred]
    induction h': t.height using Nat.strongRecOn generalizing t with
    | ind n ih =>
      cases eq : t.tree with
      | node a' l =>
        simp only [eq, Tree.elem_def] at mem
        cases mem with
        | inl mem =>
          use t
          simp [ProofTree.root, eq, mem]
        | inr mem =>
          rcases mem with ⟨t', t'_t, a_t'⟩
          specialize ih t'.height
          have height_t': t'.height < n := by
            rw [← h']
            apply Tree.heightOfMemberIsSmaller
            simp [eq, t'_t]
          have valid_t': ProofTreeSkeleton.isValid t' kb := by
            have valid := t.isValid
            unfold ProofTreeSkeleton.isValid at valid
            simp only [eq, exists_and_left, exists_and_right] at valid
            cases valid with
            | inl valid =>
              rcases valid with ⟨_,_,_,all⟩
              rw [List.forall_iff_forall_mem] at all
              simp only [List.mem_attach, forall_const, Subtype.forall] at all
              apply all
              apply t'_t
            | inr valid =>
              exfalso
              rcases valid with ⟨left,_⟩
              rw [left] at t'_t
              simp at t'_t
          specialize ih height_t' ⟨t', valid_t'⟩
          apply ih
          · apply a_t'
          · rfl

  lemma proofTreeForRule [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]
    (kb: KnowledgeBase τ) (r: GroundRule τ) (rGP: r ∈ kb.prog.groundProgram) (subs: SetLike.coe r.bodySet ⊆ kb.proofTheoreticSemantics) : ∃ t : ProofTree kb, t.root = r.head := by
    simp [proofTheoreticSemantics, Set.subset_def, ← GroundRule.in_bodySet_iff_in_body] at subs
    let l := r.body.attach.map (fun ⟨x, h⟩ => Classical.choose (subs x h))
    use ProofTree.node r.head l (by
      simp at rGP
      rcases rGP with ⟨r', hr, g, hg⟩
      left
      use r'
      use g
      simp [← hg, hr, GroundRule.ext_iff, List.ext_get_iff, l]
      intro i hi
      rw [Classical.choose_spec (subs r.body[i] (by simp))]
    )
    simp [ProofTree.root, ProofTree.node]

  lemma dbElementsHaveProofTrees (kb : KnowledgeBase τ) : ∀ a, kb.db.contains a → ∃ (t: ProofTree kb), t.root = a := by
    intro a mem
    use ProofTree.node a [] (by
      apply Or.inr
      simp only [true_and]
      exact mem
    )
    simp [ProofTree.root, ProofTree.node]
  theorem proofTheoreticSemanticsIsModel [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : kb.proofTheoreticSemantics.models kb := by
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

  lemma proofTreeAtomsInEveryModel [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : ∀ a, a ∈ kb.proofTheoreticSemantics → ∀ i : Interpretation τ, i.models kb → a ∈ i := by
    intro a pt i m
    unfold proofTheoreticSemantics at pt
    rw [Set.mem_ofPred] at pt
    rcases pt with ⟨t, root_t⟩
    unfold Interpretation.models at m
    rcases m with ⟨ruleModel,dbModel⟩
    induction h': t.height using Nat.strongRecOn generalizing a t with
    | ind n ih =>
      cases eq : t.tree with
      | node a' l =>
        have valid_t := t.isValid
        unfold ProofTreeSkeleton.isValid at valid_t
        simp only [eq, exists_and_left, exists_and_right] at valid_t
        cases valid_t with
        | inl ruleCase =>
          rcases ruleCase with ⟨r,rP,ex_g,all⟩
          rcases ex_g with ⟨g,r_ground⟩
          have r_true: i.satisfiesRule (g.applyRule' r) := by
            apply ruleModel
            simp [Program.mem_groundProgram_iff, exists_and_left]
            use r
            simp [rP]
            use g
          unfold Interpretation.satisfiesRule at r_true
          have head_a: (g.applyRule' r).head = a := by
            simp only [ProofTree.root, eq, Tree.root_def] at root_t
            simp [r_ground, root_t]
          rw [head_a] at r_true
          apply r_true
          rw [Set.subset_def]
          intros x x_body
          simp only [Finset.mem_coe] at x_body
          rw [r_ground, ← GroundRule.in_bodySet_iff_in_body] at x_body
          simp only [List.mem_map] at x_body
          rcases x_body with ⟨t_x, t_x_l, t_x_root⟩
          rw [List.forall_iff_forall_mem] at all
          simp only [List.mem_attach, forall_const, Subtype.forall] at all
          apply ih (m := t_x.height) (t := {
            tree := t_x
            isValid := by
              apply all
              apply t_x_l
            })
          · unfold ProofTree.root
            simp only
            apply t_x_root
          · unfold ProofTree.height
            simp
          · rw [← h']
            apply Tree.heightOfMemberIsSmaller
            simp [eq, t_x_l]
        | inr dbCase =>
          rcases dbCase with ⟨_, contains⟩
          apply dbModel
          simp only [ProofTree.root, eq, Tree.root_def] at root_t
          rwa [← root_t]

  def modelTheoreticSemantics [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : Interpretation τ := {a: GroundAtom τ | ∀ (i: Interpretation τ), i.models kb → a ∈ i}

  lemma modelTheoreticSemanticsSubsetOfEachModel [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : ∀ i, i.models kb → kb.modelTheoreticSemantics ⊆ i := by
    intro i m
    unfold modelTheoreticSemantics
    rw [Set.subset_def]
    intro a
    rw [Set.mem_ofPred_eq]
    intro h
    apply h
    apply m

  lemma modelTheoreticSemanticsIsModel [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : kb.modelTheoreticSemantics.models kb := by
    unfold Interpretation.models
    constructor
    · intros r rGP
      unfold Interpretation.satisfiesRule
      intro h
      unfold modelTheoreticSemantics
      simp only [Set.mem_ofPred_eq]
      by_contra h'
      push Not at h'
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

    · intros a a_db
      unfold modelTheoreticSemantics
      rw [Set.mem_ofPred_eq]
      by_contra h
      push Not at h
      rcases h with ⟨i, m, a_n_i⟩
      unfold Interpretation.models at m
      have a_i: a ∈ i := by
        rcases m with ⟨_, right⟩
        apply right
        apply a_db
      exact absurd a_i a_n_i

  theorem modelAndProofTreeSemanticsEquivalent [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (kb: KnowledgeBase τ) : kb.proofTheoreticSemantics = kb.modelTheoreticSemantics := by
    apply Set.Subset.antisymm
    · rw [Set.subset_def]
      apply proofTreeAtomsInEveryModel
    · apply modelTheoreticSemanticsSubsetOfEachModel
      apply proofTheoreticSemanticsIsModel
end KnowledgeBase
