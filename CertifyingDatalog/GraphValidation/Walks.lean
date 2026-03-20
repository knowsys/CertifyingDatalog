import CertifyingDatalog.GraphValidation.Basic
import CertifyingDatalog.Basic

variable {A: Type u} [DecidableEq A] [Hashable A]

def List.isWalk (l : List A) (G: Graph A) : Prop := (∀ (a:A), a ∈ l → a ∈ G.vertices) ∧ ∀ i > 0, ∀ (g: i < l.length), l[i.pred]'(Nat.pred_lt_of_lt' i l.length g) ∈ G.predecessors l[i]

def List.isWalk_computable (l : List A) (G: Graph A) : Bool :=  l ⊆ G.vertices ∧
  (List.range l.length).attach.all fun ⟨x, h⟩ =>
    if 0 < x
    then
      l[x.pred]'(by simp at h; exact Nat.pred_lt_of_lt' x l.length h) ∈ G.predecessors (l[x]'(by simp at h; exact h))
    else true

theorem List.isWalk_iff_isWalk_computable_eq_true (l : List A) (G: Graph A) :
    l.isWalk G ↔ l.isWalk_computable G = true := by
  simp only [isWalk, gt_iff_lt, Nat.pred_eq_sub_one, isWalk_computable, Bool.if_true_right,
    all_eq_true, mem_attach, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt, Nat.le_zero_eq, decide_eq_true_eq, forall_const,
    Subtype.forall, mem_range, Bool.decide_and, Bool.and_eq_true]
  rw [List.subset_def]
  constructor
  · intro h
    constructor
    · apply h.1
    · have := h.2
      intro i hi
      by_cases h' : 0 < i
      · right
        apply this i h' hi
      · omega
  · intro h
    constructor
    · intro a ha
      apply h.1 ha
    · intro i hi1 hi2
      have := h.2
      specialize this i hi2
      have not_zero : ¬ i = 0 := by omega
      simp only [not_zero, false_or] at this
      exact this

instance (G : Graph A) (l : List A) : Decidable (List.isWalk l G) :=
  decidable_of_bool (List.isWalk_computable l G) (Iff.symm (List.isWalk_iff_isWalk_computable_eq_true l G))

def Walk (G : Graph A) := {l : List A // l.isWalk G}

namespace Walk

  instance {G : Graph A} : Membership A (Walk G) where
    mem := fun x y => y ∈ x.1

  theorem mem_walk_iff {G : Graph A} {a : A} {w : Walk G} :
    a ∈ w ↔ a ∈ w.1 := by rfl

  def singleton (G : Graph A) (a:A) (mem: a ∈ G.vertices) : Walk G := ⟨[a], by
    unfold List.isWalk
    constructor
    · simp only [List.mem_singleton, forall_eq]
      apply mem
    · simp only [gt_iff_lt, List.length_singleton, Nat.lt_one_iff, List.getElem_singleton,
      Nat.pred_eq_sub_one]
      intro i i_gt_0 i_0
      simp [i_0] at i_gt_0
  ⟩

  @[simp]
  theorem mem_singleton {G : Graph A} {a y : A} {h : a ∈ G.vertices} :
    y ∈ Walk.singleton G a h ↔ y = a := by
  simp [singleton, mem_walk_iff]

  def isCycle {G: Graph A} (w : Walk G): Prop :=
    if h: w.val.length < 2
    then False
    else
      have len_gt_zero: 0 < w.val.length := by
        cases ll: w.val.length with
        | zero =>
          rw [ll] at h
          simp at h
        | succ n =>
          simp
      w.val.get (Fin.mk 0 len_gt_zero) = w.val.get (Fin.mk w.val.length.pred (Nat.pred_lt (Ne.symm (Nat.ne_of_lt len_gt_zero))))

  def prevInCycle {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) : A :=
    match eq : w.val.idxOf b with
    | .zero => w.val.get ⟨w.val.length - 2, by
      rw [Nat.sub_lt_iff_lt_add']
      simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
      unfold isCycle at cyc; apply Decidable.by_contra
      intro contra
      simp only [not_le] at contra
      simp only [contra, ↓reduceDIte] at cyc
    ⟩
      -- (by intro contra; simp [contra] at b_mem)
    | .succ n => w.val.get ⟨n, by apply Nat.lt_of_succ_le; rw [← eq]; apply List.idxOf_le_length⟩

  lemma prevInCycleIsInCycle {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) : w.prevInCycle cyc b ∈ w.val := by
    unfold prevInCycle
    split <;> apply List.get_mem

  lemma prevInCycleIsPred {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) (b_mem : b ∈ w.val) : w.prevInCycle cyc b ∈ G.predecessors b := by
    unfold prevInCycle
    split
    case h_1 eq =>
      unfold isCycle at cyc
      have : ¬ w.val.length < 2 := by apply Decidable.by_contra; intro contra; simp at contra; simp [contra] at cyc
      simp only [this, ↓reduceDIte, List.get_eq_getElem, Nat.pred_eq_sub_one] at cyc
      simp only [Nat.zero_eq] at eq
      simp only [← eq, List.getElem_idxOf] at cyc
      rw [cyc]
      have prop := w.prop.right
      apply prop
      simp only [gt_iff_lt]
      simp only [not_lt] at this
      omega
    case h_2 n eq =>
      have : b = w.val.get ⟨n.succ, by rw [← eq, List.idxOf_lt_length_iff]; exact b_mem⟩ := by simp at eq; simp [← eq]
      simp only [this, Nat.succ_eq_add_one, List.get_eq_getElem]
      have prop := w.prop.right
      apply prop (n + 1)
      simp only [gt_iff_lt, Nat.zero_lt_succ]

  def predecessors {G: Graph A} (walk: Walk G) : List A := match walk.val.head? with
    | .none => []
    | .some head => G.predecessors head

theorem mem_of_mem_predecessors {G : Graph A} {w : Walk G} {a : A} :
    a ∈ predecessors w → a ∈ G.vertices := by
  simp only [predecessors]
  split
  · simp
  · rename_i hd h
    apply G.complete
    have wprop := w.2
    rw [List.head?_eq_some_iff] at h
    rcases h with ⟨tl, h⟩
    rw [h] at wprop
    simp only [List.isWalk, List.mem_cons, forall_eq_or_imp, gt_iff_lt, List.length_cons,
      Nat.pred_eq_sub_one] at wprop
    apply wprop.1.1

  def successors {G: Graph A} (walk: Walk G) : List A := match walk.val.getLast? with
    | .none => []
    | .some last => G.vertices.filter (fun v => last ∈ G.predecessors v)

theorem mem_of_mem_successors {G : Graph A} {w : Walk G} {a : A} :
    a ∈ successors w → a ∈ G.vertices := by
  simp [successors]
  split
  · simp
  · grind

  theorem walk_append {G : Graph A} {w w' : Walk G} (h : w.1 ≠ [])
    (h' : w.1.getLast h ∈ w'.predecessors) : (w.1 ++ w'.1).isWalk G := by
  have walk1 := w.2
  have walk2 := w'.2
  simp only [List.isWalk, Nat.pred_eq_sub_one, gt_iff_lt, List.mem_append, List.length_append] at *
  constructor
  · grind
  · intro i hi hi'
    simp only [List.getElem_append]
    split
    · split
      · apply walk1.2 _ hi
      · omega
    · split
      · simp only [predecessors, List.getLast_eq_getElem] at h'
        split at h'
        · simp at h'
        · rename_i head h
          have : head = w'.1[0] := by
            simp [List.head?_eq_getElem?] at h
            grind
          simpa [show i = w.1.length by omega, ← this]
      · grind

  def prependPredecessor {G: Graph A} (walk: Walk G) (pred : A) (is_pred : pred ∈ walk.predecessors) : Walk G := ⟨pred::walk.val, by
    rw [← List.singleton_append]
    have h₁ : (Walk.singleton G pred (mem_of_mem_predecessors is_pred )).1 ≠ [] := by simp [singleton]
    have := walk_append h₁ is_pred
    apply this
  ⟩

  def appendSuccessor {G: Graph A} (walk: Walk G) (succ : A) (is_succ : succ ∈ walk.successors) : Walk G := ⟨walk.val++[succ], by
    by_cases h : walk.1 = []
    · simp [successors, h] at is_succ
    · have : (walk.1 ++ (Walk.singleton G succ (mem_of_mem_successors is_succ)).1).isWalk G := by
        apply walk_append h
        simp [successors] at is_succ
        split at is_succ
        · simp at is_succ
        · simp only [List.mem_filter, decide_eq_true_eq] at is_succ
          simp only [predecessors, singleton, List.head?_cons]
          grind
      apply this
  ⟩

  lemma isSubsetOfVertices {G: Graph A} (walk: Walk G): ∀ a, a ∈ walk.val -> a ∈ G.vertices := by
    have prop := walk.prop
    unfold List.isWalk at prop
    rcases prop with ⟨walk,_⟩
    apply walk

  def tail {G: Graph A} (walk: Walk G) : Walk G := ⟨walk.val.tail, by
    have prop := walk.prop
    unfold List.isWalk at *
    rcases prop with ⟨subs, conn⟩
    constructor
    · intro a a_mem
      apply subs
      apply List.mem_of_mem_tail
      exact a_mem
    · intro i i_gt_0 i_lt_len
      specialize conn (Nat.succ i)
      simp only [Nat.succ_eq_add_one, gt_iff_lt, Nat.zero_lt_succ, Nat.pred_eq_sub_one,
        Nat.add_one_sub_one, forall_const] at conn
      simp only [Nat.pred_eq_sub_one, List.length_tail] at i_lt_len
      have : 0 < walk.val.length := by
        apply lt_trans
        apply i_gt_0
        apply Nat.lt_of_lt_pred
        apply i_lt_len
      rw [walk.val.tail_getElem this i.pred]
      · rw [walk.val.tail_getElem this i]
        · simp only [Nat.succ_eq_add_one, Nat.pred_eq_sub_one,
          Nat.sub_one_add_one_eq_of_pos i_gt_0]
          apply conn
        · apply i_lt_len
      · apply lt_trans
        · apply Nat.pred_lt_of_lt
          apply i_gt_0
        · apply i_lt_len
  ⟩

  lemma head_in_tail_predecessors {G : Graph A} (w : Walk G) (neq : w.val.tail ≠ []) : w.val.head (by intro contra; rw [contra] at neq; simp at neq) ∈ w.tail.predecessors := by
    unfold predecessors
    rw [@List.head?_eq_some_head _ w.tail.val neq]
    simp only
    have : 0 < w.val.length := by apply Decidable.by_contra; intro contra; simp at contra; rw [contra] at neq; simp at neq
    have this2 : 0 < w.tail.val.length := by
      apply Decidable.by_contra
      intro contra
      simp only [not_lt, Nat.le_zero_eq, List.length_eq_zero_iff] at contra
      unfold tail at contra
      simp only at contra
      rw [contra] at neq
      simp at neq
    rw [← List.getElem_zero this]
    rw [← List.getElem_zero this2]
    unfold Walk.tail
    rw [List.tail_getElem w.val this 0]
    · apply w.prop.right 1 (by simp)
    · rw [← List.length_tail]
      unfold tail at this2
      exact this2

  def take {G : Graph A} (walk : Walk G) (n : Nat) : Walk G := ⟨walk.val.take n, by
    have prop := walk.prop
    unfold List.isWalk at *
    rcases prop with ⟨subs, conn⟩
    constructor
    · intro a a_in_take
      apply subs
      apply List.mem_of_mem_take a_in_take
    · intro i i_gt_0 i_lt_len
      rw [List.getElem_take]
      rw [List.getElem_take]
      apply conn
      apply i_gt_0
  ⟩

  def takeUntil {G : Graph A} (walk : Walk G) (a : A) : Walk G := walk.take (walk.val.idxOf a + 1)

  lemma takeUnil_ne_of_ne {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).val ≠ [] := by
    unfold takeUntil
    intro contra
    unfold take at contra
    simp only [List.take_eq_nil_iff, Nat.add_one_ne_zero, false_or] at contra
    contradiction

  lemma takeUntil_head_same {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).val.head (by apply w.takeUnil_ne_of_ne ne) = w.val.head ne := by
    unfold takeUntil
    unfold take
    rw [List.take_head _ ne _ _]
    simp

  lemma takeUntil_predecessors_same {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).predecessors = w.predecessors := by
    unfold predecessors
    rw [List.head?_eq_some_head ne]
    rw [List.head?_eq_some_head (by apply takeUnil_ne_of_ne _ ne)]
    simp only
    rw [takeUntil_head_same]

  lemma takeUntil_getLast_is_target {G : Graph A} (w : Walk G) (a : A) (mem : a ∈ w.val) : (w.takeUntil a).val.getLast (by apply takeUnil_ne_of_ne; intro contra; rw [contra] at mem; simp at mem) = a := by
    unfold takeUntil
    rw [List.getLast_eq_getElem]
    unfold Walk.take
    rw [List.getElem_take]
    simp [List.length_take_of_le (by
      show w.val.idxOf a + 1 ≤ w.val.length
      apply Nat.succ_le_of_lt
      rw [List.idxOf_lt_length_iff]
      exact mem
    )]

  def concat {G: Graph A} (w1 w2: Walk G) (w1_neq : w1.val ≠ []) (w2_neq : w2.val ≠ []) (h : w1.val.getLast w1_neq = w2.val.head w2_neq) : Walk G := ⟨w1.val++w2.tail.1, by
    by_cases h' : w2.tail.1 = []
    · simpa [h'] using w1.2
    · apply walk_append w1_neq
      rw [h]
      simp [List.head_eq_getElem, predecessors, List.head?_eq_some_head h']
      simp [Walk.tail]
      apply w2.2.2
      omega
⟩

  lemma isCycle_of_head_in_tail {G : Graph A} (w : Walk G) (neq : w.val ≠ []) (h : w.val.head neq ∈ (w.tail).val) : ((w.tail.takeUntil (w.val.head neq)).prependPredecessor (w.val.head neq) (by
      rw [takeUntil_predecessors_same]
      apply head_in_tail_predecessors
      intro contra; unfold tail at h; simp [contra] at h
      intro contra; simp [contra] at h
    )).isCycle := by
    unfold isCycle
    unfold prependPredecessor
    split
    case isTrue contra =>
      have : 0 < (w.tail.takeUntil (w.val.head neq)).val.length := by
        rw [List.length_pos_iff]
        apply takeUnil_ne_of_ne
        intro contra; rw [contra] at h; simp at h
      have : ¬ (w.tail.takeUntil (w.val.head neq)).val.length + 1 < 2 := by
        apply Nat.not_lt_of_le
        simp only [Nat.reduceLeDiff]
        apply Nat.succ_le_of_lt
        apply this
      contradiction
    case isFalse len_ge_2 =>
      have : (w.tail.takeUntil (w.val.head neq)).val.length - 1 + 1 = (w.tail.takeUntil (w.val.head neq)).val.length := by
        rw [Nat.sub_one_add_one_eq_of_pos]
        apply List.length_pos_of_ne_nil
        apply takeUnil_ne_of_ne
        intro contra; rw [contra] at h; simp at h
      have get_cons := @List.getElem_cons_succ _ (w.val.head neq) (w.tail.takeUntil (w.val.head neq)).val ((w.tail.takeUntil (w.val.head neq)).val.length - 1) (by rw [this]; simp)
      simp only [this] at get_cons
      simp only [List.length_cons, Fin.zero_eta,
        List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Nat.pred_eq_sub_one,
        Nat.add_one_sub_one]
      rw [get_cons]
      have applied_takeUntil_getLast_is_target := w.tail.takeUntil_getLast_is_target (w.val.head neq) h
      rw [List.getLast_eq_getElem] at applied_takeUntil_getLast_is_target
      rw [applied_takeUntil_getLast_is_target]

    theorem drop_until_isWalk_of_isWalk {G : Graph A} {w : Walk G} {a : A} :
      (List.drop_until w.1 a).isWalk G := by
    suffices ∀ (l : List A), l.isWalk G → (List.drop_until l a).isWalk G from this w.1 w.2
    intro l h
    induction l with
    | nil => simp [List.drop_until, h]
    | cons hd tl ih =>
      simp [List.drop_until]
      split
      · exact h
      · apply ih
        simp only [List.isWalk, List.mem_cons, forall_eq_or_imp, gt_iff_lt, List.length_cons,
          Nat.pred_eq_sub_one] at h ⊢
        rcases h with ⟨h1, h2⟩
        apply And.intro h1.right
        intro i hi1 hi2
        have hi1': 0 < i +1 := by omega
        have hi2' : i + 1 < tl.length +1 := by omega
        specialize h2 (i+1) hi1' hi2'
        cases i with
        | zero => simp at hi1
        | succ j =>
          simp only [List.getElem_cons_succ, Nat.add_one_sub_one] at h2 ⊢
          exact h2

    def removeCycles {G : Graph A} (w : Walk G) : Walk G := ⟨List.removeCycles w.1, by
        suffices ∀ (l : List A), l.isWalk G → (List.removeCycles l).isWalk G from this w.1 w.2
        intro l hl
        induction h:l.length using Nat.strong_induction_on generalizing l with
        | h n ih =>
          cases n with
          | zero =>
            simp only [List.length_eq_zero_iff] at h
            rw [h] at hl
            simp [h, List.removeCycles, hl]
          | succ k =>
            have := List.exists_of_length_succ _ h
            rcases this with ⟨hd, tl, h'⟩
            simp only [h', List.length_cons, Nat.add_right_cancel_iff] at hl h ⊢
            simp only [List.removeCycles]
            have htl : tl.isWalk G := by
              simp only [List.isWalk, List.mem_cons, forall_eq_or_imp, gt_iff_lt, List.length_cons,
                Nat.pred_eq_sub_one] at hl ⊢
              rcases hl with ⟨hl1, hl2⟩
              apply And.intro hl1.right
              intro i hi1 hi2
              cases i with
              | zero => simp at hi1
              | succ j =>
                simp only [Nat.add_one_sub_one]
                specialize hl2 (j+2) (by omega) (by omega)
                simp only [List.getElem_cons_succ, Nat.add_one_sub_one] at hl2
                exact hl2
            split
            · rename_i mem
              have : (List.drop_until tl hd).length < k + 1 := by
                rw [← h]
                rw [Nat.lt_succ_iff]
                apply List.drop_until_length
              specialize ih (List.drop_until tl hd).length this (List.drop_until tl hd)
              have walk : (List.drop_until tl hd).isWalk G := by
                apply drop_until_isWalk_of_isWalk (w:= ⟨tl, htl⟩)
              apply ih walk rfl
            · simp only [List.isWalk, List.mem_cons, forall_eq_or_imp, gt_iff_lt, List.length_cons,
              Nat.pred_eq_sub_one] at hl ⊢
              specialize ih k (by omega) tl htl h
              simp only [List.isWalk, gt_iff_lt, Nat.pred_eq_sub_one] at ih
              apply And.intro (And.intro hl.1.1 ih.1)
              rcases ih with ⟨_, ih⟩
              intro i hi1 hi2
              cases i with
              | zero => simp at hi1
              | succ j =>
                cases j with
                | zero =>
                  simp only [Nat.zero_add, List.getElem_cons_succ, Nat.sub_self, List.getElem_cons_zero]
                  rcases hl with ⟨_, hl⟩
                  specialize hl 1 (by simp)
                  simp only [Nat.zero_add, Nat.lt_add_left_iff_pos] at hi2
                  have htl' : tl ≠ [] := by
                    rw [@List.length_pos_iff_ne_nil] at hi2
                    rw [List.removeCycles_not_empty_iff] at hi2
                    exact hi2
                  have : 0 < tl.length := by
                    rw [@List.length_pos_iff_ne_nil]
                    apply htl'
                  specialize hl (by omega)
                  simp only [List.getElem_cons_succ, Nat.sub_self, List.getElem_cons_zero] at hl
                  have head_tl := List.removeCycles_head_eq_head (l := tl) htl'
                  simp only [List.head_eq_getElem_zero] at head_tl
                  simp [head_tl, hl]
                | succ m =>
                  simp only [List.getElem_cons_succ, Nat.add_one_sub_one]
                  specialize ih (m + 1) (by omega) (by omega)
                  simp only [Nat.add_one_sub_one] at ih
                  exact ih
    ⟩

end Walk

namespace Graph
  def isAcyclic (G: Graph A) := ∀ (w: Walk G), ¬ w.isCycle

  def canReach (G : Graph A) (a b : A) : Prop := ∃ (w : Walk G) (neq : w.val ≠ []), (w.val.head neq) = a ∧ (w.val.getLast neq) = b

  theorem canReach_iff_canReach_with_at_most_vertices_length
 (G : Graph A) (a b : A) :
      canReach G a b ↔ ∃ (w : Walk G) (neq : w.val ≠ []),
        w.1.length ≤ G.vertices.length ∧ (w.val.head neq) = a ∧ (w.val.getLast neq) = b := by
    simp only [canReach, ne_eq, exists_and_left]
    constructor
    · intro h
      rcases h with ⟨w, neq, h⟩
      use w.removeCycles
      have h' := w.removeCycles.2
      constructor
      · apply List.length_le_length_of_nodup_subset
        · simp only [List.isWalk, Nat.pred_eq_sub_one, gt_iff_lt] at h'
          simp only [List.subset_def]
          apply h'.1
        · apply List.nodup_removeCycles
      · have := List.removeCycles_not_empty_iff (l := w.1)
        use (this.mpr neq)
        simp only [Walk.removeCycles]
        rw [List.removeCycles_head_eq_head neq, List.removeCycles_getLast_eq_getLast neq]
        exact h
    · intro h
      rcases h with ⟨w, _, neq, h⟩
      use w
      use neq

  def canReach_computable (G : Graph A) (a b : A) : Bool :=
    (G.vertices.allSubsetListsOfLengthAtMost G.vertices.length).filter (fun x =>
      if h: x ≠ []
      then List.isWalk x G ∧ x.head h = a ∧ x.getLast h = b
      else false) ≠ ∅

  theorem canReach_iff_canReach_computable_eq_true (G : Graph A) (a b : A) :
      canReach G a b ↔ canReach_computable G a b := by
    simp [canReach_iff_canReach_with_at_most_vertices_length, canReach_computable, List.allSubsetListsOfLengthAtMost_iff]
    constructor
    · intro h
      rcases h with ⟨w, len, neq, h⟩
      use w.1
      apply And.intro len
      apply And.intro w.2.1
      apply And.intro w.2
      use neq
    · intro h
      rcases h with ⟨l, len, _, walk, neq, h⟩
      use ⟨l, walk⟩
      simp only [len, true_and]
      use neq

  instance (G : Graph A) (a b: A) : Decidable (canReach G a b) :=
    decidable_of_bool (canReach_computable G a b) (Iff.symm (canReach_iff_canReach_computable_eq_true G a b))

  lemma canReach_refl (G : Graph A) (a : A) (mem: a ∈ G.vertices) : G.canReach a a := by
    unfold canReach
    exists Walk.singleton G a mem
    simp [Walk.singleton]

  lemma canReach_pred (G : Graph A) (a b : A) (a_pred: a ∈ G.predecessors b) : G.canReach a b := by
    unfold canReach
    exists ((Walk.singleton G b (by apply mem_of_has_pred; apply a_pred)).prependPredecessor a (by
      unfold Walk.singleton
      unfold Walk.predecessors
      simp only [List.head?_cons]
      apply a_pred
    ))
    exists (by simp [Walk.singleton, Walk.prependPredecessor])

  lemma canReach_trans (G : Graph A) (a b c : A) : G.canReach a b ∧ G.canReach b c -> G.canReach a c := by
    unfold canReach
    intro ⟨walk_a_b, walk_b_c⟩
    rcases walk_a_b with ⟨w_a_b, w_a_b_neq, w_head_a, w_last_b⟩
    rcases walk_b_c with ⟨w_b_c, w_b_c_neq, w_head_b, w_last_c⟩
    exists (w_a_b.concat w_b_c w_a_b_neq w_b_c_neq (by rw [w_head_b]; rw [w_last_b]))
    exists (by
      unfold Walk.concat
      apply List.append_ne_nil_of_left_ne_nil
      exact w_a_b_neq
    )
    constructor
    · unfold Walk.concat
      rw [List.head_append' _ _ w_a_b_neq]
      exact w_head_a
    · cases Decidable.em (w_b_c.val.tail = []) with
      | inl eq =>
        have : w_b_c = Walk.singleton G c (by apply Walk.isSubsetOfVertices; rw [← w_last_c]; apply List.getLast_mem) := by
          unfold Walk.singleton
          rcases w_b_c with ⟨list, prop⟩
          cases list with
          | nil => simp at w_b_c_neq
          | cons head tail =>
            simp only [List.tail_cons] at eq
            simp only [eq]
            simp only [eq, List.getLast_singleton] at w_last_c
            simp [w_last_c]
        unfold Walk.concat
        simp only [this]
        unfold Walk.singleton
        simp only [Walk.tail, List.tail_cons, List.append_nil]
        rw [w_last_b]
        rw [← w_head_b]
        simp only [this]
        unfold Walk.singleton
        simp
      | inr neq =>
        unfold Walk.concat Walk.tail
        rw [List.getLast_append_of_right_ne_nil w_a_b.val w_b_c.val.tail neq]
        rw [List.tail_getLast]
        exact w_last_c

  lemma canReachWhenCanReachPred (G : Graph A) (a c : A) : ∀ b, b ∈ G.predecessors c -> G.canReach a b -> G.canReach a c := by
    intro a a_pred a_reaches_b
    unfold canReach at *
    rcases a_reaches_b with ⟨w, neq, get_a, get_b⟩
    exists w.appendSuccessor c (by
      unfold Walk.successors
      rw [List.getLast?_eq_some_getLast neq]
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · apply mem_of_has_pred
        apply a_pred
      · rw [get_b]
        exact a_pred
    )
    unfold Walk.appendSuccessor
    exists (by simp)
    constructor
    · rw [← get_a]
      rw [List.head_append']
    · simp

  lemma canReach_iff (G : Graph A) (a c : A) : G.canReach a c ↔ (c ∈ G.vertices ∧ a = c) ∨ ∃ b, b ∈ G.predecessors c ∧ G.canReach a b := by
    constructor
    · intro h
      unfold canReach at h
      rcases h with ⟨w, neq, head, last⟩
      cases eq : w.val with
      | nil => simp [eq] at neq
      | cons d ds =>
        cases ds with
        | nil =>
          apply Or.inl
          simp only [eq, List.head_cons] at head
          simp only [eq, List.getLast_singleton] at last
          constructor
          · apply w.prop.left
            rw [eq]
            rw [last]
            simp
          · rw [← head]
            rw [last]
        | cons _ _ =>
          apply Or.inr
          have : 0 < w.val.length - 1 := by rw [eq]; simp
          exists w.val.get ⟨w.val.length.pred.pred, by apply Nat.lt_of_lt_of_le; apply Nat.pred_lt_of_lt; apply this; apply Nat.pred_le⟩
          constructor
          · rw [← last]; rw [List.getLast_eq_getElem]; apply w.prop.right; simp; exact this
          · unfold canReach
            exists w.take (w.val.length - 1)
            exists (by intro contra; unfold Walk.take at contra; rw [List.take_eq_nil_iff] at contra; cases contra with | inl h => rw [h] at this; contradiction | inr _ => contradiction)
            constructor
            · unfold Walk.take
              rw [List.take_head w.val neq _ this]
              exact head
            · unfold Walk.take
              rw [List.take_getLast w.val neq ⟨w.val.length - 1, by apply Nat.lt_succ_of_lt; apply Nat.pred_lt_of_lt; apply Nat.lt_of_lt_pred; apply this⟩ this]
              simp
    · intro h
      cases h with
      | inl h => rw [h.right]; apply canReach_refl; apply h.left
      | inr h =>
        rcases h with ⟨b, pred, reach⟩
        apply canReach_trans
        constructor
        · exact reach
        · apply canReach_pred; apply pred

  def verticesThatReach (G: Graph A) (b : A) : Finset A := G.vertices.toFinset.filter (fun a => G.canReach a b)

  lemma verticesThatReachContainSelf (G: Graph A) (a : A) (mem: a ∈ G.vertices) : a ∈ G.verticesThatReach a := by
    unfold verticesThatReach
    rw [Finset.mem_filter]
    constructor
    · simp only [List.mem_toFinset]
      apply mem
    · apply canReach_refl
      apply mem

  lemma verticesThatReachPredSubsetReachSelf (G : Graph A) (c : A) : ∀ b, b ∈ G.predecessors c -> G.verticesThatReach b ⊆ G.verticesThatReach c := by
    intro b b_pred
    rw [Finset.subset_iff]
    intro a
    unfold verticesThatReach
    rw [Finset.mem_filter]
    intro ⟨mem, reach⟩
    rw [Finset.mem_filter]
    constructor
    · exact mem
    · apply G.canReachWhenCanReachPred a c b b_pred reach

  lemma cannotReachPredIfAcyclic (G : Graph A) (acyclic : G.isAcyclic) (b : A) : ∀ a, a ∈ G.predecessors b -> ¬ G.canReach b a := by
    intro a a_pred contra
    unfold canReach at contra
    rcases contra with ⟨w, neq, get_b, get_a⟩
    cases eq : w.val with
    | nil => simp [eq] at neq
    | cons head tail =>
      apply acyclic (w.appendSuccessor b (by
        unfold Walk.successors
        rw [List.getLast?_eq_some_getLast neq]
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        · apply mem_of_has_pred
          apply a_pred
        · rw [get_a]
          exact a_pred
      ))
      unfold Walk.isCycle
      split
      case isTrue h =>
        unfold Walk.appendSuccessor at h; simp at h
        rw [eq] at h
        have contra : ¬ List.length (head :: tail) + 1 < 2 := by simp
        exact contra h
      case isFalse h =>
        simp only [List.get_eq_getElem, Nat.pred_eq_sub_one]
        unfold Walk.appendSuccessor
        rw [List.getElem_append_left]
        · rw [List.getElem_append_right]
          · simp only [List.length_append, List.length_singleton, Nat.add_one_sub_one,
            Nat.sub_self, List.getElem_cons_zero]
            rw [← get_b]
            apply List.get_mk_zero
          · simp [eq]
        · simp [eq]

  lemma selfNotInVerticesThatReachPred (G : Graph A) (acyclic : G.isAcyclic) (b : A) : ∀ a, a ∈ G.predecessors b -> ¬ b ∈ G.verticesThatReach a := by
    intro a a_pred contra
    apply G.cannotReachPredIfAcyclic acyclic b a a_pred
    unfold verticesThatReach at contra
    rw [Finset.mem_filter] at contra
    exact contra.right

  lemma verticesThatReachPredStrictSubsetReachSelfIfAcyclic (G : Graph A) (acyclic : G.isAcyclic) (c : A) : ∀ b, b ∈ G.predecessors c -> G.verticesThatReach b ⊂ G.verticesThatReach c := by
    intro b b_pred
    rw [Finset.ssubset_def]
    constructor
    · apply G.verticesThatReachPredSubsetReachSelf c b b_pred
    · intro contra
      rw [Finset.subset_iff] at contra
      apply G.selfNotInVerticesThatReachPred acyclic c b b_pred
      apply contra
      apply verticesThatReachContainSelf
      apply mem_of_has_pred b_pred

  def reachableFromCycle (G: Graph A) (b : A) := ∃ (w : Walk G), w.isCycle ∧ ∃ (a: A), a ∈ w.val ∧ G.canReach a b

  lemma notReachableFromCycleIffPredecessorsNotReachableFromCycle (G: Graph A) (b : A) : ¬ G.reachableFromCycle b ↔ ∀ (a : A), a ∈ G.predecessors b → ¬ G.reachableFromCycle a :=
  by
    constructor
    · intro b_not_reach a a_pred a_reach
      apply b_not_reach
      unfold reachableFromCycle at *
      rcases a_reach with ⟨w, w_cycle, a', a'_in_w, a_reach_a'⟩
      exists w
      constructor
      · exact w_cycle
      · exists a'
        constructor
        · exact a'_in_w
        · apply canReach_trans
          constructor
          · exact a_reach_a'
          · apply canReach_pred; apply a_pred
    · intro h contra
      unfold reachableFromCycle at contra
      rcases contra with ⟨cyc, cyc_isCycle, a, a_mem_cyc, reach⟩
      unfold canReach at reach
      rcases reach with ⟨w, w_neq, w_a, w_b⟩
      cases Decidable.em (a = b) with
      | inl mem =>
        let prev_a := cyc.prevInCycle cyc_isCycle a
        let prev_prev := cyc.prevInCycle cyc_isCycle prev_a
        apply h prev_a
        rw [← mem]; apply Walk.prevInCycleIsPred; exact a_mem_cyc
        unfold reachableFromCycle
        exists cyc
        constructor
        · exact cyc_isCycle
        · exists prev_prev
          constructor
          · apply Walk.prevInCycleIsInCycle
          · apply canReach_pred; apply Walk.prevInCycleIsPred; apply Walk.prevInCycleIsInCycle
      | inr nmem =>
        have : 0 < w.val.length - 1 := by
          apply Decidable.by_contra
          intro contra
          simp only [not_lt, Nat.le_zero_eq] at contra
          cases eq : w.val with
          | nil => simp [eq] at w_neq
          | cons c cs =>
            have : cs = [] := by
              rw [eq] at contra
              simp only [List.length_cons, Nat.add_one_sub_one, List.length_eq_zero_iff] at contra
              exact contra
            rw [this] at eq
            simp only [eq, List.getLast_singleton] at w_b
            simp only [eq, List.head_cons] at w_a
            rw [w_a] at w_b
            apply nmem
            apply w_b
        have this2 : w.val.length - 1 < w.val.length := by apply Nat.pred_lt_of_lt; apply Nat.lt_of_lt_pred; apply this
        apply h (w.val.get ⟨w.val.length - 2, by apply Nat.lt_of_le_of_lt; apply Nat.pred_le; exact this2⟩)
        have prop := w.prop.right (w.val.length - 1) (by apply this) this2
        rw [List.getLast_eq_getElem] at w_b
        rw [w_b] at prop
        apply prop
        unfold reachableFromCycle
        exists cyc
        constructor
        · exact cyc_isCycle
        · exists a
          constructor
          · exact a_mem_cyc
          · unfold canReach
            exists w.take (w.val.length - 1)
            exists (by unfold Walk.take; intro contra; rw [List.take_eq_nil_iff] at contra; cases contra with | inl h => rw [h] at this; contradiction | inr _ => contradiction)
            constructor
            · unfold Walk.take
              rw [List.take_head w.val w_neq]
              apply w_a
              exact this
            · unfold Walk.take
              rw [List.take_getLast w.val w_neq ⟨w.val.length - 1, by apply Nat.lt_succ_of_lt; exact this2⟩]
              simp only [List.get_eq_getElem]
              have this3 : w.val.length - 1 - 1 = w.val.length - 2 := by tauto
              simp only [this3]
              simp [this]

  lemma acyclicIffAllNotReachableFromCycle (G: Graph A): isAcyclic G ↔ ∀ (a:A), ¬ G.reachableFromCycle a := by
    constructor
    · intro acyclic a contra
      unfold reachableFromCycle at contra
      unfold isAcyclic at acyclic
      rcases contra with ⟨_, cyc, _⟩
      apply acyclic
      apply cyc
    · intro h
      unfold isAcyclic
      intro w cyc
      let head := (w.val.head (by intro contra; unfold Walk.isCycle at cyc; simp [contra] at cyc))
      apply h head
      unfold reachableFromCycle
      exists w
      constructor
      · exact cyc
      · exists head
        have : head ∈ w.val := by apply List.head_mem
        constructor
        · exact this
        · apply canReach_refl; apply w.prop.left; exact this
end Graph
