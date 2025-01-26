import CertifyingDatalog.GraphValidation.Basic

variable {A: Type u} [DecidableEq A] [Hashable A]

def List.isWalk (l : List A) (G: Graph A) : Prop := (∀ (a:A), a ∈ l → a ∈ G.vertices) ∧ ∀ i > 0, ∀ (g: i < l.length), l[i.pred]'(Nat.pred_lt_of_lt' i l.length g) ∈ G.predecessors l[i]

def Walk (G : Graph A) := {l : List A // l.isWalk G}

namespace Walk
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
    match eq : w.val.indexOf b with
    | .zero => w.val.get ⟨w.val.length - 2, by
      rw [Nat.sub_lt_iff_lt_add']
      simp only [Nat.lt_add_right_iff_pos, Nat.zero_lt_succ]
      unfold isCycle at cyc; apply Decidable.by_contra
      intro contra
      simp only [not_le] at contra
      simp only [contra, ↓reduceDIte] at cyc
    ⟩
      -- (by intro contra; simp [contra] at b_mem)
    | .succ n => w.val.get ⟨n, by apply Nat.lt_of_succ_le; rw [← eq]; apply List.indexOf_le_length⟩

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
      simp only [← eq, List.getElem_indexOf] at cyc
      rw [cyc]
      have prop := w.prop.right
      apply prop
      simp only [gt_iff_lt]
      simp only [not_lt] at this
      omega
    case h_2 n eq =>
      have : b = w.val.get ⟨n.succ, by rw [← eq, List.indexOf_lt_length]; exact b_mem⟩ := by simp at eq; simp [← eq]
      simp only [this, Nat.succ_eq_add_one, List.get_eq_getElem]
      have prop := w.prop.right
      apply prop (n + 1)
      simp only [gt_iff_lt, Nat.zero_lt_succ]

  def predecessors {G: Graph A} (walk: Walk G) : List A := match walk.val.head? with
    | .none => []
    | .some head => G.predecessors head

  def successors {G: Graph A} (walk: Walk G) : List A := match walk.val.getLast? with
    | .none => []
    | .some last => G.vertices.filter (fun v => last ∈ G.predecessors v)

  def prependPredecessor {G: Graph A} (walk: Walk G) (pred : A) (is_pred : pred ∈ walk.predecessors) : Walk G := ⟨pred::walk.val, by
    have walk_prop := walk.prop
    unfold List.isWalk
    unfold List.isWalk at walk_prop
    rcases walk_prop with ⟨subs,connected⟩
    constructor
    · intro b
      simp only [Nat.pred_eq_sub_one, List.mem_cons]
      intro h
      cases h with
      | inl h =>
        rw [h]
        unfold predecessors at is_pred
        cases eq : walk.val.head? with
        | none => simp [eq] at is_pred
        | some head =>
          simp only [eq] at is_pred
          apply Graph.mem_of_is_pred _ _ _ is_pred
      | inr h =>
        apply subs
        simp only [Nat.pred_eq_sub_one]
        apply h
    · intro i i_zero i_len
      cases i with
      | zero =>
        simp at i_zero
      | succ j =>
        rw [List.getElem_cons_succ]
        cases j with
        | zero =>
          simp only [Nat.pred_eq_sub_one, Nat.zero_add, Nat.sub_self, List.getElem_cons_zero]
          unfold predecessors at is_pred
          cases eq : walk.val.head? with
          | none => simp [eq] at is_pred
          | some head =>
            simp [eq] at is_pred
            rw [List.head?_eq_head] at eq
            injection eq with eq
            rw [List.getElem_zero]
            rw [eq]
            apply is_pred
        | succ k =>
          simp only [Nat.pred_eq_sub_one, Nat.add_one_sub_one, List.getElem_cons_succ]
          specialize connected (Nat.succ k)
          simp only [Nat.succ_eq_add_one, gt_iff_lt, Nat.zero_lt_succ, Nat.pred_eq_sub_one,
            Nat.add_one_sub_one, forall_const] at connected
          simp only [Nat.pred_eq_sub_one, List.length_cons, Nat.add_lt_add_iff_right] at i_len
          specialize connected i_len
          apply connected
  ⟩

  def appendSuccessor {G: Graph A} (walk: Walk G) (succ : A) (is_succ : succ ∈ walk.successors) : Walk G := ⟨walk.val++[succ], by
    unfold List.isWalk
    constructor
    · intro a a_elem
      simp only [Nat.pred_eq_sub_one, List.mem_append, List.mem_singleton] at a_elem
      cases a_elem with
      | inl h => apply walk.prop.left; exact h
      | inr h =>
        unfold successors at is_succ
        cases eq : walk.val.getLast? with
        | none => simp [eq] at is_succ
        | some last =>
          simp only [eq, List.mem_filter, decide_eq_true_eq] at is_succ
          rw [h]
          apply is_succ.left
    · intro i i_zero i_len
      have prop := walk.prop.right
      cases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i_len) with
      | inl i_lt =>
        simp
        rw [List.getElem_append]
        rw [List.getElem_append]
        simp only [Nat.pred_eq_sub_one, List.length_append, List.length_singleton,
          Nat.add_one_sub_one] at i_lt
        simp only [i_lt, ↓reduceDIte, List.getElem_singleton]
        have i_pred_lt: i -1 < walk.1.length := by
          rw [← Nat.pred_eq_sub_one]
          apply Nat.lt_trans (Nat.pred_lt_of_lt i_zero) i_lt
        simp only [i_pred_lt, ↓reduceDIte]
        apply prop
        apply i_zero
      | inr i_eq =>
        unfold successors at is_succ
        cases eq : walk.val.getLast? with
        | none => simp [eq] at is_succ
        | some last =>
          simp only [Nat.pred_eq_sub_one, List.length_append, List.length_singleton,
            Nat.add_one_sub_one] at i_eq
          simp only [eq, List.mem_filter, decide_eq_true_eq] at is_succ
          have ⟨_, last_pred_of_succ⟩ := is_succ
          simp only [Nat.pred_eq_sub_one]
          rw [List.getElem_append]
          rw [List.getElem_append]
          simp only [i_eq, lt_self_iff_false, ↓reduceDIte, Nat.sub_self, List.getElem_cons_zero,
            Nat.sub_le, Nat.sub_eq_zero_of_le]
          have h: walk.1.length - 1 < walk.1.length := by
            rw [← i_eq,←  Nat.pred_eq_sub_one]
            apply Nat.pred_lt (Ne.symm (Nat.ne_of_lt i_zero))
          simp only [h, ↓reduceDIte]
          rw [List.getLast?_eq_getElem?] at eq
          rw [LawfulGetElem.getElem?_def] at eq
          simp only [h, ↓reduceDIte, Option.some.injEq] at eq
          rw [eq]
          apply last_pred_of_succ
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
    rw [@List.head?_eq_head _ w.tail.val neq]
    simp only
    have : 0 < w.val.length := by apply Decidable.by_contra; intro contra; simp at contra; rw [contra] at neq; simp at neq
    have this2 : 0 < w.tail.val.length := by
      apply Decidable.by_contra
      intro contra
      simp only [not_lt, Nat.le_zero_eq, List.length_eq_zero] at contra
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

  def takeUntil {G : Graph A} (walk : Walk G) (a : A) : Walk G := walk.take (walk.val.indexOf a + 1)

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
    rw [List.head?_eq_head ne]
    rw [List.head?_eq_head (by apply takeUnil_ne_of_ne _ ne)]
    simp only
    rw [takeUntil_head_same]

  lemma takeUntil_getLast_is_target {G : Graph A} (w : Walk G) (a : A) (mem : a ∈ w.val) : (w.takeUntil a).val.getLast (by apply takeUnil_ne_of_ne; intro contra; rw [contra] at mem; simp at mem) = a := by
    unfold takeUntil
    rw [List.getLast_eq_getElem]
    unfold Walk.take
    rw [List.getElem_take]
    simp [List.length_take_of_le (by
      show w.val.indexOf a + 1 ≤ w.val.length
      apply Nat.succ_le_of_lt
      rw [List.indexOf_lt_length]
      exact mem
    )]

  def concat {G: Graph A} (w1 w2: Walk G) (w1_neq : w1.val ≠ []) (w2_neq : w2.val ≠ []) (h : w1.val.getLast w1_neq = w2.val.head w2_neq) : Walk G := ⟨w1.val++w2.val.tail, by
    have ⟨subs1, conn1⟩ := w1.prop
    have ⟨subs2, conn2⟩ := w2.prop
    unfold List.isWalk
    constructor
    · intro a a_in_append
      simp only [Nat.pred_eq_sub_one, List.mem_append] at a_in_append
      cases a_in_append
      · apply subs1; assumption
      · apply subs2; rename_i h'; apply List.mem_of_mem_tail h'
    · intro i i_gt_0 i_lt_len
      rw [List.getElem_append]
      rw [List.getElem_append]
      split
      · split
        · apply conn1 _ i_gt_0
        · rename_i h h'
          simp only [Nat.pred_eq_sub_one, not_lt] at h'
          have w1_lt_w1: w1.1.length < w1.1.length := by
            have i_pred_lt_i: i.pred < i := by
              apply Nat.pred_lt (Nat.ne_of_gt i_gt_0)
            apply Nat.lt_of_le_of_lt h'
            rw [← Nat.pred_eq_sub_one]
            apply Nat.lt_trans i_pred_lt_i h
          simp at w1_lt_w1
      · split
        · rename_i h h'
          simp only [Nat.pred_eq_sub_one, not_lt] at h
          apply Nat.eq_or_lt_of_le at h
          cases h with
          | inl h =>
            rename_i w1_w2_conn _
            rw [List.getLast_eq_getElem] at w1_w2_conn
            simp only [Nat.pred_eq_sub_one, ← h]
            rw [w1_w2_conn]
            simp only [Nat.sub_self, List.getElem_tail, Nat.zero_add]
            rw [List.head_eq_getElem]
            specialize conn2 1
            apply conn2
            simp
          | inr h =>
            rw [Nat.lt_iff_le_pred i_gt_0] at h
            simp only [Nat.pred_eq_sub_one] at h'
            have := Nat.lt_of_lt_of_le h' h
            simp at this
        · simp only [Nat.pred_sub]
          rename_i h h'
          simp only [Nat.pred_eq_sub_one, not_lt] at h
          apply Nat.eq_or_lt_of_le at h
          cases h with
          | inl h =>
            rw [h] at h'
            simp only [Nat.pred_eq_sub_one, not_lt] at h'
            rw [← Nat.pred_eq_sub_one] at h'
            rw [Nat.le_pred_iff_lt i_gt_0] at h'
            simp at h'
          | inr h =>
            simp only [Nat.pred_eq_sub_one, List.getElem_tail]
            have idx: i - w1.1.length - 1 + 1 = (i - w1.1.length +1).pred := by
              refine Nat.sub_add_cancel ?_
              exact Nat.le_sub_of_add_le' h
            simp_rw [idx]
            apply conn2
            simp
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
        rw [List.length_pos]
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
      simp only [eq_mp_eq_cast, id_eq, eq_mpr_eq_cast, List.length_cons, Fin.zero_eta,
        List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Nat.pred_eq_sub_one,
        Nat.add_one_sub_one]
      rw [get_cons]
      have applied_takeUntil_getLast_is_target := w.tail.takeUntil_getLast_is_target (w.val.head neq) h
      rw [List.getLast_eq_getElem] at applied_takeUntil_getLast_is_target
      rw [applied_takeUntil_getLast_is_target]
end Walk

namespace Graph
  def isAcyclic (G: Graph A) := ∀ (w: Walk G), ¬ w.isCycle

  def canReach (G : Graph A) (a b : A) : Prop := ∃ (w : Walk G) (neq : w.val ≠ []), (w.val.head neq) = a ∧ (w.val.getLast neq) = b

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
        simp only [List.tail_cons, List.append_nil]
        rw [w_last_b]
        rw [← w_head_b]
        simp only [this]
        unfold Walk.singleton
        simp
      | inr neq =>
        unfold Walk.concat
        rw [List.getLast_append' w_a_b.val w_b_c.val.tail neq]
        rw [List.tail_getLast]
        exact w_last_c

  lemma canReachWhenCanReachPred (G : Graph A) (a c : A) : ∀ b, b ∈ G.predecessors c -> G.canReach a b -> G.canReach a c := by
    intro a a_pred a_reaches_b
    unfold canReach at *
    rcases a_reaches_b with ⟨w, neq, get_a, get_b⟩
    exists w.appendSuccessor c (by
      unfold Walk.successors
      rw [List.getLast?_eq_getLast]
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

  -- TODO: it should be possible to make this computable
  noncomputable def verticesThatReach (G: Graph A) (b : A) : Finset A := G.vertices.toFinset.filter_nc (fun a => G.canReach a b)

  lemma verticesThatReachContainSelf (G: Graph A) (a : A) (mem: a ∈ G.vertices) : a ∈ G.verticesThatReach a := by
    unfold verticesThatReach
    rw [Finset.mem_filter_nc]
    constructor
    · apply canReach_refl
      apply mem
    · simp only [List.mem_toFinset]
      apply mem

  lemma verticesThatReachPredSubsetReachSelf (G : Graph A) (c : A) : ∀ b, b ∈ G.predecessors c -> G.verticesThatReach b ⊆ G.verticesThatReach c := by
    intro b b_pred
    rw [Finset.subset_iff]
    intro a
    unfold verticesThatReach
    rw [Finset.mem_filter_nc]
    intro ⟨reach, mem⟩
    rw [Finset.mem_filter_nc]
    constructor
    · apply G.canReachWhenCanReachPred a c b b_pred reach
    · exact mem

  lemma cannotReachPredIfAcyclic (G : Graph A) (acyclic : G.isAcyclic) (b : A) : ∀ a, a ∈ G.predecessors b -> ¬ G.canReach b a := by
    intro a a_pred contra
    unfold canReach at contra
    rcases contra with ⟨w, neq, get_b, get_a⟩
    cases eq : w.val with
    | nil => simp [eq] at neq
    | cons head tail =>
      apply acyclic (w.appendSuccessor b (by
        unfold Walk.successors
        rw [List.getLast?_eq_getLast]
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
        simp only [id_eq, eq_mpr_eq_cast, List.get_eq_getElem, Nat.pred_eq_sub_one]
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
    rw [Finset.mem_filter_nc] at contra
    exact contra.left

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
      apply mem_of_has_pred _ _ _ b_pred

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
              simp only [List.length_cons, Nat.add_one_sub_one, List.length_eq_zero] at contra
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
