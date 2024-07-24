import CertifyingDatalog.GraphValidation.Basic

variable {A: Type u} [DecidableEq A] [Hashable A]

def List.isWalk (l : List A) (G: Graph A) : Prop := (∀ (a:A), a ∈ l → a ∈ G.vertices) ∧ ∀ (i: ℕ), i > 0 → ∀ (g: i < l.length), l.get (Fin.mk i.pred (Nat.pred_lt_of_lt i l.length g)) ∈ G.successors (l.get (Fin.mk i g))

def Walk (G : Graph A) := {l : List A // l.isWalk G}

namespace Walk
  def singleton (G : Graph A) (a:A) (mem: a ∈ G.vertices) : Walk G := ⟨[a], by 
    unfold List.isWalk
    constructor
    . simp
      apply mem
    . simp
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

  def nextInCycle {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) : A := 
    match eq : w.val.indexOf b with 
    | .zero => w.val.get ⟨w.val.length - 2, by 
      rw [Nat.sub_lt_iff_lt_add']
      simp 
      unfold isCycle at cyc; apply Decidable.by_contra; intro contra; simp at contra; simp [contra] at cyc
    ⟩ 
      -- (by intro contra; simp [contra] at b_mem)
    | .succ n => w.val.get ⟨n, by apply Nat.lt_of_succ_le; rw [← eq]; apply List.indexOf_le_length⟩ 

  lemma nextInCycleIsInCycle {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) : w.nextInCycle cyc b ∈ w.val := by 
    unfold nextInCycle
    split <;> apply List.get_mem
  
  lemma nextInCycleIsSucc {G: Graph A} (w : Walk G) (cyc : w.isCycle) (b : A) (b_mem : b ∈ w.val) : w.nextInCycle cyc b ∈ G.successors b := by 
    unfold nextInCycle
    split
    case h_1 eq => 
      unfold isCycle at cyc
      have : ¬ w.val.length < 2 := by apply Decidable.by_contra; intro contra; simp at contra; simp [contra] at cyc
      simp [this] at cyc
      simp at eq
      simp [← eq] at cyc
      rw [cyc]
      have prop := w.prop.right
      apply prop
      simp
      simp at this
      apply Nat.lt_sub_of_add_lt
      apply Nat.lt_of_succ_le
      simp
      exact this
    case h_2 n eq => 
      have : b = w.val.get ⟨n.succ, by rw [← eq, List.indexOf_lt_length]; exact b_mem⟩ := by simp at eq; simp [← eq]
      simp [this]
      have prop := w.prop.right
      apply prop (n + 1)
      simp

  def successors {G: Graph A} (walk: Walk G) : List A := match walk.val.head? with 
    | .none => []
    | .some head => G.successors head

  def predecessors {G: Graph A} (walk: Walk G) : List A := match walk.val.getLast? with 
    | .none => []
    | .some last => G.vertices.filter (fun v => last ∈ G.successors v)

  def appendSuccessor {G: Graph A} (walk: Walk G) (succ : A) (is_succ : succ ∈ walk.successors) : Walk G := ⟨succ::walk.val, by 
    have walk_prop := walk.prop
    unfold List.isWalk
    unfold List.isWalk at walk_prop
    rcases walk_prop with ⟨subs,connected⟩
    constructor
    . intro b
      simp
      intro h
      cases h with
      | inl h =>
        rw [h]
        unfold successors at is_succ
        cases eq : walk.val.head? with 
        | none => simp [eq] at is_succ
        | some head => 
          apply Graph.mem_of_is_succ
          simp [eq] at is_succ
          apply is_succ
      | inr h =>
        apply subs
        simp
        apply h
    . intro i i_zero i_len
      cases i with
      | zero =>
        simp at i_zero
      | succ j =>
        rw [List.get_cons_succ]
        cases j with
        | zero =>
          simp
          unfold successors at is_succ
          cases eq : walk.val.head? with 
          | none => simp [eq] at is_succ
          | some head => 
            simp [eq] at is_succ
            rw [List.head?_eq_head] at eq
            injection eq with eq
            rw [List.get_mk_zero]
            rw [eq]
            apply is_succ
        | succ k =>
          simp
          specialize connected (Nat.succ k)
          simp at connected
          simp at i_len
          specialize connected i_len
          apply connected
  ⟩ 

  def prependPredecessor {G: Graph A} (walk: Walk G) (pred : A) (is_pred : pred ∈ walk.predecessors) : Walk G := ⟨walk.val++[pred], by 
    unfold List.isWalk
    constructor
    . intro a a_elem
      simp at a_elem
      cases a_elem with 
      | inl h => apply walk.prop.left; exact h
      | inr h => 
        unfold predecessors at is_pred
        cases eq : walk.val.getLast? with
        | none => simp [eq] at is_pred
        | some last =>
          simp [eq] at is_pred
          rw [h]
          apply List.mem_of_mem_filter 
          apply is_pred
    . intro i i_zero i_len
      have prop := walk.prop.right
      cases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i_len) with 
      | inl i_lt => 
        rw [List.get_append]
        rw [List.get_append]
        apply prop
        apply i_zero
        simp at i_lt
        apply i_lt
      | inr i_eq => 
        unfold predecessors at is_pred
        cases eq : walk.val.getLast? with
        | none => simp [eq] at is_pred
        | some last =>
          simp at i_eq
          simp [eq] at is_pred
          rw [List.mem_filter] at is_pred
          have ⟨_, last_succ_of_pred⟩ := is_pred 
          simp at last_succ_of_pred
          rw [List.get_append]
          rw [List.get_append_right]
          simp
          have : walk.val ≠ [] := by 
            intro contra
            simp [contra] at eq
          rw [List.getLast?_eq_getLast walk.val this] at eq
          injection eq with eq
          rw [List.getLast_eq_get] at eq
          simp [i_eq]
          rw [eq]
          apply last_succ_of_pred
          rw [← i_eq]
          intro contra
          simp at contra
          rw [i_eq]
          simp
          rw [← i_eq]
          apply Nat.pred_lt'
          apply i_zero
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
    . intro a a_mem
      apply subs
      apply List.mem_of_mem_tail
      exact a_mem
    . intro i i_gt_0 i_lt_len
      specialize conn (Nat.succ i)
      simp at conn
      simp at i_lt_len
      have : 0 < walk.val.length := by
        apply lt_trans
        apply i_gt_0
        apply Nat.lt_of_lt_pred
        apply i_lt_len
      rw [walk.val.tail_get this ⟨i.pred, _⟩]
      rw [walk.val.tail_get this ⟨i, _⟩]
      simp [Nat.sub_one_add_one_eq_of_pos i_gt_0]
      apply conn
      apply i_lt_len
      apply lt_trans
      apply Nat.pred_lt'
      apply i_gt_0
      apply i_lt_len
  ⟩  

  lemma head_in_tail_successors {G : Graph A} (w : Walk G) (neq : w.val.tail ≠ []) : w.val.head (by intro contra; rw [contra] at neq; simp at neq) ∈ w.tail.successors := by 
    unfold successors
    rw [List.head?_eq_head w.tail.val neq]
    simp
    have : 0 < w.val.length := by apply Decidable.by_contra; intro contra; simp at contra; rw [contra] at neq; simp at neq
    have this2 : 0 < w.tail.val.length := by apply Decidable.by_contra; intro contra; simp at contra; unfold tail at contra; simp at contra; rw [contra] at neq; simp at neq
    rw [← List.get_mk_zero this]
    rw [← List.get_mk_zero this2]
    unfold Walk.tail
    rw [List.tail_get w.val this ⟨0, _⟩]
    apply w.prop.right 1 (by simp)
    rw [← List.length_tail]
    unfold tail at this2
    exact this2

  def take {G : Graph A} (walk : Walk G) (n : Nat) : Walk G := ⟨walk.val.take n, by
    have prop := walk.prop
    unfold List.isWalk at *
    rcases prop with ⟨subs, conn⟩
    constructor
    . intro a a_in_take
      apply subs
      apply List.mem_of_mem_take
      exact a_in_take
    . intro i i_gt_0 i_lt_len
      rw [List.get_take'] 
      rw [List.get_take'] 
      apply conn
      apply i_gt_0
  ⟩ 

  def takeUntil {G : Graph A} (walk : Walk G) (a : A) : Walk G := walk.take (walk.val.indexOf a + 1)

  lemma takeUnil_ne_of_ne {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).val ≠ [] := by 
    unfold takeUntil
    intro contra
    unfold take at contra
    simp at contra
    contradiction

  lemma takeUntil_head_same {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).val.head (by apply w.takeUnil_ne_of_ne ne) = w.val.head ne := by 
    unfold takeUntil
    unfold take
    rw [List.take_head _ ne _ _]
    simp
  
  lemma takeUntil_successors_same {G : Graph A} (w : Walk G) (ne : w.val ≠ []) (a : A) : (w.takeUntil a).successors = w.successors := by 
    unfold successors
    rw [List.head?_eq_head _ ne]
    rw [List.head?_eq_head _ (by apply takeUnil_ne_of_ne _ ne)]
    simp
    rw [takeUntil_head_same]

  lemma takeUntil_getLast_is_target {G : Graph A} (w : Walk G) (a : A) (mem : a ∈ w.val) : (w.takeUntil a).val.getLast (by apply takeUnil_ne_of_ne; intro contra; rw [contra] at mem; simp at mem) = a := by 
    unfold takeUntil
    rw [List.getLast_eq_get]
    unfold Walk.take
    rw [List.get_take'] 
    simp [List.length_take_of_le (by 
      show w.val.indexOf a + 1 ≤ w.val.length
      apply Nat.succ_le_of_lt
      rw [List.indexOf_lt_length]
      exact mem
    )]

  def concat {G: Graph A} (w1 w2: Walk G) (w1_neq : w1.val ≠ []) (w2_neq : w2.val ≠ []) (h : w2.val.getLast w2_neq = w1.val.head w1_neq) : Walk G := ⟨w2.val++w1.val.tail, by
    have ⟨subs1, conn1⟩ := w1.tail.prop
    have ⟨subs2, conn2⟩ := w2.prop
    unfold List.isWalk
    constructor
    . intro a a_in_append
      simp at a_in_append
      cases a_in_append
      . apply subs2; assumption
      . apply subs1; assumption
    . intro i i_gt_0 i_lt_len
      cases Decidable.em (i < w2.val.length) with 
      | inl w2_case =>
        rw [List.get_append_left _ _ w2_case]
        rw [List.get_append_left _ _ (by apply lt_trans; apply Nat.pred_lt'; apply i_gt_0; exact w2_case)]
        apply conn2
        exact i_gt_0
      | inr w1_case =>
        let j := i - w2.val.length
        have i_j_eq : i = j + w2.val.length := by 
          apply Nat.eq_add_of_sub_eq
          simp at w1_case
          apply w1_case
          simp [j]
        cases eq : j with 
        | succ k => 
          rw [List.get_append_right _ _ w1_case]
          rw [List.get_append_right _ _ (by 
            apply Nat.not_lt_of_ge
            rw [i_j_eq]
            rw [eq]
            simp
          )]
          simp only [Nat.pred_sub]
          apply conn1
          rw [i_j_eq]
          rw [eq]
          simp
          rw [Nat.sub_lt_iff_lt_add]
          rw [List.length_append] at i_lt_len
          apply lt_trans; apply Nat.pred_lt'; apply i_gt_0; apply i_lt_len
          rw [i_j_eq]
          rw [eq]
          simp
          rw [Nat.sub_lt_iff_lt_add]
          rw [List.length_append] at i_lt_len
          apply i_lt_len
          apply Nat.ge_of_not_lt
          exact w1_case
        | zero => 
          cases Decidable.em (w1.val.length > 1) with
          | inl w1_len_gt_one =>
            simp [eq] at i_j_eq
            simp [i_j_eq]
            rw [List.get_append_left _ _ (by rw [← Nat.pred_eq_sub_one]; apply Nat.pred_lt'; rw [← i_j_eq]; apply i_gt_0)]
            rw [List.get_append_right _ _ (by simp)]
            simp
            rw [← List.getLast_eq_get]
            rw [h]
            rw [← List.get_mk_zero]
            have ⟨_, w1_prop⟩ := w1.prop
            have : 0 < w1.val.length - 1 := by 
              apply Nat.lt_sub_of_add_lt
              simp
              apply w1_len_gt_one
            rw [List.tail_get w1.val (by cases eq2 : w1.val; simp [eq2] at w1_neq; simp) ⟨0, this⟩]
            specialize w1_prop 1 (by simp) (by apply w1_len_gt_one)
            apply w1_prop
            simp
            apply Nat.lt_sub_of_add_lt
            simp
            apply w1_len_gt_one
          | inr w1_len_leq_one => 
            have : w1.val.tail = [] := by 
              simp at w1_len_leq_one
              unfold List.tail
              cases eq2 : w1.val with 
              | nil => simp
              | cons head tail => simp; rw [eq2] at w1_len_leq_one; simp at w1_len_leq_one; exact w1_len_leq_one
            have : w2.val ++ w1.val.tail = w2.val := by rw [this]; simp
            have : ∀ i, (w2.val ++ w1.val.tail).get i = w2.val.get ⟨i, (by have isLt := i.isLt; simp [this] at isLt; exact isLt)⟩ := by intro i; apply List.get_of_eq; exact this
            rw [this]
            rw [this]
            apply conn2
            exact i_gt_0
  ⟩ 

  lemma isCycle_of_head_in_tail {G : Graph A} (w : Walk G) (neq : w.val ≠ []) (h : w.val.head neq ∈ (w.tail).val) : ((w.tail.takeUntil (w.val.head neq)).appendSuccessor (w.val.head neq) (by 
      rw [takeUntil_successors_same]
      apply head_in_tail_successors
      intro contra; unfold tail at h; simp [contra] at h
      intro contra; simp [contra] at h
    )).isCycle := by 
    unfold isCycle
    unfold appendSuccessor
    simp
    split
    case isTrue contra => 
      have : 0 < (w.tail.takeUntil (w.val.head neq)).val.length := by 
        rw [List.length_pos]
        apply takeUnil_ne_of_ne
        intro contra; rw [contra] at h; simp at h
      have : ¬ (w.tail.takeUntil (w.val.head neq)).val.length + 1 < 2 := by 
        apply Nat.not_lt_of_le
        simp
        apply Nat.succ_le_of_lt
        apply this
      contradiction
    case isFalse len_ge_2 =>
      have : (w.tail.takeUntil (w.val.head neq)).val.length - 1 + 1 = (w.tail.takeUntil (w.val.head neq)).val.length := by 
        rw [Nat.sub_one_add_one_eq_of_pos]
        apply List.length_pos_of_ne_nil
        apply takeUnil_ne_of_ne
        intro contra; rw [contra] at h; simp at h
      have get_cons := @List.get_cons_succ _ ((w.tail.takeUntil (w.val.head neq)).val.length - 1) (w.val.head neq) (w.tail.takeUntil (w.val.head neq)).val (by rw [this]; simp)
      simp only [this] at get_cons
      rw [get_cons]
      rw [← List.getLast_eq_get]
      rw [takeUntil_getLast_is_target]
      exact h
end Walk

namespace Graph
  def isAcyclic (G: Graph A) := ∀ (w: Walk G), ¬ w.isCycle

  def canReach (G : Graph A) (a b : A) : Prop := ∃ (w : Walk G) (neq : w.val ≠ []), (w.val.head neq) = b ∧ (w.val.getLast neq) = a

  lemma canReach_refl (G : Graph A) (a : A) (mem: a ∈ G.vertices) : G.canReach a a := by
    unfold canReach
    exists Walk.singleton G a mem
    simp [Walk.singleton]

  lemma canReach_succ (G : Graph A) (a b : A) (b_succ: b ∈ G.successors a) : G.canReach a b := by
    unfold canReach
    exists ((Walk.singleton G a (by apply mem_of_has_succ; apply b_succ)).appendSuccessor b (by 
      unfold Walk.singleton
      unfold Walk.successors
      simp
      apply b_succ
    ))
    exists (by simp [Walk.singleton, Walk.appendSuccessor])

  lemma canReach_trans (G : Graph A) (a b c : A) : G.canReach a b ∧ G.canReach b c -> G.canReach a c := by
    unfold canReach
    intro ⟨walk_a_b, walk_b_c⟩
    rcases walk_a_b with ⟨w_a_b, w_a_b_neq, w_head_b, w_last_a⟩ 
    rcases walk_b_c with ⟨w_b_c, w_b_c_neq, w_head_c, w_last_b⟩
    -- exists w_a_b.append w_b_c
    exists (w_a_b.concat w_b_c w_a_b_neq w_b_c_neq (by rw [w_head_b]; rw [w_last_b]))
    exists (by 
      unfold Walk.concat
      apply List.append_ne_nil_of_ne_nil_left
      exact w_b_c_neq
    )
    constructor
    . unfold Walk.concat
      rw [List.head_append _ _ w_b_c_neq]
      exact w_head_c
    . cases Decidable.em (w_a_b.val.tail = []) with
      | inl eq =>
        have : w_a_b = Walk.singleton G a (by apply Walk.isSubsetOfVertices; rw [← w_last_a]; apply List.getLast_mem) := by 
          unfold Walk.singleton
          rcases w_a_b with ⟨list, prop⟩
          cases list with 
          | nil => simp at w_a_b_neq
          | cons head tail => 
            simp at eq
            simp [eq]
            simp [eq] at w_last_a
            simp [w_last_a]
        unfold Walk.concat
        simp [this]
        unfold Walk.singleton
        simp
        rw [w_last_b]
        rw [← w_head_b]
        simp [this]
        unfold Walk.singleton
        simp
      | inr neq =>
        unfold Walk.concat
        rw [List.getLast_append' w_b_c.val w_a_b.val.tail neq]
        rw [List.tail_getLast]
        exact w_last_a

  lemma canReachWhenCanReachFromSucc (G : Graph A) (a c : A) : ∀ b, b ∈ G.successors a -> G.canReach b c -> G.canReach a c := by 
    intro b b_succ b_reaches_c
    unfold canReach at *
    rcases b_reaches_c with ⟨w, neq, get_c, get_b⟩
    exists w.prependPredecessor a (by 
      unfold Walk.predecessors
      rw [List.getLast?_eq_getLast]
      simp
      rw [List.mem_filter]
      constructor
      . apply mem_of_has_succ
        apply b_succ
      . simp
        rw [get_b]
        exact b_succ
    )
    unfold Walk.prependPredecessor
    exists (by simp)
    constructor
    . rw [← get_c]
      rw [List.head_append]
    . simp

  lemma canReach_iff (G : Graph A) (a c : A) : G.canReach a c ↔ (a ∈ G.vertices ∧ a = c) ∨ ∃ b, b ∈ G.successors a ∧ G.canReach b c := by 
    constructor
    . intro h 
      unfold canReach at h
      rcases h with ⟨w, neq, head, last⟩
      cases eq : w.val with 
      | nil => simp [eq] at neq
      | cons d ds => 
        cases ds with 
        | nil => 
          apply Or.inl
          simp [eq] at head
          simp [eq] at last
          constructor
          . apply w.prop.left
            rw [eq]
            rw [last]
            simp
          . rw [← head]
            rw [last]
        | cons _ _ => 
          apply Or.inr
          have : 0 < w.val.length - 1 := by rw [eq]; simp
          exists w.val.get ⟨w.val.length.pred.pred, by apply Nat.lt_of_lt_of_le; apply Nat.pred_lt'; apply this; apply Nat.pred_le⟩ 
          constructor
          . rw [← last]; rw [List.getLast_eq_get]; apply w.prop.right; simp; exact this
          . unfold canReach
            exists w.take (w.val.length - 1)
            exists (by intro contra; unfold Walk.take at contra; rw [List.take_eq_nil_iff] at contra; cases contra; contradiction; case inr h => rw [h] at this; contradiction)
            constructor
            . unfold Walk.take
              rw [List.take_head w.val neq _ this]
              exact head
            . unfold Walk.take
              rw [List.take_getLast w.val neq ⟨w.val.length - 1, by apply Nat.lt_succ_of_lt; apply Nat.pred_lt'; apply Nat.lt_of_lt_pred; apply this⟩ this]
              simp
    . intro h 
      cases h with 
      | inl h => rw [← h.right]; apply canReach_refl; apply h.left
      | inr h => 
        rcases h with ⟨b, succ, reach⟩ 
        apply canReach_trans
        constructor
        . apply canReach_succ; apply succ
        . exact reach

  -- TODO: it should be possible to make this computable
  noncomputable def reachableFrom (G: Graph A) (a : A) : Finset A := Finset.filter_nc (fun b => G.canReach a b) G.vertices.toFinset

  lemma reachableFromSelf (G: Graph A) (a : A) (mem: a ∈ G.vertices) : a ∈ G.reachableFrom a := by 
    unfold reachableFrom
    rw [Finset.mem_filter_nc]
    constructor
    apply canReach_refl
    apply mem
    simp
    apply mem

  lemma reachableFromSupersetReachableFromSucc (G : Graph A) (a : A) : ∀ b, b ∈ G.successors a -> G.reachableFrom b ⊆ G.reachableFrom a := by 
    intro b b_succ
    rw [Finset.subset_iff]
    intro c
    unfold reachableFrom
    rw [Finset.mem_filter_nc]
    intro ⟨reach, mem⟩
    rw [Finset.mem_filter_nc]
    constructor
    . apply G.canReachWhenCanReachFromSucc a c b b_succ reach
    . exact mem
  
  lemma succCannotReachSelfIfAcyclic (G : Graph A) (acyclic : G.isAcyclic) (a : A) : ∀ b, b ∈ G.successors a -> ¬ G.canReach b a := by 
    intro b b_succ contra
    unfold canReach at contra
    rcases contra with ⟨w, neq, get_c, get_b⟩
    cases eq : w.val with 
    | nil => simp [eq] at neq
    | cons head tail => 
      apply acyclic (w.prependPredecessor a (by 
        unfold Walk.predecessors
        rw [List.getLast?_eq_getLast]
        simp
        rw [List.mem_filter]
        constructor
        . apply mem_of_has_succ
          apply b_succ
        . simp
          rw [get_b]
          exact b_succ
      ))
      unfold Walk.isCycle
      split
      case isTrue h => 
        unfold Walk.prependPredecessor at h; simp at h
        rw [eq] at h
        have contra : ¬ List.length (head :: tail) + 1 < 2 := by simp
        exact contra h
      case isFalse h =>
        simp
        unfold Walk.prependPredecessor
        rw [List.get_append_left]
        rw [List.get_append_right]
        simp
        rw [← get_c]
        apply List.get_mk_zero
        simp [eq]
        simp
        simp

  lemma selfNotReachableFromSuccIfAcyclic (G : Graph A) (acyclic : G.isAcyclic) (a : A) : ∀ b, b ∈ G.successors a -> ¬ a ∈ G.reachableFrom b := by 
    intro b b_succ contra
    apply G.succCannotReachSelfIfAcyclic acyclic a b b_succ
    unfold reachableFrom at contra
    rw [Finset.mem_filter_nc] at contra
    exact contra.left

  lemma reachableFromStrictSupersetReachableFromSucc (G : Graph A) (acyclic : G.isAcyclic) (a : A) : ∀ b, b ∈ G.successors a -> G.reachableFrom b ⊂ G.reachableFrom a := by 
    intro b b_succ
    rw [Finset.ssubset_def]
    constructor
    . apply G.reachableFromSupersetReachableFromSucc a b b_succ
    . intro contra
      rw [Finset.subset_iff] at contra
      apply G.selfNotReachableFromSuccIfAcyclic acyclic a b b_succ
      apply contra
      apply reachableFromSelf
      apply mem_of_has_succ
      apply b_succ

  def reachesCycle (G: Graph A) (a : A) := ∃ (w : Walk G), w.isCycle ∧ ∃ (b: A), b ∈ w.val ∧ G.canReach a b

  lemma notReachesCycleIffSuccessorsNotReachCycle (G: Graph A) (a : A) : ¬ G.reachesCycle a ↔ ∀ (b : A), b ∈ G.successors a → ¬ G.reachesCycle b :=
  by
    constructor
    . intro a_not_reach b b_succ b_reach
      apply a_not_reach
      unfold reachesCycle at *
      rcases b_reach with ⟨w, w_cycle, b', b'_in_w, b_reach_b'⟩
      exists w
      constructor
      . exact w_cycle
      . exists b'
        constructor
        . exact b'_in_w
        . apply canReach_trans
          constructor
          . apply canReach_succ; apply b_succ
          . exact b_reach_b'
    . intro h contra
      unfold reachesCycle at contra
      rcases contra with ⟨cyc, cyc_isCycle, b, b_mem_cyc, reach⟩ 
      unfold canReach at reach
      rcases reach with ⟨w, w_neq, w_b, w_a⟩ 
      cases Decidable.em (a = b) with 
      | inl mem => 
        let next_after_b := cyc.nextInCycle cyc_isCycle b
        let next_after_next := cyc.nextInCycle cyc_isCycle next_after_b
        apply h next_after_b
        rw [mem]; apply Walk.nextInCycleIsSucc; exact b_mem_cyc
        unfold reachesCycle
        exists cyc
        constructor
        . exact cyc_isCycle
        . exists next_after_next
          constructor
          . apply Walk.nextInCycleIsInCycle
          . apply canReach_succ; apply Walk.nextInCycleIsSucc; apply Walk.nextInCycleIsInCycle
      | inr nmem =>
        have : 0 < w.val.length - 1 := by
          apply Decidable.by_contra
          intro contra
          simp at contra
          cases eq : w.val with 
          | nil => simp [eq] at w_neq
          | cons c cs =>
            have : cs = [] := by 
              rw [eq] at contra
              simp at contra
              exact contra
            rw [this] at eq
            simp [eq] at w_b
            simp [eq] at w_a
            rw [w_a] at w_b
            apply nmem
            apply w_b
        have this2 : w.val.length - 1 < w.val.length := by apply Nat.pred_lt'; apply Nat.lt_of_lt_pred; apply this 
        apply h (w.val.get ⟨w.val.length - 2, by apply Nat.lt_of_le_of_lt; apply Nat.pred_le; exact this2⟩)
        have prop := w.prop.right (w.val.length - 1) (by apply this) this2
        rw [List.getLast_eq_get] at w_a
        rw [w_a] at prop
        apply prop
        unfold reachesCycle
        exists cyc
        constructor
        . exact cyc_isCycle
        . exists b
          constructor
          . exact b_mem_cyc
          . unfold canReach
            exists w.take (w.val.length - 1)
            exists (by unfold Walk.take; intro contra; rw [List.take_eq_nil_iff] at contra; cases contra; contradiction; case inr h => rw [h] at this; contradiction)
            constructor
            . unfold Walk.take
              rw [List.take_head w.val w_neq]
              apply w_b
              exact this
            . unfold Walk.take
              rw [List.take_getLast w.val w_neq ⟨w.val.length - 1, by apply Nat.lt_succ_of_lt; exact this2⟩]
              simp
              have this3 : w.val.length - 1 - 1 = w.val.length - 2 := by tauto
              simp [this3]
              simp [this]


  lemma acyclicIffAllNotReachCycle (G: Graph A): isAcyclic G ↔ ∀ (a:A), ¬ G.reachesCycle a := by 
    constructor
    . intro acyclic a contra
      unfold reachesCycle at contra
      unfold isAcyclic at acyclic
      rcases contra with ⟨_, cyc, _⟩
      apply acyclic
      apply cyc
    . intro h
      unfold isAcyclic
      intro w cyc
      let head := (w.val.head (by intro contra; unfold Walk.isCycle at cyc; simp [contra] at cyc))
      apply h head
      unfold reachesCycle
      exists w
      constructor
      . exact cyc
      . exists head
        have : head ∈ w.val := by apply List.head_mem
        constructor
        . exact this
        . apply canReach_refl; apply w.prop.left; exact this
end Graph
