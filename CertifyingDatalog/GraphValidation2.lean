import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation
import Mathlib.Data.List.Card
import Mathlib.Data.Finset.Card


structure Graph (A: Type) where
  (vertices: List A)
  (predecessors: A → List A)
  (complete: ∀ (a:A), a ∈ vertices →  ∀ (a':A), a' ∈ predecessors a → a' ∈ vertices)


variable {A: Type}[DecidableEq A]

lemma pred_lt (n m: ℕ) (h:n < m ): n.pred < m :=
by
  cases n with
  | zero =>
    unfold Nat.pred
    simp
    apply h
  | succ n =>
    unfold Nat.pred
    simp
    apply Nat.lt_of_succ_lt h

lemma Nat.pred_gt_zero_iff (n: ℕ): n.pred > 0 ↔ n ≥ 2 :=
by
  cases n with
  | zero =>
    simp
  | succ n =>
    cases n with
    | zero =>
      simp
    | succ m =>
      simp
      rw [Nat.two_le_iff]
      simp


def isPath (l: List A) (G: Graph A): Prop :=
 ( ∀ (a:A), a ∈ l → a ∈ G.vertices ) ∧ ∀ (i: ℕ)(h: i > 0) (g: i < l.length), l.get (Fin.mk i.pred (pred_lt i l.length g)) ∈ G.predecessors (l.get (Fin.mk i g) )

 lemma isPathSingleton (G: Graph A) (a:A) (mem: a ∈ G.vertices): isPath [a] G :=
by
  unfold isPath
  constructor
  simp
  apply mem

  simp
  intro i i_gt_0 i_0
  simp [i_0] at i_gt_0


lemma ge_two_im_gt_zero (n: ℕ) (h: n ≥ 2): n > 0 :=
by
  cases n with
  | zero =>
    simp at h
  | succ m =>
    simp

def isCircle (l: List A) (G: Graph A): Prop :=
  if h: l.length < 2
  then False
  else
    have l_not_zero: 0 < l.length :=
    by
      cases ll: l.length with
      | zero =>
        rw [ll] at h
        simp at h
      | succ n =>
        simp


  isPath l G ∧ l.get (Fin.mk 0 l_not_zero) = l.get (Fin.mk l.length.pred (Nat.pred_lt (Ne.symm (Nat.ne_of_lt l_not_zero))))


def isAcyclic (G: Graph A) := ∀ (l: List A), ¬ isCircle l G

lemma isAcyclicIffAllVerticesAreNotInCircle (G: Graph A): isAcyclic G ↔ ∀ (a:A), a ∈ G.vertices → ∀ (c: List A), isCircle c G → a ∉ c :=
by
  constructor
  intro h
  intro a _ c circle
  unfold isAcyclic at h
  specialize h c
  exact absurd circle h

  intro h
  by_contra p
  unfold isAcyclic at p
  push_neg at p
  rcases p with ⟨c, circle⟩
  have mem_c: ∃ (a:A), a ∈ G.vertices ∧ a ∈ c
  unfold isCircle at circle
  by_cases c_len: List.length c < 2
  simp [c_len] at circle
  simp [c_len] at circle
  rcases circle with ⟨path, _⟩
  unfold isPath at path
  rcases path with ⟨mem,_⟩
  push_neg at c_len
  use (List.get c (Fin.mk 0 (ge_two_im_gt_zero c.length c_len)))
  constructor
  apply mem
  rw [List.mem_iff_get]
  simp
  rw [List.mem_iff_get]
  simp

  rcases mem_c with ⟨b, b_G, b_c⟩
  specialize h b b_G c circle
  exact absurd b_c h


lemma NotInCircleIfAllPredecessorsAreNot (a: A) (G: Graph A) (h: ∀ (b:A), b ∈ G.predecessors a → ¬ (∃ (c: List A), isCircle c G ∧ b ∈ c) ): ∀ (c: List A), isCircle c G  → ¬  a ∈ c :=
by
  by_contra p
  push_neg at p
  rcases p with ⟨c, circle, a_c⟩
  have circle': isCircle c G
  apply circle


  unfold isCircle at circle
  by_cases c_length: c.length < 2
  simp [c_length] at circle

  simp [c_length] at circle
  rcases circle with ⟨path, ends⟩
  unfold isPath at path
  rcases path with ⟨subs, connected⟩
  rw [List.mem_iff_get] at a_c
  rcases a_c with ⟨n, c_n⟩

  by_cases h_n: n.val = 0
  specialize connected c.length.pred
  simp at c_length

  have pred_n_gt_0: c.length.pred > 0
  rw [Nat.pred_gt_zero_iff]
  apply c_length

  specialize connected pred_n_gt_0
  have pred_lt_self: Nat.pred (List.length c) < List.length c
  apply Nat.pred_lt
  by_contra p
  rw [p] at c_length
  simp at c_length
  specialize connected pred_lt_self
  have predpred_lt_self: Nat.pred (Nat.pred (List.length c)) < List.length c
  apply Nat.lt_of_le_of_lt (m:= Nat.pred (List.length c))
  apply Nat.pred_le
  apply pred_lt_self
  specialize h (List.get c (Fin.mk (Nat.pred (Nat.pred (List.length c))) predpred_lt_self))
  rw [← ends] at connected

  have h_n': n = { val := 0, isLt := (_ : 0 < List.length c) }
  rw [Fin.mk_eq_mk]
  apply h_n
  apply ge_two_im_gt_zero
  apply c_length

  rw [← h_n', c_n] at connected
  specialize h connected
  push_neg at h
  specialize h c circle'
  simp [List.mem_iff_get] at h

  --negative case
  specialize connected n.val
  simp at connected
  have zero_lt_n: 0 < n.val
  cases q: n.val with
  | zero =>
    simp [q] at h_n
  | succ m =>
    simp
  specialize connected zero_lt_n n.isLt
  specialize h (List.get c (Fin.mk n.val.pred (pred_lt n.val c.length n.isLt)))
  rw [← c_n] at h
  specialize h connected
  push_neg at h
  specialize h c circle'
  simp [List.mem_iff_get] at h

lemma isPath_extends_predecessors {a: A} {l: List A} {G: Graph A} (path: isPath (a::l) G): ∀ (b:A), b ∈ (G.predecessors a) → isPath (b::a::l) G :=
by
  intro b b_mem
  unfold isPath
  unfold isPath at path
  rcases path with ⟨subs,connected⟩
  constructor
  intro a'
  simp

  intro h
  cases h with
  | inl h =>
    rw [h]
    apply G.complete a
    apply subs
    simp
    apply b_mem
  | inr h =>
    apply subs
    simp
    apply h

  intro i i_zero i_len
  cases i with
  | zero =>
    simp at i_zero
  | succ j =>
    rw [List.get_cons_succ]
    cases j with
    | zero =>
      simp
      apply b_mem
    | succ k =>
      simp
      specialize connected (Nat.succ k)
      simp at connected
      simp at i_len
      have g: Nat.succ k < List.length (a :: l)
      rw [Nat.succ_lt_succ_iff] at i_len
      simp
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      apply i_len
      specialize connected g
      apply connected

lemma isPathImplSubset {l: List A} {G: Graph A} (path: isPath l G ): l.toFinset ⊆ G.vertices.toFinset :=
by
  rw [Finset.subset_iff]
  unfold isPath at path
  rcases path with ⟨h,_⟩
  simp [List.mem_toFinset]
  apply h

lemma isPath_of_cons {a: A} {l:List A} {G:Graph A} (path: isPath (a::l) G): isPath l G :=
by
  unfold isPath at *
  rcases path with ⟨subs, conn⟩
  constructor
  intro a' a'_l
  apply subs
  simp
  right
  apply a'_l

  intro i i_zero i_len
  specialize conn (Nat.succ i)
  simp at conn
  have g:  Nat.succ i < List.length (a :: l)
  simp
  apply Nat.succ_lt_succ
  apply i_len
  specialize conn g
  cases i with
  | zero =>
    simp at i_zero
  | succ j =>
    rw [List.get_cons_succ] at conn
    apply conn

lemma removeFrontOfLtMin (a b c: ℕ) (hab: b ≤ a) (hac: c ≤ a) : a - b < a -c ↔ b > c :=
by
  induction a with
  | zero =>
    simp at *
    rw [hab, hac]
  | succ n ih =>
    cases hab with
    | refl =>
      cases hac with
      | refl =>
        simp
      | step hc =>
        simp
    | step hb =>
      cases hac with
      | refl =>
        simp
        apply Nat.le_succ_of_le hb
      | step hc =>
        specialize ih hb hc
        rw [← ih]
        rw [Nat.succ_sub hb, Nat.succ_sub hc]
        rw [Nat.succ_lt_succ_iff]

lemma CardOfGraphSubCardOfPathZeroIffPathContainsEveryVertex (G: Graph A) (p: List A) (path: isPath p G): Finset.card (List.toFinset G.vertices) - Finset.card (List.toFinset p) = Nat.zero ↔ ∀ (a:A), a ∈ G.vertices → a ∈ p :=
by
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  intro h
  have subs: (List.toFinset p) ⊆ List.toFinset G.vertices
  apply isPathImplSubset path

  rw [Finset.subset_iff_eq_of_card_le h] at subs
  intro a
  rw [← List.mem_toFinset, ← List.mem_toFinset, subs]
  simp

  intro h
  apply Finset.card_le_of_subset
  rw [Finset.subset_iff]
  intro a
  rw [List.mem_toFinset, List.mem_toFinset]
  apply h

def getSubListToMember (l: List A) (a: A) (mem: a ∈ l): List A :=
  match l with
  | [] =>
    have h: False :=
    by
      simp at mem

    False.elim h
  | hd::tl =>
    if p: a = hd
    then [hd]
    else
      have mem': a ∈ tl :=
      by
        simp[p] at mem
        apply mem
      hd::getSubListToMember tl a mem'

lemma getSubListToMemberPreservesFront (hd a hd': A) (tl tl': List A) (mem: a ∈ hd'::tl') (result: getSubListToMember (hd'::tl') a mem = hd::tl): hd' = hd :=
by
  unfold getSubListToMember at result
  by_cases a_hd: a = hd'
  all_goals{
  simp [a_hd] at result
  simp [result]
  }



lemma getSubListToMemberPreservesPath (l: List A) (a:A) (mem: a ∈ l) (G: Graph A) (path: isPath l G): isPath (getSubListToMember l a mem) G :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    apply isPathSingleton
    unfold isPath at path
    simp [path]

    simp [a_hd]
    unfold isPath
    admit


lemma frontRepetitionInPathImpliesCircle (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G) (mem: a ∈ visited): isCircle (a::(getSubListToMember visited a mem)) G :=
by
  sorry

def dfsStep (G: Graph A) (a:A) (visited: List A) (path: isPath (a::visited) G): Except String Unit :=
  if h: a ∈ visited
  then Except.error "Circle detected"
  else
      List.map_except_unit (G.predecessors a).attach (fun ⟨x, _h⟩ => dfsStep G x (a::visited) (isPath_extends_predecessors path x _h ) )
termination_by dfsStep G a visited path => ((List.toFinset G.vertices).card - (List.toFinset visited).card)
decreasing_by
  simp_wf
  rw [← List.mem_toFinset] at h
  rw [removeFrontOfLtMin]
  simp
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use a
  apply Finset.card_le_of_subset
  rw [Finset.subset_iff]
  intro x
  simp
  intro p
  rw [← List.mem_toFinset]
  unfold isPath at path
  apply isPathImplSubset path
  simp
  apply p

  apply Finset.card_le_of_subset
  apply isPathImplSubset
  apply isPath_of_cons path

lemma dfsStepUnitIffNoCircleWithA (G: Graph A) (a:A) (visited: List A) (path: isPath (a::visited) G): dfsStep G a visited path = Except.ok () ↔ ¬ ∃ (c: List A), isCircle c G ∧ a ∈ c :=
by
  induction' h:((List.toFinset G.vertices).card - (List.toFinset visited).card) with n ih generalizing visited a

  -- base: there is a circle as every vertex is in the path
  rw [CardOfGraphSubCardOfPathZeroIffPathContainsEveryVertex G visited (isPath_of_cons path)] at h
  unfold dfsStep
  specialize h a
  have a_mem: a ∈ G.vertices
  unfold isPath at path
  rcases path with ⟨path,_⟩
  apply path
  simp
  specialize h a_mem
  simp [h]
  use (a :: getSubListToMember visited a h)
  simp
  apply frontRepetitionInPathImpliesCircle a G visited path h

  unfold dfsStep
  by_cases h: a ∈ visited
  simp [h]
  use (a::(getSubListToMember visited a h))
  constructor
  apply frontRepetitionInPathImpliesCircle
  apply path
  simp

  simp [h]
  rw [List.map_except_unitIsUnitIffAll]
  simp [NotInCircleIfAllPredecessorsAreNot]







def validateAndStep (G: Graph A) (f: A → List A → Except String Unit) (a:A) (mem: a ∈ G.vertices): Except String Unit:=
  match f a (G.predecessors a) with
  | Except.error e => Except.error e
  | Except.ok _ =>
    dfsStep G a [] (isPathSingleton G a mem)

lemma validateAndStepSemantics (G: Graph A) (f: A → List A → Except String Unit) (a:A) (mem: a ∈ G.vertices): validateAndStep G f a mem = Except.ok () ↔ f a (G.predecessors a) = Except.ok () ∧ ¬ ∃ (c: List A), isCircle c G ∧ a ∈ c :=
by
  unfold validateAndStep
  cases f a (G.predecessors a) with
  | error e =>
    simp
  | ok _ =>
    simp
    rw [dfsStepUnitIffNoCircleWithA]
    simp

def dfs (G: Graph A) (f: A → List A → Except String Unit): Except String Unit :=
  List.map_except_unit (G.vertices).attach (fun ⟨x, _h⟩ => validateAndStep G f x _h)

lemma dfs_semantics (G: Graph A) (f: A → List A → Except String Unit): dfs G f = Except.ok () ↔ isAcyclic G ∧ ∀ (a:A), a ∈ G.vertices → f a (G.predecessors a) = Except.ok () :=
by
  unfold dfs
  rw [List.map_except_unitIsUnitIffAll, isAcyclicIffAllVerticesAreNotInCircle]
  simp [validateAndStepSemantics, imp_and, forall_and, and_comm]
