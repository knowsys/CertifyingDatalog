import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation
import Mathlib.Data.List.Card
import Mathlib.Data.Finset.Card


structure Graph (A: Type) where
  (vertices: List A)
  (predecessors: A → List A)
  (complete: ∀ (a:A), a ∈ vertices →  ∀ (a':A), a' ∈ predecessors a → a' ∈ vertices)

section dfs
variable {A: Type}[DecidableEq A] {B: Type} [DecidableEq B]

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

def isCycle (l: List A) (G: Graph A): Prop :=
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

lemma IsPathOfisCycle (l: List A) (G: Graph A) (h: isCycle l G): isPath l G :=
by
  unfold isCycle at h
  by_cases h' : List.length l < 2
  simp [h'] at h

  simp [h'] at h
  simp [h]

def isAcyclic (G: Graph A) := ∀ (l: List A), ¬ isCycle l G





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

lemma isPathImplSubset' {l: List A} {G: Graph A} (path: isPath l G ): ∀ (a:A), a ∈ l → a ∈ G.vertices :=
by
  unfold isPath at path
  rcases path with ⟨path,_⟩
  apply path

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

lemma getFirstForNonequal_isLt  (l: List A) (h:l ≠ []): 0 < l.length :=
by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

lemma getLastForNonequal_isLt (l: List A) (h:l ≠ []): l.length.pred < l.length :=
by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    apply Nat.pred_lt
    simp

def canReach (a b: A) (G: Graph A):= ∃ (p: List A) (neq: p ≠ []), isPath p G ∧ p.get (Fin.mk 0 (getFirstForNonequal_isLt p neq)) = a ∧ p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p neq)) = b

lemma canReach_refl (a:A) (G: Graph A) (mem: a ∈ G.vertices): canReach a a G :=
by
  unfold canReach
  use [a]
  have neq: [a] ≠ []
  simp
  use neq
  constructor
  unfold isPath
  constructor
  intro a'
  simp
  intro h
  rw [h]
  apply mem

  intro i i_zero i_lt
  simp at i_lt
  rw [i_lt] at i_zero
  simp at i_zero
  simp

-- added based on https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/finset.2Efilter
noncomputable def Finset.filter_nc (p: A → Prop) (S: Finset A):= @Finset.filter A p (Classical.decPred p) S

lemma Finset.mem_filter_nc (a:A) (p: A → Prop) (S: Finset A): a ∈ Finset.filter_nc p S ↔ p a ∧ a ∈ S :=
by
  unfold filter_nc
  have dec: DecidablePred p
  apply Classical.decPred
  simp [Finset.mem_filter]
  rw [And.comm]

noncomputable def globalPredecessors (b:A) (G: Graph A): Finset A := Finset.filter_nc (fun a => canReach a b G) G.vertices.toFinset


lemma isPathExtendBack (p: List A) (a: A) (G: Graph A) (path: isPath p G) (nonempty_p: p ≠ []) (mem: a ∈ G.vertices) (backExtend: p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p nonempty_p)) ∈ G.predecessors a): isPath (p++[a]) G :=
by
  unfold isPath at *
  simp at *
  rcases path with ⟨subs, conn⟩
  constructor
  intro b b_mem
  cases b_mem with
  | inl b_p =>
    apply subs b b_p
  | inr b_a =>
    rw [b_a]
    apply mem

  intro i i_zero i_len
  by_cases i_original: i < p.length
  rw [List.get_append i i_original]
  have i_original_pred: i.pred < p.length
  apply Nat.lt_trans (m:= i)
  apply Nat.pred_lt
  apply Ne.symm
  apply Nat.ne_of_lt
  apply i_zero
  apply i_original
  rw [List.get_append i.pred i_original_pred]
  apply conn i i_zero

  simp at i_original
  cases i_original with
  | refl =>
    rw [List.get_append_right (i:= p.length), List.get_append p.length.pred (getLastForNonequal_isLt p nonempty_p)]
    simp
    apply backExtend
    simp
    push_neg
    apply Nat.le_refl
  | step h =>
    simp at i_len
    rw [← Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at i_len
    simp at h
    rw [← not_lt] at h
    exact absurd i_len h

lemma globalPredecessorsSubsetWhenPredecessor (a b:A) (G: Graph A) (mem: a ∈ G.vertices) (pred: b ∈ G.predecessors a): globalPredecessors b G ⊆ globalPredecessors a G:=
by
  rw [Finset.subset_iff]
  intro x
  rw [globalPredecessors, Finset.mem_filter_nc]
  intro h
  rcases h with ⟨reach, mem'⟩
  rw [globalPredecessors, Finset.mem_filter_nc]
  constructor
  unfold canReach at *
  rcases reach with ⟨p, neq, path, get_x, get_b⟩
  use (p++[a])
  have neq': (p++[a]) ≠ []
  simp
  use neq'
  constructor
  apply isPathExtendBack p a G path neq mem
  rw [get_b]
  apply pred

  constructor
  rw [List.get_append_left]
  apply get_x
  rw [List.get_append_right]
  simp
  simp
  simp
  apply mem'




lemma nodeNotInGlobalPredecessorOfPredecessorInAcyclic (a b:A) (G: Graph A) (acyclic: isAcyclic G) (pred: b ∈ G.predecessors a): ¬  a ∈ globalPredecessors b G :=
by
  by_contra p
  unfold globalPredecessors at p
  rw [Finset.mem_filter_nc] at p
  rcases p with ⟨reach,mem⟩
  unfold canReach at reach
  rcases reach with ⟨p,nonempty, path, get_a, get_b⟩
  have cycle: isCycle (p++[a]) G
  unfold isCycle
  simp
  cases p with
  | nil =>
    simp at nonempty
  | cons hd tl =>
    have h : ¬  List.length (hd :: tl) + 1 < 2
    simp
    rw [← Nat.succ_eq_add_one]
    simp_arith
    simp only [h]
    simp
    constructor
    rw [← List.cons_append]
    apply isPathExtendBack
    apply path
    rw [← List.mem_toFinset]
    apply mem
    rw [get_b]
    apply pred
    simp

    rw [List.get_append_right]
    simp
    rw [List.get_eq_iff, List.get?_cons_zero, Option.some_inj] at get_a
    apply get_a
    simp
    simp


  unfold isAcyclic at acyclic
  specialize acyclic (p++[a])
  exact absurd cycle acyclic

lemma globalPredecessorsSSubsetWhenAcyclicAndPredecessor (G: Graph A) (a b: A) (acyclic: isAcyclic G) (pred: b ∈ G.predecessors a) (mem_a: a ∈ G.vertices): globalPredecessors b G  ⊂ globalPredecessors a G :=
by
  rw [Finset.ssubset_def]
  constructor
  apply globalPredecessorsSubsetWhenPredecessor a b G mem_a pred

  rw [Finset.subset_iff]
  simp
  use a
  constructor
  unfold globalPredecessors
  rw [Finset.mem_filter_nc]
  constructor
  unfold canReach
  use [a]
  have neq: [a] ≠ []
  simp
  use neq
  constructor
  apply isPathSingleton
  apply mem_a
  constructor
  simp
  simp
  rw [List.mem_toFinset]
  apply mem_a

  apply nodeNotInGlobalPredecessorOfPredecessorInAcyclic
  apply acyclic
  apply pred





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

lemma zero_lt_inhabited_list_length (a:A) (l: List A) (mem: a ∈ l): 0 < l.length :=
by
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp



lemma getSubListToMemberNonEmpty (a: A) (l: List A) (mem: a ∈ l): getSubListToMember l a mem ≠ [] :=
by
  unfold getSubListToMember
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp
    by_cases a_hd: a = hd
    simp [a_hd]
    simp [a_hd]

lemma getSubListToMemberHasNotLengthZero (a: A) (l: List A) (mem: a ∈ l): List.length (getSubListToMember l a mem) ≠ 0 :=
by
  cases h:(getSubListToMember l a mem) with
    | nil =>
      have not_h: ¬  (getSubListToMember l a mem) = []
      push_neg
      apply getSubListToMemberNonEmpty
      exact absurd h not_h
    | cons hd tl =>
      simp

lemma getSubListToMember_length (a: A) (l: List A) (mem: a ∈ l): List.length (getSubListToMember l a mem) = Nat.succ (Nat.pred (List.length (getSubListToMember l a mem))) :=
by
  apply Eq.symm
  apply Nat.succ_pred
  apply getSubListToMemberHasNotLengthZero


lemma getSubListToMember_len_le_original (a: A) (l: List A) (mem: a ∈ l): (getSubListToMember l a mem).length ≤ l.length :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    rw [Nat.one_eq_succ_zero, Nat.succ_le_succ_iff]
    apply Nat.zero_le

    simp [a_hd]
    simp[a_hd] at mem
    rw [Nat.succ_le_succ_iff]
    apply ih

lemma zero_lt_inhabited_list_length' (l: List A) (nonempty: l ≠ []): 0 < l.length :=
by
  cases l with
  | nil =>
    simp at nonempty
  | cons hd tl =>
    simp

lemma getSubListToMemberPreservesFront' (a:A) (l: List A) (mem: a ∈ l) : List.get l (Fin.mk 0 (zero_lt_inhabited_list_length a l mem)) = List.get (getSubListToMember l a mem) (Fin.mk 0 (zero_lt_inhabited_list_length' (getSubListToMember l a mem) (getSubListToMemberNonEmpty a l mem))) :=
by
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp
    apply Eq.symm
    rw [List.get_eq_iff]
    simp
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    simp [a_hd]


lemma getSubListToMemberEndsWithElement (a: A) (l: List A) (mem: a ∈ l): List.get? (getSubListToMember l a mem) (getSubListToMember l a mem).length.pred  = a  :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp [getSubListToMember]
    by_cases a_hd: a = hd
    subst a_hd
    simp

    simp [a_hd]
    simp[a_hd] at mem
    specialize ih mem

    rw [getSubListToMember_length, List.get?_cons_succ]
    apply ih




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
    simp [a_hd] at mem
    specialize ih mem (isPath_of_cons path)
    unfold isPath at *
    rcases path with ⟨subs_ht, conn_ht⟩
    rcases ih with ⟨subs_ih, conn_ih⟩
    constructor
    intro b b_mem
    simp at b_mem
    cases b_mem with
    | inl b_hd =>
      apply subs_ht
      rw [b_hd]
      simp
    | inr b_tl =>
      apply subs_ih
      apply b_tl

    intro i i_zero i_len
    cases i with
    | zero =>
      simp at i_zero
    | succ j =>
      simp
      cases j with
      | zero =>
        simp
        specialize conn_ht (Nat.succ 0)
        simp at conn_ht
        simp at i_len
        have g: Nat.succ 0 < List.length (hd :: tl)
        simp
        apply Nat.lt_of_lt_of_le
        apply i_len
        apply Nat.succ_le_succ
        apply getSubListToMember_len_le_original

        specialize conn_ht g
        cases tl with
        | nil =>
          simp at mem
        | cons hd' tl' =>
          simp at conn_ht
          have isLt: Nat.zero < List.length (getSubListToMember (hd' :: tl') a mem)
          rw [getSubListToMember_length]
          apply Nat.zero_lt_succ
          have get_result: List.get (getSubListToMember (hd' :: tl') a mem) { val := 0, isLt := isLt } = hd'
          rw [List.get_eq_iff]
          simp
          unfold getSubListToMember
          by_cases a_hd: a = hd'
          simp [a_hd]
          simp [a_hd]
          simp [get_result]
          apply conn_ht
      | succ k =>
        specialize conn_ih (Nat.succ k)
        simp at conn_ih
        simp at i_len
        rw [Nat.succ_lt_succ_iff, ← Nat.succ_eq_add_one] at i_len
        specialize conn_ih i_len
        apply conn_ih

def reachedFromCycle (a:A) (G: Graph A):= ∃ (c: List A), isCycle c G ∧ ∃ (b: A), b ∈ c ∧ canReach b a G

lemma NotreachedFromCycleIffPredecessorsNotReachedFromCycle (a: A) (G: Graph A) (mem: a ∈ G.vertices): ¬ reachedFromCycle a G ↔ ∀ (b:A), b ∈ G.predecessors a → ¬ reachedFromCycle b G :=
by
  constructor
  intro h
  unfold reachedFromCycle at h
  simp at h
  by_contra p
  simp at p
  rcases p with ⟨x, x_pred, reach⟩
  unfold reachedFromCycle at reach
  rcases reach with ⟨c, cycle, b, b_c, reach_b_x⟩
  specialize h c cycle b b_c
  have reach_b_a: canReach b a G
  unfold canReach
  unfold canReach at reach_b_x
  rcases reach_b_x with ⟨p, neq, path, get_b, get_x⟩
  use p++[a]
  have neq': p++[a] ≠ []
  simp
  use neq'
  constructor
  apply isPathExtendBack p a G path neq mem
  rw [get_x]
  apply x_pred
  constructor
  rw [List.get_append_left]
  apply get_b
  rw [List.get_append_right]
  simp
  simp
  simp
  exact absurd reach_b_a h

  --back direction
  intro h
  by_contra p
  unfold reachedFromCycle at p
  rcases p with ⟨c, cycle, b, b_c, reach_b_a⟩
  unfold canReach at reach_b_a
  rcases reach_b_a with ⟨p, neq, path, get_b, get_a⟩
  by_cases b_pred: b ∈ G.predecessors a
  have reachCirc_b: reachedFromCycle b G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use b
  constructor
  apply b_c
  unfold canReach
  use [b]
  have neq': [b] ≠ []
  simp
  use neq'
  constructor
  apply isPathSingleton
  apply G.complete
  apply mem
  apply b_pred
  simp

  specialize h b b_pred
  exact absurd reachCirc_b h

  -- b not connected with a directly
  by_cases singletonPath: p.length = 1
  have a_b: a = b
  simp [singletonPath] at get_a
  rw [← get_a, get_b]

  have pred_in_c: ∃ (d:A), d ∈ c ∧ d ∈ G.predecessors a
  unfold isCycle at cycle
  by_cases h : List.length c < 2
  simp [h] at cycle
  simp [h] at cycle
  rcases cycle with ⟨path, ends⟩
  unfold isPath at path
  rcases path with ⟨subs,conn⟩
  have isLt_zero_c: 0 < c.length
  cases c with
  | nil =>
    simp at b_c
  | cons hd tl =>
    simp
  rw [List.mem_iff_get?] at b_c
  rcases b_c with ⟨n, get_c_b⟩
  cases n with
  | zero =>
    specialize conn (Nat.pred c.length)
    have conn_1: Nat.pred (List.length c) > 0
    simp at h
    cases c with
    | nil =>
      simp at h
    | cons hd tl =>
      cases tl with
      | nil =>
        simp at h
      | cons hd tl =>
        simp
    specialize conn conn_1
    have g : Nat.pred (List.length c) < List.length c
    apply Nat.pred_lt
    cases c with
    | nil =>
      simp at h
    | cons hd tl =>
      simp
    specialize conn g
    have ha: List.get c (Fin.mk (Nat.pred (List.length c)) g) = b
    rw [← ends, List.get_eq_iff]
    simp
    apply get_c_b
    rw [ha, ← a_b] at conn
    have isLt': Nat.pred (Nat.pred (List.length c)) < c.length
    apply Nat.lt_of_le_of_lt (m:= Nat.pred c.length)
    rw [Nat.pred_le_iff, Nat.succ_pred]
    apply Nat.pred_le
    cases c with
    | nil =>
      simp at h
    | cons hd tl =>
      simp
    apply Nat.pred_lt
    cases c with
    | nil =>
      simp at h
    | cons hd tl =>
      simp
    use (List.get c (Fin.mk (Nat.pred (Nat.pred (List.length c))) isLt' ))
    constructor
    apply List.get_mem
    apply conn
  | succ m =>
    specialize conn (Nat.succ m)
    have conn1: Nat.succ m > 0
    simp
    specialize conn conn1
    rw [List.get?_eq_some] at get_c_b
    rcases get_c_b with ⟨g,c_get⟩
    specialize conn g
    have isLt: Nat.pred (Nat.succ m) < c.length
    simp
    apply Nat.lt_trans (m:= Nat.succ m)
    apply Nat.lt_succ_self
    apply g
    use List.get c (Fin.mk (Nat.pred (Nat.succ m)) isLt)
    constructor
    apply List.get_mem
    rw [c_get, ← a_b] at conn
    apply conn


  rcases pred_in_c with ⟨d, d_c, d_pred⟩
  specialize h d d_pred
  have reachCirc_d: reachedFromCycle d G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use d
  constructor
  apply d_c
  unfold canReach
  use [d]
  have neq': [d] ≠ []
  simp
  use neq'
  simp
  apply isPathSingleton
  apply isPathImplSubset' (IsPathOfisCycle c G cycle) d d_c
  exact absurd reachCirc_d h


  have isLt: Nat.pred (Nat.pred p.length) < p.length
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    cases tl with
    | nil =>
      simp
    | cons hd' tl' =>
      simp
      apply Nat.lt_trans (m:= Nat.succ tl'.length)
      apply Nat.lt_succ_self
      apply Nat.lt_succ_self

  have reachCirc: reachedFromCycle (p.get (Fin.mk (Nat.pred (Nat.pred p.length)) isLt)) G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use b
  constructor
  apply b_c
  unfold canReach
  have mem_p: (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) ∈ p
  apply List.get_mem

  use (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p)
  have neq': (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p) ≠ []
  apply getSubListToMemberNonEmpty
  use neq'
  constructor
  apply getSubListToMemberPreservesPath (path:= path)
  constructor
  rw [← get_b]
  apply Eq.symm
  apply getSubListToMemberPreservesFront'
  rw [List.get_eq_iff]
  simp
  apply getSubListToMemberEndsWithElement


  specialize h (List.get p { val := Nat.pred (Nat.pred (List.length p)), isLt := isLt })
  unfold isPath at path
  rcases path with ⟨_, conn⟩
  specialize conn  (Nat.pred (List.length p))

  have gt_zero:  Nat.pred (List.length p) > 0
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    simp
    cases tl with
    | nil =>
      simp at singletonPath
    | cons hd' tl' =>
      simp

  have g : Nat.pred (List.length p) < List.length p
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    simp
  specialize conn gt_zero g

  rw [get_a] at conn
  specialize h conn
  exact absurd reachCirc h

lemma acyclicIffAllNotReachedFromCycle (G: Graph A): isAcyclic G ↔ ∀ (a:A), ¬ reachedFromCycle a G :=
by
  constructor
  intro acyclic
  intro a
  unfold reachedFromCycle
  simp
  intro c cycle
  unfold isAcyclic at acyclic
  specialize acyclic c
  exact absurd cycle acyclic

  intro h
  by_contra cyclic
  unfold isAcyclic at cyclic
  simp at cyclic
  rcases cyclic with ⟨c, cycle⟩
  unfold isCycle at cycle
  by_cases g:List.length c < 2
  simp [g] at cycle
  simp [g] at cycle
  have isLt: 0 < List.length c
  cases c with
  | nil =>
    simp at g
  | cons hd tl =>
    simp
  specialize h (List.get c (Fin.mk 0 isLt))
  unfold reachedFromCycle at h
  simp at h
  specialize h c
  unfold isCycle at h
  simp [g, cycle] at h
  specialize h (List.get c (Fin.mk 0 isLt))
  simp [List.get_mem] at h
  unfold canReach at h
  simp at h
  specialize h ([List.get c (Fin.mk 0 isLt)])
  have path: isPath [List.get c { val := 0, isLt := isLt }] G
  apply isPathSingleton
  rcases cycle with ⟨path_c,_⟩
  unfold isPath at path_c
  rcases path_c with ⟨path_c,_⟩
  apply path_c
  apply List.get_mem

  specialize h path
  simp[cycle] at h




lemma frontRepetitionInPathImpliesCycle (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G) (mem: a ∈ visited): isCycle (a::(getSubListToMember visited a mem)) G :=
by
  unfold isCycle
  simp
  have h : ¬ Nat.succ (List.length (getSubListToMember visited a mem)) < 2
  push_neg
  cases h':getSubListToMember visited a mem with
  | nil =>
    have p: getSubListToMember visited a mem ≠ []
    apply getSubListToMemberNonEmpty
    exact absurd h' p
  | cons hd tl =>
    simp
    rw [Nat.two_le_iff]
    simp

  simp [h]
  constructor
  cases h':getSubListToMember visited a mem with
  | nil =>
    have p: getSubListToMember visited a mem ≠ []
    apply getSubListToMemberNonEmpty
    exact absurd h' p
  | cons hd tl =>
    apply isPath_extends_predecessors
    rw [← h']
    apply getSubListToMemberPreservesPath (path:= isPath_of_cons path)
    unfold isPath at path
    rcases path with ⟨_, conn⟩
    specialize conn (Nat.succ 0)
    simp at conn
    have g : Nat.succ 0 < List.length (a :: visited)
    simp
    apply Nat.succ_lt_succ
    cases visited with
    | nil =>
      simp at mem
    | cons hd' tl' =>
      simp
    specialize conn g
    have isLt: 0 < List.length visited
    apply Nat.lt_of_succ_lt_succ
    apply g
    have first_vis: List.get visited { val := 0, isLt := isLt} = hd
    cases visited with
    | nil =>
      simp at mem
    | cons hd' tl' =>
      simp [List.get_cons_zero]
      apply getSubListToMemberPreservesFront (result:=h')
    simp [first_vis] at conn
    apply conn

  apply Eq.symm
  rw [List.get_eq_iff]
  simp
  rw [getSubListToMember_length  a visited mem, List.get?_cons_succ, getSubListToMemberEndsWithElement]

lemma except_is_ok_iff_exists {A B: Type} (e: Except A B): (∃ (b:B), e = Except.ok b) ↔ Except.isOk e :=
by
  cases e with
  | error msg =>
    unfold Except.isOk
    unfold Except.toBool
    simp
  | ok u =>
    unfold Except.isOk
    unfold Except.toBool
    simp

lemma except_is_ok_of_ok {A B: Type} (b:B): Except.isOk (Except.ok b: Except A B) = true :=
by
  unfold Except.isOk
  unfold Except.toBool
  simp

lemma except_is_ok_of_error {A B: Type} (a:A) : Except.isOk (Except.error a: Except A B) = true → False:=
by
  unfold Except.isOk
  unfold Except.toBool
  simp

def foldl_except_set (f: A → Finset B → (Except String (Finset B))) (l: List A) (init: Finset B): Except String (Finset B) :=
  match l with
  | [] => Except.ok init
  | hd::tl =>
    match f hd init with
    | Except.error msg => Except.error msg
    | Except.ok S => foldl_except_set f tl S


lemma foldl_except_set_preserves_p {A B: Type} (f: A → Finset B → (Except String (Finset B))) (p: B → Prop) (l: List A) (init: Finset B) (init_prop: ∀ (b:B), b ∈ init → p b) (S: Finset B) (h: foldl_except_set f l init = Except.ok S ) (f_prev: ∀ (a:A) (S S': Finset B), (∀ (b:B), b ∈ S → p b) → f a S = Except.ok S' → (∀ (b:B), b ∈ S' → p b) ): ∀ (b:B), b ∈ S → p b :=
by
  induction l generalizing init with
  | nil =>
    unfold foldl_except_set at h
    simp at h
    intro b
    rw [← h]
    apply init_prop
  | cons hd tl ih =>
    unfold foldl_except_set at h
    cases f_hd:f hd init with
    | error e=>
      simp [f_hd] at h
    | ok S' =>
      simp [f_hd] at h
      specialize ih S'
      apply ih
      apply f_prev
      apply init_prop
      apply f_hd
      apply h



lemma foldl_except_set_is_ok {A B: Type} (f: A → Finset B → (Except String (Finset B))) (p: B → Prop) (l: List A) (init: Finset B) (init_prop: ∀ (b:B), b ∈ init → p b) (f_ignore_B: ∀ (a:A) (S S': Finset B), (∀ (b:B), b ∈ S → p b) →  (∀ (b:B), b ∈ S' → p b) → (Except.isOk (f a S) ↔ Except.isOk (f a S'))) (f_prev: ∀ (a:A) (S S': Finset B), (∀ (b:B), b ∈ S → p b) → f a S = Except.ok S' → (∀ (b:B), b ∈ S' → p b) ): (∃ (S: Finset B), foldl_except_set f l init = Except.ok S) ↔ ∀ (a:A), a ∈ l → Except.isOk (f a init) :=
by
  induction l generalizing init with
  | nil =>
    unfold foldl_except_set
    simp
  | cons hd tl ih =>
    constructor
    intro h a a_mem
    simp at a_mem
    rcases h with ⟨S, foldl⟩
    cases a_mem with
    | inl a_hd =>
      unfold foldl_except_set at foldl
      rw [a_hd]
      cases h: f hd init with
      | ok S' =>
        unfold Except.isOk
        unfold Except.toBool
        simp
      | error e =>
        simp [h] at foldl
    | inr a_tl =>
      unfold foldl_except_set at foldl
      cases h: f hd init with
      | ok S' =>
        specialize ih S'
        have S'_prop: ∀ (b : B), b ∈ S' → p b
        apply f_prev hd init S' init_prop h
        specialize ih S'_prop
        simp [h] at foldl
        rw [← f_ignore_B a S' init S'_prop init_prop]
        revert a
        rw [← ih]
        use S
      | error e =>
        simp [h] at foldl

    intro h
    have f_hd_result: ∃ (S: Finset B), f hd init = Except.ok S
    rw [except_is_ok_iff_exists]
    apply h
    simp
    unfold foldl_except_set
    rcases f_hd_result with ⟨S', f_S'⟩
    simp [f_S']
    specialize ih S'
    have S'_prop: ∀ (b:B), b ∈ S' → p b
    apply f_prev hd init S' init_prop f_S'
    specialize ih S'_prop
    rw [ih]
    intro a a_mem
    rw [f_ignore_B a S' init S'_prop init_prop]
    apply h
    simp [a_mem]


def addElementIfOk (e: Except String (Finset A)) (a:A): Except String (Finset A) :=
  match e with
  | Except.ok S => Except.ok (S ∪ {a})
  | Except.error msg => Except.error msg

lemma addElementIfOk_exists_ok (e: Except String (Finset A)) (a:A): (∃ (S: Finset A), addElementIfOk e a = Except.ok S) ↔ ∃ (S:Finset A), e = Except.ok S :=
by
  constructor
  intro h
  rcases h with ⟨S, add⟩
  unfold addElementIfOk at add
  cases e with
  | ok S' =>
    use S'
  | error e =>
    simp at add

  intro h
  rcases h with ⟨S, e_S⟩
  rw [e_S]
  simp [addElementIfOk]

lemma addElementIfOk_exists_ok' (e: Except String (Finset A)) (a:A) (S: Finset A): addElementIfOk e a = Except.ok S ↔ ∃ (S': Finset A), S = S' ∪ {a} ∧ e = Except.ok S' :=
by
  cases e with
  | error e =>
    unfold addElementIfOk
    simp
  | ok u =>
    unfold addElementIfOk
    simp [eq_comm]


lemma canReachLemma (a:A) (G: Graph A) (mem: a ∈ G.vertices) (f: A → List A → Except String Unit): (∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ()) ↔ (∀ (b: A), b ∈ G.predecessors a → (∀ (c : A), canReach c b G → f c (Graph.predecessors G c) = Except.ok ())) ∧ f a (G.predecessors a) = Except.ok () :=
by
  sorry
  /-
  constructor
  intro h
  constructor
  intro b b_pred
  intro c reach_c
  apply h
  unfold canReach
  unfold canReach at reach_c
  rcases reach_c with ⟨p, neq, path, get_c, get_b⟩
  use p++[a]
  have neq': p++[a] ≠ []
  simp
  use neq'
  constructor
  unfold isPath
  constructor
  intro a' a'p
  simp at a'p
  cases a'p with
  | inl a'p =>
    apply isPathImplSubset' path a' a'p
  | inr a'p =>
    rw [a'p]
    apply mem
  intro i i_zero i_len
  simp at i_len
  rw [← Nat.succ_eq_add_one, Nat.lt_succ_iff_lt_or_eq] at i_len
  unfold isPath at path
  rcases path with ⟨subs,conn⟩
  cases i_len with
  | inl i_lt_p =>
    rw [List.get_append_left, List.get_append_left]
    apply conn i i_zero i_lt_p
  | inr i_p =>
    rw [List.get_append_left, List.get_append_right]
    rw [List.get_eq_iff] at get_b
    simp at get_b
    rw [← i_p, List.get?_eq_some] at get_b
    rcases get_b with ⟨h', getb⟩
    simp
    swap
    rw [i_p]
    simp
    simp[getb]
    apply b_pred

  constructor
  rw [List.get_append_left]
  apply get_c
  rw [List.get_append_right]
  simp
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    simp
  simp

  -- f at same spot
  apply h
  apply canReach_refl a G mem

  -- back direction
  intro h
  intro b reach
  unfold canReach at reach
  rcases reach with ⟨p, neq, path, get_b, get_a⟩
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    cases tl with
    | nil =>
      simp at get_a
      simp at get_b
      rw [← get_b, get_a]
      apply And.right h
    | cons hd' tl' =>
      rcases h with ⟨left,right⟩
      have isLt: Nat.pred (Nat.pred (hd::hd'::tl').length) < (hd::hd'::tl').length
      simp
      apply Nat.lt_trans (m:= Nat.succ tl'.length)
      simp
      simp
      have pred: List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt) ∈ G.predecessors a
      rw [← get_a]
      unfold isPath at path
      rcases path with ⟨subs,conn⟩
      apply conn
      simp
      specialize left (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) pred
      apply left
      unfold canReach
      use (getSubListToMember (hd::hd'::tl') (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) (List.get_mem (hd::hd'::tl') (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt))
      simp
      constructor
      apply getSubListToMemberPreservesPath (hd::hd'::tl') (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) (List.get_mem (hd::hd'::tl') (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt) G path
      constructor
      constructor
      rw [← get_b]
      apply Eq.symm
      apply getSubListToMemberPreservesFront'
      apply getSubListToMemberNonEmpty
      rw [List.get_eq_iff]
      apply getSubListToMemberEndsWithElement
  -/


def dfs_step (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currPath: List A) (path: isPath (a::currPath) G) (not_mem: ¬ a ∈ currPath) (visited: Finset A) : Except String (Finset A) :=
  if a ∈ visited
  then Except.ok visited
  else
    match f a (G.predecessors a) with
    | Except.error msg => Except.error msg
    | Except.ok _ =>
      addElementIfOk (foldl_except_set (fun ⟨x, _h⟩ S =>
      if x_path: x ∈ (a::currPath)
      then Except.error "Cycle detected"
      else
        dfs_step x G f (a::currPath) (isPath_extends_predecessors path x _h) x_path S) (G.predecessors a).attach visited) a
termination_by dfs_step node G f currPath path not_mem visited => Finset.card (List.toFinset G.vertices \ List.toFinset currPath)
decreasing_by
  simp_wf
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  simp
  use a
  constructor
  intro _
  left
  rfl

  rw [Finset.subset_iff]
  intro b
  simp
  intro h
  cases h with
  | inl h =>
    rw [h]
    constructor
    have mem_path: a ∈ a::currPath
    simp
    apply isPathImplSubset' path a mem_path
    apply not_mem
  | inr h =>
    rcases h with ⟨left,right⟩
    push_neg at right
    simp [left,right]


lemma dfs_step_sematics' (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currPath: List A) (path: isPath (a::currPath) G) (not_mem: ¬ a ∈ currPath) (visited: Finset A) (visited_prop: ∀ (a:A), a ∈ visited → ¬ reachedFromCycle a G ∧ ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok ()):  Except.isOk (dfs_step a G f currPath path not_mem visited) ↔  ¬ reachedFromCycle a G ∧ (∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok ()) ∧ ∀ (S: Finset A), (dfs_step a G f currPath path not_mem visited) = Except.ok S →  ∀ (a:A), a ∈ S → ¬ reachedFromCycle a G ∧ ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok () :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currPath)  with n ih generalizing a currPath visited

  --base case: impossible as a is not in path and yet everything must be in the path
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices
  apply isPathImplSubset' path
  simp
  specialize h a_G
  exact absurd h not_mem

  --step
  have a_mem: a ∈ G.vertices
  apply isPathImplSubset' path
  simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currPath)) = n
  rw [Nat.succ_eq_add_one] at h
  have h': List.toFinset G.vertices \ List.toFinset currPath = insert a (List.toFinset G.vertices \ List.toFinset (a :: currPath))
  rw [Finset.ext_iff]
  simp
  intro a'
  by_cases a_a': a = a'
  simp [a_a']
  rw [← a_a']
  constructor
  apply a_mem
  apply not_mem
  constructor
  intro ha
  right
  simp [ha]
  apply Ne.symm a_a'
  intro ha
  cases ha with
  | inl a_a =>
    exact absurd (Eq.symm a_a) a_a'
  | inr ha =>
    rw [not_or] at ha
    simp [ha]
  rw [h', Finset.card_insert_of_not_mem, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, Nat.succ_inj'] at h
  apply h
  simp

  constructor
  intro dfs
  unfold dfs_step at dfs
  by_cases a_visited: a ∈ visited
  rw [← and_assoc]
  constructor
  apply visited_prop a a_visited
  intro S
  unfold dfs_step
  simp [a_visited]
  intro vis_S
  simp [← vis_S]
  apply visited_prop

  simp only [a_visited, Bool.not_eq_true, List.mem_cons, ite_false] at dfs
  cases h_f:f a (G.predecessors a) with
  | error e =>
    simp [h_f] at dfs
    exfalso
    apply except_is_ok_of_error e dfs
  | ok u =>
    simp [h_f] at dfs
    rw [← except_is_ok_iff_exists, addElementIfOk_exists_ok, foldl_except_set_is_ok (init:=visited) (init_prop:=visited_prop)] at dfs
    simp at dfs
    rw [NotreachedFromCycleIffPredecessorsNotReachedFromCycle (mem:= a_mem), canReachLemma (mem:= a_mem)]
    rw [← and_assoc]
    constructor
    simp [h_f]
    rw [← forall_and]
    intro pred
    rw [← imp_and]
    intro pred_mem
    specialize dfs pred pred_mem
    have pred_path: ¬ pred ∈ a::currPath
    by_contra p
    simp at p
    simp [p] at dfs
    apply except_is_ok_of_error _ dfs

    specialize ih pred (a::currPath) (isPath_extends_predecessors path pred pred_mem) pred_path visited visited_prop card
    simp at pred_path
    simp [pred_path] at dfs
    rw [ih] at dfs
    rcases dfs with ⟨reachCycle, reachf, subs⟩
    constructor
    apply reachCycle
    apply reachf

    intro S dfs_S
    unfold dfs_step at dfs_S
    simp [a_visited, h_f] at dfs_S
    rw [addElementIfOk_exists_ok'] at dfs_S
    rcases dfs_S with ⟨S', S_S', S'_get⟩
    intro b
    rw [S_S']
    simp
    intro b_mem
    cases b_mem with
    | inl b_S' =>
      admit
    | inr b_a =>
      rw [b_a]
      admit

    simp
    intro a' pred S S' S_prop S'_prop
    by_cases ha': a' = a ∨ a' ∈ currPath
    simp [ha']
    simp [ha']
    rw [← List.mem_cons] at ha'
    have ih': ∀ (a : A) (currPath : List A) (path : isPath (a :: currPath) G) (not_mem : ¬a ∈ currPath) (visited : Finset A),
  (∀ (a : A),
      a ∈ visited → ¬reachedFromCycle a G ∧ ∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ()) →
    Finset.card (List.toFinset G.vertices \ List.toFinset currPath) = n →
      (Except.isOk (dfs_step a G f currPath path not_mem visited) = true ↔
        ¬reachedFromCycle a G ∧
          (∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ()) ∧
            ∀ (S : Finset A),
              dfs_step a G f currPath path not_mem visited = Except.ok S →
                ∀ (a : A),
                  a ∈ S →
                    ¬reachedFromCycle a G ∧ ∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ())
    apply ih
    specialize ih a' (a::currPath) (isPath_extends_predecessors path a' pred) ha' S S_prop card
    rw [ih]
    specialize ih' a' (a::currPath) (isPath_extends_predecessors path a' pred) ha' S' S'_prop card
    rw [ih']
    simp
    intros


    admit

    simp
    intro a' pred S S' S_prop dfs_S'
    have ha': ¬ ( a' = a ∨ a' ∈ currPath)
    by_contra p
    simp [p] at dfs_S'
    simp[ha'] at dfs_S'
    rw [← List.mem_cons] at ha'
    specialize ih a' (a::currPath) (isPath_extends_predecessors path a' pred) ha' S S_prop card
    have h_ex: Except.isOk (dfs_step a' G f (a::currPath) (isPath_extends_predecessors path a' pred) ha' S) = true
    rw [dfs_S']
    apply except_is_ok_of_ok
    rw [ih] at h_ex
    rcases h_ex with ⟨_, _, hS⟩
    specialize hS S' dfs_S'
    apply hS

  --back direction
  simp

















def dfs_go (G: Graph A) (f: A → List A → Except String Unit) (S: Finset A): Except String Unit :=
  match foldl_except_set (fun ⟨x,_h⟩ S => dfs_step x G f [] (isPathSingleton G x _h) S) G.vertices.attach S with
  | Except.error msg => Except.error msg
  | Except.ok _ => Except.ok ()

lemma dfs_go_semantics (G: Graph A) (f: A → List A → Except String Unit) (S: Finset A) (hS: ∀ (a:A), a ∈ S → ¬reachedFromCycle a G ∧ f a (Graph.predecessors G a) = Except.ok ()): dfs_go G f S = Except.ok () ↔ (∀ (a : A), ¬reachedFromCycle a G) ∧ ∀ (a : A), a ∈ G.vertices → f a (Graph.predecessors G a) = Except.ok () :=
by
  unfold dfs_go
  sorry


def dfs (G: Graph A) (f: A → List A → Except String Unit): Except String Unit := dfs_go G f ∅

lemma dfs_semantics (G: Graph A) (f: A → List A → Except String Unit): dfs G f = Except.ok () ↔ isAcyclic G ∧ ∀ (a:A), a ∈ G.vertices → f a (G.predecessors a) = Except.ok () :=
by
  sorry

def extractTree {A: Type} [DecidableEq A] (a:A) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): tree A :=
  tree.node a (List.map (fun ⟨x, _h⟩ => extractTree x G (G.complete a mem x _h) acyclic) (G.predecessors a).attach)
termination_by extractTree a G mem acyclic => Finset.card (globalPredecessors a G)
decreasing_by
  simp_wf
  apply Finset.card_lt_card
  apply globalPredecessorsSSubsetWhenAcyclicAndPredecessor
  apply acyclic
  apply _h
  apply mem


lemma rootOfExtractTree (a:A) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): root (extractTree a G mem acyclic ) = a :=
by
  unfold extractTree
  unfold root
  simp

variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants]

def locallyValid (P: program τ) (d: database τ) (v: groundAtom τ) (G: Graph (groundAtom τ)): Prop :=
 (∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding r g = groundRuleFromAtoms v (G.predecessors v) ) ∨ ((G.predecessors v) = [] ∧ d.contains v)

def locallyValidityChecker (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (l: List (groundAtom τ)) (a: groundAtom τ)(ruleToString: rule τ → String): Except String Unit :=
  if l.isEmpty
  then
    if d.contains a
    then Except.ok ()
    else checkRuleMatch m (groundRule.mk a l) ruleToString
  else
    checkRuleMatch m (groundRule.mk a l) ruleToString

lemma locallyValidityCheckerUnitIffLocallyValid (P: List (rule τ)) (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (G: Graph (groundAtom τ)) (a: groundAtom τ) (l: List (groundAtom τ)) (l_prop: l = G.predecessors a) (ruleToString: rule τ → String) (ssm: m = parseProgramToSymbolSequenceMap P (fun _ => [])):  locallyValidityChecker m d l a ruleToString = Except.ok () ↔ locallyValid P.toFinset d a G :=
by
  unfold locallyValid
  unfold locallyValidityChecker
  rw [l_prop]
  simp
  constructor

  intro h
  by_cases empty: List.isEmpty (G.predecessors a) = true
  simp [empty] at h
  by_cases db: d.contains a
  right
  constructor
  rw [List.isEmpty_iff_eq_nil] at empty
  apply empty
  apply db
  simp at db
  specialize h db
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)] at h
  left
  simp at h
  apply h

  simp [empty] at h
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)] at h
  left
  simp at h
  apply h

  intro h
  by_cases empty: List.isEmpty (Graph.predecessors G a)
  rw [if_pos empty]
  by_cases db: d.contains a
  simp [db]
  simp [db]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨_, n_db⟩
    exact absurd n_db db
  simp [empty]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨n_empty, _⟩
    rw [← List.isEmpty_iff_eq_nil] at n_empty
    exact absurd n_empty empty



lemma extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic (P: program τ) (d: database τ) (a: groundAtom τ) (G: Graph (groundAtom τ)) (acyclic: isAcyclic G) (mem: a ∈ G.vertices) (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): isValid P d (extractTree a G mem acyclic) :=
by
  induction' h:(height (extractTree a G mem acyclic)) using Nat.strongInductionOn with n ih generalizing a
  have valid_a: locallyValid P d a G
  apply valid a mem
  unfold locallyValid at valid_a
  cases valid_a with
  | inl ruleCase =>
    rcases ruleCase with ⟨r,g,rP, grounding_r⟩
    unfold extractTree
    unfold isValid
    left
    use r
    use g
    constructor
    apply rP
    constructor
    simp
    rw [grounding_r, groundRuleEquality]
    unfold groundRuleFromAtoms
    simp
    apply List.ext_get
    rw [List.length_map, List.length_attach]
    intro n h1 h2
    simp
    rw [rootOfExtractTree]
    rw [List.all₂_iff_forall]
    simp
    intro t x x_pred extract
    specialize ih (height t)
    have height_t_n: height t < n
    rw [← h]
    apply heightOfMemberIsSmaller
    unfold member
    unfold extractTree
    simp
    use x
    use x_pred

    specialize ih height_t_n x (G.complete a mem x x_pred)
    rw [extract] at ih
    simp at ih
    apply ih
  | inr dbCase =>
    unfold extractTree
    unfold isValid
    right
    simp
    apply dbCase

lemma verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (P: program τ) (d: database τ)  (G: Graph (groundAtom τ)) (acyclic: isAcyclic G)  (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): List.toSet G.vertices ⊆ proofTheoreticSemantics P d :=
by
  rw [Set.subset_def]
  intro a a_mem
  rw [← List.toSet_mem] at a_mem
  unfold proofTheoreticSemantics
  simp
  use extractTree a G a_mem acyclic
  constructor
  apply rootOfExtractTree
  apply extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic
  apply valid
