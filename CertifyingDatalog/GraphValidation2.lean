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
  have circle: isCircle (p++[a]) G
  unfold isCircle
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
  exact absurd circle acyclic

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


lemma frontRepetitionInPathImpliesCircle (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G) (mem: a ∈ visited): isCircle (a::(getSubListToMember visited a mem)) G :=
by
  unfold isCircle
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


def foldl_except_set (f: A → Finset B → (Except String (Finset B))) (l: List A) (init: Finset B): Except String (Finset B) :=
  match l with
  | [] => Except.ok init
  | hd::tl =>
    match f hd init with
    | Except.error msg => Except.error msg
    | Except.ok S => foldl_except_set f tl S

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

def dfs_step (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currPath: List A) (path: isPath (a::currPath) G) (visited: Finset A) : Except String (Finset A) :=
  if a ∈ visited
  then Except.ok visited
  else
    if a_path: a ∈ currPath
    then Except.error "Cycle detected"
    else
      match f a (G.predecessors a) with
      | Except.error msg => Except.error msg
      | Except.ok _ =>
        match foldl_except_set (fun ⟨x, _h⟩ S => dfs_step x G f (a::currPath) (isPath_extends_predecessors path x _h) S) (G.predecessors a).attach visited with
        | Except.error msg => Except.error msg
        | Except.ok S => Except.ok (S ∪ {a})
termination_by dfs_step node G f currPath path visited => Finset.card (List.toFinset G.vertices \ List.toFinset currPath)
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
    apply a_path
  | inr h =>
    rcases h with ⟨left,right⟩
    push_neg at right
    simp [left,right]
