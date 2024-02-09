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

def isPath (l: List A) (G: Graph A): Prop :=
  match l with
  | [] => True
  | hd::tl =>
    match tl with
    | [] => hd ∈ G.vertices
    | hd'::tl' =>
      hd ∈ G.vertices ∧ hd ∈ (G.predecessors hd') ∧ isPath (hd'::tl') G

def List.getFirst (l: List A) (nonempty: l ≠ []): A :=
  match l with
  | [] => have f: False := by
            simp at nonempty
    False.elim f
  | hd::_ => hd

def isCircle (l: List A) (G: Graph A): Prop :=
  if h:List.length l < 2
  then False
  else
    have l_nonempty: l ≠ [] :=
    by
      cases l with
      | nil =>
        simp at h
      | cons hd tl =>
        simp

    isPath l G ∧ List.getLast l l_nonempty = List.getFirst l l_nonempty


def isAcyclic (G: Graph A) := ∀ (l: List A), ¬ isCircle l G

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




lemma isPath_front_member_graph{a: A} {l: List A} {G: Graph A} (path: isPath (a::l) G): a ∈ G.vertices :=
by
  cases l with
  | nil =>
    unfold isPath at path
    simp at path
    apply path
  | cons hd tl =>
    unfold isPath at path
    simp at path
    simp [path]

lemma isPath_extends_predecessors {a: A} {l: List A} {G: Graph A} (path: isPath (a::l) G): ∀ (b:A), b ∈ (G.predecessors a) → isPath (b::a::l) G :=
by
  intro b b_mem
  unfold isPath
  simp
  constructor
  apply G.complete a
  apply isPath_front_member_graph path
  apply b_mem
  constructor
  apply b_mem
  apply path



lemma isPath_of_cons {a: A} {l:List A} {G:Graph A} (path: isPath (a::l) G): isPath l G :=
by
  unfold isPath at path
  cases l with
  | nil =>
    unfold isPath
    apply True.intro
  | cons hd tl =>
    simp at path
    simp [path]

lemma isPathImplSubset {l: List A} {G: Graph A} (path: isPath l G ): l.toFinset ⊆ G.vertices.toFinset :=
by
  rw [Finset.subset_iff]
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    intro x x_mem
    simp at x_mem
    cases x_mem with
    | inl x_hd =>
      unfold isPath at path
      cases tl with
      | nil =>
        simp at *
        rw [x_hd]
        apply path
      | cons hd' tl' =>
        simp at path
        rw [List.mem_toFinset]
        simp [x_hd,path]
    | inr x_tl =>
      apply ih
      apply isPath_of_cons path
      simp [x_tl]


def extractTreeStep (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G): tree A :=
  if h: a ∈ visited
  then tree.node a []
  else
  tree.node a (List.map (fun ⟨x, _h⟩ => extractTreeStep x G (a::visited) (isPath_extends_predecessors path x _h)) (G.predecessors a).attach)
termination_by extractTreeStep a G visited path => ((List.toFinset G.vertices).card - (List.toFinset visited).card)
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
  apply isPathImplSubset path
  simp
  apply p

  apply Finset.card_le_of_subset
  apply isPathImplSubset
  apply isPath_of_cons path
