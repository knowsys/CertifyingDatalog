import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic


def List.toSet {A: Type} (l: List A): Set A :=
  match l with
  | [] => ∅
  | hd::tl => {hd} ∪ tl.toSet

lemma List.toSet_mem {A: Type} (a:A) (l: List A): a ∈ l ↔ a ∈ l.toSet := by
  induction l with
  | nil =>
    unfold List.toSet
    simp
  | cons hd tl ih =>
    unfold List.toSet
    simp
    rw [ih]

def List.map_except_unit {A B: Type} (l: List A) (f: A → Except B Unit): Except B Unit :=
  match l with
  | [] => Except.ok ()
  | hd::tl =>
    match f hd with
    | Except.ok () => List.map_except_unit tl f
    | Except.error b => Except.error b

lemma List.map_except_unitIsUnitIffAll {A B: Type} (l: List A) (f: A → Except B Unit): List.map_except_unit l f = Except.ok () ↔ ∀ (a:A), a ∈ l → f a = Except.ok () :=
by
  induction l with
  | nil =>
    simp
    unfold List.map_except_unit
    rfl
  | cons hd tl ih =>
    unfold List.map_except_unit
    simp
    cases f hd with
    | ok u =>
      simp
      rw [ih]
    | error e =>
      simp

def List.eraseAll {A: Type} [DecidableEq A] (l: List A) (a:A):List A :=
  match l with
  | [] => []
  | hd::tl => if a = hd
              then List.eraseAll tl a
              else hd::(List.eraseAll tl a)


lemma List.mem_eraseAll {A: Type} [DecidableEq A] (l: List A) (a b:A): a ∈ List.eraseAll l b ↔ a ∈ l ∧ ¬ a = b :=
by
  induction l with
  | nil =>
    unfold List.eraseAll
    simp
  | cons hd tl ih =>
    unfold List.eraseAll
    by_cases hd_b: b = hd
    simp [hd_b]
    rw [← hd_b]
    rw [ih]
    simp
    intro hn
    intro h
    contradiction

    simp [hd_b]
    rw [ih]
    constructor
    intro h
    cases h with
    | inl h =>
      constructor
      left
      apply h
      rw [h]
      apply Ne.symm
      simp [hd_b]
    | inr h =>
      constructor
      right
      simp [h]
      simp [h]

    intro h
    rcases h with ⟨left,right⟩
    cases left with
    | inl h' =>
      left
      apply h'
    | inr h' =>
      right
      constructor
      apply h'
      apply right



def List.diff' {A: Type} [DecidableEq A] (l1 l2: List A) : List A :=
  match l2 with
  | [] => l1
  | hd::tl => List.diff' (List.eraseAll l1 hd) tl

lemma List.mem_diff' {A: Type} [DecidableEq A] (l1 l2: List A) (a: A): a ∈ List.diff' l1 l2 ↔ a ∈ l1 ∧ ¬ a ∈ l2 :=
by
  induction l2 generalizing l1 with
  | nil =>
    unfold List.diff'
    simp
  | cons hd tl ih =>
    unfold List.diff'
    simp
    rw [ih]
    rw [List.mem_eraseAll]
    tauto

lemma List.diff'_empty {A: Type} [DecidableEq A] (l1 l2: List A): List.diff' l1 l2 = [] ↔ ∀ (a:A), a ∈ l1 → a ∈ l2 := by
  induction l2 generalizing l1 with
  | nil =>
    unfold diff'
    constructor
    intro h a
    rw [h]
    simp

    cases l1 with
    | nil =>
      simp
    | cons hd tl =>
      simp
      exists hd
      intro contra
      contradiction

  | cons hd tl ih =>
    constructor
    intros h
    unfold diff' at h
    intro a a_l1
    by_cases a_hd: a = hd
    rw [a_hd]
    simp

    simp
    right
    specialize ih (eraseAll l1 hd)
    apply Iff.mp ih
    apply h
    rw [List.mem_eraseAll]
    constructor
    apply a_l1
    apply a_hd

    intro h
    unfold diff'
    rw [ih]
    intro a a_erase
    rw [List.mem_eraseAll] at a_erase
    rcases a_erase with ⟨a_l1, a_hd⟩
    specialize h a a_l1
    simp at h
    simp [a_hd] at h
    apply h

def List.map_except.go {A B C: Type} (f: A → Except B C) (l: List A) (curr: List C): Except B (List C) :=
  match l with
  | nil => Except.ok curr
  | cons hd tl =>
    match f hd with
    | Except.ok c =>
      List.map_except.go f tl  (curr.append [c])
    | Except.error msg =>
      Except.error msg

def List.map_except {A B C: Type} (f: A → Except B C) (l: List A): Except B (List C) := List.map_except.go f l []

lemma List.map_except_go_ok_length {A B C: Type} (f: A → Except B C) (l1: List A) (curr l2: List C) (h: List.map_except.go f l1 curr = Except.ok l2):
  List.length l1 + List.length curr = List.length l2 :=
  by
    induction l1 generalizing curr with
    | nil =>
      unfold map_except.go at h
      simp at h
      rw [h]
      simp
    | cons hd tl ih =>
      unfold map_except.go at h
      simp at h
      cases p:f hd with
      | error e =>
        simp [p] at h
      | ok c =>
        simp [p] at h
        specialize ih (curr ++ [c]) h
        rw [← ih]
        simp
        rw [Nat.add_assoc, Nat.add_comm (m:= 1)]
