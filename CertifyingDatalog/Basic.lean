import Mathlib.Data.Set.Basic


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
