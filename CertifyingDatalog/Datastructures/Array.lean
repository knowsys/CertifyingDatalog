import CertifyingDatalog.Datastructures.List

namespace Array

  lemma mem_iff_get (a:A) (as: Array A): a ∈ as ↔ ∃ i : Fin as.size, as[i] = a := by
    rw [mem_def, List.mem_iff_get]
    constructor
    · intro h
      rcases h with ⟨n, get_n⟩
      use n
      apply get_n
    · intro h
      rcases h with ⟨i, get_i⟩
      use i
      exact get_i

  lemma get_set_not_eq (as: Array A) (i: Fin as.size) (j : Nat) (hj : j < as.size) (v : A) (i_j: ¬ j = i.val): (as.set i v)[j]'(by simp [*]) = as[j] := by
    rw [get_set]
    simp
    intro h
    simp_rw[h] at i_j
    simp at i_j
    exact hj

  lemma mem_iff_exists (as: Array A) (a:A): a ∈ as ↔ ∃ (i: Fin as.size), a = as[i] :=
  by
    cases as with
    | mk l  =>
      rw [mem_def]
      simp
      rw [List.mem_iff_get]
      constructor
      intro h
      rcases h with ⟨n, get_n⟩
      use n
      apply Eq.symm
      apply get_n

      intro h
      rcases h with ⟨i, get_i⟩
      use i
      apply Eq.symm
      apply get_i

  lemma mem_set_iff (as: Array A) (i: Fin as.size) (a d: A): a ∈ as.set i d ↔ a = d ∨ ∃ (j: Fin as.size), j ≠ i ∧ a = as[j] :=
  by
    cases as with
    | mk data =>
      unfold set
      rw [mem_def]
      simp
      rw [List.mem_set_iff]
      tauto

  lemma foldl_union [DecidableEq B] (as: Array A) (f: A → Finset B) (S: Finset B) (b: B):  b ∈ (foldl (fun x y => x ∪ f y) S as) ↔ b ∈ S ∨ ∃ (a: A), a ∈ as ∧ b ∈ f a :=
  by
    cases as with
    | mk data =>
      simp
      induction data generalizing S with
      | nil =>
        simp
      | cons hd tl ih =>
        unfold List.foldl
        rw [ih]
        simp
        tauto

  lemma get_mem (as: Array A) (i: Fin as.size): as[i] ∈ as :=
  by
    rw [mem_def]
    apply getElem_mem_toList

end Array
