import CertifyingDatalog.Datastructures.List

namespace Array

  lemma mem_iff_get {a:A} {as: Array A}: a ∈ as ↔ ∃ i : Fin as.size, as[i] = a := by
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
end Array
