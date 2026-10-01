module

import Aesop.BuiltinRules
import Mathlib.Data.Finset.Attr
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

public section

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
