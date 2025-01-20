import Mathlib.Data.Finset.Basic

namespace Finset
  -- added based on https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/finset.2Efilter
  noncomputable def filter_nc (p: A → Prop) (S: Finset A) := @Finset.filter A p (Classical.decPred p) S

  lemma mem_filter_nc {a:A} {p: A → Prop} {S: Finset A} : a ∈ filter_nc p S ↔ p a ∧ a ∈ S :=
  by
    simp [filter_nc, Finset.mem_filter, And.comm]
end Finset
