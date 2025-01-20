import Std.Data.HashSet

variable {A : Type u} [Hashable A] [DecidableEq A]

namespace Std.HashSet
  def subset (S S': HashSet A): Prop := ∀ (b:A), S.contains b → S'.contains b

  instance : HasSubset (HashSet A) where
    Subset := subset

  theorem subset_refl {S: HashSet A} : S ⊆ S := by
    unfold HasSubset.Subset
    unfold instHasSubset_certifyingDatalog
    simp
    unfold subset
    simp

  theorem subset_trans {S1 S2 S3: HashSet A} (h1: S1 ⊆ S2) (h2: S2 ⊆ S3): S1 ⊆ S3 := by
    unfold HasSubset.Subset at *
    unfold instHasSubset_certifyingDatalog at *
    simp at *
    unfold subset at *
    intro b S1_b
    apply h2
    apply h1
    apply S1_b

  theorem subset_iff  {S1 S2: HashSet A} : S1 ⊆ S2 ↔ (∀ (a:A), S1.contains a → S2.contains a) := by
    unfold HasSubset.Subset
    unfold instHasSubset_certifyingDatalog
    simp
    unfold subset
    simp
end Std.HashSet

