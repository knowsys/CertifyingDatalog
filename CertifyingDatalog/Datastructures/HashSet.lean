import CertifyingDatalog.Datastructures.HashMap

namespace Batteries
  abbrev HashSet (A : Type u) [Hashable A] [DecidableEq A] := Batteries.HashMap A Unit

  variable {A : Type u} [Hashable A] [DecidableEq A]

  namespace HashSet
    def empty: HashSet A := HashMap.empty

    def contains (S: HashSet A) (a:A): Bool := HashMap.contains S a

    def insert (S: HashSet A) (a:A): HashSet A := HashMap.insert S a ()

    lemma contains_insert {S: HashSet A} (a:A ): ∀ (a':A), (S.insert a).contains a' ↔ S.contains a' ∨ a = a' := by
      intro a'
      unfold insert
      unfold contains
      simp [HashMap.contains_iff, HashMap.keys'_iff_kv]
      constructor
      intro h
      rcases h with ⟨b, h⟩
      rw [HashMap.insert_semantics] at h
      simp at h
      cases h with
      | inl h =>
        left
        use b
        simp[h]
      | inr h =>
        right
        apply h

      intro h
      use ()
      rw [HashMap.insert_semantics]
      simp
      by_cases a_a': a = a'
      simp [a_a']

      simp [a_a']
      simp [a_a'] at h
      constructor
      rcases h with ⟨_, h⟩
      apply h
      apply Ne.symm
      apply a_a'

    lemma empty_contains: ∀ (a:A), ¬ empty.contains a :=
    by
      intro a
      simp
      apply HashMap.empty_contains

    def subset (S S': HashSet A): Prop := ∀ (b:A), S.contains b → S'.contains b

    instance : HasSubset (HashSet A) := ⟨subset⟩

    lemma subset_refl {S: HashSet A} : S ⊆ S :=
    by
      unfold_projs at *
      unfold subset at *
      simp


    lemma subset_trans {S1 S2 S3: HashSet A} (h1: S1 ⊆ S2) (h2: S2 ⊆ S3): S1 ⊆ S3 :=
    by
      unfold_projs at *
      unfold subset at *
      intro b S1_b
      apply h2
      apply h1
      apply S1_b

    lemma subset_iff  {S1 S2: HashSet A} : S1 ⊆ S2 ↔ (∀ (a:A), S1.contains a → S2.contains a) :=
    by
      unfold_projs
      unfold subset
      simp
  end HashSet
end Batteries
