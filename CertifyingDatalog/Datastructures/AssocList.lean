import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Tauto

namespace Batteries.AssocList
  theorem eq_iff_toList (l1 l2: AssocList A B): l1 = l2 ↔ l1.toList = l2.toList :=
  by
    induction l1 generalizing l2 with
    | nil =>
      cases l2 with
      | nil =>
        simp
      | cons hda hdb tl =>
        simp
    | cons hda hdb tl ih =>
      cases l2 with
      | nil =>
        simp
      | cons hda' hdb' tl' =>
        simp
        rw [ih]
        tauto

  instance [DecidableEq A] [DecidableEq B] : DecidableEq (AssocList A B) :=
    fun l1 l2 =>
      match decEq l1.toList l2.toList with
      | isTrue h => isTrue (Iff.mpr (AssocList.eq_iff_toList l1 l2) h)
      | isFalse h => isFalse (Iff.mpr (Iff.ne (AssocList.eq_iff_toList l1 l2)) h)

  lemma toList_cons (hda: A) (hdb: B) (tl: AssocList A B): toList (cons hda hdb tl) = (hda, hdb)::tl.toList := by
    unfold AssocList.toList
    split
    rfl
    next n =>
      simp

  lemma pairwise_diff_to_element_if_all_diff [DecidableEq A] (l: AssocList A B)(a:A) (h:List.Pairwise (fun x y => ¬x.1 = y.1) l.toList): List.Pairwise (fun x y => ¬((x.1 == a) = true ∧ (y.1 == a) = true)) (AssocList.toList l ) := by
    induction l with
    | nil =>
      simp
    | cons hda hdb tl ih =>
      simp
      constructor
      intro a' b' ab'_tl hda_a
      rw [← hda_a]
      simp at h
      intro contra
      apply (And.left h)
      exact ab'_tl
      rw [contra]
      simp at ih
      apply ih
      simp at h
      apply And.right h
end Batteries.AssocList

