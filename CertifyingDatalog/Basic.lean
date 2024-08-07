import CertifyingDatalog.Datastructures.Array
import CertifyingDatalog.Datastructures.AssocList
import CertifyingDatalog.Datastructures.Except
import CertifyingDatalog.Datastructures.Finset
import CertifyingDatalog.Datastructures.HashMap
import CertifyingDatalog.Datastructures.HashSet
import CertifyingDatalog.Datastructures.List
import CertifyingDatalog.Datastructures.Tree

namespace Nat
  lemma pred_lt_of_lt' (n m : ℕ) (h : n < m) : n.pred < m := by
    cases n with
    | zero =>
      unfold Nat.pred
      simp
      apply h
    | succ n =>
      unfold Nat.pred
      simp
      apply Nat.lt_of_succ_lt h

  lemma pred_gt_zero_iff_ge_two (n : ℕ) : n.pred > 0 ↔ n ≥ 2 := by 
    cases n with
    | zero => simp
    | succ n => cases n <;> simp

  lemma ge_two_im_gt_zero (n: ℕ) (h: n ≥ 2): n > 0 := by
    cases n with
    | zero =>
      simp at h
    | succ m =>
      simp
end Nat

