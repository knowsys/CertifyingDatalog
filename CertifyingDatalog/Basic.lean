module

public import CertifyingDatalog.Datastructures.Array
public import CertifyingDatalog.Datastructures.Except
public import CertifyingDatalog.Datastructures.Finset
public import CertifyingDatalog.Datastructures.HashSet
public import CertifyingDatalog.Datastructures.List
public import CertifyingDatalog.Datastructures.Tree

@[expose] public section

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

namespace Option
universe u

lemma filter_true {α : Type u} {o : Option α}:
    o.filter (fun _ => true) = o := by
  unfold Option.filter
  cases o <;> rfl

lemma forall_ne {α : Type u} {o : Option α} :
    (∀ (a : α), ¬ o = some a) ↔ o = none := by
  cases o with
  | none => simp
  | some a' => simp

end Option
