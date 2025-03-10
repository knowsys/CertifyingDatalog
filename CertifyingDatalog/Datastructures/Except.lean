namespace Except
  theorem is_ok_iff_exists (e: Except A B): (∃ (b:B), e = Except.ok b) ↔ Except.isOk e := by
    cases e with
    | error msg =>
      unfold Except.isOk
      unfold Except.toBool
      simp
    | ok u =>
      unfold Except.isOk
      unfold Except.toBool
      simp

  theorem is_ok_of_ok (b:B): Except.isOk (Except.ok b: Except A B) = true := by
    unfold Except.isOk
    unfold Except.toBool
    simp

  theorem is_ok_of_error (a:A) : Except.isOk (Except.error a: Except A B) = true → False := by
    unfold Except.isOk
    unfold Except.toBool
    simp

  theorem not_equal_ok_unit (e: Except A Unit): ¬ e = Except.ok () ↔ ∃ (a:A), e = Except.error a := by
    cases e with
    | ok u => simp
    | error e => simp
end Except
