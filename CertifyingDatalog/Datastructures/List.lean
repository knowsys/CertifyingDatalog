import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace List
  def toSet {A: Type u} [DecidableEq A] (l: List A): Set A := l.toFinset.toSet

  lemma toSet_mem {A: Type u} [DecidableEq A] (a:A) (l: List A): a ∈ l ↔ a ∈ l.toSet := by simp [toSet]

  def mapExceptUnit (l: List A) (f: A → Except B Unit): Except B Unit :=
    match l with
    | [] => Except.ok ()
    | hd::tl =>
      match f hd with
      | Except.ok () => mapExceptUnit tl f
      | Except.error b => Except.error b

  lemma mapExceptUnit_iff (l: List A) (f: A → Except B Unit): mapExceptUnit l f = Except.ok () ↔ ∀ (a:A), a ∈ l → f a = Except.ok () :=
  by
    induction l with
    | nil => simp [mapExceptUnit]
    | cons hd tl ih =>
      cases eq : f hd with
      | ok u => simp [eq, mapExceptUnit, ih]
      | error e => simp [eq, mapExceptUnit]

  def mapExcept.go (f: A → Except B C) (l: List A) (curr: List C): Except B (List C) :=
    match l with
    | nil => Except.ok curr
    | cons hd tl =>
      match f hd with
      | Except.ok c =>
        mapExcept.go f tl (curr.append [c])
      | Except.error msg =>
        Except.error msg

  def mapExcept (f: A → Except B C) (l: List A): Except B (List C) := mapExcept.go f l []

  lemma mapExcept_go_ok_length (f: A → Except B C) (l1: List A) (curr l2: List C) (h: mapExcept.go f l1 curr = Except.ok l2):
    length l1 + length curr = length l2 :=
    by
      induction l1 generalizing curr with
      | nil =>
        unfold mapExcept.go at h
        simp at h
        rw [h]
        simp
      | cons hd tl ih =>
        unfold mapExcept.go at h
        simp at h
        cases p:f hd with
        | error e =>
          simp [p] at h
        | ok c =>
          simp [p] at h
          specialize ih (curr ++ [c]) h
          rw [← ih]
          simp
          rw [Nat.add_assoc, Nat.add_comm (m:= 1)]

  lemma mapExcept_ok_length (f: A → Except B C) (l1: List A) (l2: List C) (h: mapExcept f l1 = Except.ok l2): length l1 = length l2 :=
  by
    have h': length l1 + @length C nil = length l2 := by
      apply mapExcept_go_ok_length f l1
      unfold mapExcept at h
      apply h
    simp at h'
    apply h'

  def foldl_union {A : Type u} {B : Type v} [DecidableEq B]  (f: A → Finset B) (init: Finset B) (l: List A): Finset B := foldl (fun x y => x ∪ f y) init l

  lemma mem_foldl_union {A : Type u} {B : Type v} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (b:B): b ∈ foldl_union f init l ↔ b ∈ init ∨ ∃ (a:A), a ∈ l ∧ b ∈ f a :=
  by
    unfold foldl_union
    induction l generalizing init with
    | nil => simp
    | cons hd tl ih => simp [ih, or_assoc]

  lemma subset_foldl_union {A : Type u} {B : Type v} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B): init ⊆ foldl_union f init l := by
    unfold foldl_union
    induction l generalizing init with
    | nil => simp
    | cons hd tl ih =>
      simp
      apply Finset.Subset.trans (s₂ := init ∪ f hd)
      . apply Finset.subset_union_left
      . apply ih

  lemma subset_result_foldl_union {A : Type u} {B : Type v} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (a:A) (mem: a ∈ l): f a ⊆ foldl_union f init l := by
    unfold foldl_union
    induction l generalizing init with
    | nil => contradiction
    | cons hd tl ih =>
      simp at mem
      simp
      cases mem with
      | inl a_hd =>
        rw [a_hd]
        apply Finset.Subset.trans (s₂ := init ∪ f hd)
        . apply Finset.subset_union_right
        . apply subset_foldl_union
      | inr a_tl =>
        apply ih
        exact a_tl

  lemma foldl_union_empty {A : Type u} {B : Type v} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B):foldl_union f init l = ∅ ↔ init = ∅ ∧ ∀ (a:A), a ∈ l → f a = ∅ := by
    unfold foldl_union
    induction l generalizing init with
    | nil => simp
    | cons hd tl ih =>
      simp [ih, Finset.union_eq_empty, and_assoc]

  lemma foldl_union_subset_set {A : Type u} {B : Type v} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (S: Set B): ↑( foldl_union f init l) ⊆ S ↔ ↑init ⊆ S ∧ ∀ (a:A), a ∈ l → ↑ (f a) ⊆ S:= by
    unfold foldl_union
    induction l generalizing init with
    | nil => simp
    | cons hd tl ih =>
      simp [ih, and_assoc]

  lemma foldl_append_mem (l1: List A) (l2: List B) (f: B → List A) (a: A): a ∈ foldl (fun x y => x ++ f y) l1 l2 ↔ a ∈ l1 ∨ ∃ (b: B), b ∈ l2 ∧ a ∈ f b := by
    induction l2 generalizing l1 with
    | nil => simp
    | cons hd tl ih =>
      unfold foldl
      rw [ih]
      simp [or_assoc]

  theorem foldl_cons_is_concat (as bs : List α) : as.foldl (fun acc a => a :: acc) bs = as.reverse ++ bs := by 
    revert bs
    induction as with 
    | nil => simp 
    | cons a as ih => 
      simp
      intro _
      apply ih

  theorem elem_concat_iff_elem_of_one (as bs : List α) : ∀ e, e ∈ (as ++ bs) ↔ e ∈ as ∨ e ∈ bs := by simp 

  theorem find_concat (as bs : List α) : ∀ f, (as ++ bs).find? f = (as.find? f).orElse (fun () => bs.find? f) := by 
    intro f 
    induction as with 
    | nil => simp
    | cons a as ih =>
      have find_sem : ∀ a as, (a :: as).find? f = if f a then some a else (as.find? f) := by 
        intro a as
        conv => left; unfold find?
        split 
        case h_1 _ h => simp[h]
        case h_2 _ h => simp[h]
      have : ∀ (a : α) (as bs : List α), (a :: as ++ bs) = (a :: (as ++ bs)) := by simp
      rw [this]
      rw [find_sem]
      split
      case isTrue h => rw [find_sem]; simp[h]
      case isFalse h => rw [find_sem]; simp[h]; rw [ih]

  lemma find?_mem_iff (l: List A) (p: A → Bool) (a:A) (unique: List.Pairwise (fun x y => ¬ (p x = true ∧ p y = true)) l): l.find? p = some a ↔ a ∈ l ∧ p a = true := by
    induction l with
    | nil =>
      simp
    | cons hd tl ih =>
      unfold List.find?
      by_cases p_hd: p hd = true
      simp [p_hd]
      constructor
      intro hd_a
      constructor
      left
      apply Eq.symm hd_a
      rw [← hd_a]
      exact p_hd
      intro h
      rcases h with ⟨a_mem, p_a⟩
      cases a_mem with
      | inl a_hd =>
        apply Eq.symm a_hd
      | inr a_tl =>
        simp at unique
        rcases unique with ⟨unique, _⟩
        specialize unique a a_tl p_hd
        rw [unique] at p_a
        contradiction

      simp [p_hd]
      rw [ih]
      aesop
      aesop

  lemma mem_set (l: List A)(i: Fin l.length) (a d: A): a ∈ l.set i d ↔ a = d ∨ ∃ (j: Fin l.length), j ≠ i ∧ a = l[j] := by
    simp
    induction l with
    | nil =>
      exfalso
      simp at i
      have h: i.val < 0 := i.isLt
      simp at h
    | cons hd tl ih =>
      cases hi: i.val with
      | zero =>
        simp
        rw [List.mem_iff_get]
        constructor
        intro h
        cases h with
        | inl a_d =>
          left
          apply a_d
        | inr get_a =>
          rcases get_a with ⟨k, get_a⟩
          right
          have isLt_k: Nat.succ k.val < (hd::tl).length := by simp
          use Fin.mk (Nat.succ k.val) isLt_k
          constructor
          cases i with
          | mk i_val isLt_i =>
            simp
            simp at hi
            rw [hi]
            simp
          rw [← get_a]
          rw [← List.get_cons_succ (a:=hd)]

        intro h
        cases h with
        | inl ad =>
          left;apply ad
        | inr h =>
          rcases h with ⟨j, j_i, get_j⟩
          right
          cases hj:j.val with
          | zero =>
            rw [← Ne.eq_def, ← Fin.val_ne_iff, hj, hi] at j_i
            simp at j_i
          | succ k =>
            have isLt_k: k < tl.length := by
              rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hj]
              apply j.isLt
            use Fin.mk k isLt_k
            rw [get_j]
            have hj': j = Fin.mk k.succ (by simp [isLt_k]) := by
              rw [Fin.ext_iff]
              simp
              apply hj
            rw [hj', List.get_cons_succ]
      | succ m =>
        rw [List.set_succ]
        simp
        have isLt_m: m < tl.length := by
          rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hi]
          apply i.isLt
        specialize ih (Fin.mk m isLt_m)
        rw [ih]
        constructor
        intro h
        cases h with
        | inl ahd =>
          right
          use 0
          simp [ahd]
          rw [← Ne.eq_def, ← Fin.val_ne_iff]
          simp [Fin.ext, hi]
        | inr h =>
          cases h with
          | inl ad =>
            left;apply ad
          | inr h =>
            rcases h with ⟨j,j_i, get_j⟩
            right
            have isLt_j: j.val.succ < (hd::tl).length := by simp
            use Fin.mk j.val.succ isLt_j
            constructor
            rw [← Ne.eq_def, ← Fin.val_ne_iff]
            simp
            rw [hi]
            rw [← Ne.eq_def, Nat.succ_ne_succ]
            rw [← Ne.eq_def, ← Fin.val_ne_iff] at j_i
            simp at j_i
            rw [Ne.eq_def]
            apply j_i

            simp
            apply get_j

        intro h
        cases h with
        | inl ad =>
          right;left;apply ad
        | inr h =>
          rcases h with ⟨j, j_i, get_j⟩
          cases hj: j.val with
          | zero =>
            left
            rw [get_j]
            have j_zero: j = 0 := by
              rw [Fin.ext_iff]
              apply hj
            rw [j_zero, List.get_cons_zero]
          | succ n =>
            right
            right
            have isLt_n: n < tl.length := by
              rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hj]
              apply j.isLt
            use Fin.mk n isLt_n
            simp
            constructor
            rw [← Ne.eq_def, ← Nat.succ_ne_succ, Nat.succ_eq_add_one, ← hj, Nat.succ_eq_add_one, ← hi]
            rw [Fin.val_ne_iff]
            apply j_i
            have isLt_succ_n: n + 1 < (hd::tl).length := by simp; apply isLt_n
            rw [get_j, ← List.get_cons_succ (a:=hd) (h:= isLt_succ_n)]
            congr
            rw [Fin.ext_iff]
            simp [hj]

  lemma replaceF_distinct_mem [DecidableEq A] (l: List (A × B)) (dist: List.Pairwise (fun x y => ¬ x.1 = y.1) l) (a: A) (ab ab': A × B) (mem: ∃ (c: A × B), c ∈ l ∧ c.1 = a): ab ∈  List.replaceF (fun x => if x.1 == a then some ab' else none) l ↔ (ab ∈ l ∧ ab.1 ≠ a) ∨ ab = ab' := by
    induction l with
    | nil =>
      simp at mem
    | cons hd tl ih =>
      unfold List.replaceF
      simp
      by_cases hd_a: hd.1 = a
      simp [hd_a]
      by_cases ab_a: ab.1 = a
      have ab_tl: ¬ ab ∈ tl := by
        simp at dist
        rcases dist with ⟨dist, _⟩
        specialize dist ab.1 ab.2
        simp at dist
        by_contra ab_tl
        specialize dist ab_tl
        rw [← ab_a] at hd_a
        contradiction
      simp [ab_a, ab_tl]

      simp[ab_a]
      have ab_hd: ¬ ab = hd := by
        by_contra h
        rw [h] at ab_a
        contradiction
      simp [ab_hd]
      tauto

      simp [hd_a]
      rw [List.pairwise_cons] at dist
      rcases dist with ⟨_, tl_dist⟩
      specialize ih tl_dist
      have mem': (∃ c ∈ tl, c.1 = a) := by
        rcases mem with ⟨c, c_mem, c_a⟩
        simp at c_mem
        have c_hd: ¬ c = hd := by
          by_contra p
          rw [p] at c_a
          contradiction
        simp [c_hd] at c_mem
        use c
      specialize ih mem'
      simp at ih
      rw [ih]

      rw [← or_assoc, or_and_left]
      have h: (ab = hd ∨ ¬ab.1 = a) ↔ ¬ ab.1 = a := by
        constructor
        intro h
        cases h with
        | inl h =>
          rw [h]
          apply hd_a
        | inr h =>
          apply h
        tauto
      rw [h]

  lemma tail_get (l : List A) (h : 0 < l.length) : ∀ i : Fin (l.length - 1), 
    l.tail.get ⟨i.val, by rw [length_tail]; exact i.isLt⟩ = 
    l.get ⟨i.val.succ, by 
      have isLt := Nat.succ_lt_succ i.isLt; 
      conv at isLt => right; rw [Nat.succ_eq_add_one]
      rw [Nat.sub_one_add_one_eq_of_pos h] at isLt
      apply isLt⟩ := by 
        cases l with 
        | nil => contradiction
        | cons a as => simp

  lemma tail_getLast (l : List A) (h : l.tail ≠ []) : l.tail.getLast h = l.getLast (by intro contra; simp [contra] at h) := by 
    cases l with 
    | nil => simp at h
    | cons a as =>
      simp
      rw [List.getLast_cons]

  lemma head_append (as bs : List A) (h : as ≠ []) : (as ++ bs).head (by intro contra; simp at contra; apply h; apply contra.left) = as.head h := by 
    cases as with 
    | nil => contradiction
    | cons a as => rfl
  
  lemma take_head (l : List A) (ne : l ≠ []) (n : Nat) (h : 0 < n) : (l.take n).head (by intro contra; simp at contra; cases contra; contradiction; case inr h' => rw [h'] at h; contradiction) = l.head ne := by 
    cases n.eq_zero_or_eq_succ_pred with 
    | inl contra => rw [contra] at h; contradiction
    | inr eq => 
      let m := n.pred
      have eq : n = m.succ := by simp [m]; rw [eq]; simp
      cases l with 
      | nil => contradiction
      | cons a as =>
        simp
        simp [eq]

  lemma take_getLast (l : List A) (ne : l ≠ []) (n : Fin (l.length + 1)) (h : 0 < n.val) : (l.take n.val).getLast (by intro contra; simp at contra; cases contra; contradiction; case inr h' => rw [h'] at h; contradiction) = l.get ⟨n.val - 1, by apply Nat.sub_lt_right_of_lt_add; apply Nat.le_of_pred_lt; apply h; apply n.isLt⟩ := by 
    have : (l.take n.val).length = n.val := by simp; apply Nat.le_of_lt_succ; apply n.isLt
    rw [List.getLast_eq_get]
    simp only [this]
    rw [List.get_take']
end List
