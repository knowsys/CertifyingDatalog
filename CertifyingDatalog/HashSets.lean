import Std.Data.HashMap
import Std.Data.AssocList
import Mathlib.Data.List.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.AllAny



namespace Std
section HashMap
variable {A:Type} [Hashable A] [BEq A] [LawfulBEq A] [DecidableEq A] {B: Type} [DecidableEq B]

lemma Array.foldl_union (as: Array A) (f: A → Finset B) (S: Finset B) (b: B):  b ∈ (Array.foldl (fun x y => x ∪ f y) S as) ↔ b ∈ S ∨ ∃ (a: A), a ∈ as ∧ b ∈ f a :=
by
  simp [Array.foldl_eq_foldl_data, Array.mem_def]
  cases as with
  | mk data =>
    simp
    induction data generalizing S with
    | nil =>
      simp
    | cons hd tl ih =>
      unfold List.foldl
      rw [ih]
      simp
      tauto

lemma Array.get_mem (as: Array A) (i: Fin as.size): as[i] ∈ as :=
by
  rw [Array.mem_def]
  apply Array.getElem_mem_data

lemma AssocList.eq_iff_toList (l1 l2: AssocList A B): l1 = l2 ↔ l1.toList = l2.toList :=
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

instance: DecidableEq (AssocList A B) :=
  fun l1 l2 =>
    match decEq l1.toList l2.toList with
    | isTrue h => isTrue (Iff.mpr (AssocList.eq_iff_toList l1 l2) h)
    | isFalse h => isFalse (Iff.mpr (Iff.ne (AssocList.eq_iff_toList l1 l2)) h)


def HashMap.Imp.Buckets.keys' (buckets: HashMap.Imp.Buckets A B): Finset A := Array.foldl (fun x y => x ∪ (y.toList.map Prod.fst).toFinset) ∅ buckets.val



lemma HashMap.Imp.Buckets.keys'_mem_iff (buckets: HashMap.Imp.Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (l: AssocList A B), l ∈ buckets.val ∧ l.contains a:=
by
  unfold keys'
  rw [Array.foldl_union]
  simp

def HashMap.Imp.keys' (m: HashMap.Imp A B): Finset A :=
  match m with
  | ⟨_, buckets⟩ => buckets.keys'

def AssocList.containsKeyValue (l: AssocList A B) (a: A) (b: B): Bool :=
  match l with
  | nil => false
  | cons hda hdb tl =>
    if a == hda
    then
      if b == hdb
      then true
      else AssocList.containsKeyValue  tl a b
    else AssocList.containsKeyValue  tl a b

lemma AssocList.mem_containsKeyValue_iff_mem_toList (l: AssocList A B) (ab :A × B): AssocList.containsKeyValue l ab.1 ab.2 ↔ ab ∈ l.toList :=
by
  induction l with
  | nil =>
    unfold containsKeyValue
    simp
  | cons hda hdb tl ih =>
    unfold containsKeyValue
    constructor
    intro h
    simp
    by_cases hda_ab: ab.1 = hda
    by_cases hdb_ab: ab.2 = hdb
    left
    ext
    simp[*]
    simp[*]

    simp[hda_ab, hdb_ab] at h
    right
    rw [← ih]
    simp [h, hda_ab]

    simp [hda_ab] at h
    right
    rw [← ih]
    apply h

    -- back direction
    intro h
    unfold toList at h
    simp at h
    by_cases hda_ab: ab.1 = hda
    by_cases hdb_ab: ab.2 = hdb
    simp [hda_ab, hdb_ab]

    simp [hda_ab]
    cases h with
    | inl h =>
      rw [h] at hdb_ab
      simp at hdb_ab
    | inr h =>
      rw [← ih, hda_ab] at h
      simp [h]


    cases h with
    | inl h =>
      rw [h] at hda_ab
      simp at hda_ab
    | inr h =>
      rw [← ih] at h
      simp [h]


lemma HashMap.Imp.contains_iff (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m): m.contains a ↔ a ∈ m.keys' :=
by
  cases m with
  | mk size buckets =>
    unfold contains
    simp only
    constructor
    intro h
    unfold keys'
    simp
    unfold HashMap.Imp.Buckets.keys'
    rw [Array.foldl_union]
    simp
    use buckets.1.get (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    simp
    constructor
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    rw [AssocList.contains_eq, List.any_iff_exists] at h
    simp at h
    apply h

    intro h
    unfold keys' at h
    simp at h
    rw [HashMap.Imp.Buckets.keys'_mem_iff] at h
    rcases h with ⟨l, l_buckets, a_l⟩
    rw [Std.HashMap.Imp.WF_iff] at wf
    simp at wf
    rcases wf with ⟨_, wf⟩
    rw [Std.AssocList.contains_eq, List.any_iff_exists]
    unfold mkIdx
    simp
    rw [Std.AssocList.contains_eq, List.any_iff_exists] at a_l
    rcases a_l with ⟨ab, ab_mem, ab_a⟩
    use ab.2
    rw [← Array.contains_def] at l_buckets
    unfold Array.contains at l_buckets
    rw [Array.any_iff_exists] at l_buckets
    rcases l_buckets with ⟨i, _, i_len, l_buckets⟩
    simp at l_buckets

    have i_val : i = USize.toNat (UInt64.toUSize (hash a) % Array.size buckets.val) := by
      have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val),
      Std.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := wf.hash_self

      specialize hash_self i.val i_len
      unfold AssocList.All at hash_self
      specialize hash_self ab
      rw [← l_buckets] at hash_self
      specialize hash_self ab_mem
      simp at ab_a
      rw [← ab_a]
      rw [hash_self]

    simp [← i_val, ← l_buckets]
    simp at ab_a
    rw [← ab_a]
    apply ab_mem


def HashMap.keys' (m: HashMap A B): Finset A := m.val.keys'

lemma HashMap.contains_iff (m: HashMap A B): m.contains a ↔ a ∈ m.keys' :=
by
  unfold contains
  unfold keys'
  rw [Imp.contains_iff]
  apply m.2




end HashMap

abbrev HashSet (A:Type) [Hashable A] [BEq A] := HashMap A Unit

section HashSet
variable {A:Type} [Hashable A] [BEq A][LawfulBEq A]

def HashSet.contains (S: HashSet A) (a:A): Bool := HashMap.contains S a

def HashSet.insert (S: HashSet A) (a:A): HashSet A := HashMap.insert S a ()


end HashSet
