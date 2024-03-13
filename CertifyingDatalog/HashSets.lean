import Std.Data.HashMap
import Std.Data.AssocList
import Mathlib.Data.List.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.AllAny



namespace Std
section HashMap
variable {A:Type} [Hashable A] [DecidableEq A] {B: Type} [DecidableEq B]

lemma Array.mem_if_exists (as: Array A) (a:A): a ∈ as ↔ ∃ (i: Fin as.size), a = as[i] :=
by
  cases as with
  | mk l  =>
    rw [Array.mem_def]
    simp
    rw [List.mem_iff_get]
    constructor
    intro h
    rcases h with ⟨n, get_n⟩
    use n
    apply Eq.symm
    apply get_n

    intro h
    rcases h with ⟨i, get_i⟩
    use i
    apply Eq.symm
    apply get_i

lemma List.mem_set (l: List A)(i: Fin l.length) (a d: A): a ∈ l.set i d ↔ a = d ∨ ∃ (j: Fin l.length), j ≠ i ∧ a = l[j] := by
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
        have isLt_k: Nat.succ k.val < (hd::tl).length := by
          simp
          apply Nat.succ_lt_succ
          apply k.isLt
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
          rw [← Ne.def,←  Fin.val_ne_iff, hj, hi] at j_i
          simp at j_i
        | succ k =>
          have isLt_k: k < tl.length := by
            rw [← Nat.succ_lt_succ_iff, ← hj]
            apply j.isLt
          use Fin.mk k isLt_k
          rw [get_j]
          have hj': j = Fin.mk k.succ _ := by
            rw [Fin.ext_iff]
            simp
            apply hj
            rw [Nat.succ_lt_succ_iff]
            apply isLt_k
          rw [hj', List.get_cons_succ]
    | succ m =>
      rw [List.set_succ]
      simp
      have isLt_m: m < tl.length := by
        rw [← Nat.succ_lt_succ_iff, ← hi]
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
        rw [← Ne.def, ← Fin.val_ne_iff]
        simp [Fin.ext, hi]
      | inr h =>
        cases h with
        | inl ad =>
          left;apply ad
        | inr h =>
          rcases h with ⟨j,j_i, get_j⟩
          right
          have isLt_j: j.val.succ < (hd::tl).length := by
            simp
            rw [Nat.succ_lt_succ_iff]
            apply j.isLt
          use Fin.mk j.val.succ isLt_j
          constructor
          rw [← Ne.def, ← Fin.val_ne_iff]
          simp
          rw [hi]
          rw [← Ne.def,Nat.succ_ne_succ]
          rw [← Ne.def, ← Fin.val_ne_iff] at j_i
          simp at j_i
          rw [Ne.def]
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
            rw [← Nat.succ_lt_succ_iff, ← hj]
            apply j.isLt
          use Fin.mk n isLt_n
          simp
          constructor
          rw [← Ne.def, ← Nat.succ_ne_succ, ← hj, ← hi]
          rw [Fin.val_ne_iff]
          apply j_i
          have isLt_succ_n: n + 1 < (hd::tl).length := by
            simp
            rw [← Nat.succ_eq_add_one, Nat.succ_lt_succ_iff]
            apply isLt_n
          rw [get_j, ← List.get_cons_succ (a:=hd) (h:= isLt_succ_n)]
          congr
          rw [Fin.ext_iff]
          simp [hj]




lemma Array.mem_set (as: Array A) (i: Fin as.size) (a d: A): a ∈ as.set i d ↔ a = d ∨ ∃ (j: Fin as.size), j ≠ i ∧ a = as[j] :=
by
  cases as with
  | mk data =>
    unfold Array.set
    rw [Array.mem_def]
    simp
    rw [List.mem_set]
    tauto

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

lemma Array.foldl_union_set (as: Array A) (f: A → Finset B) (i: Fin as.size) (d: A) (S: Finset B) (b: B):  b ∈ (Array.foldl (fun x y => x ∪ f y) S (as.set i d)) ↔ b ∈ S ∨ b ∈ f d ∨  ∃ (j: Fin as.size), j ≠ i ∧ b ∈ f as[j] := by
  rw [Array.foldl_union]
  constructor
  intro h
  cases h with
  | inl bS =>
    left; apply bS
  | inr a_set =>
    rcases a_set with ⟨a, a_mem, b_a⟩
    rw [Array.mem_def] at a_mem
    unfold Array.set at a_mem
    simp at a_mem
    right
    rw [List.mem_iff_get] at a_mem
    rcases a_mem with ⟨n, get_n⟩
    rw [List.get_set] at get_n
    by_cases i_n: i.val = n.val
    simp [i_n] at get_n
    left
    rw [get_n]
    apply b_a

    simp [i_n] at get_n
    right
    have isLt_n: n.val < as.size := by
      unfold Array.size
      have h: ↑n < List.length (List.set as.data (↑i) d) := by
        apply n.2
      admit
    use Fin.mk n.val isLt_n
    simp
    constructor
    rw [Fin.ext_iff]
    simp [Eq.comm, i_n]

    have as_n_a: as[n] = a := by
      unfold_projs
      unfold Array.get
      apply get_n
    simp at as_n_a
    rw [as_n_a]
    apply b_a

  intro h
  cases h with
  | inl bS =>
    left; apply bS
  | inr get_a =>
    right
    cases get_a with
    | inl bfd =>
      use d
      rw [Array.mem_def, Array.set]
      simp
      constructor
      admit
      apply bfd
    | inr get_j =>
      rcases get_j with ⟨j, j_i, b_j⟩
      use as[j]
      constructor
      admit
      apply b_j




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


instance: DecidableEq (AssocList A B) :=
  fun l1 l2 =>
    match decEq l1.toList l2.toList with
    | isTrue h => isTrue (Iff.mpr (AssocList.eq_iff_toList l1 l2) h)
    | isFalse h => isFalse (Iff.mpr (Iff.ne (AssocList.eq_iff_toList l1 l2)) h)



def HashMap.Imp.Buckets.kv (buckets: HashMap.Imp.Buckets A B): Finset (A × B) := Array.foldl (fun x y => x ∪ y.toList.toFinset) ∅ buckets.val

def HashMap.Imp.kv (m: HashMap.Imp A B): Finset (A × B) := m.2.kv


def HashMap.Imp.kv_member (m: HashMap.Imp A B) (a: A) (b:B): Bool :=
  let ⟨_, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  let bkt := buckets.1[i]

  bkt.containsKeyValue a b

lemma HashMap.Imp.kv_member_iff_in_kv (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a: A) (b:B): (a,b) ∈ m.kv ↔ HashMap.Imp.kv_member m a b = true :=
by
  cases m with
  | mk size buckets =>
    unfold Imp.kv
    unfold Imp.Buckets.kv
    rw [Array.foldl_union]
    unfold kv_member
    simp
    rw [HashMap.Imp.WF_iff] at wf
    simp at wf
    constructor
    intro h
    rcases h with ⟨bkt, bkt_mem, ab_mem⟩
    rw [Array.mem_if_exists] at bkt_mem
    rcases bkt_mem with ⟨i, bkt_i⟩
    have i_eq: i = (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2) := by
      have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val), Std.AssocList.All (fun (k : A) (x : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := by
        rcases wf with ⟨_, wf⟩
        apply wf.hash_self
      specialize hash_self i i.isLt
      unfold AssocList.All at hash_self
      specialize hash_self (a,b)
      rw [bkt_i] at ab_mem
      specialize hash_self ab_mem
      unfold mkIdx
      simp
      rw [Fin.ext_iff, ← hash_self]

    rw [i_eq] at bkt_i
    simp at bkt_i
    rw [← bkt_i]
    rw [← AssocList.mem_containsKeyValue_iff_mem_toList] at ab_mem
    simp at ab_mem
    apply ab_mem

    intro h
    use buckets.1.get (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    simp
    constructor
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    rw [← AssocList.mem_containsKeyValue_iff_mem_toList]
    exact h


def HashMap.Imp.Buckets.keys' (buckets: HashMap.Imp.Buckets A B): Finset A := Array.foldl (fun x y => x ∪ (y.toList.map Prod.fst).toFinset) ∅ buckets.val



lemma HashMap.Imp.Buckets.keys'_mem_iff (buckets: HashMap.Imp.Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (l: AssocList A B), l ∈ buckets.val ∧ l.contains a:=
by
  unfold keys'
  rw [Array.foldl_union]
  simp

def HashMap.Imp.keys' (m: HashMap.Imp A B): Finset A :=
  match m with
  | ⟨_, buckets⟩ => buckets.keys'




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

lemma HashMap.Imp.expand_go_mem (i : Nat) (source : Array (AssocList A B)) (target : Buckets A B) (bkt: AssocList A B): bkt ∈ (HashMap.Imp.expand.go i source target).1 ↔ bkt ∈ target.1 ∨ ∃ (j: Fin source.size), j.val ≥ i ∧ bkt = source[j] := by
  induction' h:(source.size - i)  with n ih generalizing source i target

  rw [Nat.sub_eq_zero_iff_le] at h
  unfold expand.go
  admit

  unfold expand.go
  have h_i: i < source.size := by
    admit
  simp [h_i]
  specialize ih (i+1) (source.set (Fin.mk i h_i) AssocList.nil) (List.foldl (fun d x => reinsertAux d x.1 x.2) target (AssocList.toList source[i]))
  simp at ih
  have h': Array.size source - (i + 1) = n := by
    admit
  specialize ih h'
  rw [ih]



lemma HashMap.Imp.expand_preserves_mem  (size : Nat) (buckets : Buckets A B) (a:A) (b:B): (∃ (bkt: AssocList A B),  (a,b) ∈ bkt.toList ∧ bkt ∈ buckets.1) ↔ ∃ (bkt: AssocList A B),  bkt ∈ (expand size buckets).buckets.1 ∧  (a,b) ∈ bkt.toList := by
  unfold expand
  simp
  simp [HashMap.Imp.expand_go_mem]
  constructor
  intro h
  rcases h with ⟨bkt, ab_mem, bkt_mem⟩
  use bkt
  constructor
  right
  rw [Array.mem_if_exists] at bkt_mem
  apply bkt_mem
  apply ab_mem


  intro h
  rcases h with ⟨bkt, bkt_mem, ab_mem⟩
  use bkt
  constructor
  apply ab_mem
  cases bkt_mem with
  | inl h =>
    unfold Buckets.mk at h
    simp at h
    unfold mkArray at h
    rw [Array.mem_def] at h
    simp at h
    rw [List.mem_replicate] at h
    rcases h with ⟨_, empty⟩
    rw [empty] at ab_mem
    unfold AssocList.toList at ab_mem
    simp at ab_mem
  | inr h =>
    rw [Array.mem_if_exists]
    apply h


lemma HashMap.Imp.insert_semantics (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a ≠ a') ∨ (a, b) = (a', b') :=
by
  rw [← Imp.kv_member_iff_in_kv (wf:=wf), ← Imp.kv_member_iff_in_kv (wf:= Imp.WF.insert wf)]
  cases m with
  | mk size buckets =>
    unfold insert
    simp
    rw [cond_eq_if]
    unfold kv
    unfold Buckets.kv
    simp
    rw [Array.foldl_union, Array.foldl_union]

    split
    simp
    unfold Buckets.update
    unfold Array.uset
    simp only [Array.mem_set]
    constructor
    intro h
    rcases h with ⟨l, h⟩
    rcases h with ⟨get_l, ab_l⟩
    cases get_l with
    | inl replace =>
      rw [replace] at ab_l
      rw [← AssocList.mem_containsKeyValue_iff_mem_toList] at ab_l
      simp at ab_l
      admit
    | inr h =>
      left
      constructor
      use l
      constructor

    admit

    simp
    split
    simp
    unfold Buckets.update
    unfold Array.uset
    simp
    simp [Array.mem_set]

    admit


    rw [← HashMap.Imp.expand_preserves_mem]




def HashMap.keys' (m: HashMap A B): Finset A := m.val.keys'

lemma HashMap.contains_iff (m: HashMap A B): m.contains a ↔ a ∈ m.keys' :=
by
  unfold contains
  unfold keys'
  rw [Imp.contains_iff]
  apply m.2

def HashMap.kv_member (m: HashMap A B) (a: A) (b:B): Bool := m.1.kv_member a b


lemma HashMap.insert_semantics (m: HashMap A B) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a' ≠ a) ∨ (a, b) = (a', b') :=
by
  sorry


end HashMap

abbrev HashSet (A:Type) [Hashable A] [BEq A] := HashMap A Unit

section HashSet
variable {A:Type} [Hashable A] [BEq A][LawfulBEq A]

def HashSet.contains (S: HashSet A) (a:A): Bool := HashMap.contains S a

def HashSet.insert (S: HashSet A) (a:A): HashSet A := HashMap.insert S a ()


end HashSet
