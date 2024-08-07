import Mathlib.Data.Bool.AllAny
import Batteries.Data.HashMap.WF

import CertifyingDatalog.Datastructures.Array
import CertifyingDatalog.Datastructures.AssocList
import CertifyingDatalog.Datastructures.List

variable {A : Type u} [DecidableEq A] [Hashable A] {B : Type v} [DecidableEq B]

instance: Batteries.HashMap.LawfulHashable A := {hash_eq := by simp}

instance: PartialEquivBEq A := {symm:= by simp, trans:= by simp}

namespace Batteries.HashMap.Imp.Buckets
  lemma mem_update (buckets: Buckets A B) (i : USize) (d: AssocList A B) (h : USize.toNat i < Array.size buckets.1) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (buckets.update i d h).1 ∧ ab ∈ bkt.toList) ↔ ab ∈ d.toList ∨ ∃ (j: Fin buckets.1.size), j.1 ≠ i.toNat ∧ ab ∈ (buckets.1[j]).toList :=
  by
    unfold update
    simp [Array.mem_set_iff]
    constructor
    intro g
    cases g with
    | inl g =>
      left
      apply g
    | inr g =>
      rcases g with ⟨bkt, g, ab_bkt⟩
      rcases g with ⟨j, j_i, bkt_j⟩
      right
      use j
      constructor
      rw [← Ne.eq_def, ← Fin.val_ne_iff] at j_i
      simp at j_i
      apply j_i
      rw [← bkt_j]
      apply ab_bkt

    intro g
    cases g with
    | inl g =>
      left
      apply g
    | inr g =>
      rcases g with ⟨j, j_i, ab_mem⟩
      right
      use buckets.1[j]
      constructor
      use j
      constructor
      rw [← Ne.eq_def, ← Fin.val_ne_iff]
      simp
      apply j_i
      simp
      apply ab_mem

  def kv (buckets: Buckets A B): Finset (A × B) := Array.foldl (fun x y => x ∪ y.toList.toFinset) ∅ buckets.val

  def keys' (buckets: Buckets A B): Finset A := Array.foldl (fun x y => x ∪ (y.toList.map Prod.fst).toFinset) ∅ buckets.val

  lemma keys'_iff_kv (buckets: Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (b:B), (a,b) ∈ buckets.kv:= by
    unfold keys'
    unfold kv
    simp_rw [Array.foldl_union]
    simp
    tauto

  lemma keys'_mem_iff (buckets: Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (l: AssocList A B), l ∈ buckets.val ∧ l.contains a:=
  by
    unfold keys'
    rw [Array.foldl_union]
    simp

  def toList (buckets : Buckets A B) : List (A × B) := List.foldl (fun mb a => List.foldl (fun mb a => a :: mb) mb a.toList) [] buckets.val.data

  theorem in_toList_means_in_list_at_index (buckets : Buckets A B) : (a, b) ∈ buckets.toList -> a ∈ buckets.keys' := by 
    intro h
    rw [keys'_iff_kv]
    exists b
    unfold kv
    simp [Array.foldl_eq_foldl_data]
    unfold toList at h
    revert h
    have : ∀ bucket_list : List _, (a, b) ∈ List.foldl (fun mb a => List.foldl (fun mb a => a :: mb) mb a.toList) bucket_list buckets.val.data -> (a, b) ∈ List.foldl (fun x y => x ∪ y.toList.toFinset) bucket_list.toFinset buckets.val.data := by 
      induction buckets.val.data with 
      | nil => simp
      | cons bucket buckets ih => 
        intro bucket_list h
        simp at h 
        simp
        have : (bucket.toList.reverse ++ bucket_list).toFinset = bucket_list.toFinset ∪ bucket.toList.toFinset := by 
          apply Finset.ext
          intro pair 
          simp [Or.comm]
        rw [← this]
        apply ih
        rw [List.foldl_cons_is_concat] at h
        apply h
    apply this []

  theorem in_list_at_index_means_in_toList (buckets : Buckets A B) : a ∈ buckets.keys' -> ∃ b, (a,b) ∈ buckets.toList := by 
    intro h
    rw [keys'_iff_kv] at h
    cases h with | intro b hb =>
      unfold kv at hb
      simp [Array.foldl_eq_foldl_data] at hb
      exists b
      unfold toList
      revert hb
      have : ∀ bucket_list : List _, (a, b) ∈ List.foldl (fun x y => x ∪ y.toList.toFinset) bucket_list.toFinset buckets.val.data -> (a, b) ∈ List.foldl (fun mb a => List.foldl (fun mb a => a :: mb) mb a.toList) bucket_list buckets.val.data := by 
        induction buckets.val.data with 
        | nil => simp
        | cons bucket buckets ih => 
          intro bucket_list hb
          simp at hb
          simp
          rw [List.foldl_cons_is_concat]
          apply ih
          have : (bucket.toList.reverse ++ bucket_list).toFinset = bucket_list.toFinset ∪ bucket.toList.toFinset := by 
            apply Finset.ext
            intro pair 
            simp [Or.comm]
          rw [this]
          apply hb
      apply this []

  lemma distinct_elements (buckets: Buckets A B) (wf: Buckets.WF buckets) (l: AssocList A B) (mem: l ∈ buckets.1): List.Pairwise (fun x y => ¬x.1 = y.1) l.toList := by
    have dist: ∀ (bucket : Batteries.AssocList A B),
    bucket ∈ buckets.val.data →
      List.Pairwise (fun (a b : A × B) => ¬(a.fst == b.fst) = true) (Batteries.AssocList.toList bucket) := by
        apply wf.distinct
    simp at dist
    apply dist
    rw [← Array.mem_def]
    apply mem

  lemma element_member_in_hash_bucket (a: A ) (b: B) (buckets: Buckets A B) (wf: Buckets.WF buckets) (i: Fin (buckets.1.size)): (a,b) ∈ buckets.1[↑i].toList →  i.val = USize.toNat (mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
    have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val),
    Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := by
      apply wf.hash_self
    specialize hash_self i.val i.isLt
    unfold AssocList.All at hash_self
    simp at hash_self
    unfold mkIdx
    simp
    intro h
    apply Eq.symm
    apply hash_self
    apply h
end Batteries.HashMap.Imp.Buckets

namespace Batteries.HashMap.Imp
  def kv (m: Imp A B): Finset (A × B) := m.2.kv

  def kv_member (m: Imp A B) (a: A) (b:B): Bool :=
    let ⟨_, buckets⟩ := m
    let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
    let bkt := buckets.1[i]

    (a,b) ∈ bkt.toList

  lemma kv_member_iff_in_kv (m: Imp A B) (wf: Imp.WF m) (a: A) (b:B): (a,b) ∈ m.kv ↔ Imp.kv_member m a b = true :=
  by
    cases m with
    | mk size buckets =>
      unfold Imp.kv
      unfold Imp.Buckets.kv
      rw [Array.foldl_union]
      unfold kv_member
      simp
      rw [Imp.WF_iff] at wf
      simp at wf
      constructor
      intro h
      rcases h with ⟨bkt, bkt_mem, ab_mem⟩
      rw [Array.mem_iff_exists] at bkt_mem
      rcases bkt_mem with ⟨i, bkt_i⟩
      have i_eq: i = (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2) := by
        have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val), Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := by
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
      apply ab_mem

      intro h
      use buckets.1.get (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
      simp
      constructor
      exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
      exact h

  def keys' (m: Imp A B): Finset A :=
    match m with
    | ⟨_, buckets⟩ => buckets.keys'

  lemma keys'_iff_kv (m: Imp A B) (a:A): a ∈ m.keys' ↔ ∃ (b:B), (a,b) ∈ m.kv:= by
    unfold keys'
    unfold kv
    cases m with
    | mk size buckets =>
      simp
      rw [Buckets.keys'_iff_kv]


  lemma contains_iff (m: Imp A B) (wf: Imp.WF m): m.contains a ↔ a ∈ m.keys' :=
  by
    cases m with
    | mk size buckets =>
      unfold contains
      simp only
      constructor
      intro h
      unfold keys'
      simp
      unfold Buckets.keys'
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
      rw [Buckets.keys'_mem_iff] at h
      rcases h with ⟨l, l_buckets, a_l⟩
      rw [Imp.WF_iff] at wf
      simp at wf
      rcases wf with ⟨_, wf⟩
      rw [Batteries.AssocList.contains_eq, List.any_iff_exists]
      unfold mkIdx
      simp
      rw [Batteries.AssocList.contains_eq, List.any_iff_exists] at a_l
      rcases a_l with ⟨ab, ab_mem, ab_a⟩
      use ab.2
      rw [← Array.contains_def] at l_buckets
      unfold Array.contains at l_buckets
      rw [Array.any_iff_exists] at l_buckets
      rcases l_buckets with ⟨i, _, i_len, l_buckets⟩
      simp at l_buckets

      have i_val : i = USize.toNat (UInt64.toUSize (hash a) % Array.size buckets.val) := by
        have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val),
        Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := wf.hash_self

        specialize hash_self i.val i_len
        unfold AssocList.All at hash_self
        specialize hash_self ab
        rw [l_buckets] at hash_self
        specialize hash_self ab_mem
        simp at ab_a
        rw [← ab_a]
        rw [hash_self]

      simp [← i_val, ← l_buckets]
      simp at ab_a
      simp [← ab_a]
      rw [l_buckets]
      apply ab_mem

  lemma foldl_reinsertAux (source:(AssocList A B)) (target: Buckets A B) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (List.foldl (fun d x => reinsertAux d x.1 x.2) target (AssocList.toList source)).1 ∧ ab ∈ bkt.toList ) ↔ (∃ (bkt: AssocList A B),  bkt ∈ target.1 ∧ ab ∈ bkt.toList) ∨ ab ∈ source.toList := by
    induction source generalizing target with
    | nil =>
      unfold List.foldl
      simp
    | cons hda hdb tl ih =>
      unfold List.foldl
      simp
      rw [ih]
      unfold reinsertAux
      simp
      rw [Buckets.mem_update, AssocList.toList_cons]
      simp

      rw [or_assoc (a:= ab = (hda, hdb)), or_comm (a:= (ab = (hda, hdb))), or_assoc (c:= ab ∈ AssocList.toList tl), Array.splitLemma (b:= ab) (f:= AssocList.toList) (as:=target.1) (i:=USize.toNat (Imp.mkIdx target.2 (UInt64.toUSize (hash hda)))) (h:= (Imp.mkIdx target.2 (UInt64.toUSize (hash hda))).2)]
      simp

  lemma expand_go_mem (i : Nat) (source : Array (AssocList A B)) (target : Buckets A B) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (expand.go i source target).1 ∧ ab ∈ bkt.toList) ↔ ∃ (bkt: AssocList A B), (bkt ∈ target.1 ∨ ∃ (j: Fin source.size), j.val ≥ i ∧ bkt = source[j]) ∧ ab ∈ bkt.toList := by
    induction' h:(source.size - i)  with n ih generalizing source i target

    rw [Nat.sub_eq_zero_iff_le] at h
    unfold expand.go
    have if_cond: ¬ i < Array.size source := by
      apply Nat.not_lt_of_le
      apply h
    simp [if_cond]

    constructor
    intro g
    rcases g with ⟨bkt, bkt_mem, ab_mem⟩
    use bkt
    constructor
    left
    apply bkt_mem
    apply ab_mem

    intro g
    rcases g with ⟨bkt, g, ab_mem⟩
    cases g with
    | inl g =>
      use bkt
    | inr g =>
      rcases g with ⟨j, i_le_j, _⟩
      have lt_self: Array.size source < Array.size source := by
        apply Nat.lt_of_le_of_lt (m:=j.val)
        apply Nat.le_trans
        apply h
        apply i_le_j
        apply j.isLt
      simp at lt_self
    --step
    unfold expand.go
    split
    swap
    rename_i h'
    simp at h'
    exfalso
    aesop
    rename_i h_i
    simp [h_i]
    specialize ih (i+1) (source.set (Fin.mk i h_i) AssocList.nil) (List.foldl (fun d x => reinsertAux d x.1 x.2) target (AssocList.toList source[i]))
    simp at ih
    rw [ih]
    swap
    rw [← Nat.succ_eq_add_one, Nat.sub_succ, h]
    simp

    simp_rw [or_and_right, exists_or]
    constructor
    intro g
    cases g with
    | inl g =>
      rw [foldl_reinsertAux] at g
      cases g with
      | inl g =>
        left
        apply g
      | inr g =>
        right
        use source.get (Fin.mk i h_i)
        constructor
        use (Fin.mk i h_i)
        simp
        apply g
    | inr g =>
      rcases g with ⟨bkt,g,ab_mem⟩
      right
      use bkt
      rcases g with ⟨j, j_i, bkt_set⟩
      have j_isLt: j.val < Array.size source := by
        have h: j.val < Array.size (Array.set source {val:=i, isLt := h_i} AssocList.nil) := by
          apply j.isLt
        simp at h
        exact h

      have i_j: ¬ i = j.val := by
        by_contra p
        simp_rw [← p, ← Nat.succ_eq_add_one, Nat.succ_le_iff] at j_i
        simp at j_i
      constructor
      use Fin.mk j.val j_isLt
      simp
      constructor
      apply Nat.le_trans (m:= i+1)
      simp
      apply j_i
      simp [bkt_set]
      rw [Array.get_set_not_eq]
      simp
      aesop
      exact ab_mem

    intro g
    rw [foldl_reinsertAux]
    cases g with
    | inl g =>
      left
      left
      apply g
    | inr g =>
      rcases g with ⟨bkt, g, ab_mem⟩
      rcases g with ⟨j,i_j, bkt_j⟩
      by_cases j_i: i = j.val
      left
      right
      have source_eq: source[i] = source[j.val] := by
        simp_rw [j_i]
      rw [source_eq, ← bkt_j]
      apply ab_mem

      right
      use bkt
      have h_k: ∃ (k: Fin (Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil))), k.val = j.val := by
        have k': j.val < (Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil)) := by
          rw [Array.size_set]
          apply j.isLt
        use Fin.mk j.val k'
      rcases h_k with ⟨k, k_j⟩
      · constructor
        use k
        constructor
        · rw [k_j, ← Nat.succ_eq_add_one, Nat.succ_le_iff]
          apply Nat.lt_of_le_of_ne
          apply i_j
          exact j_i
        rw [Array.get_set]
        simp
        split
        · rename_i i_k
          rw [i_k] at j_i
          contradiction

        · rw [bkt_j]
          simp_rw [k_j]
        have h': source.size = Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil) := by
          simp
        simp_rw [h']
        exact k.isLt
        exact ab_mem

  lemma expand_preserves_mem  (size : Nat) (buckets : Buckets A B) (a:A) (b:B): (∃ (bkt: AssocList A B),  bkt ∈ buckets.1 ∧ (a,b) ∈ bkt.toList) ↔ ∃ (bkt: AssocList A B),  bkt ∈ (expand size buckets).buckets.1 ∧  (a,b) ∈ bkt.toList := by
    unfold expand
    simp [expand_go_mem]
    unfold Buckets.mk
    unfold mkArray

    constructor
    intro h
    rcases h with ⟨bkt, bkt_mem, ab_mem⟩
    use bkt
    constructor
    right
    rw [Array.mem_iff_exists] at bkt_mem
    apply bkt_mem
    apply ab_mem

    intro h
    rcases h with ⟨bkt, bkt_mem, ab_mem⟩
    use bkt
    constructor
    cases bkt_mem with
    | inl h =>
      unfold Buckets.mk at h
      simp at h
      rw [Array.mem_def] at h
      simp at h
      rcases h with ⟨_, empty⟩
      rw [empty] at ab_mem
      unfold AssocList.toList at ab_mem
      contradiction
    | inr h =>
      rw [Array.mem_iff_exists]
      apply h

    apply ab_mem

  lemma insert_semantics (m: Imp A B) (wf: Imp.WF m) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a ≠ a') ∨ (a, b) = (a', b') :=
  by
    rw [← kv_member_iff_in_kv (wf:=wf), ← kv_member_iff_in_kv (wf:= Imp.WF.insert wf)]
    cases m with
    | mk size buckets =>
      rw [Imp.WF_iff] at wf
      simp at wf
      rcases wf with ⟨_, wf⟩
      unfold insert
      simp
      rw [cond_eq_if]
      unfold kv
      unfold Buckets.kv
      simp
      rw [Array.foldl_union, Array.foldl_union]
      simp

      split
      rename_i mem
      simp at mem
      simp
      rw [Buckets.mem_update]
      rw [Array.splitLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
      simp
      simp_rw [cond_eq_if]
      rcases mem with ⟨b_,mem⟩
      rw [List.replaceF_distinct_mem]
      simp
      constructor
      intro h
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          left
          rcases h with ⟨h, a_a'⟩
          constructor
          left
          apply h
          apply Ne.symm
          apply a_a'
        | inr h =>
          right
          simp [h]
      | inr h =>
        left
        constructor
        right
        apply h
        rcases h with ⟨j, j_hash, ab'_mem⟩
        by_contra a_a'
        have j_hash': j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
          apply Buckets.element_member_in_hash_bucket
          apply wf
          rw [a_a']
          apply ab'_mem
        contradiction
      intro h
      cases h with
      | inl h =>
        rcases h with ⟨h, a_a'⟩
        cases h with
        | inl h =>
          left
          left
          constructor
          apply h
          apply Ne.symm
          apply a_a'
        | inr h =>
          right
          apply h
      | inr h =>
        left
        right
        simp [h]
      apply Buckets.distinct_elements
      apply wf
      apply Array.get_mem (as:=buckets.1) (i:= Fin.mk (USize.toNat (mkIdx buckets.2 (UInt64.toUSize (hash a)))) (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)
      use (a,b_)



      rename_i a_mem
      simp at a_mem
      split
      simp
      rw [Buckets.mem_update]
      simp
      rw [Array.splitLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
      simp
      constructor
      intro h
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          right
          simp [h]
        | inr h =>
          left;
          constructor
          left
          apply h
          by_contra p
          specialize a_mem b'
          rw [← p] at h
          contradiction
      | inr h =>
        left
        constructor
        right
        apply h
        by_contra a_a'
        rcases h with ⟨j, j_idx, ab'_mem⟩
        have j_idx': ↑j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
          apply Buckets.element_member_in_hash_bucket a b'
          apply wf
          rw [a_a']
          apply ab'_mem
        contradiction
      intro h
      cases h with
      | inl h =>
        rcases h with ⟨h, _⟩
        cases h with
        | inl h =>
          left;right;
          apply h
        | inr h =>
          right
          apply h
      | inr h =>
        left;left
        simp [h]


      rw [← expand_preserves_mem]
      rw [Buckets.mem_update]
      rw [Array.splitLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
      simp
      constructor
      intro h
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          right
          simp [h]
        | inr h =>
          left
          constructor
          left
          apply h
          by_contra p
          specialize a_mem b'
          rw [p] at a_mem
          rw [p] at h
          contradiction
      | inr h =>
        left
        constructor
        right
        apply h
        by_contra p
        rcases h with ⟨j, j_mdIx, ab'_mem⟩
        rw [← p] at ab'_mem
        have j_idx': j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
          apply Buckets.element_member_in_hash_bucket a b'
          apply wf
          apply ab'_mem
        contradiction

      intro h
      cases h with
      | inl h =>
        rcases h with ⟨h,_⟩
        cases h with
        | inl h =>
          left
          right
          apply h
        | inr h =>
          right
          apply h
      | inr h =>
        left
        left
        simp [h]

  lemma pairwise_diff_to_element_if_bucket (l: AssocList A B) (m: Imp A B) (wf: Imp.WF m) (mem: l ∈ m.buckets.1) (a:A): List.Pairwise (fun x y => ¬((x.1 == a) = true ∧ (y.1 == a) = true))
    (AssocList.toList l ) := by
      have distinct: List.Pairwise (fun x y => ¬x.1 = y.1) l.toList := by
        apply Buckets.distinct_elements
        rw [Imp.WF_iff] at wf
        apply And.right wf
        exact mem
      simp at distinct
      apply AssocList.pairwise_diff_to_element_if_all_diff
      exact distinct

  lemma find_iff_kv (m: Imp A B) (wf: Imp.WF m) (a:A) (b:B): m.find? a = some b ↔ m.kv_member a b = true := by
    cases m with
    | mk size buckets =>
      unfold kv_member
      unfold find?
      simp
      constructor
      intro h
      rcases h with ⟨a',mem⟩
      rw [List.find?_mem_iff] at mem
      simp at mem
      rcases mem with ⟨mem, a_a'⟩
      rw [a_a'] at mem
      exact mem
      apply pairwise_diff_to_element_if_bucket
      use wf
      simp
      exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)

      intro h
      use a
      rw [List.find?_mem_iff]
      simp
      exact h
      apply pairwise_diff_to_element_if_bucket
      use wf
      simp
      exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)

  lemma contains_iff_find? (m: Imp A B) (wf: Imp.WF m) (a:A): m.contains a ↔ ∃ (b:B), m.find? a = some b := by
    unfold contains
    unfold find?
    cases m with
    | mk size buckets =>
      simp
      constructor
      intro h
      rcases h with ⟨b, mem⟩
      use b
      use a
      rw [List.find?_mem_iff]
      simp
      exact mem
      apply pairwise_diff_to_element_if_bucket
      use wf
      simp
      exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)

      intro h
      rcases h with ⟨b,a',mem⟩
      use b
      rw [List.find?_mem_iff] at mem
      simp at mem
      aesop
      apply pairwise_diff_to_element_if_bucket
      use wf
      simp
      exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
end Batteries.HashMap.Imp

namespace Batteries.HashMap
  def keys' (m: HashMap A B): Finset A := m.val.keys'

  lemma contains_iff (m: HashMap A B) (a: A): m.contains a ↔ a ∈ m.keys' :=
  by
    unfold contains
    unfold keys'
    rw [Imp.contains_iff]
    apply m.2

  def kv_member (m: HashMap A B) (a: A) (b:B): Bool := m.1.kv_member a b

  lemma find_iff_kv (m: HashMap A B)  (a:A) (b:B): m.find? a = some b ↔ m.kv_member a b = true := by
    unfold find?
    unfold kv_member
    apply Imp.find_iff_kv
    exact m.2

  lemma keys'_iff_kv (m: HashMap A B) (a:A): a ∈ m.keys' ↔ ∃ (b:B), m.kv_member a b:= by
    cases m with
    | mk m wf =>
      unfold keys'
      unfold kv_member
      simp
      rw [Imp.keys'_iff_kv]
      simp_rw [Imp.kv_member_iff_in_kv (wf:=wf)]


  lemma insert_semantics (m: HashMap A B) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a' ≠ a) ∨ (a, b) = (a', b') :=
  by
    unfold kv_member
    unfold insert
    simp [Imp.insert_semantics m.1 m.2 a a' b b']
    tauto

  lemma contains_insert (m : HashMap A B) (a a': A) (b:B): (m.insert a b).contains a' ↔ m.contains a' ∨ a == a' := by
    simp_rw [contains_iff, keys'_iff_kv]
    constructor
    intro h
    rcases h with ⟨b',h⟩
    rw [insert_semantics] at h
    by_cases a_a': a = a'
    simp [a_a']

    simp [a_a'] at *
    use b'
    simp [h]

    intro h'
    by_cases a_a': a = a'
    use b
    rw [insert_semantics]
    right
    rw [a_a']

    simp[a_a'] at h'
    rcases h' with ⟨b', h⟩
    use b'
    rw [insert_semantics]
    left
    simp [h, a_a']
    aesop

  lemma find_insert (m: HashMap A B) (a a': A) (b :B): (m.insert a b).find? a' = if a' = a then some b else m.find? a' := by
    split
    rename_i h
    rw [find_iff_kv, insert_semantics, h]
    right
    rfl

    rename_i h
    cases h': find? m a' with
    | some b2 =>
      rw [find_iff_kv, insert_semantics]
      left
      constructor
      rw [← find_iff_kv]
      exact h'
      aesop
    | none =>
      rw [Option.eq_none_iff_forall_not_mem]
      by_contra p
      simp at p
      rcases p with ⟨b2, find_b2⟩
      rw [find_iff_kv, insert_semantics] at find_b2
      simp[h] at find_b2
      cases find_b2 with
      | inl h_1 =>
        rw [← find_iff_kv] at h_1
        rw [h_1] at h'
        simp at h'
      | inr h_1 =>
        aesop

  lemma contains_iff_find? (m: HashMap A B)  (a:A): m.contains a ↔ ∃ (b:B), m.find? a = some b := by
    unfold contains
    unfold find?
    apply Imp.contains_iff_find?
    exact m.2

  lemma contains_of_find? (m: HashMap A B)  (a:A) (b:B) (h: m.find? a = some b): m.contains a := by
    rw [contains_iff_find?]
    use b

  lemma findD_eq_find? (m: HashMap A B) (a:A) (b:B): m.findD a b = match m.find? a with
                      | some b' => b'
                      | none => b := by
    unfold findD
    rw [Option.getD_eq_iff]
    aesop

  lemma not_contains_find_none (m: HashMap A B) (a:A) (h: ¬ m.contains a = true): m.find? a = none := by
    rw [contains_iff_find?] at h
    simp at h
    cases h':find? m a with
    | some b =>
      specialize h b
      contradiction
    | none =>
      rfl

  section ForGraphValivation
    theorem findD_is_default_when_not_contains (hm : HashMap A B) (a : A) (h : ¬ hm.contains a) : ∀ b, hm.findD a b = b := by
      intro b
      rw [findD_eq_find?]
      split
      rename_i b' find
      have mem: contains hm a = true := by
        apply contains_of_find?
        exact find
      contradiction

      rfl

    theorem in_projection_of_toList_iff_contains (hm : HashMap A B) (a : A) : a ∈ hm.toList.map Prod.fst ↔ hm.contains a := by
      rw [List.mem_map]
      simp
      unfold toList
      unfold fold
      unfold Imp.fold
      unfold Id.run
      unfold Imp.foldM
      simp [Array.foldlM_eq_foldlM_data, List.foldlM_eq_foldl]
      
      rw [contains_iff] 
      
      constructor
      · intro h 
        cases h with | intro b hb => 
          apply Imp.Buckets.in_toList_means_in_list_at_index
          apply hb
      · intro h 
        unfold keys' at h
        unfold Imp.keys' at h
        simp at h
        cases Imp.Buckets.in_list_at_index_means_in_toList _ h with | intro b hb => exists b

    lemma empty_contains: ∀ (a:A), (@HashMap.empty A B).contains a = false :=
    by
      intro a
      unfold contains
      unfold empty
      unfold mkHashMap
      unfold Imp.empty
      simp
      unfold Imp.empty'
      unfold Imp.contains
      simp
      unfold Imp.Buckets.mk
      simp

    theorem ofList_mapped_to_pair_contains_iff_list_elem (l : List A) (a : A) : ∀ b : B, (ofList (l.map (fun a => (a, b)))).contains a ↔ a ∈ l := by 
      intro b
      unfold ofList
      simp
      
      have : ∀ hm : HashMap A B, (List.foldl (fun m x => m.insert x.1 x.2) hm (List.map (fun a => (a, b)) l)).contains a = true ↔ hm.contains a ∨ a ∈ l := by 
        induction l with 
        | nil => simp 
        | cons head tail ih => 
          simp
          intro hm 
          rw [ih (hm.insert head b)]
          rw [contains_insert]
          have : a = head ↔ head = a := by constructor <;> apply Eq.symm
          rw [this]
          simp [or_assoc]

      have applied_this := this empty
      rw [empty_contains] at applied_this
      simp at applied_this
      apply applied_this

    theorem findD_ofList_is_list_find_getD (l : List (A × B)) (a : A) : ∀ b, (ofList l).findD a b = ((l.reverse.find? (fun x => x.fst == a)).map Prod.snd).getD b := by 
      intro b 
      unfold ofList
      simp

      have : ∀ hm : HashMap A B, (List.foldl (fun m x => m.insert x.1 x.2) hm l).findD a b = (Option.map Prod.snd (List.find? (fun x => x.1 == a) l.reverse)).getD (hm.findD a b) := by 
        induction l with 
        | nil => simp
        | cons head tail ih => 
          simp
          intro hm
          rw [ih (hm.insert head.1 head.2)]
          have findD_insert : ∀ b, (hm.insert head.1 head.2).findD a b = if a = head.1 then head.2 else hm.findD a b := by 
            intro b
            rw [findD_eq_find?]
            rw [findD_eq_find?]
            rw [find_insert]
            split
            case h_1 _ b hb => 
              split at hb
              case isTrue h => 
                simp [h]
                injection hb with hb
                rw [hb]
              case isFalse h => 
                simp [h]
                rw [hb]
            case h_2 b _ hb => 
              split at hb
              case isTrue _ => contradiction
              case isFalse h => 
                simp [h]
                rw [hb]
          rw [findD_insert]
          split
          case isTrue h =>
            have : (tail.reverse ++ [head]).find? (fun x => x.1 == a) = (tail.reverse.find? (fun x => x.1 == a)).getD head := by 
              rw [List.find_concat]
              have : [head].find? (fun x => x.1 == a) = some head := by unfold List.find?; simp [h]
              rw [this]
              have : ∀ {α} (opt : Option α) (x : α), opt.orElse (fun _ => some x) = Option.some (opt.getD x) := by 
                intro _ opt x
                unfold Option.orElse
                split <;> simp
              rw [this]
            rw [this]
            simp
          case isFalse h =>
            have : (tail.reverse ++ [head]).find? (fun x => x.1 == a) = tail.reverse.find? (fun x => x.1 == a) := by 
              rw [List.find_concat]
              have : (head.1 == a) = false := by simp; intro contra; apply h; rw [contra]
              have : [head].find? (fun x => x.1 == a) = none := by unfold List.find?; simp [this]
              rw [this]
              have : ∀ {α} (opt : Option α), opt.orElse (fun _ => none) = opt := by
                intro _ opt
                unfold Option.orElse
                split <;> simp
              rw [this]
            rw [this]

      rw [this]
      rw [findD_is_default_when_not_contains]
      simp
      apply empty_contains

    theorem findD_insert (hm : HashMap A B) (a a' : A) (h: ¬ hm.contains a = true): ∀ b, (hm.insert a b).findD a' b = hm.findD a' b := by
      intro b
      rw [findD_eq_find?, findD_eq_find?, find_insert]
      by_cases a_a': a' = a
      simp [a_a']
      have find_hm : find? hm a = none := by
        apply not_contains_find_none
        exact h
      simp [find_hm]

      simp [a_a']

    theorem findD_insert' (hm : HashMap A B) (a : A) (b : B) : ∀ b', (hm.insert a b).findD a b' = b := by
      intro b'
      rw [findD_eq_find?, find_insert]
      simp

    theorem findD_insert'' (hm : HashMap A B) (a a' : A) (h : a ≠ a') : ∀ b b', (hm.insert a b).findD a' b' = hm.findD a' b' := by
      intro b b'
      rw [findD_eq_find?, findD_eq_find?, find_insert]
      aesop
  end ForGraphValivation
end Batteries.HashMap

