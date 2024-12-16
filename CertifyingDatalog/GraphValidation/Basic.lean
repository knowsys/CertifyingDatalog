import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog

theorem Std.HashMap.mem_keys_iff_contains [DecidableEq A] [Hashable A] (hm : Std.HashMap A B) (k : A) : k ∈ hm.keys ↔ hm.contains k := by
  sorry

theorem Std.HashMap.ofList_mapped_to_pair_contains_iff_list_elem [DecidableEq A] [Hashable A] (l : List A) (a : A) : ∀ b : B, (Std.HashMap.ofList (l.map (fun a => (a, b)))).contains a ↔ a ∈ l := by
  intro b
  unfold ofList
  unfold DHashMap.Const.ofList
  unfold DHashMap.Const.insertMany
  unfold contains
  simp

  have : ∀ hm : HashMap A B, (List.foldl (fun m x => m.insert x.1 x.2) hm (List.map (fun a => (a, b)) l)).contains a = true ↔ hm.contains a ∨ a ∈ l := by
    induction l with
    | nil => simp
    | cons head tail ih =>
      simp
      intro hm
      rw [ih (hm.insert head b)]
      rw [contains_insert]
      simp
      have : a = head ↔ head = a := by constructor <;> apply Eq.symm
      rw [this]
      conv => left; left; rw [or_comm]
      rw [or_assoc]

  have applied_this := this empty
  simp at applied_this
  sorry
  /- apply applied_this -/

theorem Std.HashMap.getD_ofList_is_list_find_getD [DecidableEq A] [Hashable A] (l : List (A × B)) (a : A) : ∀ b, (Std.HashMap.ofList l).getD a b = ((l.reverse.find? (fun x => x.fst == a)).map Prod.snd).getD b := by
  sorry

abbrev PreGraph (A: Type u) [DecidableEq A] [Hashable A] := Std.HashMap A (List A)

namespace PreGraph
  variable {A: Type u} [DecidableEq A] [Hashable A]

  def vertices (g : PreGraph A) : List A := g.keys
  def predecessors (g : PreGraph A) (a : A) : List A := g.getD a []

  def complete (pg: PreGraph A) := ∀ (a:A), pg.contains a →  ∀ (a':A), a' ∈ (pg.predecessors a) → pg.contains a'

  theorem in_vertices_iff_contains (pg: PreGraph A) (a : A) : a ∈ pg.vertices ↔ pg.contains a := by unfold vertices; apply Std.HashMap.mem_keys_iff_contains
  theorem in_predecessors_iff_found (pg: PreGraph A) (a : A) : ∀ b, b ∈ pg.predecessors a ↔ b ∈ (pg.getD a []) := by unfold predecessors; intros; rfl

  def from_vertices (vs : List A) : PreGraph A := Std.HashMap.ofList (vs.map (fun v => (v, [])))

  def add_vertex (pg : PreGraph A) (v : A) : PreGraph A :=
    if pg.contains v then
      pg
    else
      pg.insert v []

  def add_vertices (pg : PreGraph A) (vs : List A) : PreGraph A :=
    vs.foldl (fun (acc : PreGraph A) u => acc.add_vertex u) pg

  theorem add_vertices_contains_iff_contains_or_in_list (pg : PreGraph A) (vs : List A) : ∀ v, (pg.add_vertices vs).contains v ↔ pg.contains v ∨ (¬ pg.contains v ∧ v ∈ vs) := by
    induction vs generalizing pg with
    | nil => simp [add_vertices]
    | cons u us ih =>
      simp [add_vertices]
      intro v
      unfold add_vertices at ih
      rw [ih]
      constructor
      intro h
      cases h with
      | inl hl =>
        unfold add_vertex at hl
        split at hl
        apply Or.inl
        exact hl
        rw [Std.HashMap.contains_insert] at hl
        cases Decidable.em (pg.contains v) with
        | inl v_in_pg => apply Or.inl; exact v_in_pg
        | inr v_not_in_pg =>
          simp at hl
          cases hl with
          | inl hl => apply Or.inr; constructor; simp at v_not_in_pg; exact v_not_in_pg; apply Or.inl; apply Eq.symm; exact hl
          | inr _ => contradiction
      | inr hr =>
        unfold add_vertex at hr
        split at hr
        apply Or.inr
        constructor
        simp at hr
        exact hr.left
        apply Or.inr
        exact hr.right
        rw [Std.HashMap.contains_insert] at hr
        cases Decidable.em (pg.contains v) with
        | inl v_in_pg => apply Or.inl; exact v_in_pg
        | inr v_not_in_pg => apply Or.inr; constructor; simp at v_not_in_pg; exact v_not_in_pg; apply Or.inr; exact hr.right
      intro h
      cases h with
      | inl hl =>
        apply Or.inl;
        unfold add_vertex
        split
        exact hl
        rw [Std.HashMap.contains_insert]
        simp
        apply Or.inr
        exact hl
      | inr hr =>
        let ⟨hrl, hrr⟩ := hr
        cases hrr with
        | inl v_is_u =>
          apply Or.inl
          unfold add_vertex
          split
          case isTrue u_in_pg =>
            apply False.elim; rw [v_is_u] at hrl
            have : ¬ pg.contains u := by simp [hrl]
            contradiction
          rw [Std.HashMap.contains_insert]
          simp
          apply Or.inl
          rw [v_is_u]
        | inr v_in_us =>
          cases Decidable.em ((pg.add_vertex u).contains v)
          apply Or.inl
          assumption
          apply Or.inr
          constructor
          assumption
          exact v_in_us

  theorem add_vertices_getD_semantics (pg : PreGraph A) (vs : List A) (a : A): (pg.add_vertices vs).getD a [] = pg.getD a [] := by
    induction vs generalizing pg with
    | nil => simp [add_vertices]
    | cons u us ih =>
      simp [add_vertices]
      have ih_plugged_in := ih (pg.add_vertex u)
      unfold add_vertices at ih_plugged_in
      rw [ih_plugged_in]
      unfold add_vertex
      split
      . rfl
      case isFalse h =>
        rw [Std.HashMap.getD_insert]
        simp
        intro eq
        apply Eq.symm
        rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false]
        rw [← eq]
        simp at h
        exact h

  def add_vertex_with_predecessors (pg : PreGraph A) (v : A) (vs : List A) : PreGraph A :=
    let pg_with_added_predecessors := if pg.contains v then pg.insert v ((pg.predecessors v) ++ vs) else pg.insert v vs
    PreGraph.add_vertices pg_with_added_predecessors vs

  theorem from_vertices_contains_exactly_the_passed_vertices (vs : List A) : ∀ v, v ∈ (PreGraph.from_vertices vs).vertices ↔ v ∈ vs := by
    unfold vertices
    unfold from_vertices
    intro v
    rw [Std.HashMap.mem_keys_iff_contains, Std.HashMap.ofList_mapped_to_pair_contains_iff_list_elem]

  theorem from_vertices_no_vertex_has_predecessors (vs : List A) : ∀ v, (PreGraph.from_vertices vs).getD v [] = [] := by
    intro needle
    unfold from_vertices
    rw [Std.HashMap.getD_ofList_is_list_find_getD]
    sorry

  theorem from_vertices_is_complete (vs : List A) : (PreGraph.from_vertices vs).complete := by
    let pg := PreGraph.from_vertices vs
    have : ∀ v, pg.getD v [] = [] := by
      intro v
      apply from_vertices_no_vertex_has_predecessors
    intro a ha b hb
    rw [← in_vertices_iff_contains] at ha
    unfold predecessors at hb
    rw [this a] at hb
    contradiction

  theorem add_vertex_with_predecessors_contains_iff_contains_or_in_new_vertices (pg : PreGraph A) (v : A) (vs : List A) : ∀ a, (pg.add_vertex_with_predecessors v vs).contains a ↔ (pg.contains a ∧ a = v) ∨ (pg.contains a ∧ a ≠ v) ∨ ((¬ pg.contains a) ∧ a = v) ∨ ((¬ pg.contains a) ∧ a ≠ v ∧ a ∈ vs) := by
    unfold add_vertex_with_predecessors
    simp
    intro a
    rw [add_vertices_contains_iff_contains_or_in_list]
    constructor
    intro h
    cases h with
    | inl hl =>
      split at hl
      case isTrue hl' =>
        rw [Std.HashMap.contains_insert] at hl
        simp at hl
        cases hl with
        | inl hll =>
          apply Or.inl
          constructor
          rw [← hll]
          apply hl'
          rw [hll]
        | inr hlr =>
          cases Decidable.em (a = v) with
          | inl a_eq_v => apply Or.inl; constructor; exact hlr; exact a_eq_v
          | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hlr; exact a_neq_v
      case isFalse hr' =>
        rw [Std.HashMap.contains_insert] at hl
        simp at hl
        cases hl with
        | inl hll =>
          apply Or.inr
          apply Or.inr
          apply Or.inl
          constructor
          rw [← hll]
          simp at hr'
          apply hr'
          rw [hll]
        | inr hlr =>
          cases Decidable.em (a = v) with
          | inl a_eq_v => apply Or.inl; constructor; exact hlr; exact a_eq_v
          | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hlr; exact a_neq_v
    | inr hr =>
      let ⟨hrl, hrr⟩ := hr
      split at hrl
      case isTrue hl' =>
        rw [Std.HashMap.contains_insert] at hrl
        simp at hrl
        cases Decidable.em (a = v) with
        | inl a_eq_v =>
          rw [a_eq_v] at hrl
          have contra := hrl.left
          contradiction
        | inr a_neq_v =>
          cases Decidable.em (pg.contains a) with
          | inl pg_contains =>
            rw [pg_contains] at hrl
            have contra := hrl.right
            contradiction
          | inr pg_not_contains =>
            apply Or.inr
            apply Or.inr
            apply Or.inr
            constructor
            simp at pg_not_contains
            apply pg_not_contains
            constructor
            apply a_neq_v
            apply hrr
      case isFalse hr' =>
        rw [Std.HashMap.contains_insert] at hrl
        simp at hrl
        cases Decidable.em (a = v) with
        | inl a_eq_v =>
          rw [a_eq_v] at hrl
          have contra := hrl.left
          contradiction
        | inr a_neq_v =>
          cases Decidable.em (pg.contains a) with
          | inl pg_contains =>
            rw [pg_contains] at hrl
            have contra := hrl.right
            contradiction
          | inr pg_not_contains =>
            apply Or.inr
            apply Or.inr
            apply Or.inr
            constructor
            simp at pg_not_contains
            apply pg_not_contains
            constructor
            apply a_neq_v
            apply hrr

    intro h
    cases h with
    | inl hll =>
      apply Or.inl
      split
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inl
      rw [hll.right]
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inl
      rw [hll.right]
    | inr hlr => cases hlr with
    | inl hll =>
      apply Or.inl
      split
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inr
      rw [hll.left]
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inr
      rw [hll.left]
    | inr hlr => cases hlr with
    | inl hll =>
      apply Or.inl
      split
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inr
      rw [hll.right]
      assumption
      rw [Std.HashMap.contains_insert]
      simp
      apply Or.inl
      rw [hll.right]
    | inr hlr =>
      apply Or.inr
      split
      rw [Std.HashMap.contains_insert]
      simp
      constructor
      constructor
      intro contra
      apply hlr.right.left
      rw [contra]
      apply hlr.left
      apply hlr.right.right
      constructor
      intro contra
      rw [Std.HashMap.contains_insert] at contra
      simp at contra
      cases contra with
      | inl contra => apply hlr.right.left; rw [contra]
      | inr contra => have contra' := hlr.left; rw [contra'] at contra; contradiction
      apply hlr.right.right

  theorem add_vertex_with_predecessors_getD_semantics_1 (pg : PreGraph A) (v a : A) (vs : List A) (h : pg.contains a ∧ a = v) : (pg.add_vertex_with_predecessors v vs).getD a [] = (pg.predecessors v) ++ vs := by
    unfold add_vertex_with_predecessors
    simp
    rw [add_vertices_getD_semantics]
    rw [← h.right]
    simp [h.left]

  theorem add_vertex_with_predecessors_getD_semantics_2 (pg : PreGraph A) (v a : A) (vs : List A) (h : pg.contains a ∧ a ≠ v) : (pg.add_vertex_with_predecessors v vs).getD a [] = (pg.predecessors a) := by
    unfold add_vertex_with_predecessors
    simp
    rw [add_vertices_getD_semantics]
    split
    rw [Std.HashMap.getD_insert]
    simp
    split
    case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
    unfold predecessors
    rfl
    rw [Std.HashMap.getD_insert]
    simp
    split
    case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
    unfold predecessors
    rfl

  theorem add_vertex_with_predecessors_getD_semantics_3 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ pg.contains a) ∧ a = v) : (pg.add_vertex_with_predecessors v vs).getD a [] = vs := by
    unfold add_vertex_with_predecessors
    simp
    rw [add_vertices_getD_semantics]
    rw [← h.right]
    simp [h.left]

  theorem add_vertex_with_predecessors_getD_semantics_4 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ pg.contains a) ∧ a ≠ v) : (pg.add_vertex_with_predecessors v vs).getD a [] = [] := by
    unfold add_vertex_with_predecessors
    simp
    simp at h
    rw [add_vertices_getD_semantics]
    split
    rw [Std.HashMap.getD_insert]
    simp
    split
    case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
    rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false]
    apply h.left
    rw [Std.HashMap.getD_insert]
    simp
    split
    case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
    rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false]
    apply h.left

  theorem add_vertex_with_predecessors_still_complete (pg : PreGraph A) (v : A) (vs : List A) (pg_is_complete : pg.complete) : (pg.add_vertex_with_predecessors v vs).complete := by
    unfold complete
    unfold predecessors
    intro a ha
    rw [add_vertex_with_predecessors_contains_iff_contains_or_in_new_vertices] at ha
    intro a' ha'
    rw [add_vertex_with_predecessors_contains_iff_contains_or_in_new_vertices]
    cases ha with
    | inl contains_and_eq =>
      rw [add_vertex_with_predecessors_getD_semantics_1 pg v a _ contains_and_eq] at ha'
      rw [List.mem_append_eq] at ha'
      cases ha' with
      | inl ha' =>
        cases Decidable.em (a' = v) with
        | inl hl => apply Or.inl; constructor; apply pg_is_complete; exact contains_and_eq.left; rw [contains_and_eq.right]; apply ha'; exact hl
        | inr hr => apply Or.inr; apply Or.inl; constructor; apply pg_is_complete; exact contains_and_eq.left;  rw [contains_and_eq.right]; apply ha'; exact hr
      | inr ha' =>
        cases Decidable.em (a' = v) with
        | inl hl =>
          cases Decidable.em (pg.contains a') with
          | inl hll => apply Or.inl; constructor; exact hll; exact hl
          | inr hlr => apply Or.inr; apply Or.inr; apply Or.inl; constructor; exact hlr; exact hl
        | inr hr =>
          cases Decidable.em (pg.contains a') with
          | inl hrl => apply Or.inr; apply Or.inl; constructor; exact hrl; exact hr
          | inr hrr => apply Or.inr; apply Or.inr; apply Or.inr; constructor; exact hrr; constructor; exact hr; exact ha'
    | inr rest => cases rest with
    | inl contains_and_neq =>
      rw [add_vertex_with_predecessors_getD_semantics_2 pg v a _ contains_and_neq] at ha'
      cases Decidable.em (a' = v) with
      | inl hl => apply Or.inl; constructor; apply pg_is_complete; exact contains_and_neq.left; apply ha'; exact hl
      | inr hr => apply Or.inr; apply Or.inl; constructor; apply pg_is_complete; exact contains_and_neq.left; apply ha'; exact hr
    | inr rest => cases rest with
    | inl not_contains_and_eq =>
      rw [add_vertex_with_predecessors_getD_semantics_3 pg v a _ not_contains_and_eq] at ha'
      cases Decidable.em (a' = v) with
      | inl hl =>
        cases Decidable.em (pg.contains a') with
        | inl hll => apply Or.inl; constructor; exact hll; exact hl
        | inr hlr => apply Or.inr; apply Or.inr; apply Or.inl; constructor; exact hlr; exact hl
      | inr hr =>
        cases Decidable.em (pg.contains a') with
        | inl hrl => apply Or.inr; apply Or.inl; constructor; exact hrl; exact hr
        | inr hrr => apply Or.inr; apply Or.inr; apply Or.inr; constructor; exact hrr; constructor; exact hr; exact ha'
    | inr not_contains_and_neq =>
      rw [add_vertex_with_predecessors_getD_semantics_4 pg v a _ (⟨not_contains_and_neq.left, not_contains_and_neq.right.left⟩)] at ha'
      contradiction
end PreGraph

abbrev Graph (A: Type u) [DecidableEq A] [Hashable A] := { pg : PreGraph A // pg.complete }

namespace Graph
  variable {A: Type u} [DecidableEq A] [Hashable A]

  def vertices (g : Graph A) : List A := g.val.vertices
  def predecessors (g : Graph A) (a : A) : List A := g.val.predecessors a

  theorem complete (g : Graph A) : ∀ (a:A), a ∈ g.vertices →  ∀ (a':A), a' ∈ g.predecessors a → a' ∈ g.vertices := by
    intro a ha b hb
    unfold vertices
    rw [PreGraph.in_vertices_iff_contains]
    apply g.property
    · rw [← PreGraph.in_vertices_iff_contains]
      apply ha
    · unfold predecessors at hb
      apply hb

  def from_vertices (vs : List A) : Graph A :=
    {
      val := PreGraph.from_vertices vs
      property := by apply PreGraph.from_vertices_is_complete
    }

  def add_vertex_with_predecessors (g : Graph A) (v : A) (vs : List A) : Graph A :=
    {
      val := g.val.add_vertex_with_predecessors v vs
      property := by apply PreGraph.add_vertex_with_predecessors_still_complete; apply g.property
    }

  theorem mem_of_has_pred (G : Graph A) (a b : A) : b ∈ G.predecessors a -> a ∈ G.vertices := by
    intro b_pred
    unfold predecessors at b_pred
    rw [PreGraph.in_predecessors_iff_found] at b_pred
    cases eq : G.val.contains a with
    | false =>
      rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false] at b_pred
      contradiction
      exact eq
    | true =>
      unfold vertices
      rw [PreGraph.in_vertices_iff_contains]
      exact eq

  theorem mem_of_is_pred (G : Graph A) (a b : A) : b ∈ G.predecessors a -> b ∈ G.vertices := by
    intro b_pred
    unfold predecessors at b_pred
    rw [PreGraph.in_predecessors_iff_found] at b_pred
    cases eq : G.val.contains a with
    | false =>
      rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false] at b_pred
      contradiction
      exact eq
    | true =>
      apply complete
      apply mem_of_has_pred
      apply b_pred
      apply b_pred
end Graph
