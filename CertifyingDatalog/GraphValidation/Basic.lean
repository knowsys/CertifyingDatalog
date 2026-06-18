import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog

variable {A: Type u} [DecidableEq A] [Hashable A]

variable (A) in abbrev PreGraph := Std.HashMap A (List A)

namespace PreGraph

  def vertices (g : PreGraph A) : List A := g.keys
  def predecessors (g : PreGraph A) (a : A) : List A := g.getD a []

  def complete (g: PreGraph A) := ∀ a ∈ g, (g.predecessors a).all fun x => x ∈ g
  theorem in_vertices_iff_mem {pg: PreGraph A} {a : A} : a ∈ pg.vertices ↔ a ∈ pg := by
    unfold vertices
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains]

  theorem in_predecessors_iff_found {pg: PreGraph A} {a : A} : ∀ b, b ∈ pg.predecessors a ↔ b ∈ (pg.getD a []) := by
    unfold predecessors; intros; rfl

  def from_vertices (vs : List A) : PreGraph A := Std.HashMap.ofList (vs.map (fun v => (v, [])))

  def add_vertex (pg : PreGraph A) (v : A) : PreGraph A :=
    if v ∈ pg then
      pg
    else
      pg.insert v []

  def add_vertices (pg : PreGraph A) (vs : List A) : PreGraph A :=
    vs.foldl (fun (acc : PreGraph A) u => acc.add_vertex u) pg

  theorem mem_add_vertices_iff_mem_or_in_list {pg : PreGraph A} {vs : List A} : ∀ v, v ∈ (pg.add_vertices vs) ↔ v ∈ pg ∨ (¬ v ∈ pg ∧ v ∈ vs) := by
    induction vs generalizing pg with
    | nil => simp [add_vertices]
    | cons u us ih =>
      simp only [add_vertices, List.foldl_cons, List.mem_cons]
      intro v
      unfold add_vertices at ih
      rw [ih]
      constructor
      · intro h
        cases h with
        | inl hl =>
          unfold add_vertex at hl
          split at hl
          · apply Or.inl
            exact hl
          · rw [Std.HashMap.mem_insert] at hl
            cases Decidable.em (v ∈ pg) with
            | inl v_in_pg => apply Or.inl; exact v_in_pg
            | inr v_not_in_pg =>
              simp only [beq_iff_eq] at hl
              cases hl with
              | inl hl => simp [v_not_in_pg, hl]
              | inr _ => contradiction
        | inr hr =>
          unfold add_vertex at hr
          split at hr
          · apply Or.inr
            constructor
            · exact hr.left
            · apply Or.inr
              exact hr.right
          · rw [Std.HashMap.mem_insert] at hr
            cases Decidable.em (v ∈ pg) with
            | inl v_in_pg => apply Or.inl; exact v_in_pg
            | inr v_not_in_pg => simp [v_not_in_pg, hr]
      · intro h
        cases h with
        | inl hl =>
          apply Or.inl;
          unfold add_vertex
          split
          · exact hl
          · rw [Std.HashMap.mem_insert]
            simp only [beq_iff_eq]
            apply Or.inr
            exact hl
        | inr hr =>
          let ⟨hrl, hrr⟩ := hr
          cases hrr with
          | inl v_is_u =>
            apply Or.inl
            unfold add_vertex
            split
            · case isTrue u_in_pg =>
              apply False.elim; rw [v_is_u] at hrl
              have : ¬ u ∈ pg := by simp [hrl]
              contradiction
            · rw [Std.HashMap.mem_insert]
              simp
              apply Or.inl
              rw [v_is_u]
          | inr v_in_us =>
            cases Decidable.em (v ∈ pg.add_vertex u)
            · apply Or.inl
              assumption
            · apply Or.inr
              constructor
              · assumption
              · exact v_in_us

  theorem add_vertices_getD_semantics (pg : PreGraph A) (vs : List A) (a : A): (pg.add_vertices vs).getD a [] = pg.getD a [] := by
    induction vs generalizing pg with
    | nil => simp [add_vertices]
    | cons u us ih =>
      simp only [add_vertices, List.foldl_cons]
      have ih_plugged_in := ih (pg.add_vertex u)
      unfold add_vertices at ih_plugged_in
      rw [ih_plugged_in]
      unfold add_vertex
      split
      . rfl
      · case isFalse h =>
          rw [Std.HashMap.getD_insert]
          simp only [beq_iff_eq, ite_eq_right_iff, List.nil_eq]
          intro eq
          apply Eq.symm
          rw [Std.HashMap.getD_eq_fallback]
          simp [← eq, h]

  def add_vertex_with_predecessors (pg : PreGraph A) (v : A) (vs : List A) : PreGraph A :=
    let pg_with_added_predecessors := if v ∈ pg then pg.insert v ((pg.predecessors v) ++ vs) else pg.insert v vs
    PreGraph.add_vertices pg_with_added_predecessors vs

  theorem mem_from_vertices_iff_mem (vs : List A) : ∀ v, v ∈ (PreGraph.from_vertices vs).vertices ↔ v ∈ vs := by
    unfold vertices
    unfold from_vertices
    intro v
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_ofList]
    simp

  theorem from_vertices_no_vertex_has_predecessors (vs : List A) : ∀ v, (PreGraph.from_vertices vs).getD v [] = [] := by
    have aux (pg : PreGraph A) (vs : List A) (precond : ∀ needle, pg.getD needle [] = []): ∀ v, (pg.insertMany (vs.map (fun v => (v, [])))).getD v [] = [] := by
      intro needle
      induction vs generalizing pg with
      | nil => simp [precond]
      | cons hd tl ih =>
        rw [List.map_cons, Std.HashMap.insertMany_cons]
        apply ih
        intro needle
        rw [Std.HashMap.getD_insert]
        simp [precond]

    apply aux Std.HashMap.emptyWithCapacity vs
    simp

  theorem from_vertices_is_complete (vs : List A) : (PreGraph.from_vertices vs).complete := by
    have : ∀ v, (PreGraph.from_vertices vs).getD v [] = [] := by
      intro v
      apply from_vertices_no_vertex_has_predecessors
    intro a ha
    simp [predecessors, this a]

  theorem mem_add_vertex_with_predecessors_iff_mem_or_in_new_vertices (pg : PreGraph A) (v : A) (vs : List A) : ∀ a, a ∈ (pg.add_vertex_with_predecessors v vs) ↔ (a ∈ pg ∧ a = v) ∨ (a ∈ pg ∧ a ≠ v) ∨ ((¬ a ∈ pg) ∧ a = v) ∨ ((¬ a ∈ pg) ∧ a ≠ v ∧ a ∈ vs) := by
    unfold add_vertex_with_predecessors
    simp only [ne_eq]
    intro a
    rw [mem_add_vertices_iff_mem_or_in_list]
    constructor
    · intro h
      cases h with
      | inl hl =>
        split at hl
        case isTrue hl' =>
          rw [Std.HashMap.mem_insert] at hl
          simp only [beq_iff_eq] at hl
          cases hl with
          | inl hll =>
            simp [← hll, hl']
          | inr hlr =>
            cases Decidable.em (a = v) with
            | inl a_eq_v => apply Or.inl; constructor; exact hlr; exact a_eq_v
            | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hlr; exact a_neq_v
        case isFalse hr' =>
          rw [Std.HashMap.mem_insert] at hl
          simp only [beq_iff_eq] at hl
          cases hl with
          | inl hll =>
            simp [← hll, hr']
          | inr hlr =>
            cases Decidable.em (a = v) with
            | inl a_eq_v => apply Or.inl; constructor; exact hlr; exact a_eq_v
            | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hlr; exact a_neq_v
      | inr hr =>
        let ⟨hrl, hrr⟩ := hr
        split at hrl
        case isTrue hl' =>
          rw [Std.HashMap.mem_insert] at hrl
          simp only [beq_iff_eq, not_or] at hrl
          cases Decidable.em (a = v) with
          | inl a_eq_v =>
            rw [a_eq_v] at hrl
            have contra := hrl.left
            contradiction
          | inr a_neq_v =>
            cases Decidable.em (a ∈ pg) with
            | inl mem =>
              simp only [mem, true_and, not_true_eq_false, false_and, or_self, or_false]
              have contra := hrl.right
              contradiction
            | inr not_mem =>
              simp [not_mem, a_neq_v, hrr]
        case isFalse hr' =>
          rw [Std.HashMap.mem_insert] at hrl
          simp only [beq_iff_eq, not_or] at hrl
          cases Decidable.em (a = v) with
          | inl a_eq_v =>
            rw [a_eq_v] at hrl
            have contra := hrl.left
            contradiction
          | inr a_neq_v =>
            cases Decidable.em (a ∈ pg) with
            | inl mem =>
              simp only [mem, not_true_eq_false, and_false] at hrl
            | inr not_mem =>
              simp [not_mem, a_neq_v, hrr]
    · intro h
      cases h with
      | inl hll =>
        apply Or.inl
        split
        · rw [Std.HashMap.mem_insert]
          simp only [beq_iff_eq]
          apply Or.inl
          rw [hll.right]
        · rw [Std.HashMap.mem_insert]
          simp only [beq_iff_eq]
          apply Or.inl
          rw [hll.right]
      | inr hlr => cases hlr with
        | inl hll =>
          apply Or.inl
          split
          · rw [Std.HashMap.mem_insert]
            simp only [beq_iff_eq]
            apply Or.inr
            simp [hll.left]
          · rw [Std.HashMap.mem_insert]
            simp only [beq_iff_eq]
            apply Or.inr
            simp [hll.left]
        | inr hlr => cases hlr with
          | inl hll =>
            apply Or.inl
            split
            · rw [Std.HashMap.mem_insert]
              simp only [beq_iff_eq]
              apply Or.inr
              rw [hll.right]
              assumption
            · rw [Std.HashMap.mem_insert]
              simp only [beq_iff_eq]
              apply Or.inl
              rw [hll.right]
          | inr hlr =>
            apply Or.inr
            split
            · rw [Std.HashMap.mem_insert]
              simp
              constructor
              · constructor
                · intro contra
                  apply hlr.right.left
                  rw [contra]
                · apply hlr.left
              · apply hlr.right.right
            · constructor
              · intro contra
                rw [Std.HashMap.mem_insert] at contra
                simp only [beq_iff_eq] at contra
                cases contra with
                | inl contra => apply hlr.right.left; rw [contra]
                | inr contra => have contra' := hlr.left; contradiction
              · apply hlr.right.right

  theorem add_vertex_with_predecessors_getD_semantics_1 (pg : PreGraph A) (v a : A) (vs : List A) (h : a ∈ pg ∧ a = v) : (pg.add_vertex_with_predecessors v vs).getD a [] = (pg.predecessors v) ++ vs := by
    unfold add_vertex_with_predecessors
    simp only
    rw [add_vertices_getD_semantics]
    rw [← h.right]
    simp [h.left]

  theorem add_vertex_with_predecessors_getD_semantics_2 (pg : PreGraph A) (v a : A) (vs : List A) (h : a ∈ pg ∧ a ≠ v) : (pg.add_vertex_with_predecessors v vs).getD a [] = (pg.predecessors a) := by
    unfold add_vertex_with_predecessors
    simp only
    rw [add_vertices_getD_semantics]
    split
    · rw [Std.HashMap.getD_insert]
      simp [beq_iff_eq]
      split
      · case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
      · simp [predecessors]
    · rw [Std.HashMap.getD_insert]
      simp only [beq_iff_eq]
      split
      · case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
      · simp [predecessors]

  theorem add_vertex_with_predecessors_getD_semantics_3 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ a ∈ pg) ∧ a = v) : (pg.add_vertex_with_predecessors v vs).getD a [] = vs := by
    unfold add_vertex_with_predecessors
    simp only
    rw [add_vertices_getD_semantics]
    rw [← h.right]
    simp [h.left]

  theorem add_vertex_with_predecessors_getD_semantics_4 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ a ∈ pg) ∧ a ≠ v) : (pg.add_vertex_with_predecessors v vs).getD a [] = [] := by
    unfold add_vertex_with_predecessors
    simp only
    simp only [ne_eq] at h
    rw [add_vertices_getD_semantics]
    split
    · rw [Std.HashMap.getD_insert]
      simp
      split
      · case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
      · rw [Std.HashMap.getD_eq_fallback]
        apply h.left
    · rw [Std.HashMap.getD_insert]
      simp only [beq_iff_eq]
      split
      · case isTrue eq => have h_right := h.right; rw [eq] at h_right; contradiction
      · rw [Std.HashMap.getD_eq_fallback]
        apply h.left

  theorem add_vertex_with_predecessors_still_complete (pg : PreGraph A) (v : A) (vs : List A) (pg_is_complete : pg.complete) : (pg.add_vertex_with_predecessors v vs).complete := by
    simp [complete] at pg_is_complete
    simp [complete, predecessors]
    intro a ha
    rw [mem_add_vertex_with_predecessors_iff_mem_or_in_new_vertices] at ha
    intro a' ha'
    rw [mem_add_vertex_with_predecessors_iff_mem_or_in_new_vertices]
    cases ha with
    | inl mem_and_eq =>
      rw [add_vertex_with_predecessors_getD_semantics_1 pg v a _ mem_and_eq] at ha'
      rw [List.mem_append] at ha'
      cases ha' with
      | inl ha' =>
        cases Decidable.em (a' = v) with
        | inl hl => simp [hl, mem_and_eq.1, ← mem_and_eq.2]
        | inr hr => rw [mem_and_eq.2] at mem_and_eq
                    simp [hr, pg_is_complete v mem_and_eq.1 a' ha']
      | inr ha' =>
        cases Decidable.em (a' = v) with
        | inl hl =>
          cases Decidable.em (a' ∈ pg) with
          | inl hll => apply Or.inl; constructor; exact hll; exact hl
          | inr hlr => apply Or.inr; apply Or.inr; apply Or.inl; constructor; exact hlr; exact hl
        | inr hr =>
          cases Decidable.em (a' ∈ pg) with
          | inl hrl => apply Or.inr; apply Or.inl; constructor; exact hrl; exact hr
          | inr hrr => apply Or.inr; apply Or.inr; apply Or.inr; constructor; exact hrr; constructor; exact hr; exact ha'
    | inr rest => cases rest with
    | inl mem_and_neq =>
      rw [add_vertex_with_predecessors_getD_semantics_2 pg v a _ mem_and_neq] at ha'
      cases Decidable.em (a' = v) with
      | inl hl => apply Or.inl; constructor; apply pg_is_complete; exact mem_and_neq.left; apply ha'; exact hl
      | inr hr => apply Or.inr; apply Or.inl; constructor; apply pg_is_complete; exact mem_and_neq.left; apply ha'; exact hr
    | inr rest => cases rest with
    | inl not_mem_and_eq =>
      rw [add_vertex_with_predecessors_getD_semantics_3 pg v a _ not_mem_and_eq] at ha'
      cases Decidable.em (a' = v) with
      | inl hl =>
        cases Decidable.em (a' ∈ pg) with
        | inl hll => apply Or.inl; constructor; exact hll; exact hl
        | inr hlr => apply Or.inr; apply Or.inr; apply Or.inl; constructor; exact hlr; exact hl
      | inr hr =>
        cases Decidable.em (a' ∈ pg) with
        | inl hrl => apply Or.inr; apply Or.inl; constructor; exact hrl; exact hr
        | inr hrr => apply Or.inr; apply Or.inr; apply Or.inr; constructor; exact hrr; constructor; exact hr; exact ha'
    | inr not_contains_and_neq =>
      rw [add_vertex_with_predecessors_getD_semantics_4 pg v a _ (⟨not_contains_and_neq.left, not_contains_and_neq.right.left⟩)] at ha'
      contradiction
end PreGraph

variable (A) in abbrev Graph := { pg : PreGraph A // pg.complete }

namespace Graph
  def vertices (g : Graph A) : List A := g.val.vertices
  def predecessors (g : Graph A) (a : A) : List A := g.val.predecessors a

  theorem complete (g : Graph A) : ∀ (a:A), a ∈ g.vertices →  ∀ (a':A), a' ∈ g.predecessors a → a' ∈ g.vertices := by
    intro a ha b hb
    unfold vertices
    rw [PreGraph.in_vertices_iff_mem]
    have := g.property
    simp [PreGraph.complete] at this
    apply this
    · rw [← PreGraph.in_vertices_iff_mem]
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

  theorem mem_of_has_pred {G : Graph A} {a b : A} : b ∈ G.predecessors a -> a ∈ G.vertices := by
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
      rw [PreGraph.in_vertices_iff_mem]
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
