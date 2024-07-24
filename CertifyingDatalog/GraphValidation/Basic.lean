import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog

abbrev PreGraph (A: Type u) [DecidableEq A] [Hashable A] := Batteries.HashMap A (List A)

namespace PreGraph
  variable {A: Type u} [DecidableEq A] [Hashable A]

  def vertices (g : PreGraph A) : List A := g.toList.map Prod.fst
  def successors (g : PreGraph A) (a : A) : List A := g.findD a []

  def complete (pg: PreGraph A) := ∀ (a:A), pg.contains a →  ∀ (a':A), a' ∈ (pg.successors a) → pg.contains a'

  theorem in_vertices_iff_contains (pg: PreGraph A) (a : A) : a ∈ pg.vertices ↔ pg.contains a := by unfold vertices; apply Batteries.HashMap.in_projection_of_toList_iff_contains
  theorem in_successors_iff_found (pg: PreGraph A) (a : A) : ∀ b, b ∈ pg.successors a ↔ b ∈ (pg.findD a []) := by unfold successors; intros; rfl

  def from_vertices (vs : List A) : PreGraph A := Batteries.HashMap.ofList (vs.map (fun v => (v, [])))

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
        rw [Batteries.HashMap.contains_insert] at hl
        cases Decidable.em (pg.contains v) with
        | inl v_in_pg => apply Or.inl; exact v_in_pg
        | inr v_not_in_pg =>
          cases hl with
          | inl _ => contradiction
          | inr hl => apply Or.inr; constructor; simp at v_not_in_pg; exact v_not_in_pg; apply Or.inl; apply Eq.symm; exact LawfulBEq.eq_of_beq hl
      | inr hr =>
        unfold add_vertex at hr
        split at hr
        apply Or.inr
        constructor
        simp at hr
        exact hr.left
        apply Or.inr
        exact hr.right
        rw [Batteries.HashMap.contains_insert] at hr
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
        rw [Batteries.HashMap.contains_insert]
        apply Or.inl
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
          rw [Batteries.HashMap.contains_insert]
          apply Or.inr
          rw [v_is_u]
          simp
        | inr v_in_us =>
          cases Decidable.em ((pg.add_vertex u).contains v)
          apply Or.inl
          assumption
          apply Or.inr
          constructor
          assumption
          exact v_in_us

  theorem add_vertices_findD_semantics (pg : PreGraph A) (vs : List A) (a : A): (pg.add_vertices vs).findD a [] = pg.findD a [] := by
    induction vs generalizing pg with
    | nil => simp [add_vertices]
    | cons u us ih =>
      simp [add_vertices]
      have ih_plugged_in := ih (pg.add_vertex u)
      unfold add_vertices at ih_plugged_in
      rw [ih_plugged_in]
      unfold add_vertex
      split
      rfl
      rw [Batteries.HashMap.findD_insert]
      assumption

  def add_vertex_with_successors (pg : PreGraph A) (v : A) (vs : List A) : PreGraph A :=
    let pg_with_added_successors := if pg.contains v then pg.insert v ((pg.successors v) ++ vs) else pg.insert v vs
    PreGraph.add_vertices pg_with_added_successors vs

  theorem from_vertices_contains_exactly_the_passed_vertices (vs : List A) : ∀ v, v ∈ (PreGraph.from_vertices vs).vertices ↔ v ∈ vs := by
    unfold vertices
    unfold from_vertices
    intro v
    rw [Batteries.HashMap.in_projection_of_toList_iff_contains, Batteries.HashMap.ofList_mapped_to_pair_contains_iff_list_elem]

  theorem from_vertices_no_vertex_has_successors (vs : List A) : ∀ v, (PreGraph.from_vertices vs).findD v [] = [] := by
    intro needle
    unfold from_vertices
    rw [Batteries.HashMap.findD_ofList_is_list_find_getD]

    induction vs with 
    | nil => simp
    | cons v vs ih => 
      simp
      rw [List.find_concat]

      have : ∀ {α β} (opta optb : Option α) (f : α -> β), (opta.orElse (fun _ => optb)).map f = (opta.map f).orElse (fun _ => (optb.map f)) := by intro _ _ opta optb f; cases opta <;> simp
      rw [this]
      have : ∀ {α} (opta optb : Option α) b, (opta.orElse (fun _ => optb)).getD b = opta.getD (optb.getD b) := by intro _ opta optb b; cases opta <;> simp
      rw [this]
      have : (Option.map Prod.snd (List.find? (fun x => x.1 == needle) [(v, [])])).getD [] = ([] : List A) := by unfold List.find?; simp; split <;> simp
      rw [this]
      apply ih

  theorem from_vertices_is_complete (vs : List A) : (PreGraph.from_vertices vs).complete := by
    let pg := PreGraph.from_vertices vs
    have : ∀ v, pg.findD v [] = [] := by
      intro v
      apply from_vertices_no_vertex_has_successors
    intro a ha b hb
    rw [← in_vertices_iff_contains] at ha
    unfold successors at hb
    rw [this a] at hb
    contradiction

  theorem add_vertex_with_successors_contains_iff_contains_or_in_new_vertices (pg : PreGraph A) (v : A) (vs : List A) : ∀ a, (pg.add_vertex_with_successors v vs).contains a ↔ (pg.contains a ∧ a = v) ∨ (pg.contains a ∧ a ≠ v) ∨ ((¬ pg.contains a) ∧ a = v) ∨ ((¬ pg.contains a) ∧ a ≠ v ∧ a ∈ vs) := by
    unfold add_vertex_with_successors
    simp
    intro a
    rw [add_vertices_contains_iff_contains_or_in_list]
    constructor
    intro h
    cases h with
    | inl hl =>
      split at hl
      case isTrue hl' =>
        rw [Batteries.HashMap.contains_insert] at hl
        cases hl with
        | inl hll =>
          cases Decidable.em (a = v) with
          | inl a_eq_v => apply Or.inl; constructor; exact hll; exact a_eq_v
          | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hll; exact a_neq_v
        | inr hlr =>
          have : v = a := by apply LawfulBEq.eq_of_beq; apply hlr
          apply Or.inl
          constructor
          rw [← this]
          apply hl'
          rw [this]
      case isFalse hr' =>
        rw [Batteries.HashMap.contains_insert] at hl
        cases hl with
        | inl hll =>
          cases Decidable.em (a = v) with
          | inl a_eq_v => apply Or.inl; constructor; exact hll; exact a_eq_v
          | inr a_neq_v => apply Or.inr; apply Or.inl; constructor; exact hll; exact a_neq_v
        | inr hlr =>
          have : v = a := by apply LawfulBEq.eq_of_beq; apply hlr
          apply Or.inr
          apply Or.inr
          apply Or.inl
          constructor
          rw [← this]
          simp at hr'
          apply hr'
          rw [this]
    | inr hr =>
      let ⟨hrl, hrr⟩ := hr
      split at hrl
      case isTrue hl' =>
        rw [Batteries.HashMap.contains_insert] at hrl
        cases Decidable.em (a = v) with
        | inl a_eq_v =>
          apply False.elim
          apply hrl
          apply Or.inr
          rw [a_eq_v]
          simp
        | inr a_neq_v =>
          cases Decidable.em (pg.contains a) with
          | inl pg_contains =>
            apply False.elim
            apply hrl
            apply Or.inl
            rw [pg_contains]
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
        rw [Batteries.HashMap.contains_insert] at hrl
        cases Decidable.em (a = v) with
        | inl a_eq_v =>
          apply False.elim
          apply hrl
          apply Or.inr
          rw [a_eq_v]
          simp
        | inr a_neq_v =>
          cases Decidable.em (pg.contains a) with
          | inl pg_contains =>
            apply False.elim
            apply hrl
            apply Or.inl
            rw [pg_contains]
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
      rw [Batteries.HashMap.contains_insert]
      apply Or.inl
      exact hll.left
      rw [Batteries.HashMap.contains_insert]
      apply Or.inl
      exact hll.left
    | inr hlr => cases hlr with
    | inl hll =>
      apply Or.inl
      split
      rw [Batteries.HashMap.contains_insert]
      apply Or.inl
      exact hll.left
      rw [Batteries.HashMap.contains_insert]
      apply Or.inl
      exact hll.left
    | inr hlr => cases hlr with
    | inl hll =>
      apply Or.inl
      split
      rw [Batteries.HashMap.contains_insert]
      apply Or.inr
      rw [hll.right]
      simp
      rw [Batteries.HashMap.contains_insert]
      apply Or.inr
      rw [hll.right]
      simp
    | inr hlr =>
      apply Or.inr
      split
      rw [Batteries.HashMap.contains_insert]
      constructor
      intro contra
      cases contra
      have : ¬ pg.contains a := by simp [hlr.left]
      contradiction
      case inr v_is_a =>
        have : a = v := by apply Eq.symm; exact LawfulBEq.eq_of_beq v_is_a
        have : a ≠ v := hlr.right.left
        contradiction
      exact hlr.right.right
      rw [Batteries.HashMap.contains_insert]
      constructor
      intro contra
      cases contra
      have : ¬ pg.contains a := by simp [hlr.left]
      contradiction
      case inr v_is_a =>
        have : a = v := by apply Eq.symm; exact LawfulBEq.eq_of_beq v_is_a
        have : a ≠ v := hlr.right.left
        contradiction
      exact hlr.right.right

  theorem add_vertex_with_successors_findD_semantics_1 (pg : PreGraph A) (v a : A) (vs : List A) (h : pg.contains a ∧ a = v) : (pg.add_vertex_with_successors v vs).findD a [] = (pg.successors v) ++ vs := by
    unfold add_vertex_with_successors
    simp
    rw [add_vertices_findD_semantics]
    rw [← h.right]
    simp [h.left]
    rw [Batteries.HashMap.findD_insert']

  theorem add_vertex_with_successors_findD_semantics_2 (pg : PreGraph A) (v a : A) (vs : List A) (h : pg.contains a ∧ a ≠ v) : (pg.add_vertex_with_successors v vs).findD a [] = (pg.successors a) := by
    unfold add_vertex_with_successors
    simp
    rw [add_vertices_findD_semantics]
    split
    rw [Batteries.HashMap.findD_insert'']
    unfold successors
    rfl
    have contra := h.right
    intro contra'
    rw [contra'] at contra
    contradiction
    rw [Batteries.HashMap.findD_insert'']
    unfold successors
    rfl
    have contra := h.right
    intro contra'
    rw [contra'] at contra
    contradiction

  theorem add_vertex_with_successors_findD_semantics_3 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ pg.contains a) ∧ a = v) : (pg.add_vertex_with_successors v vs).findD a [] = vs := by
    unfold add_vertex_with_successors
    simp
    rw [add_vertices_findD_semantics]
    rw [← h.right]
    simp [h.left]
    rw [Batteries.HashMap.findD_insert']

  theorem add_vertex_with_successors_findD_semantics_4 (pg : PreGraph A) (v a : A) (vs : List A) (h : (¬ pg.contains a) ∧ a ≠ v) : (pg.add_vertex_with_successors v vs).findD a [] = [] := by
    unfold add_vertex_with_successors
    simp
    rw [add_vertices_findD_semantics]
    split
    rw [Batteries.HashMap.findD_insert'']
    rw [Batteries.HashMap.findD_is_default_when_not_contains]
    exact h.left
    have contra := h.right
    intro contra'
    rw [contra'] at contra
    contradiction
    rw [Batteries.HashMap.findD_insert'']
    rw [Batteries.HashMap.findD_is_default_when_not_contains]
    exact h.left
    have contra := h.right
    intro contra'
    rw [contra'] at contra
    contradiction

  theorem add_vertex_with_successors_still_complete (pg : PreGraph A) (v : A) (vs : List A) (pg_is_complete : pg.complete) : (pg.add_vertex_with_successors v vs).complete := by
    unfold complete
    unfold successors
    intro a ha
    rw [add_vertex_with_successors_contains_iff_contains_or_in_new_vertices] at ha
    intro a' ha'
    rw [add_vertex_with_successors_contains_iff_contains_or_in_new_vertices]
    cases ha with
    | inl contains_and_eq =>
      rw [add_vertex_with_successors_findD_semantics_1 pg v a _ contains_and_eq] at ha'
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
      rw [add_vertex_with_successors_findD_semantics_2 pg v a _ contains_and_neq] at ha'
      cases Decidable.em (a' = v) with
      | inl hl => apply Or.inl; constructor; apply pg_is_complete; exact contains_and_neq.left; apply ha'; exact hl
      | inr hr => apply Or.inr; apply Or.inl; constructor; apply pg_is_complete; exact contains_and_neq.left; apply ha'; exact hr
    | inr rest => cases rest with
    | inl not_contains_and_eq =>
      rw [add_vertex_with_successors_findD_semantics_3 pg v a _ not_contains_and_eq] at ha'
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
      rw [add_vertex_with_successors_findD_semantics_4 pg v a _ (⟨not_contains_and_neq.left, not_contains_and_neq.right.left⟩)] at ha'
      contradiction
end PreGraph

abbrev Graph (A: Type u) [DecidableEq A] [Hashable A] := { pg : PreGraph A // pg.complete }

namespace Graph
  variable {A: Type u} [DecidableEq A] [Hashable A] 

  def vertices (g : Graph A) : List A := g.val.vertices
  def successors (g : Graph A) (a : A) : List A := g.val.successors a

  theorem complete (g : Graph A) : ∀ (a:A), a ∈ g.vertices →  ∀ (a':A), a' ∈ g.successors a → a' ∈ g.vertices := by
    intro a ha b hb
    unfold vertices
    rw [PreGraph.in_vertices_iff_contains]
    apply g.property
    . rw [← PreGraph.in_vertices_iff_contains]
      apply ha
    . unfold successors at hb
      apply hb

  def from_vertices (vs : List A) : Graph A :=
    {
      val := PreGraph.from_vertices vs
      property := by apply PreGraph.from_vertices_is_complete
    }

  def add_vertex_with_successors (g : Graph A) (v : A) (vs : List A) : Graph A :=
    {
      val := g.val.add_vertex_with_successors v vs
      property := by apply PreGraph.add_vertex_with_successors_still_complete; apply g.property
    }

  theorem mem_of_has_succ (G : Graph A) (a b : A) : b ∈ G.successors a -> a ∈ G.vertices := by 
    intro b_succ
    unfold successors at b_succ
    rw [PreGraph.in_successors_iff_found] at b_succ
    rw [Batteries.HashMap.findD_eq_find?] at b_succ
    cases eq : Batteries.HashMap.find? G.val a with
    | none => simp [eq] at b_succ
    | some _ =>
      unfold vertices
      rw [PreGraph.in_vertices_iff_contains]
      apply Batteries.HashMap.contains_of_find?
      exact eq

  theorem mem_of_is_succ (G : Graph A) (a b : A) : b ∈ G.successors a -> b ∈ G.vertices := by 
    intro b_succ
    unfold successors at b_succ
    rw [PreGraph.in_successors_iff_found] at b_succ
    rw [Batteries.HashMap.findD_eq_find?] at b_succ
    cases eq : Batteries.HashMap.find? G.val a with
    | none => simp [eq] at b_succ
    | some _ =>
      apply complete
      apply mem_of_has_succ
      apply b_succ
      apply b_succ
end Graph
