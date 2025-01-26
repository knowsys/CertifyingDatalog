import CertifyingDatalog.Datastructures.List

inductive Tree (A: Type u)
| node: A → List (Tree A) → Tree A

namespace Tree
  variable {A: Type u}

  def member (t1 t2: Tree A): Prop :=
    match t1 with
    | .node _ l => t2 ∈ l

  def elem  [DecidableEq A] (a: A) (t: Tree A): Bool  :=
    match t with
    | .node a' l => (a=a') ∨ List.any l.attach (fun ⟨x, _h⟩ => elem a x)

  def elements (t: Tree A): List A :=
    match t with
    | .node a l => List.foldl (fun x ⟨y,_h⟩ => x ++ elements y) [a] l.attach

  def root: Tree A → A
  | .node a _ => a

  def children: Tree A → List A
  | .node _ l => List.map root l

  def height (t : Tree A): ℕ :=
    match t with
    | .node a l => 1 + (l.attach.map (fun ⟨x, _h⟩ => height x)).max?.getD 0

  lemma height_def (a: A) (l: List (Tree A)): (Tree.node a l).height = 1 + (l.map height).max?.getD 0 :=
  by
    unfold height
    simp

  lemma heightOfMemberIsSmaller (t1 t2: Tree A) (mem: member t1 t2): height t2 < height t1 :=
  by
    cases t1 with
    | node a l =>
      unfold member at mem
      simp only at mem
      rw [height_def]

      cases eq : (l.map height).max? with
      | none => rw [List.max?_eq_none_iff] at eq; simp at eq; rw [eq] at mem; contradiction
      | some max =>
        simp only [Option.getD_some]
        rw [Nat.lt_one_add_iff]
        rw [List.max?_eq_some_iff'] at eq
        apply eq.right
        apply List.mem_map_of_mem
        exact mem

  lemma elem_iff_memElements  [DecidableEq A] (t: Tree A) (a : A) : t.elem a = true ↔ a ∈ t.elements :=
  by
    induction' h' : t.height using Nat.strongRecOn with n ih generalizing t
    cases t with
    | node a' l =>
      unfold elements
      rw [List.foldl_append_mem]
      unfold Tree.elem
      simp only [List.any_eq_true, List.mem_attach, true_and, Subtype.exists, exists_prop,
        Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq, List.mem_singleton]
      constructor
      · intro h
        cases h with
        | inl h =>
          left
          apply h
        | inr h =>
          rcases h with ⟨t', t_l, a_t⟩
          specialize ih t'.height
          have height_t': t'.height < n := by
            rw [← h']
            apply Tree.heightOfMemberIsSmaller
            unfold Tree.member
            simp
            apply t_l
          specialize ih height_t' t'
          right
          use t'
          constructor
          apply t_l
          rw [← ih rfl]
          apply a_t

      · intro h
        cases h with
        | inl h =>
          left
          apply h
        | inr h =>
          rcases h with ⟨t', t_l, a_t⟩
          specialize ih t'.height
          have height_t': t'.height < n := by
            rw [← h']
            apply Tree.heightOfMemberIsSmaller
            unfold Tree.member
            simp only
            apply t_l
          specialize ih height_t' t'
          right
          use t'
          constructor
          · apply t_l
          · rw [ih rfl]
            apply a_t
end Tree
